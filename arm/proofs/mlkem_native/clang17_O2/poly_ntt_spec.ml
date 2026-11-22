(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number-theoretic transform from ML-KEM.                           *)
(* This is the code for mlkem_poly_ntt from mlkem-native's portable C        *)
(* implementation compiled by clang 17 with -O2 (see mlkem_native/README.md), *)
(* verified in the whole image (see libmlkem.ml) with the specification of   *)
(* the gcc 12 -O2 code.                                                      *)
(*                                                                           *)
(* As at gcc 12 -O2, the code is a loop over the 7 layers with a loop over   *)
(* the blocks of the layer inside. In the proofs the layers are numbered     *)
(* l = 0 to 6 in the order in which they are done, so that layer l has 2^l   *)
(* blocks of 2 * len coefficients with len = 2^(7-l), and a block does len   *)
(* butterflies with one zeta. Clang has vectorized the butterflies of a      *)
(* block, except in the last two layers. For len >= 8 (l <= 4) the code of a *)
(* block first checks whether the lower half of the block, from the start    *)
(* of the block, and the upper half, len coefficients further on, may        *)
(* overlap in the address arithmetic. The two ends that it compares are      *)
(* computed with the same arithmetic modulo 2^64, so they are equal, also if *)
(* the block wraps around the end of the address space, and the check always *)
(* succeeds. The code then does the butterflies 8 at a time with 128-bit     *)
(* vectors, in len / 8 iterations. As len is a multiple of 8, the scalar     *)
(* loop that follows the vector loop does nothing, and the code jumps over   *)
(* it. For len = 4 and len = 2 (l = 5, 6) the code takes the scalar loop for *)
(* the whole block. The scalar loop after a failed check and the scalar loop *)
(* after the vector loop are not reached and are not verified.               *)
(*                                                                           *)
(* A Montgomery multiplication by a zeta z, in the vector and in the scalar  *)
(* code, computes the quotient as the high half of t * 3329^-1 * 2^16, with  *)
(* t = x * z, then adds the product of the quotient and -3329 to t and takes *)
(* the high half. The code keeps 3329^-1 * 2^16 and -3329 in X10, X12 and in *)
(* the vector registers Q0 and Q1 for the whole function.                    *)
(*                                                                           *)
(* The code saves X19 to X28 on the stack, with a frame of 80 bytes (the     *)
(* return address in X30 is not changed), where the gcc 12 -O2 code has no   *)
(* frame. It reads the table of zetas from rodata_mlk_zetas and no other     *)
(* read-only data, as at gcc 12 -O2.                                         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/libmlkem.ml";;
needs "common/int_linear.ml";;

let MLKEM_NATIVE_POLY_NTT_CLANG17_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O2_mc
   [layout_range "mlkem_poly_ntt"];;

(* The computation done by the C code, with its 16-bit and 32-bit integer    *)
(* arithmetic, as for gcc 12 -O2. The NTT is done in 7 layers, layer l+1     *)
(* consisting of 2^l blocks of 2^(8-l) consecutive coefficients. A block     *)
(* uses one zeta to do butterflies on pairs of coefficients 2^(7-l) apart,   *)
(* independently.                                                            *)
(* ------------------------------------------------------------------------- *)

let ntt_fqmul_c = define
 `ntt_fqmul_c (z:int16) (y:int16) =
    montred_scalar(word_mul (word_sx y) (word_sx z))`;;

let ntt_block_c = define
 `ntt_block_c (z:int16) start len (m:num->int16) i =
    if start <= i /\ i < start + len
    then word_add (m i) (ntt_fqmul_c z (m(i + len)))
    else if start + len <= i /\ i < start + 2 * len
    then word_sub (m(i - len)) (ntt_fqmul_c z (m i))
    else m i`;;

let ntt_blocks_c = define
 `ntt_blocks_c l 0 (r:num->int16) = r /\
  ntt_blocks_c l (SUC b) r =
    ntt_block_c (iword(EL (2 EXP l + b) mlk_zetas))
                (2 * 2 EXP (7 - l) * b) (2 EXP (7 - l))
                (ntt_blocks_c l b r)`;;

let ntt_layers_c = define
 `ntt_layers_c 0 (x:num->int16) = x /\
  ntt_layers_c (SUC l) x = ntt_blocks_c l (2 EXP l) (ntt_layers_c l x)`;;

(* ------------------------------------------------------------------------- *)
(* Normalization of linear arithmetic on addresses and indices.              *)
(* ------------------------------------------------------------------------- *)

(* Normalize linear natural number expressions: sums of numeral multiples
   of variables and a constant *)
let NTT_LIN_CONV =
  let rec lin tm =
    if is_numeral tm then ([],dest_numeral tm) else
    if is_var tm then ([tm,num_1],num_0) else
    match tm with
      Comb(Comb(Const("+",_),a),b) ->
        let (l1,c1) = lin a and (l2,c2) = lin b in
        let l = itlist (fun (v,k) acc ->
                  if can (assoc v) acc
                  then (v,k +/ assoc v acc)::(filter (fun (w,_) -> w <> v) acc)
                  else (v,k)::acc) l1 l2 in
        (l,c1 +/ c2)
    | Comb(Comb(Const("*",_),a),b) ->
        if is_numeral a then
          let (l,c) = lin b in
          let k = dest_numeral a in (map (fun (v,m) -> (v,k */ m)) l,k */ c)
        else if is_numeral b then
          let (l,c) = lin a in
          let k = dest_numeral b in (map (fun (v,m) -> (v,k */ m)) l,k */ c)
        else failwith "lin"
    | _ -> failwith "lin" in
  fun tm ->
    if type_of tm <> `:num` then failwith "NTT_LIN_CONV" else
    let (l,c) = lin tm in
    let l = filter (fun (_,k) -> k <>/ num_0) l in
    let l = sort (fun (v,_) (w,_) -> fst(dest_var v) < fst(dest_var w)) l in
    let mkt (v,k) = if k = num_1 then v else mk_binop `( * ):num->num->num` (mk_numeral k) v in
    let ts = map mkt l @ (if c <>/ num_0 || l = [] then [mk_numeral c] else []) in
    let nf = List.fold_left (fun acc t -> mk_binop `(+):num->num->num` acc t) (hd ts) (tl ts) in
    if nf = tm then failwith "NTT_LIN_CONV" else
    ARITH_RULE (mk_eq(tm,nf));;

(* ------------------------------------------------------------------------- *)
(* Word and index lemmas, and tactics for the setup of the blocks.           *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Lemmas about the code.                                                    *)
(* ------------------------------------------------------------------------- *)

(*** Splitting off the 8 coefficients of one iteration of the vector loop,
 *** and their addresses relative to those of the two 128-bit loads
 ***)

let RANGE8_SPLIT_STMT =
  `!P i n. 8 * (i + 1) <= n
           ==> ((!j. 8 * i <= j /\ j < n ==> P j) <=>
                (!j. 8 * (i + 1) <= j /\ j < n ==> P j) /\
                (!k. k < 8 ==> P(8 * i + k)))`;;


let RANGE8_SPLIT = assume_spec RANGE8_SPLIT_STMT;;


let NTT_VEC_ADDR_STMT =
  `!a n i k. word_add a (word(2 * (n + (8 * i + k)))):int64 =
             word_add (word_add a (word(2 * n + 16 * i))) (word(2 * k))`;;


let NTT_VEC_ADDR = assume_spec NTT_VEC_ADDR_STMT;;


let NTT_VEC_ADDR2_STMT =
  `!a n l i k. word_add a (word(2 * (n + l + (8 * i + k)))):int64 =
               word_add (word_add a (word(2 * (n + l) + 16 * i)))
                        (word(2 * k))`;;


let NTT_VEC_ADDR2 = assume_spec NTT_VEC_ADDR2_STMT;;


(*** The zeta duplicated in the lanes of a vector, from a W register ***)

let WORD_ZX_ZX_SX_16_STMT =
  `!z:int16. word_zx(word_zx(word_sx z:int32):int64):int16 = z`;;


let WORD_ZX_ZX_SX_16 = assume_spec WORD_ZX_ZX_SX_16_STMT;;


(*** The values of registers computed from small numbers. REG_SMALL_TAC r v
 *** replaces the value of register r in the assumptions by v, proving the
 *** equation as WORD_SMALL_TAC does, but also with shifts right
 ***)

let NTT_DIV8_STMT =
  `!n. (8 * n) DIV 8 = n`;;


let NTT_DIV8 = assume_spec NTT_DIV8_STMT;;


let NTT_SMALL_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SUB_CASES; VAL_WORD_ZX_GEN;
              VAL_WORD; VAL_WORD_SHL; VAL_WORD_USHR;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(MOD_LT_ASM_TAC ORELSE CHANGED_TAC(REWRITE_TAC[NTT_DIV8]) ORELSE
         (COND_CASES_TAC THEN TRY(FIRST_ASSUM(fun th ->
            if is_neg(concl th) then
              (MP_TAC th THEN SIMPLE_ARITH_TAC) else NO_TAC)))) THEN
  SIMPLE_ARITH_TAC;;

let NTT_VAL_LE_64_STMT =
  `!x y. x < 2 EXP 64 /\ y < 2 EXP 64
         ==> ((val(word x:int64) <= val(word y:int64)) <=> x <= y)`;;

let NTT_VAL_LE_64 = assume_spec NTT_VAL_LE_64_STMT;;


let NTT_WORD_OR_1_STMT =
  `!x. EVEN x ==> word_or (word x:int64) (word 1) = word(x + 1)`;;

let NTT_WORD_OR_1 = assume_spec NTT_WORD_OR_1_STMT;;


let NTT_WORD_ADD_NUM_STMT =
  `!x y. word_add (word x:int64) (word y) = word(x + y)`;;

let NTT_WORD_ADD_NUM = assume_spec NTT_WORD_ADD_NUM_STMT;;


(*** Decide the carry flag of a 64-bit comparison of small numbers ***)

let NTT_CF_TAC =
  W(fun (asl,w) ->
    let tms = setify (find_terms
      (can (term_match [] `val(word x:int64) <= val(word y:int64)`))
      (list_mk_conj(map (concl o snd) asl))) in
    MAP_EVERY (fun t ->
      let x = rand(rand(rand(rator t))) and y = rand(rand(rand t)) in
      MP_TAC(SPECL [x;y] NTT_VAL_LE_64) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))]) tms) THEN
  DECIDE_FLAGS_TAC;;

let NTT_WORD_OR_2_STMT =
  `!x. x MOD 4 = 0 ==> word_or (word x:int64) (word 2) = word(x + 2)`;;

let NTT_WORD_OR_2 = assume_spec NTT_WORD_OR_2_STMT;;


(*** Fold word_or of an even number with 1, a multiple of 4 with 2 ***)

let NTT_OR_TAC =
  W(fun (asl,w) ->
    let tms = setify (find_terms
      (fun t -> can (term_match [] `word_or (word x:int64) (word 1)`) t ||
                can (term_match [] `word_or (word x:int64) (word 2)`) t)
      (list_mk_conj(map (concl o snd) asl))) in
    MAP_EVERY (fun t ->
      let x = rand(rand(rator t)) in
      let th = if rand t = `word 1:int64` then NTT_WORD_OR_1 else NTT_WORD_OR_2 in
      MP_TAC(SPEC x th) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[EVEN_MOD; GSYM DIVIDES_MOD] THEN CONV_TAC NUMBER_RULE;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))]) tms);;


let NTT_FOLD_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> is_const t && fst(dest_const t) = "memory")) (concl th)
    then th else REWRITE_RULE[NTT_WORD_ADD_NUM; ADD_CLAUSES] th) THEN NTT_OR_TAC;;


let NTT_CMP_TAC = NTT_FOLD_TAC THEN PTR_DECIDE_FLAGS_TAC THEN NTT_CF_TAC;;


let REG_WORD_TAC r v =
  FIRST_X_ASSUM(fun th ->
    let l,t = dest_eq(concl th) in
    if is_comb l && is_comb(rator l) && rand(rator l) = r
    then SUBGOAL_THEN (mk_eq(t,v)) (fun eth -> ASSUME_TAC(TRANS th eth)) THENL
          [CONV_TAC WORD_RULE; ALL_TAC]
    else failwith "REG_WORD_TAC");;


let NTT_VAL_WORD_64_STMT =
  `!x. x < 2 EXP 64 ==> val(word x:int64) = x`;;

let NTT_VAL_WORD_64 = assume_spec NTT_VAL_WORD_64_STMT;;


(*** Replace val(word x) by x for the small x in the assumptions ***)

let NTT_VAL_TAC =
  W(fun (asl,w) ->
    let tms = setify (find_terms
      (fun t -> can (term_match [] `val(word x:int64)`) t &&
                not(is_numeral(rand(rand t))))
      (list_mk_conj(map (concl o snd) asl))) in
    MAP_EVERY (fun t ->
      let x = rand(rand t) in
      MP_TAC(SPEC x NTT_VAL_WORD_64) THEN
      ANTS_TAC THENL
       [SIMPLE_ARITH_TAC;
        DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))]) tms);;


let REG_NUM_TAC r v =
  FIRST_X_ASSUM(fun th ->
    let l,t = dest_eq(concl th) in
    if is_comb l && is_comb(rator l) && rand(rator l) = r
    then SUBGOAL_THEN (mk_eq(t,v)) (fun eth -> ASSUME_TAC(TRANS th eth)) THENL
          [REWRITE_TAC[WORD_EQ; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
           CONV_TAC NUMBER_RULE; ALL_TAC]
    else failwith "REG_NUM_TAC");;


let ZETA_UXTW_TAC n =
  MP_TAC(SPEC n VAL_WORD_ZX_UXTW) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `mlk_zetas` (concl th)
    then MP_TAC(SPEC n th) else failwith "") THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC];;


(*** A fact about the memory at a block, from the facts at the start ***)

let NTT_MEM_TAC =
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  W(fun (asl,w) ->
    let f = rand(rand w) in
    FIRST_ASSUM(fun th ->
      let c = concl th in
      if is_forall c &&
         (let b = snd(dest_forall c) in
          is_imp b && (let a = lhand b in
                       is_binary "<" a && rand a = `256`))
      then MP_TAC(SPEC f th) else failwith "NTT_MEM_TAC") THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> ASSUME_TAC(CONV_RULE(DEPTH_CONV NTT_LIN_CONV) th)) THEN
    ASM_REWRITE_TAC[]);;


let NTT_SHL1_STMT = `!x. word_shl (word x:int64) 1 = word(2 * x)`;;

let NTT_SHL1 = assume_spec NTT_SHL1_STMT;;


let NTT_FOLD_SHL_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[NTT_SHL1]) THEN NTT_FOLD_TAC THEN
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> is_const t && fst(dest_const t) = "memory")) (concl th)
    then th else CONV_RULE(DEPTH_CONV NTT_LIN_CONV) th);;

let NTT_LANE_STMT =
  `!t:int32.
     word_subword
      (word_add (word_mul (word_ishr (word_mul t (word 4076929024)) 16)
                          (word 4294963967)) t) (16,16):int16 =
     montred_scalar t`;;

let NTT_LANE = assume_spec NTT_LANE_STMT;;


let NTT_LANE_CONV =
  let pat = lhand(snd(strip_forall(concl NTT_LANE))) in
  fun tm -> INSTANTIATE (term_match [] pat tm) (SPEC_ALL NTT_LANE);;

let ntt_norm tm =
  rhs(concl((NUM_REDUCE_CONV THENC DEPTH_CONV NTT_LIN_CONV) tm));;

(*** Merging the memory reads of the vector loop into the 128-bit loads, and
 *** the join of the parts of a block
 ***)

let NTT_MERGE_RULE tm =
  CONV_RULE(DEPTH_CONV NTT_LIN_CONV)
   (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
     (READ_MEMORY_MERGE_CONV 3 tm));;


let NTT_JOIN_FIN_TAC =
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_ARITH_TAC);;


let NTT_WORDS_TAC = REWRITE_TAC[WORD_ADD; WORD_MUL] THEN CONV_TAC WORD_RULE;;

let NIS n = ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_CLANG17_O2_EXEC [n];;


(*** The butterflies of a block, for the lower and the upper half ***)

let NTT_BLOCK_C_LO8_STMT =
  `!z start len m i k.
     8 * (i + 1) <= len /\ k < 8
     ==> ntt_block_c z start len m (start + 8 * i + k) =
         word_add (m(start + 8 * i + k))
                  (ntt_fqmul_c z (m(start + len + 8 * i + k)))`;;

let NTT_BLOCK_C_LO8 = assume_spec NTT_BLOCK_C_LO8_STMT;;

let NTT_BLOCK_C_HI8_STMT =
  `!z start len m i k.
     8 * (i + 1) <= len /\ k < 8
     ==> ntt_block_c z start len m (start + len + 8 * i + k) =
         word_sub (m(start + 8 * i + k))
                  (ntt_fqmul_c z (m(start + len + 8 * i + k)))`;;

let NTT_BLOCK_C_HI8 = assume_spec NTT_BLOCK_C_HI8_STMT;;

(*** The coefficients of a block, from its parts below, inside and above ***)

let NTT_BLOCK_JOIN_STMT =
  `!(P:num->int16) z start len m.
     start + 2 * len <= 256 /\
     (!j. j < start ==> P j = m j) /\
     (!j. start + 2 * len <= j /\ j < 256 ==> P j = m j) /\
     (!j. j < len ==> P(start + j) = ntt_block_c z start len m (start + j)) /\
     (!j. j < len
          ==> P(start + len + j) = ntt_block_c z start len m (start + len + j))
     ==> !i. i < 256 ==> P i = ntt_block_c z start len m i`;;

let NTT_BLOCK_JOIN = assume_spec NTT_BLOCK_JOIN_STMT;;

let NTT_FQMUL_SYM = prove
 (`!z y. ntt_fqmul_c z y = montred_scalar(word_mul (word_sx z) (word_sx y))`,
  REWRITE_TAC[ntt_fqmul_c; WORD_MUL_SYM]);;

(*** The substitution of the parameters of layer l (l = 0 to 6): LEN = 2^(7-l)
 *** butterflies per half block, NBLK = 2^l blocks, NN = LEN / 8 iterations of
 *** the vector loop, LW = l + 1 the value of W13 in the layer
 ***)

let ntt_subst l tm =
  ntt_norm(subst [mk_small_numeral(1 lsl (7 - l)),`LEN:num`;
                  mk_small_numeral(1 lsl l),`NBLK:num`;
                  mk_small_numeral((1 lsl (7 - l)) / 8),`NN:num`;
                  mk_small_numeral(l + 1),`LW:num`;
                  mk_small_numeral l,`LL:num`] tm);;

(*** The statement for one block of layer l: l = 0 to 4 are vector blocks
 *** with len = 2^(7-l) = 8 * NN, l = 5 and 6 scalar blocks. The block starts
 *** at the code of the loop over the blocks and ends at its test.
 ***)

let ntt_block_goal_tm =
  `!a zetas pc b (m:num->int16).
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size); (word zetas,256)] /\
     b < NBLK
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_clang17_O2_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2) /\
               read X0 s = a /\ read X1 s = word(4 * LEN) /\
               read X2 s = word(NBLK + b) /\ read X3 s = word(2 * LEN + 2) /\
               read X4 s = word_neg(word(2 * LEN)) /\
               read X5 s = word_neg(word(2 * LEN)) /\
               read X6 s = word_add a (word(2 * LEN)) /\
               read X7 s = word_add a (word(4 * LEN * b)) /\
               read X8 s = word 1 /\ read X9 s = word 256 /\
               read X10 s = word 4076929024 /\ read X11 s = word zetas /\
               read X12 s = word 4294963967 /\ read X13 s = word LW /\
               read X14 s = word_neg(word(2 * LEN * b)) /\
               read X15 s = word b /\ read X16 s = word(2 * LEN * b) /\
               read X17 s = word LEN /\ read X18 s = word(2 * LEN) /\
               read X19 s = word(2 * LEN * b + 1) /\
               read X20 s = word(2 * LEN * b + LEN) /\
               read Q0 s = word 0xf3010000f3010000f3010000f3010000 /\
               read Q1 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               (!j. j < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * j)))) s =
                        iword(EL j mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        m i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_clang17_O2_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2_test) /\
               read X0 s = a /\ read X1 s = word(4 * LEN) /\
               read X2 s = word(NBLK + b + 1) /\
               read X3 s = word(2 * LEN + 2) /\
               read X4 s = word_neg(word(2 * LEN)) /\
               read X5 s = word_neg(word(2 * LEN)) /\
               read X6 s = word_add a (word(2 * LEN)) /\
               read X7 s = word_add a (word(4 * LEN * (b + 1))) /\
               read X8 s = word 1 /\ read X9 s = word 256 /\
               read X10 s = word 4076929024 /\ read X11 s = word zetas /\
               read X12 s = word 4294963967 /\ read X13 s = word LW /\
               read X14 s = word_neg(word(2 * LEN * (b + 1))) /\
               read X15 s = word(b + 1) /\
               read X16 s = word(2 * LEN * (b + 1)) /\
               read X17 s = word LEN /\ read X18 s = word(2 * LEN) /\
               read X19 s = word(2 * LEN * (b + 1) + 1) /\
               read X20 s = word(2 * LEN * (b + 1) + LEN) /\
               read Q0 s = word 0xf3010000f3010000f3010000f3010000 /\
               read Q1 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               (!j. j < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * j)))) s =
                        iword(EL j mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        ntt_block_c (iword(EL (NBLK + b) mlk_zetas))
                                    (2 * LEN * b) LEN m i))
          (MAYCHANGE [PC; X2; X7; X14; X15; X16; X19; X20; X21; X22; X23;
                      X24; X25; X26; X27; X28] ,,
           MAYCHANGE [Q2; Q3; Q4; Q5] ,, MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,512)])`;;

let ntt_block_goal l = ntt_subst l ntt_block_goal_tm;;

(*** The invariant of the vector loop, after i iterations ***)
let ntt_vblock_inv_tm =
  `\i s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_clang17_O2_mc /\
        read X0 s = a /\ read X1 s = word(4 * LEN) /\
        read X2 s = word(NBLK + b) /\ read X3 s = word(2 * LEN + 2) /\
        read X4 s = word_neg(word(2 * LEN)) /\
        read X5 s = word_neg(word(2 * LEN)) /\
        read X6 s = word_add a (word(2 * LEN)) /\
        read X7 s = word_add a (word(4 * LEN * b)) /\
        read X8 s = word 1 /\ read X9 s = word 256 /\
        read X10 s = word 4076929024 /\ read X11 s = word zetas /\
        read X12 s = word 4294963967 /\ read X13 s = word LW /\
        read X14 s = word_neg(word(2 * LEN * b)) /\
        read X15 s = word b /\ read X16 s = word(2 * LEN * b) /\
        read X17 s = word LEN /\ read X18 s = word(2 * LEN) /\
        read X19 s = word(2 * LEN * b + 1) /\
        read X20 s = word(2 * LEN * b + LEN) /\
        read X22 s = word_zx(word_sx(iword(EL (NBLK + b) mlk_zetas):int16):int32) /\
        read X23 s = word LEN /\ read X25 s = word LEN /\
        read X26 s = word(LEN - 8 * i) /\
        read X27 s = word_add a (word(4 * LEN * b + 16 * i)) /\
        read Q0 s = word 0xf3010000f3010000f3010000f3010000 /\
        read Q1 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        (read ZF s <=> (i = 0 \/ i = NN)) /\
        (!j. j < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * j)))) s =
                 iword(EL j mlk_zetas)) /\
        (!j. j < 2 * LEN * b
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s = m j) /\
        (!j. 2 * LEN * b + 2 * LEN <= j /\ j < 256
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s = m j) /\
        (!j. j < 8 * i
             ==> read(memory :> bytes16(word_add a
                         (word(2 * (2 * LEN * b + j))))) s =
                 ntt_block_c (iword(EL (NBLK + b) mlk_zetas)) (2 * LEN * b) LEN m
                             (2 * LEN * b + j)) /\
        (!j. 8 * i <= j /\ j < LEN
             ==> read(memory :> bytes16(word_add a
                         (word(2 * (2 * LEN * b + j))))) s =
                 m (2 * LEN * b + j)) /\
        (!j. j < 8 * i
             ==> read(memory :> bytes16(word_add a
                         (word(2 * (2 * LEN * b + LEN + j))))) s =
                 ntt_block_c (iword(EL (NBLK + b) mlk_zetas)) (2 * LEN * b) LEN m
                             (2 * LEN * b + LEN + j)) /\
        (!j. 8 * i <= j /\ j < LEN
             ==> read(memory :> bytes16(word_add a
                         (word(2 * (2 * LEN * b + LEN + j))))) s =
                 m (2 * LEN * b + LEN + j))`;;

let ntt_vblock_inv l = ntt_subst l ntt_vblock_inv_tm;;

(*** The invariant of the scalar loop of a block of layers l = 5 and 6
 *** (len = 4, 2) after jj iterations ***)
let ntt_sblock_inv_tm =
  `\jj s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_clang17_O2_mc /\
        read X0 s = a /\ read X1 s = word(4 * LEN) /\
        read X2 s = word(NBLK + b) /\ read X3 s = word(2 * LEN + 2) /\
        read X4 s = word_neg(word(2 * LEN)) /\
        read X5 s = word_neg(word(2 * LEN)) /\
        read X6 s = word_add a (word(2 * LEN)) /\
        read X7 s = word_add a (word(4 * LEN * b)) /\
        read X8 s = word 1 /\ read X9 s = word 256 /\
        read X10 s = word 4076929024 /\ read X11 s = word zetas /\
        read X12 s = word 4294963967 /\ read X13 s = word LW /\
        read X14 s = word_neg(word(2 * LEN * b)) /\
        read X15 s = word b /\ read X16 s = word(2 * LEN * b) /\
        read X17 s = word LEN /\ read X18 s = word(2 * LEN) /\
        read X19 s = word(2 * LEN * b + 1) /\
        read X20 s = word(2 * LEN * b + LEN) /\
        read X21 s = word(2 * LEN * b + LEN) /\
        read X22 s = word_zx(word_sx(iword(EL (NBLK + b) mlk_zetas):int16):int32) /\
        read X24 s = word(2 * LEN * b + jj) /\
        read Q0 s = word 0xf3010000f3010000f3010000f3010000 /\
        read Q1 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        (read CF s <=> jj = LEN) /\
        (!j. j < 128
             ==> read(memory :> bytes16(word_add (word zetas)
                                                 (word(2 * j)))) s =
                 iword(EL j mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 if 2 * LEN * b <= i /\ i < 2 * LEN * b + jj \/
                    2 * LEN * b + LEN <= i /\ i < 2 * LEN * b + LEN + jj
                 then ntt_block_c (iword(EL (NBLK + b) mlk_zetas)) (2 * LEN * b) LEN m i
                 else m i)`;;

let ntt_sblock_inv l = ntt_subst l ntt_sblock_inv_tm;;

(*** The facts for lanes k < 8 of an iteration of the vector loop ***)

let NTT_LOHI_FACTS z start len m i hyp =
  let mk lemma k =
    let th = SPECL [z; start; len; m; i; mk_small_numeral k] lemma in
    let ant = lhand(concl th) in
    let th' = MP th (CONJ hyp (EQT_ELIM(NUM_REDUCE_CONV (rand ant)))) in
    CONV_RULE(DEPTH_CONV NTT_LIN_CONV) th' in
  map (mk NTT_BLOCK_C_LO8) (0--7) @ map (mk NTT_BLOCK_C_HI8) (0--7);;

let NTT_STORE_FACTS_TAC sn =
  let pat = vsubst [mk_var(sn,`:armstate`),`s:armstate`]
    `read (memory :> bytes128 a) s = x` in
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE(ONCE_DEPTH_CONV NTT_LANE_CONV) o
    CONV_RULE(DEPTH_CONV NTT_LIN_CONV) o
    CONV_RULE(TOP_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) o
    REWRITE_RULE[WORD_ZX_ZX_SX_16] o
    CONV_RULE (SIMD_SIMPLIFY_CONV []) o CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (fun th -> can (term_match [] pat) (concl th))));;

let NTT_JOIN_TAC =
  MATCH_MP_TAC NTT_BLOCK_JOIN THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(DEPTH_CONV NTT_LIN_CONV) THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC; NTT_JOIN_FIN_TAC; NTT_JOIN_FIN_TAC; NTT_JOIN_FIN_TAC;
    NTT_JOIN_FIN_TAC];;

(*** The proof of the block lemma for a vector layer l = 0 to 4 ***)

let NTT_VBLOCK_TAC l =
  let len = 1 lsl (7 - l) and nn = 1 lsl (4 - l) and nblk = 1 lsl l in
  let sub t =
    ntt_norm(subst [mk_small_numeral len,`LEN:num`; mk_small_numeral nn,`NN:num`;
                    mk_small_numeral nblk,`NBLK:num`] t) in
  let tm1 = sub `word LEN:int64` in
  let tmzeta = sub `NBLK + b` in
  let eqth = sub `word_add (word_add a (word (4 * LEN * b + 2))) (word (2 * LEN - 2)):int64 = word_add (word_add a (word (2 * LEN))) (word (4 * LEN * b))` in
  let hyp = subst [mk_small_numeral len,`LEN:num`] `8 * (i + 1) <= LEN` in
  let lo_addr = sub `read(memory :> bytes128(word_add a (word(4 * LEN * b + 16 * i)))) s0` in
  let hi_addr = sub `read(memory :> bytes128(word_add a (word(4 * LEN * b + 16 * i + 2 * LEN)))) s0` in
  let facts = NTT_LOHI_FACTS (sub `iword(EL (NBLK + b) mlk_zetas):int16`)
                (sub `2 * LEN * b`) (mk_small_numeral len) `m:num->int16` `i:num`
                (ASSUME hyp) in
  let ilt = sub `i < NN` in
  let icases = MP_TAC(ASSUME ilt) THEN SPEC_TAC(`i:num`,`i:num`) THEN
               CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
               CONV_TAC WORD_REDUCE_CONV THEN TRY(CONV_TAC NUM_REDUCE_CONV) in
  let memtac = REWRITE_TAC[CHUNK8_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
               CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NTT_LIN_CONV) THEN
               ASM_REWRITE_TAC(facts @ [NTT_FQMUL_SYM]) in
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP_TAC (mk_small_numeral nn) `pc + mlkem_poly_ntt_loop3`
   `pc + mlkem_poly_ntt_loop3_back` (ntt_vblock_inv l) THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    (*** From the head of the block to the vector loop ***)

    ENSURES_INIT_TAC "s0" THEN NIS 1 THEN NTT_CMP_TAC THEN NIS 2 THEN NIS 3 THEN
    NTT_FOLD_TAC THEN NIS 4 THEN NIS 5 THEN NTT_CMP_TAC THEN NIS 6 THEN NIS 7 THEN
    NIS 8 THEN NTT_VAL_TAC THEN
    REG_NUM_TAC `X23` tm1 THEN ZETA_UXTW_TAC tmzeta THEN NIS 9 THEN NIS 10 THEN
    NTT_CMP_TAC THEN NIS 11 THEN NIS 12 THEN NTT_CMP_TAC THEN NIS 13 THEN
    NIS 14 THEN NIS 15 THEN NIS 16 THEN NTT_VAL_TAC THEN
    REG_NUM_TAC `X26` tm1 THEN NIS 17 THEN NTT_FOLD_TAC THEN
    MAP_EVERY NIS (18--22) THEN
    SUBGOAL_THEN eqth (fun eqth ->
      NIS 23 THEN
      RULE_ASSUM_TAC(REWRITE_RULE[eqth; LE_REFL; WORD_SUB_REFL; VAL_WORD_0])) THENL
     [NTT_WORDS_TAC; ALL_TAC] THEN
    NIS 24 THEN NIS 25 THEN REG_WORD_TAC `X24` tm1 THEN MAP_EVERY NIS (26--29) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; ADD_CLAUSES] THEN
    REPEAT CONJ_TAC THEN NTT_MEM_TAC;

    (*** The loop body, 8 butterflies at once ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN hyp ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun th ->
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MATCH_MP RANGE8_SPLIT th]) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
       (STRIP_ASSUME_TAC o CONV_RULE(DEPTH_CONV NTT_LIN_CONV) o
        REWRITE_RULE[WORD_ADD_0] o REWRITE_RULE[NTT_VEC_ADDR] o
        REWRITE_RULE[NTT_VEC_ADDR2] o CONV_RULE EXPAND_CASES_CONV)))
     [ASSUME hyp; ASSUME hyp] THEN
    MP_TAC(NTT_MERGE_RULE lo_addr) THEN MP_TAC(NTT_MERGE_RULE hi_addr) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
    MAP_EVERY (fun n ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_CLANG17_O2_EXEC [n] THEN
      SIMD_SIMPLIFY_TAC[]) (1--18) THEN
    NTT_STORE_FACTS_TAC "s18" THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [icases;
      NTT_WORDS_TAC;
      icases;
      memtac;
      memtac];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    (if nn = 1 then ASM_ARITH_TAC else
     ENSURES_INIT_TAC "s0" THEN NIS 1 THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);

    (*** The loop exit and the end of the block ***)

    ENSURES_INIT_TAC "s0" THEN NIS 1 THEN NIS 2 THEN NTT_CMP_TAC THEN
    MAP_EVERY NIS (3--10) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [NTT_SMALL_TAC; NTT_WORDS_TAC; NTT_WORDS_TAC; NTT_WORDS_TAC;
      NTT_WORDS_TAC; NTT_WORDS_TAC; NTT_WORDS_TAC; NTT_JOIN_TAC]];;

(*** The setup of a scalar block (layers l = 5 and 6) up to the scalar loop ***)

let NTT_SSETUP_TAC l =
  let len = 1 lsl (7 - l) in
  let wlen = mk_comb(`word:num->int64`,mk_small_numeral len) in
  let tmzeta = ntt_norm(subst [mk_small_numeral(1 lsl l),`NBLK:num`] `NBLK + b`) in
  ENSURES_INIT_TAC "s0" THEN
  NIS 1 THEN NTT_CMP_TAC THEN NIS 2 THEN NIS 3 THEN NTT_FOLD_TAC THEN NIS 4 THEN
  NIS 5 THEN NTT_CMP_TAC THEN NIS 6 THEN NIS 7 THEN NIS 8 THEN NTT_VAL_TAC THEN
  REG_NUM_TAC `X23` wlen THEN ZETA_UXTW_TAC tmzeta THEN NIS 9 THEN NIS 10 THEN
  NTT_CMP_TAC THEN NIS 11 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `~(a <= i /\ i < a:num)`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;;
let NTT_COND_TAC l =
  let len = 1 lsl (7 - l) in
  let k1 = mk_small_numeral(4*len) and k2 = mk_small_numeral(2*len) in
  let lo = mk_comb(mk_comb(`(+):num->num->num`,mk_comb(mk_comb(`( * ):num->num->num`,k1),`b:num`)),`2 * jj`) in
  let hi = mk_comb(mk_comb(`(+):num->num->num`,k2),lo) in
  let i1 = ntt_norm(subst [mk_small_numeral len,`LEN:num`] `2 * LEN * b + jj`)
  and i2 = ntt_norm(subst [mk_small_numeral len,`LEN:num`] `(2 * LEN * b + LEN) + jj`) in
  let eq1 = ARITH_RULE(mk_eq(mk_comb(mk_comb(`( * ):num->num->num`,`2`),i1),
                             lo)) in
  let eq2 = ARITH_RULE(mk_eq(mk_comb(mk_comb(`( * ):num->num->num`,`2`),i2),
                             hi)) in
  DISCH_THEN(fun th ->
    let c = rand(rator(rator(rhs(concl th)))) in
    SUBGOAL_THEN (mk_neg c) (fun nth ->
      ASSUME_TAC(REWRITE_RULE[eq1; eq2] (REWRITE_RULE[nth] th))) THENL
     [ASM_ARITH_TAC; ALL_TAC]);;

let NTT_SBODY_START_TAC l =
  let len = 1 lsl (7 - l) in
  let i1 = ntt_norm(subst [mk_small_numeral len,`LEN:num`] `2 * LEN * b + jj`)
  and i2 = ntt_norm(subst [mk_small_numeral len,`LEN:num`] `(2 * LEN * b + LEN) + jj`) in
  X_GEN_TAC `jj:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in `m:num->int16` (concl th)
    then MP_TAC(SPEC i1 th) THEN MP_TAC(SPEC i2 th) THEN
         ASSUME_TAC(BETA_RULE(MATCH_MP (SPEC
           (mk_abs(`i:num`, mk_conj(mk_neg(mk_eq(`i:num`,i1)),mk_neg(mk_eq(`i:num`,i2)))))
           (MESON[] `!R P Q. (!i:num. P i ==> Q i)
                             ==> (!i. P i /\ R i ==> Q i)`)) th))
    else failwith "") THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN NTT_COND_TAC l THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN NTT_COND_TAC l;;
(*** Lemmas for the scalar block ***)

let NTT_DROP_REGS_TAC =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),_)),_) -> is_const c
    | Comb(Comb(Const("<=>",_),Comb(Comb(Const("read",_),c),_)),_) -> is_const c
    | _ -> false))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match [] `MAYCHANGE x y z`) (concl th))));;

(*** Normalize the addresses of the stores of the last step ***)
let NTT_NORM_STORES_TAC = RULE_ASSUM_TAC(fun th ->
  match concl th with
    Comb(Comb(Const("=",_),l),_) when can (term_match [] `read (memory :> bytes16 (word_add a (word x))) s`) l ->
      CONV_RULE(LAND_CONV(DEPTH_CONV NTT_LIN_CONV)) th
  | _ -> th);;

let NTT_ZX_ADD_ZX = prove
 (`!lo:int16 x:int32. word_zx(word_add (word_zx lo:int32) x):int16 =
                      word_add lo (word_zx x)`,
  BITBLAST_TAC);;

let NTT_ZX_SUB_ZX = prove
 (`!lo:int16 x:int32. word_zx(word_sub (word_zx lo:int32) x):int16 =
                      word_sub lo (word_zx x)`,
  BITBLAST_TAC);;

let NTT_ZX_USHR_16 = prove
 (`!x:int32. word_zx(word_ushr x 16):int16 = word_subword x (16,16)`,
  BITBLAST_TAC);;

let NTT_MONTRED_ADD = prove
 (`!lo:int16 t:int32.
     word_zx(word_add (word_zx lo:int32)
       (word_ushr (word_add t (word_mul (word_ishr (word_mul t (word 4076929024)) 16)
                                        (word 4294963967))) 16)):int16 =
     word_add lo (montred_scalar t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NTT_ZX_ADD_ZX; NTT_ZX_USHR_16] THEN
  ONCE_REWRITE_TAC[ISPEC `t:int32` WORD_ADD_SYM] THEN
  REWRITE_TAC[NTT_LANE]);;

let NTT_MONTRED_SUB = prove
 (`!lo:int16 t:int32.
     word_zx(word_sub (word_zx lo:int32)
       (word_ushr (word_add t (word_mul (word_ishr (word_mul t (word 4076929024)) 16)
                                        (word 4294963967))) 16)):int16 =
     word_sub lo (montred_scalar t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NTT_ZX_SUB_ZX; NTT_ZX_USHR_16] THEN
  ONCE_REWRITE_TAC[ISPEC `t:int32` WORD_ADD_SYM] THEN
  REWRITE_TAC[NTT_LANE]);;
(*** The body of the scalar loop: one butterfly, jj iterations done ***)

let NTT_SBODY_TAC l =
  let len = 1 lsl (7 - l) in
  let i1 = ntt_norm(subst [mk_small_numeral len,`LEN:num`] `2 * LEN * b + jj`)
  and i2 = ntt_norm(subst [mk_small_numeral len,`LEN:num`] `(2 * LEN * b + LEN) + jj`) in
  NTT_SBODY_START_TAC l THEN
  NIS 1 THEN NTT_FOLD_SHL_TAC THEN NIS 2 THEN NIS 3 THEN NTT_CMP_TAC THEN
  MAP_EVERY NIS (4--14) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  NTT_NORM_STORES_TAC THEN
  CONJ_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC (mk_eq(`i:num`,i1)) THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN CONV_TAC(DEPTH_CONV NTT_LIN_CONV) THEN
    ASM_REWRITE_TAC[] THEN NTT_DROP_REGS_TAC THEN MLKEM_NATIVE_W_SIMP_TAC THEN
    REWRITE_TAC[WORD_ADD_0; NTT_MONTRED_ADD; ntt_block_c; ntt_fqmul_c] THEN
    REPEAT COND_CASES_TAC THEN TRY(ASM_ARITH_TAC) THEN
    REWRITE_TAC[ADD_AC; WORD_ADD_SYM];
    ALL_TAC] THEN
  ASM_CASES_TAC (mk_eq(`i:num`,i2)) THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN CONV_TAC(DEPTH_CONV NTT_LIN_CONV) THEN
    ASM_REWRITE_TAC[] THEN NTT_DROP_REGS_TAC THEN MLKEM_NATIVE_W_SIMP_TAC THEN
    REWRITE_TAC[WORD_ADD_0; NTT_MONTRED_SUB; ntt_block_c; ntt_fqmul_c] THEN
    REPEAT COND_CASES_TAC THEN TRY(ASM_ARITH_TAC) THEN REWRITE_TAC[ADD_SUB];
    ALL_TAC] THEN
  NTT_DROP_REGS_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) && free_in `m:num->int16` (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;;
(*** The proof of the block lemma for a scalar layer l = 5, 6 ***)

let NTT_SBLOCK_TAC l =
  let len = 1 lsl (7 - l) in
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP_TAC (mk_small_numeral len)
   `pc + mlkem_poly_ntt_loop4`
   `pc + mlkem_poly_ntt_loop4_back` (ntt_sblock_inv l) THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;
    NTT_SSETUP_TAC l;
    NTT_SBODY_TAC l;
    X_GEN_TAC `jj:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN NIS 1 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ENSURES_INIT_TAC "s0" THEN MAP_EVERY NIS (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [NTT_SMALL_TAC; NTT_WORDS_TAC; NTT_WORDS_TAC; NTT_WORDS_TAC;
      NTT_WORDS_TAC; NTT_WORDS_TAC; NTT_WORDS_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) && free_in `m:num->int16` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[ntt_block_c] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC];;

let NTT_BLOCK_STMTS = map ntt_block_goal (0--6);;

let NTT_BLOCK_THMS = map assume_spec NTT_BLOCK_STMTS;;

(* ------------------------------------------------------------------------- *)
(* The lemma for one layer.                                                  *)
(* ------------------------------------------------------------------------- *)

(*** The statement of the lemma for layer l (l = 0 to 6), with len = 2^(7-l)
 *** coefficients in each half of a block and 2^l blocks, from the head of
 *** the layer (the code at loop1, with W13 = l + 1) to its end (loop2_exit).
 *** The invariant of the loop over the blocks is that of the block lemma
 *** after b blocks.
 ***)

let ntt_layer_inv_tm =
  let (_,bd) = strip_forall ntt_block_goal_tm in
  let (_,ens) = dest_imp bd in
  let (_,args) = strip_comb ens in
  let p = el 1 args in
  let (s,body) = dest_abs p in
  let cs = filter (fun c -> not(can (find_term (fun t -> t = `PC`)) c))
                  (conjuncts body) in
  let body' = list_mk_conj cs in
  let body'' = subst [`ntt_blocks_c LL b r`,`m:num->int16`] body' in
  mk_abs(`b:num`,mk_abs(s,body''));;

let ntt_layer_inv l = ntt_subst l ntt_layer_inv_tm;;

let ntt_layer_tm =
  `!a zetas pc (r:num->int16).
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size); (word zetas,256)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_clang17_O2_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop1) /\
               read X0 s = a /\ read X8 s = word 1 /\ read X9 s = word 256 /\
               read X10 s = word 4076929024 /\ read X11 s = word zetas /\
               read X12 s = word 4294963967 /\ read X13 s = word LW /\
               read Q0 s = word 0xf3010000f3010000f3010000f3010000 /\
               read Q1 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               (!j. j < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * j)))) s =
                        iword(EL j mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        r i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_clang17_O2_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2_exit) /\
               read X0 s = a /\ read X8 s = word 1 /\ read X9 s = word 256 /\
               read X10 s = word 4076929024 /\ read X11 s = word zetas /\
               read X12 s = word 4294963967 /\ read X13 s = word LW /\
               read Q0 s = word 0xf3010000f3010000f3010000f3010000 /\
               read Q1 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               (!j. j < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * j)))) s =
                        iword(EL j mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        ntt_blocks_c LL NBLK r i))
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X14; X15; X16; X17; X18;
                      X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
           MAYCHANGE [Q2; Q3; Q4; Q5] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,512)])`;;

let ntt_layer_goal l = ntt_subst l ntt_layer_tm;;

(*** The proof of the lemma for layer l, from the block lemmas in
 *** NTT_BLOCK_THMS (indexed by l) ***)

let NTT_LAYER_TAC l =
  let blk = List.nth NTT_BLOCK_THMS l in
  let ltm = mk_small_numeral l in
  let nb = 1 lsl l in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [ltm,`l:num`; `i:num`,`b:num`] (SPEC_ALL(CONJUNCT2 ntt_blocks_c)))) in
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP_TAC (mk_small_numeral nb)
   `pc + mlkem_poly_ntt_loop2`
   `pc + mlkem_poly_ntt_loop2_test` (ntt_layer_inv l) THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    (*** The head of the layer, up to the first block ***)

    ENSURES_INIT_TAC "s0" THEN MAP_EVERY NIS (1--17) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0; CONJUNCT1 ntt_blocks_c;
                WORD_NEG_0; WORD_ADD_0] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN ASM_REWRITE_TAC[];

    (*** One block ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`a:int64`; `zetas:num`; `pc:num`; `i:num`;
                  mk_comb(mk_comb(mk_comb(`ntt_blocks_c`,ltm),`i:num`),`r:num->int16`)]
                 blk) THEN
    ASM_REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
    DISCH_THEN(ENSURES_WEAKEN_TAC) THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[sth] THEN CONV_TAC(DEPTH_CONV NTT_LIN_CONV) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];

    (*** The test between blocks ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    (if nb = 1 then ASM_ARITH_TAC else
     ENSURES_INIT_TAC "s0" THEN NIS 1 THEN NTT_CMP_TAC THEN NTT_VAL_TAC THEN
     NIS 2 THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     COND_CASES_TAC THENL [ASM_ARITH_TAC; REFL_TAC]);

    (*** The exit from the layer ***)

    ENSURES_INIT_TAC "s0" THEN NIS 1 THEN NTT_CMP_TAC THEN NTT_VAL_TAC THEN
    NIS 2 THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];;


let NTT_LAYER_STMTS = map ntt_layer_goal (0--6);;

let NTT_LAYER_THMS = map assume_spec NTT_LAYER_STMTS;;

(* ------------------------------------------------------------------------- *)
(* All the layers.                                                           *)
(* ------------------------------------------------------------------------- *)

(*** All seven layers, from the head of the layer loop for the first layer ***)

let ntt_layers_tm =
  `!a zetas pc (x:num->int16).
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size); (word zetas,256)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_clang17_O2_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop1) /\
               read X0 s = a /\ read X8 s = word 1 /\ read X9 s = word 256 /\
               read X10 s = word 4076929024 /\ read X11 s = word zetas /\
               read X12 s = word 4294963967 /\ read X13 s = word 1 /\
               read Q0 s = word 0xf3010000f3010000f3010000f3010000 /\
               read Q1 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               (!j. j < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * j)))) s =
                        iword(EL j mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i))
          (\s. read PC s = word(pc + mlkem_poly_ntt_loop1_exit) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        ntt_layers_c 7 x i))
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X13; X14; X15; X16; X17;
                      X18; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
           MAYCHANGE [Q2; Q3; Q4; Q5] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,512)])`;;

(*** The assertions of the layer lemma l, with the layer input r replaced ***)

let ntt_layer_states l r_tm =
  let (_,bd) = strip_forall(ntt_layer_goal l) in
  let (_,ens) = dest_imp bd in
  let (_,args) = strip_comb ens in
  let p = el 1 args and q = el 2 args in
  let blocks = mk_comb(mk_comb(mk_comb(`ntt_blocks_c`,mk_small_numeral l),
                               mk_small_numeral(1 lsl l)),`r:num->int16`) in
  let q' = subst [mk_comb(mk_comb(`ntt_layers_c`,mk_small_numeral(l+1)),`x:num->int16`),blocks] q in
  subst [r_tm,`r:num->int16`] p, subst [r_tm,`r:num->int16`] q';;

let ntt_lhead l =
  fst(ntt_layer_states l
       (mk_comb(mk_comb(`ntt_layers_c`,mk_small_numeral l),`x:num->int16`)));;

let ntt_lend l =
  snd(ntt_layer_states l
       (mk_comb(mk_comb(`ntt_layers_c`,mk_small_numeral l),`x:num->int16`)));;

let NTT_LAYER_APPLY_TAC l =
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral l,`l:num`] (SPEC_ALL(CONJUNCT2 ntt_layers_c)))) in
  MP_TAC(SPECL [`a:int64`; `zetas:num`; `pc:num`;
                mk_comb(mk_comb(`ntt_layers_c`,mk_small_numeral l),`x:num->int16`)]
              (List.nth NTT_LAYER_THMS l)) THEN
  ASM_REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(ENSURES_WEAKEN_TAC) THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[CONJUNCT1 ntt_layers_c];
    GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[sth];
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;

(*** From the end of layer l to the head of layer l + 1 or the exit ***)

let NTT_LAYER_BACK_TAC l =
  ENSURES_INIT_TAC "s0" THEN NIS 1 THEN NIS 2 THEN W32_DECIDE_FLAGS_TAC THEN
  NIS 3 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV);;

let NTT_LAYERS_TAC =
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun l ->
    ENSURES_SEQUENCE_TAC `pc + mlkem_poly_ntt_loop2_exit` (ntt_lend l) THEN
    CONJ_TAC THENL [NTT_LAYER_APPLY_TAC l; ALL_TAC] THEN
    if l = 6 then ALL_TAC else
    ENSURES_SEQUENCE_TAC `pc + mlkem_poly_ntt_loop1` (ntt_lhead (l + 1)) THEN
    CONJ_TAC THENL [NTT_LAYER_BACK_TAC l; ALL_TAC]) (0--6) THEN
  NTT_LAYER_BACK_TAC 6;;

let NTT_LAYERS_STMT = ntt_layers_tm;;

let NTT_LAYERS = assume_spec NTT_LAYERS_STMT;;

(* ------------------------------------------------------------------------- *)
(* The computation of the C code gives the NTT.                              *)
(* ------------------------------------------------------------------------- *)

(*** The computation of the C code gives the NTT, within the same bounds as
 *** the hand-written kernel.
 ***)

let NTT_BLOCKS_C_CLOSED_STMT =
  `!l b r i.
     ntt_blocks_c l b r i =
     if i < 2 * 2 EXP (7 - l) * b
     then let z = iword(EL (2 EXP l + i DIV (2 * 2 EXP (7 - l))) mlk_zetas) in
          if i MOD (2 * 2 EXP (7 - l)) < 2 EXP (7 - l)
          then word_add (r i) (ntt_fqmul_c z (r(i + 2 EXP (7 - l))))
          else word_sub (r(i - 2 EXP (7 - l))) (ntt_fqmul_c z (r i))
     else r i`;;

let NTT_BLOCKS_C_CLOSED = assume_spec NTT_BLOCKS_C_CLOSED_STMT;;

let NTT_LAYERS_C_STEP_STMT =
  `!l x i.
     l < 7 /\ i < 256
     ==> ntt_layers_c (SUC l) x i =
         let z = iword(EL (2 EXP l + i DIV (2 * 2 EXP (7 - l))) mlk_zetas) in
         if i MOD (2 * 2 EXP (7 - l)) < 2 EXP (7 - l)
         then word_add (ntt_layers_c l x i)
                       (ntt_fqmul_c z (ntt_layers_c l x (i + 2 EXP (7 - l))))
         else word_sub (ntt_layers_c l x (i - 2 EXP (7 - l)))
                       (ntt_fqmul_c z (ntt_layers_c l x i))`;;

let NTT_LAYERS_C_STEP = assume_spec NTT_LAYERS_C_STEP_STMT;;

let NTT_LAYERS_C_CORRECT_STMT =
  `!x. (!i. i < 256 ==> abs(ival(x i)) <= &8191)
       ==> !i. i < 256
               ==> (ival(ntt_layers_c 7 x i) == forward_ntt (ival o x) i)
                   (mod &3329) /\
                   abs(ival(ntt_layers_c 7 x i)) <= &23594`;;

let NTT_LAYERS_C_CORRECT = assume_spec NTT_LAYERS_C_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_NTT_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a (x:num->int16) pc stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    aligned 16 stackpointer /\
    nonoverlapping (a,512) (word_sub stackpointer (word 80),80) /\
    ALLPAIRS nonoverlapping
     [(a,512); (word_sub stackpointer (word 80),80)]
     [(word pc,libmlkem_size)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_clang17_O2_mc /\
           read PC s = word (pc + mlkem_poly_ntt) /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [a] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = returnaddress /\
           ((!i. i < 256 ==> abs(ival(x i)) <= &8191)
            ==> !i. i < 256
                    ==> let zi =
                          read(memory :> bytes16(word_add a (word(2 * i)))) s
                        in (ival zi == forward_ntt (ival o x) i) (mod &3329) /\
                           abs(ival zi) <= &23594))
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
       MAYCHANGE [memory :> bytes(a,512);
                  memory :> bytes(word_sub stackpointer (word 80),80)])`;;

let MLKEM_NATIVE_POLY_NTT_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_NTT_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(* ------------------------------------------------------------------------- *)
(* The statements for the safety of the blocks and layers.                   *)
(* ------------------------------------------------------------------------- *)

(*** The statement of the safety lemma for one block of layer l ***)

let ntt_block_safe_tm =
  `exists f_ev_blk.
   forall e a zetas pc b sp lr v0 v1 v2 v3 v4 v5 v6 v7 v8 v9.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size); (word zetas,256); (sp,80)] /\
     b < NBLK
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_clang17_O2_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2) /\
               read X0 s = a /\ read X1 s = word(4 * LEN) /\
               read X2 s = word(NBLK + b) /\ read X3 s = word(2 * LEN + 2) /\
               read X4 s = word_neg(word(2 * LEN)) /\
               read X5 s = word_neg(word(2 * LEN)) /\
               read X6 s = word_add a (word(2 * LEN)) /\
               read X7 s = word_add a (word(4 * LEN * b)) /\
               read X8 s = word 1 /\ read X9 s = word 256 /\
               read X11 s = word zetas /\ read X13 s = word LW /\
               read X14 s = word_neg(word(2 * LEN * b)) /\
               read X15 s = word b /\ read X16 s = word(2 * LEN * b) /\
               read X17 s = word LEN /\ read X18 s = word(2 * LEN) /\
               read X19 s = word(2 * LEN * b + 1) /\
               read X20 s = word(2 * LEN * b + LEN) /\
               read SP s = sp /\
               read X30 s = lr /\
               read(memory :> bytes64 sp) s = v0 /\
               read(memory :> bytes64 (word_add sp (word 8))) s = v1 /\
               read(memory :> bytes64 (word_add sp (word 16))) s = v2 /\
               read(memory :> bytes64 (word_add sp (word 24))) s = v3 /\
               read(memory :> bytes64 (word_add sp (word 32))) s = v4 /\
               read(memory :> bytes64 (word_add sp (word 40))) s = v5 /\
               read(memory :> bytes64 (word_add sp (word 48))) s = v6 /\
               read(memory :> bytes64 (word_add sp (word 56))) s = v7 /\
               read(memory :> bytes64 (word_add sp (word 64))) s = v8 /\
               read(memory :> bytes64 (word_add sp (word 72))) s = v9 /\
               read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_clang17_O2_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2_test) /\
               read X0 s = a /\ read X1 s = word(4 * LEN) /\
               read X2 s = word(NBLK + b + 1) /\ read X3 s = word(2 * LEN + 2) /\
               read X4 s = word_neg(word(2 * LEN)) /\
               read X5 s = word_neg(word(2 * LEN)) /\
               read X6 s = word_add a (word(2 * LEN)) /\
               read X7 s = word_add a (word(4 * LEN * (b + 1))) /\
               read X8 s = word 1 /\ read X9 s = word 256 /\
               read X11 s = word zetas /\ read X13 s = word LW /\
               read X14 s = word_neg(word(2 * LEN * (b + 1))) /\
               read X15 s = word (b + 1) /\ read X16 s = word(2 * LEN * (b + 1)) /\
               read X17 s = word LEN /\ read X18 s = word(2 * LEN) /\
               read X19 s = word(2 * LEN * (b + 1) + 1) /\
               read X20 s = word(2 * LEN * (b + 1) + LEN) /\
               read SP s = sp /\
               read X30 s = lr /\
               read(memory :> bytes64 sp) s = v0 /\
               read(memory :> bytes64 (word_add sp (word 8))) s = v1 /\
               read(memory :> bytes64 (word_add sp (word 16))) s = v2 /\
               read(memory :> bytes64 (word_add sp (word 24))) s = v3 /\
               read(memory :> bytes64 (word_add sp (word 32))) s = v4 /\
               read(memory :> bytes64 (word_add sp (word 40))) s = v5 /\
               read(memory :> bytes64 (word_add sp (word 48))) s = v6 /\
               read(memory :> bytes64 (word_add sp (word 56))) s = v7 /\
               read(memory :> bytes64 (word_add sp (word 64))) s = v8 /\
               read(memory :> bytes64 (word_add sp (word 72))) s = v9 /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_blk a zetas pc b /\
                 memaccess_inbounds e2 [a,512; word zetas,256] [a,512])
          (MAYCHANGE [PC; X2; X7; X14; X15; X16; X19; X20; X21; X22; X23;
                      X24; X25; X26; X27; X28] ,,
           MAYCHANGE [Q2; Q3; Q4; Q5] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,512)])`;;

let ntt_block_safe_goal l = ntt_subst l ntt_block_safe_tm;;

let SAFE_ZETA_UXTW_TAC n =
  MP_TAC(SPEC n VAL_WORD_ZX_UXTW) THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC];;

(*** As NTT_FOLD_SHL_TAC, but leaving the assumptions about the events as they are,
 *** so that the events keep the form in which the head of the block put them
 ***)

let NTT_SAFE_FOLD_SHL_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[NTT_SHL1]) THEN NTT_FOLD_TAC THEN
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> (is_const t &&
                                 (fst(dest_const t) = "memory" ||
                                  fst(dest_const t) = "events")) ||
                                t = `e2:(uarch_event)list`)) (concl th)
    then th else CONV_RULE(DEPTH_CONV NTT_LIN_CONV) th);;

(*** The register state at a block head or after jj iterations of the scalar
 *** loop, for the events: the addresses depend on these
 ***)

let ntt_safe_regs_tm =
  `read X0 s = a /\ read X1 s = word(4 * LEN) /\
   read X2 s = word(NBLK + b) /\ read X3 s = word(2 * LEN + 2) /\
   read X4 s = word_neg(word(2 * LEN)) /\
   read X5 s = word_neg(word(2 * LEN)) /\
   read X6 s = word_add a (word(2 * LEN)) /\
   read X7 s = word_add a (word(4 * LEN * b)) /\
   read X8 s = word 1 /\ read X9 s = word 256 /\
   read X11 s = word zetas /\ read X13 s = word LW /\
   read X14 s = word_neg(word(2 * LEN * b)) /\
   read X15 s = word b /\ read X16 s = word(2 * LEN * b) /\
   read X17 s = word LEN /\ read X18 s = word(2 * LEN) /\
   read X19 s = word(2 * LEN * b + 1) /\
   read X20 s = word(2 * LEN * b + LEN)`;;

let ntt_safe_sinv_tm =
  `\jj s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_clang17_O2_mc /\
        read X0 s = a /\ read X1 s = word(4 * LEN) /\
        read X2 s = word(NBLK + b) /\ read X3 s = word(2 * LEN + 2) /\
        read X4 s = word_neg(word(2 * LEN)) /\
        read X5 s = word_neg(word(2 * LEN)) /\
        read X6 s = word_add a (word(2 * LEN)) /\
        read X7 s = word_add a (word(4 * LEN * b)) /\
        read X8 s = word 1 /\ read X9 s = word 256 /\
        read X11 s = word zetas /\ read X13 s = word LW /\
        read X14 s = word_neg(word(2 * LEN * b)) /\
        read X15 s = word b /\ read X16 s = word(2 * LEN * b) /\
        read X17 s = word LEN /\ read X18 s = word(2 * LEN) /\
        read X19 s = word(2 * LEN * b + 1) /\
        read X20 s = word(2 * LEN * b + LEN) /\
        read X21 s = word(2 * LEN * b + LEN) /\
        read X24 s = word(2 * LEN * b + jj) /\
        read SP s = sp /\
               read X30 s = lr /\
               read(memory :> bytes64 sp) s = v0 /\
               read(memory :> bytes64 (word_add sp (word 8))) s = v1 /\
               read(memory :> bytes64 (word_add sp (word 16))) s = v2 /\
               read(memory :> bytes64 (word_add sp (word 24))) s = v3 /\
               read(memory :> bytes64 (word_add sp (word 32))) s = v4 /\
               read(memory :> bytes64 (word_add sp (word 40))) s = v5 /\
               read(memory :> bytes64 (word_add sp (word 48))) s = v6 /\
               read(memory :> bytes64 (word_add sp (word 56))) s = v7 /\
               read(memory :> bytes64 (word_add sp (word 64))) s = v8 /\
               read(memory :> bytes64 (word_add sp (word 72))) s = v9`;;

let ntt_safe_sinv l = ntt_subst l ntt_safe_sinv_tm;;

let NTT_SBLOCK_SAFE_TAC l =
  let len = 1 lsl (7 - l) in
  let lenw = mk_small_numeral len in
  let tmpl = subst [lenw,`LEN:num`]
   `\(a:int64) (zetas:num) (pc:num) (b:num).
      APPEND (f_ev_exit a zetas pc b)
        (APPEND (ENUMERATEL LEN (\j. f_ev_loop a zetas pc b j))
                (f_ev_setup a zetas pc b)) :(uarch_event)list` in
  let kz = ntt_subst l `NBLK + b` in
  let wlen = mk_comb(`word:num->int64`,lenw) in
  let cnd = ntt_subst l `(2 * LEN * b + i) + 1 < 2 * LEN * b + LEN` in
  let cnd' = subst [lenw,`LEN:num`] `i + 1 < LEN` in
  CONCRETIZE_F_EVENTS_TAC tmpl THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC lenw `pc + mlkem_poly_ntt_loop4`
   `pc + mlkem_poly_ntt_loop4_exit` (ntt_safe_sinv l) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The head of the block, to the scalar loop ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    NIS 1 THEN NTT_CMP_TAC THEN NIS 2 THEN NIS 3 THEN NTT_FOLD_TAC THEN
    NIS 4 THEN NIS 5 THEN NTT_CMP_TAC THEN NIS 6 THEN NIS 7 THEN NIS 8 THEN
    NTT_VAL_TAC THEN REG_NUM_TAC `X23` wlen THEN
    SAFE_ZETA_UXTW_TAC kz THEN NIS 9 THEN NIS 10 THEN NTT_CMP_TAC THEN
    NIS 11 THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    NIS 1 THEN NTT_SAFE_FOLD_SHL_TAC THEN NIS 2 THEN NIS 3 THEN NTT_CMP_TAC THEN
    MAP_EVERY NIS (4--15) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN (mk_eq(cnd,cnd')) (fun th -> REWRITE_TAC[th]) THENL
     [ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The exit and the end of the block ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    MAP_EVERY NIS (1--8) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [NTT_SMALL_TAC; NTT_WORDS_TAC; NTT_WORDS_TAC; NTT_WORDS_TAC;
      NTT_WORDS_TAC; NTT_WORDS_TAC; NTT_WORDS_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC];;

(*** The vector loop: the registers after i iterations ***)

let ntt_safe_vinv_tm =
  `\i s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_clang17_O2_mc /\
        read X0 s = a /\ read X1 s = word(4 * LEN) /\
        read X2 s = word(NBLK + b) /\ read X3 s = word(2 * LEN + 2) /\
        read X4 s = word_neg(word(2 * LEN)) /\
        read X5 s = word_neg(word(2 * LEN)) /\
        read X6 s = word_add a (word(2 * LEN)) /\
        read X7 s = word_add a (word(4 * LEN * b)) /\
        read X8 s = word 1 /\ read X9 s = word 256 /\
        read X11 s = word zetas /\ read X13 s = word LW /\
        read X14 s = word_neg(word(2 * LEN * b)) /\
        read X15 s = word b /\ read X16 s = word(2 * LEN * b) /\
        read X17 s = word LEN /\ read X18 s = word(2 * LEN) /\
        read X19 s = word(2 * LEN * b + 1) /\
        read X20 s = word(2 * LEN * b + LEN) /\
        read X23 s = word LEN /\ read X25 s = word LEN /\
        read X26 s = word(LEN - 8 * i) /\
        read X27 s = word_add a (word(4 * LEN * b + 16 * i)) /\
        read SP s = sp /\
               read X30 s = lr /\
               read(memory :> bytes64 sp) s = v0 /\
               read(memory :> bytes64 (word_add sp (word 8))) s = v1 /\
               read(memory :> bytes64 (word_add sp (word 16))) s = v2 /\
               read(memory :> bytes64 (word_add sp (word 24))) s = v3 /\
               read(memory :> bytes64 (word_add sp (word 32))) s = v4 /\
               read(memory :> bytes64 (word_add sp (word 40))) s = v5 /\
               read(memory :> bytes64 (word_add sp (word 48))) s = v6 /\
               read(memory :> bytes64 (word_add sp (word 56))) s = v7 /\
               read(memory :> bytes64 (word_add sp (word 64))) s = v8 /\
               read(memory :> bytes64 (word_add sp (word 72))) s = v9`;;

let ntt_safe_vinv l = ntt_subst l ntt_safe_vinv_tm;;

let NTT_VSAFE_FRAME_TAC l =
  let nn = 1 lsl (4 - l) in
  let nnw = mk_small_numeral nn in
  let tmpl = subst [nnw,`NN:num`]
   `\(a:int64) (zetas:num) (pc:num) (b:num).
      APPEND (f_ev_exit a zetas pc b)
        (APPEND (ENUMERATEL NN (\i. f_ev_loop a zetas pc b i))
                (f_ev_setup a zetas pc b)) :(uarch_event)list` in
  CONCRETIZE_F_EVENTS_TAC tmpl THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC nnw `pc + mlkem_poly_ntt_loop3`
   `pc + mlkem_poly_ntt_loop3_exit` (ntt_safe_vinv l);;

let NTT_VSAFE_SETUP_TAC l =
  let len = 1 lsl (7 - l) in
  let lenw = mk_small_numeral len in
  let wlen = mk_comb(`word:num->int64`,lenw) in
  let kz = ntt_subst l `NBLK + b` in
  let eqth = ntt_subst l `word_add (word_add a (word (4 * LEN * b + 2))) (word (2 * LEN - 2)):int64 = word_add (word_add a (word (2 * LEN))) (word (4 * LEN * b))` in
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  NIS 1 THEN NTT_CMP_TAC THEN NIS 2 THEN NIS 3 THEN NTT_FOLD_TAC THEN NIS 4 THEN
  NIS 5 THEN NTT_CMP_TAC THEN NIS 6 THEN NIS 7 THEN NIS 8 THEN NTT_VAL_TAC THEN
  REG_NUM_TAC `X23` wlen THEN SAFE_ZETA_UXTW_TAC kz THEN NIS 9 THEN NIS 10 THEN
  NTT_CMP_TAC THEN NIS 11 THEN NIS 12 THEN NTT_CMP_TAC THEN NIS 13 THEN
  NIS 14 THEN NIS 15 THEN NIS 16 THEN NTT_VAL_TAC THEN
  REG_NUM_TAC `X26` wlen THEN NIS 17 THEN NTT_FOLD_TAC THEN
  MAP_EVERY NIS (18--22) THEN
  SUBGOAL_THEN eqth (fun eqth ->
    NIS 23 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[eqth; LE_REFL; WORD_SUB_REFL; VAL_WORD_0])) THENL
   [NTT_WORDS_TAC; ALL_TAC] THEN
  NIS 24 THEN NIS 25 THEN REG_WORD_TAC `X24` wlen THEN MAP_EVERY NIS (26--29) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0; WORD_ADD_0] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let NTT_VSAFE_BODY_TAC l =
  let flagc = ntt_subst l `~(val(word_sub (word (LEN - 8 * i)) (word 8):int64) = 0) <=> i + 1 < NN` in
  let ilt = ntt_subst l `i < NN` in
  let icases = MP_TAC(ASSUME ilt) THEN SPEC_TAC(`i:num`,`i:num`) THEN
               CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
               CONV_TAC WORD_REDUCE_CONV THEN TRY(CONV_TAC NUM_REDUCE_CONV) THEN
               REWRITE_TAC[] in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY NIS (1--19) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN flagc SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM WORD_SUB; VAL_WORD; DIMINDEX_64] THEN
    NTT_SMALL_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [icases; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let NTT_VSAFE_EXIT_TAC l =
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY NIS (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [NTT_SMALL_TAC; NTT_WORDS_TAC; NTT_WORDS_TAC; NTT_WORDS_TAC;
    NTT_WORDS_TAC; NTT_WORDS_TAC; NTT_WORDS_TAC; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let NTT_VBLOCK_SAFE_TAC l =
  NTT_VSAFE_FRAME_TAC l THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC; NTT_VSAFE_SETUP_TAC l; NTT_VSAFE_BODY_TAC l;
    NTT_VSAFE_EXIT_TAC l];;

(*** The events of the blocks of each layer ***)

let NTT_BLOCK_SAFE_STMTS = map ntt_block_safe_goal (0--6);;

let NTT_BLOCK_SAFE_THMS = map assume_spec NTT_BLOCK_SAFE_STMTS;;

let NTT_BLOCK_EVENTS =
  map (fun l ->
        new_specification ["ntt_clang17_O2_block_events_" ^ string_of_int l]
                          (el l NTT_BLOCK_SAFE_THMS)) (0--6);;


(*** The registers at the head of block b of layer l, for the layer lemma ***)

let ntt_safe_linv_tm =
  let (_,bd) = strip_forall(snd(dest_exists(ntt_block_safe_tm))) in
  let (_,ens) = dest_imp bd in
  let (_,args) = strip_comb ens in
  let p = el 1 args in
  let (s,body) = dest_abs p in
  let cs = filter (fun c -> not(can (find_term (fun t -> t = `PC`)) c) &&
                            not(can (find_term (fun t -> t = `events`)) c))
                  (conjuncts body) in
  mk_abs(`b:num`,mk_abs(s,list_mk_conj cs));;

let ntt_safe_linv l = ntt_subst l ntt_safe_linv_tm;;

(*** The statement of the safety lemma for layer l ***)

let ntt_layer_safe_tm =
  `exists f_ev_lay.
   forall e a zetas pc sp lr v0 v1 v2 v3 v4 v5 v6 v7 v8 v9.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size); (word zetas,256); (sp,80)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_clang17_O2_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop1) /\
               read X0 s = a /\ read X8 s = word 1 /\ read X9 s = word 256 /\
               read X11 s = word zetas /\ read X13 s = word LW /\
               read SP s = sp /\
               read X30 s = lr /\
               read(memory :> bytes64 sp) s = v0 /\
               read(memory :> bytes64 (word_add sp (word 8))) s = v1 /\
               read(memory :> bytes64 (word_add sp (word 16))) s = v2 /\
               read(memory :> bytes64 (word_add sp (word 24))) s = v3 /\
               read(memory :> bytes64 (word_add sp (word 32))) s = v4 /\
               read(memory :> bytes64 (word_add sp (word 40))) s = v5 /\
               read(memory :> bytes64 (word_add sp (word 48))) s = v6 /\
               read(memory :> bytes64 (word_add sp (word 56))) s = v7 /\
               read(memory :> bytes64 (word_add sp (word 64))) s = v8 /\
               read(memory :> bytes64 (word_add sp (word 72))) s = v9 /\
               read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_clang17_O2_mc /\
               read PC s = word(pc + mlkem_poly_ntt_loop2_exit) /\
               read X0 s = a /\ read X8 s = word 1 /\ read X9 s = word 256 /\
               read X11 s = word zetas /\ read X13 s = word LW /\
               read SP s = sp /\
               read X30 s = lr /\
               read(memory :> bytes64 sp) s = v0 /\
               read(memory :> bytes64 (word_add sp (word 8))) s = v1 /\
               read(memory :> bytes64 (word_add sp (word 16))) s = v2 /\
               read(memory :> bytes64 (word_add sp (word 24))) s = v3 /\
               read(memory :> bytes64 (word_add sp (word 32))) s = v4 /\
               read(memory :> bytes64 (word_add sp (word 40))) s = v5 /\
               read(memory :> bytes64 (word_add sp (word 48))) s = v6 /\
               read(memory :> bytes64 (word_add sp (word 56))) s = v7 /\
               read(memory :> bytes64 (word_add sp (word 64))) s = v8 /\
               read(memory :> bytes64 (word_add sp (word 72))) s = v9 /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_lay a zetas pc /\
                 memaccess_inbounds e2 [a,512; word zetas,256] [a,512])
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X14; X15; X16; X17; X18;
                      X19; X20; X21; X22; X23; X24; X25; X26; X27; X28] ,,
           MAYCHANGE [Q2; Q3; Q4; Q5] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,512)])`;;

let ntt_layer_safe_goal l = ntt_subst l ntt_layer_safe_tm;;

let ntt_layer_safe_template l =
  let nbw = mk_small_numeral(1 lsl l) in
  let blk = mk_const("ntt_clang17_O2_block_events_" ^ string_of_int l,[]) in
  let a = `a:int64` and zetas = `zetas:num` and pc = `pc:num` and i = `i:num` in
  let app x y = list_mk_icomb "APPEND" [x;y]
  and fev nm args =
    list_mk_comb(mk_var(nm,itlist (mk_fun_ty o type_of) args
                                 `:(uarch_event)list`),args) in
  let body =
    app `[]:(uarch_event)list`
     (app (mk_icomb(mk_icomb(`ENUMERATEL:num->(num->(uarch_event)list)->
                                       (uarch_event)list`,nbw),
           mk_abs(i,app (fev "f_ev_ltest" [a;zetas;pc;i])
                        (list_mk_comb(blk,[a;zetas;pc;i])))))
        (fev "f_ev_lhead" [a;zetas;pc])) in
  list_mk_abs([a;zetas;pc],body);;

(*** The test between the blocks, with the flags decided from the index ***)

let NTT_LSAFE_TEST_TAC l =
  let nbw = mk_small_numeral(1 lsl l) in
  let want = subst [nbw,`NBLK:num`] `i + 1 < NBLK` in
  let cnd = ntt_subst l `256 <= 2 * LEN * (i + 1)` in
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  NIS 1 THEN NTT_CMP_TAC THEN NTT_VAL_TAC THEN NIS 2 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV NTT_LIN_CONV) THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN (mk_eq(cnd,mk_neg want)) SUBST_ALL_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
                  ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let NTT_LAYER_SAFE_TAC l =
  let nbw = mk_small_numeral(1 lsl l) in
  let linv = ntt_safe_linv l in
  let ev_inst ev = SPECL ([ev; `a:int64`; `zetas:num`; `pc:num`; `i:num`; `sp:int64`; `lr:int64`] @
                          map (fun k -> mk_var("v" ^ string_of_int k,`:int64`)) (0--9))
                         (el l NTT_BLOCK_EVENTS) in
  let mid = rand(concl((BETA_CONV THENC DEPTH_CONV NTT_LIN_CONV)(mk_comb(linv,`i + 1`)))) in
  CONCRETIZE_F_EVENTS_TAC (ntt_layer_safe_template l) THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC nbw `pc + mlkem_poly_ntt_loop2`
   `pc + mlkem_poly_ntt_loop2_exit` linv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The head of the layer ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    MAP_EVERY NIS (1--17) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0; WORD_NEG_0; WORD_ADD_0] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** One block and the test after it ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ENUMERATEL_ADD1] THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_ntt_loop2_test` mid THEN
    CONJ_TAC THENL [EVENTS_LEMMA_TAC ev_inst; NTT_LSAFE_TEST_TAC l];

    (*** The exit ***)

    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[APPEND; APPEND_NIL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND; APPEND_NIL]) THEN FIRST_X_ASSUM ACCEPT_TAC];;

let NTT_LAYER_SAFE_STMTS = map ntt_layer_safe_goal (0--6);;

let NTT_LAYER_SAFE_THMS = map assume_spec NTT_LAYER_SAFE_STMTS;;

let NTT_LAYER_EVENTS =
  map (fun l ->
        new_specification ["ntt_clang17_O2_layer_events_" ^ string_of_int l]
                          (el l NTT_LAYER_SAFE_THMS)) (0--6);;


(*** The events of the whole code, as the events of the frame and the
 *** constants, the layers with the code between them, and the return. The
 *** stack pointer after the frame is allocated is the parameter sp.
 ***)

let ntt_top_template =
  let lay l = list_mk_comb
   (mk_const("ntt_clang17_O2_layer_events_" ^ string_of_int l,[]),
    [`a:int64`; `pc + rodata_mlk_zetas`; `pc:num`])
  and fev nm =
    list_mk_comb
     (mk_var(nm,`:int64->num->int64->int64->(uarch_event)list`),
      [`a:int64`;`pc:num`;`sp:int64`;`returnaddress:int64`]) in
  let app x y = list_mk_icomb "APPEND" [x;y] in
  let rec chain l acc =
    if l = 7 then acc else
    let acc' = app (lay l) acc in
    chain (l + 1)
      (if l = 6 then acc' else app (fev ("f_ev_back" ^ string_of_int l)) acc') in
  let start = fev "f_ev_setup" in
  list_mk_abs([`a:int64`;`pc:num`;`sp:int64`;`returnaddress:int64`],
              app (fev "f_ev_fin") (chain 0 start));;

(*** The stack after the frame is allocated, and the states between the
 *** pieces
 ***)

let ntt_safe_stack_tm =
  let slot k v =
    if k = 0 then
      subst [v,`V:int64`]
       `read(memory :> bytes64 stackpointer) s = V`
    else
      subst [v,`V:int64`; mk_small_numeral(8 * k),`K:num`]
       `read(memory :> bytes64(word_add stackpointer (word K))) s = V` in
  let vals = [`x28_init:int64`; `x27_init:int64`; `x26_init:int64`;
              `x25_init:int64`; `x24_init:int64`; `x23_init:int64`;
              `x22_init:int64`; `x21_init:int64`; `x20_init:int64`;
              `x19_init:int64`] in
  list_mk_conj(`read SP s = stackpointer` ::
               map2 slot (0--9) vals);;

let ntt_safe_layer_tm l =
  mk_abs(`s:armstate`,
    list_mk_conj
     [subst [mk_small_numeral(l + 1),`L:num`]
        `read X0 s = a /\ read X8 s = word 1 /\ read X9 s = word 256 /\
         read X11 s = word(pc + rodata_mlk_zetas) /\ read X13 s = word L /\
         read X30 s = returnaddress`;
      ntt_safe_stack_tm]);;

let ntt_layer_events_inst l ev =
  SPECL ([ev; `a:int64`; `pc + rodata_mlk_zetas`; `pc:num`;
          `stackpointer:int64`; `returnaddress:int64`;
          `x28_init:int64`; `x27_init:int64`; `x26_init:int64`;
          `x25_init:int64`; `x24_init:int64`; `x23_init:int64`;
          `x22_init:int64`; `x21_init:int64`; `x20_init:int64`;
          `x19_init:int64`])
        (el l NTT_LAYER_EVENTS);;

(*** The events of a lemma are in bounds for the regions of the whole code ***)

let MEMACCESS_WIDEN_TAC =
  FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Comb(Const("memaccess_inbounds",_),e),rr),wr) ->
        (fun (asl,w) ->
          match w with
            Comb(Comb(Comb(Const("memaccess_inbounds",_),e'),rr'),wr')
            when e' = e ->
              (MP_TAC(ISPECL [e;rr;rr';wr;wr'] MEMACCESS_INBOUNDS_MEM) THEN
               REWRITE_TAC[ALL; MEM] THEN DISCH_THEN MATCH_MP_TAC THEN
               ACCEPT_TAC th) (asl,w)
          | _ -> failwith "MEMACCESS_WIDEN_TAC")
    | _ -> failwith "MEMACCESS_WIDEN_TAC");;

(*** Simulation of a short piece of straight-line code with flags ***)

let NTT_SAFE_SIM_TAC n =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY (fun i ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_CLANG17_O2_EXEC [i] THEN
    MLKEM_NATIVE_ADRP_TAC THEN TRY W32_DECIDE_FLAGS_TAC) (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let NTT_SAFE_SETUP_TAC =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY (fun i ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_CLANG17_O2_EXEC [i] THEN
    MLKEM_NATIVE_ADRP_TAC) (1--15) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; DISCHARGE_SAFETY_PROPERTY_TAC];;

let NTT_SAFE_TOP_TAC =
  CONCRETIZE_F_EVENTS_TAC ntt_top_template THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `nonoverlapping_modulo (2 EXP 64) (val (a:int64),512) (pc + 45920,256)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2 EXP 64`; `val(a:int64)`; `512`; `pc:num`; `46176`;
                   `val(a:int64)`; `512`; `pc + 45920`; `256`]
            NONOVERLAPPING_MODULO_SUBREGIONS) THEN
    ASM_REWRITE_TAC[CONTAINED_MODULO_REFL] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [ARITH_TAC; MATCH_MP_TAC CONTAINED_MODULO_SIMPLE THEN ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun (n,c) -> ENSURES_PRESERVED_TAC n c)
   ["x19_init",`X19`; "x20_init",`X20`; "x21_init",`X21`; "x22_init",`X22`;
    "x23_init",`X23`; "x24_init",`X24`; "x25_init",`X25`; "x26_init",`X26`;
    "x27_init",`X27`; "x28_init",`X28`] THEN

  (*** The return after the last layer ***)

  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlkem_poly_ntt_loop2_exit` (ntt_safe_layer_tm 6) THEN
  CONJ_TAC THENL [ALL_TAC; NTT_SAFE_SIM_TAC 9] THEN

  (*** The layers, with the code between them ***)

  MAP_EVERY (fun l ->
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mlkem_poly_ntt_loop1` (ntt_safe_layer_tm l) THEN
    CONJ_TAC THENL
     [ALL_TAC;
      EVENTS_LEMMA_TAC (ntt_layer_events_inst l) THEN MEMACCESS_WIDEN_TAC] THEN
    if l = 0 then ALL_TAC else
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mlkem_poly_ntt_loop2_exit` (ntt_safe_layer_tm (l - 1)) THEN
    CONJ_TAC THENL [ALL_TAC; NTT_SAFE_SIM_TAC 3]) (rev(0--6)) THEN

  (*** The frame and the constants ***)

  NTT_SAFE_SETUP_TAC;;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + rodata_mlk_zetas):int64`,`256`]
    ~keep_maychanges:true
    (assoc "mlkem_reduce" subroutine_signatures)
    MLKEM_NATIVE_POLY_NTT_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_NTT_CLANG17_O2_EXEC;;

let MLKEM_NATIVE_POLY_NTT_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e a pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (a,512) (word_sub stackpointer (word 80),80) /\
       ALLPAIRS nonoverlapping
        [a,512; word_sub stackpointer (word 80),80]
        [word pc,libmlkem_size]
       ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mlkem_native_libmlkem_clang17_O2_mc /\
                read PC s = word (pc + mlkem_poly_ntt) /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a] s /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a pc (word_sub stackpointer (word 80))
                                returnaddress /\
                  memaccess_inbounds e2
                   [a,512; word_sub stackpointer (word 80),80;
                    word (pc + rodata_mlk_zetas),256]
                   [a,512; word_sub stackpointer (word 80),80])
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
            MAYCHANGE [memory :> bytes(a,512);
                       memory :> bytes(word_sub stackpointer (word 80),
                                       80)])`;;

let MLKEM_NATIVE_POLY_NTT_CLANG17_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_NTT_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
