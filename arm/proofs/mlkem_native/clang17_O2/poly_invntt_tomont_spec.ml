(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse number-theoretic transform from ML-KEM.                           *)
(* This is the code for mlkem_poly_invntt_tomont from mlkem-native's         *)
(* portable C implementation compiled by clang 17 with -O2 (see              *)
(* mlkem_native/README.md), verified in the whole image (see libmlkem.ml)    *)
(* with the specification of the gcc 12 -O2 code.                            *)
(*                                                                           *)
(* As at gcc 12 -O2, the coefficients are first scaled by a Montgomery       *)
(* multiplication by 1441, in a loop that clang has vectorized (all 256      *)
(* coefficients, 16 per iteration), and then the 7 layers are done in loops  *)
(* over the layers and the blocks. The code saves X19 to X30 on the stack,   *)
(* with a frame of 96 bytes that it allocates after the scaling loop. Unlike *)
(* the gcc 12 -O2 code it keeps its constants in immediates, so the theorem  *)
(* of constant time and memory safety lists only the table of zetas as       *)
(* read-only data.                                                           *)
(*                                                                           *)
(* In the proofs the layers are numbered n = 0 to 6 in the order in which    *)
(* they are done, so that layer n has blocks of 2 * len coefficients with    *)
(* len = 2^(n+1), and 2^(6-n) blocks. The code of a block, given its zeta,   *)
(* first computes the number of butterflies it can do 8 at a time with       *)
(* 128-bit vectors. For len >= 8 (n >= 2) it checks that the two halves of   *)
(* the block do not overlap in the address arithmetic. The two ends that it  *)
(* compares are computed with the same arithmetic modulo 2^64, so the check  *)
(* always succeeds, also if the block wraps around the end of the address    *)
(* space, but the code reaches the vector loop through one of two paths. The *)
(* vector loop does len / 8 iterations. For len = 2 and len = 4 (n = 0, 1)   *)
(* the code takes the scalar loop for the whole block. The scalar loop that  *)
(* follows the vector loop and the scalar loop after a failed check are not  *)
(* reachable and are not verified. A Barrett reduction of a sum and a        *)
(* Montgomery multiplication by a zeta, in the vector and in the scalar      *)
(* code, compute the same values (see BARRED_VEC_LANE and NTT_LANE).         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/libmlkem.ml";;
needs "common/int_linear.ml";;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O2_mc
   [layout_range "mlkem_poly_invntt_tomont"];;

(* ------------------------------------------------------------------------- *)
(* The computation done by the C code, with its 16-bit and 32-bit integer    *)
(* arithmetic. The coefficients are first scaled by a Montgomery             *)
(* multiplication by 1441 = 2^25 mod 3329, in a loop that the compiler has   *)
(* vectorized. Then the inverse NTT is done in 7 layers, for l = 7 down to   *)
(* 1, layer l consisting of 2^(l-1) blocks of 2^(9-l) consecutive            *)
(* coefficients. A block uses one zeta to do butterflies on pairs of         *)
(* coefficients 2^(8-l) apart, independently, with a Barrett reduction of    *)
(* the sums.                                                                 *)
(* ------------------------------------------------------------------------- *)

let invntt_scale_c = define
 `invntt_scale_c (x:num->int16) i =
    montred_neon(word_mul (word_sx(x i)) (word 1441))`;;

let invntt_fqmul_c = define
 `invntt_fqmul_c (z:int16) (y:int16) =
    montred_scalar(word_mul (word_sx y) (word_sx z))`;;

let invntt_block_c = define
 `invntt_block_c (z:int16) start len (m:num->int16) i =
    if start <= i /\ i < start + len
    then barred(word_add (m i) (m(i + len)))
    else if start + len <= i /\ i < start + 2 * len
    then invntt_fqmul_c z (word_sub (m i) (m(i - len)))
    else m i`;;

let invntt_blocks_c = define
 `invntt_blocks_c l 0 (r:num->int16) = r /\
  invntt_blocks_c l (SUC b) r =
    invntt_block_c (iword(EL (2 EXP l - 1 - b) mlk_zetas))
                   (2 * 2 EXP (8 - l) * b) (2 EXP (8 - l))
                   (invntt_blocks_c l b r)`;;

let invntt_layers_c = define
 `invntt_layers_c 0 (x:num->int16) = x /\
  invntt_layers_c (SUC n) x =
    invntt_blocks_c (7 - n) (2 EXP (6 - n)) (invntt_layers_c n x)`;;

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

(* ------------------------------------------------------------------------- *)
(* The statement of the lemma for one block, for each layer.                 *)
(* ------------------------------------------------------------------------- *)

(* generated by gen.py *)
let inv_subst n tm =
  let len = 1 lsl (n + 1) in
  ntt_norm (subst [mk_small_numeral len,`LEN:num`; mk_small_numeral(128 / len),`NB:num`; mk_small_numeral(len / 8),`NN:num`; mk_small_numeral(7 - n),`LW:num`] tm);;


let inv_block_goal_tm = `!a zetas pc b k (m:num->int16).
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size); (word zetas,256)] /\
     b < NB /\ k + b + 1 = 2 * NB
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_clang17_O2_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3) /\
               read X0 s = a /\ read X1 s = word LEN /\ read X2 s = word k /\
  read X3 s = word(2 * LEN) /\ read X4 s = word(4 * LEN) /\
  read X5 s = word_neg(word(2 * LEN)) /\ read X6 s = word(2 * LEN + 2) /\
  read X7 s = word_neg(word(2 * LEN)) /\ read X8 s = word zetas /\
  read X9 s = word LW /\ read X10 s = word 20159 /\ read X11 s = word 256 /\
  read X12 s = word 4076929024 /\ read X13 s = word 4294967295 /\
  read X14 s = word 33554432 /\ read X15 s = word 4294963967 /\
  read X16 s = word_neg(word(2 * LEN * b)) /\ read X17 s = word b /\
  read X18 s = word(2 * LEN * b) /\
  read X19 s = word_add a (word(2 * LEN)) /\
  read X20 s = word_add a (word(4 * LEN * b)) /\
  read X21 s = word(2 * LEN * b + 1) /\ read X22 s = word(2 * LEN * b + LEN) /\
  read Q0 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
  read Q1 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
  read Q2 s = word 0xf3010000f3010000f3010000f3010000 /\
  read Q3 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               (!j. j < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * j)))) s =
                        iword(EL j mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        m i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_clang17_O2_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3_test) /\
               read X0 s = a /\ read X1 s = word LEN /\ read X2 s = word (k - 1) /\
  read X3 s = word(2 * LEN) /\ read X4 s = word(4 * LEN) /\
  read X5 s = word_neg(word(2 * LEN)) /\ read X6 s = word(2 * LEN + 2) /\
  read X7 s = word_neg(word(2 * LEN)) /\ read X8 s = word zetas /\
  read X9 s = word LW /\ read X10 s = word 20159 /\ read X11 s = word 256 /\
  read X12 s = word 4076929024 /\ read X13 s = word 4294967295 /\
  read X14 s = word 33554432 /\ read X15 s = word 4294963967 /\
  read X16 s = word_neg(word(2 * LEN * (b + 1))) /\ read X17 s = word (b + 1) /\
  read X18 s = word(2 * LEN * (b + 1)) /\
  read X19 s = word_add a (word(2 * LEN)) /\
  read X20 s = word_add a (word(4 * LEN * (b + 1))) /\
  read X21 s = word(2 * LEN * (b + 1) + 1) /\ read X22 s = word(2 * LEN * (b + 1) + LEN) /\
  read Q0 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
  read Q1 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
  read Q2 s = word 0xf3010000f3010000f3010000f3010000 /\
  read Q3 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               (!j. j < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * j)))) s =
                        iword(EL j mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        invntt_block_c (iword(EL k mlk_zetas))
                                       (2 * LEN * b) LEN m i))
          (MAYCHANGE [PC; X2; X16; X17; X18; X20; X21; X22; X23; X24; X25;
                      X26; X27; X28; X29; X30] ,,
           MAYCHANGE [Q4; Q5; Q6; Q7; Q16; Q17; Q18] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,512)])`;;

let inv_block_goal n = inv_subst n inv_block_goal_tm;;

let inv_vinv_tm = `\i s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_clang17_O2_mc /\
        read X0 s = a /\ read X1 s = word LEN /\ read X2 s = word k /\
  read X3 s = word(2 * LEN) /\ read X4 s = word(4 * LEN) /\
  read X5 s = word_neg(word(2 * LEN)) /\ read X6 s = word(2 * LEN + 2) /\
  read X7 s = word_neg(word(2 * LEN)) /\ read X8 s = word zetas /\
  read X9 s = word LW /\ read X10 s = word 20159 /\ read X11 s = word 256 /\
  read X12 s = word 4076929024 /\ read X13 s = word 4294967295 /\
  read X14 s = word 33554432 /\ read X15 s = word 4294963967 /\
  read X16 s = word_neg(word(2 * LEN * b)) /\ read X17 s = word b /\
  read X18 s = word(2 * LEN * b) /\
  read X19 s = word_add a (word(2 * LEN)) /\
  read X20 s = word_add a (word(4 * LEN * b)) /\
  read X21 s = word(2 * LEN * b + 1) /\ read X22 s = word(2 * LEN * b + LEN) /\
  read Q0 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
  read Q1 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
  read Q2 s = word 0xf3010000f3010000f3010000f3010000 /\
  read Q3 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        read X24 s = word_zx(word_sx(iword(EL k mlk_zetas):int16):int32) /\
        read X26 s = word LEN /\ read X27 s = word LEN /\
        read X28 s = word(LEN - 8 * i) /\
        read X29 s = word_add a (word(4 * LEN * b + 16 * i)) /\
        (i = 0 \/ (read ZF s <=> i = NN)) /\
        (!j. j < 128
        ==> read(memory :> bytes16(word_add (word zetas)
                                (word(2 * j)))) s =
            iword(EL j mlk_zetas)) /\
        (!j. j < 2 * LEN * b
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s = m j) /\
        (!j. 2 * LEN * b + 2 * LEN <= j /\ j < 256
             ==> read(memory :> bytes16(word_add a (word(2 * j)))) s = m j) /\
        (!j. j < 8 * i
             ==> read(memory :> bytes16(word_add a (word(2 * (2 * LEN * b + j))))) s =
                 invntt_block_c (iword(EL k mlk_zetas)) (2 * LEN * b) LEN m
                             (2 * LEN * b + j)) /\
        (!j. 8 * i <= j /\ j < LEN
             ==> read(memory :> bytes16(word_add a (word(2 * (2 * LEN * b + j))))) s =
                 m (2 * LEN * b + j)) /\
        (!j. j < 8 * i
             ==> read(memory :> bytes16(word_add a
                         (word(2 * (2 * LEN * b + LEN + j))))) s =
                 invntt_block_c (iword(EL k mlk_zetas)) (2 * LEN * b) LEN m
                             (2 * LEN * b + LEN + j)) /\
        (!j. 8 * i <= j /\ j < LEN
             ==> read(memory :> bytes16(word_add a
                         (word(2 * (2 * LEN * b + LEN + j))))) s =
                 m (2 * LEN * b + LEN + j))`;;

let inv_vinv n = inv_subst n inv_vinv_tm;;

let inv_sinv_tm = `\jj s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_clang17_O2_mc /\
        read X0 s = a /\ read X1 s = word LEN /\ read X2 s = word k /\
  read X3 s = word(2 * LEN) /\ read X4 s = word(4 * LEN) /\
  read X5 s = word_neg(word(2 * LEN)) /\ read X6 s = word(2 * LEN + 2) /\
  read X7 s = word_neg(word(2 * LEN)) /\ read X8 s = word zetas /\
  read X9 s = word LW /\ read X10 s = word 20159 /\ read X11 s = word 256 /\
  read X12 s = word 4076929024 /\ read X13 s = word 4294967295 /\
  read X14 s = word 33554432 /\ read X15 s = word 4294963967 /\
  read X16 s = word_neg(word(2 * LEN * b)) /\ read X17 s = word b /\
  read X18 s = word(2 * LEN * b) /\
  read X19 s = word_add a (word(2 * LEN)) /\
  read X20 s = word_add a (word(4 * LEN * b)) /\
  read X21 s = word(2 * LEN * b + 1) /\ read X22 s = word(2 * LEN * b + LEN) /\
  read Q0 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
  read Q1 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
  read Q2 s = word 0xf3010000f3010000f3010000f3010000 /\
  read Q3 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        read X23 s = word(2 * LEN * b + LEN) /\
        read X24 s = word_zx(word_sx(iword(EL k mlk_zetas):int16):int32) /\
        read X25 s = word(2 * LEN * b + jj) /\
        (read CF s <=> jj = LEN) /\
        (!j. j < 128
        ==> read(memory :> bytes16(word_add (word zetas)
                                (word(2 * j)))) s =
            iword(EL j mlk_zetas)) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                 if 2 * LEN * b <= i /\ i < 2 * LEN * b + jj \/
                    2 * LEN * b + LEN <= i /\ i < 2 * LEN * b + LEN + jj
                 then invntt_block_c (iword(EL k mlk_zetas)) (2 * LEN * b) LEN m i
                 else m i)`;;

let inv_sinv n = inv_subst n inv_sinv_tm;;

let INVNTT_BLOCK_C_LO8_STMT =
  `!z start len m i k.
     8 * (i + 1) <= len /\ k < 8
     ==> invntt_block_c z start len m (start + 8 * i + k) =
         barred (word_add (m(start + len + 8 * i + k)) (m(start + 8 * i + k)))`;;

let INVNTT_BLOCK_C_LO8 = assume_spec INVNTT_BLOCK_C_LO8_STMT;;


let INVNTT_BLOCK_C_HI8_STMT =
  `!z start len m i k.
     8 * (i + 1) <= len /\ k < 8
     ==> invntt_block_c z start len m (start + len + 8 * i + k) =
         invntt_fqmul_c z (word_sub (m(start + len + 8 * i + k))
                                    (m(start + 8 * i + k)))`;;

let INVNTT_BLOCK_C_HI8 = assume_spec INVNTT_BLOCK_C_HI8_STMT;;


let INVNTT_BLOCK_JOIN_STMT =
  `!(P:num->int16) z start len m.
     start + 2 * len <= 256 /\
     (!j. j < start ==> P j = m j) /\
     (!j. start + 2 * len <= j /\ j < 256 ==> P j = m j) /\
     (!j. j < len ==> P(start + j) = invntt_block_c z start len m (start + j)) /\
     (!j. j < len
          ==> P(start + len + j) = invntt_block_c z start len m (start + len + j))
     ==> !i. i < 256 ==> P i = invntt_block_c z start len m i`;;

let INVNTT_BLOCK_JOIN = assume_spec INVNTT_BLOCK_JOIN_STMT;;


let INVNTT_FQMUL_SYM = prove
 (`!z y. invntt_fqmul_c z y = montred_scalar(word_mul (word_sx z) (word_sx y))`,
  REWRITE_TAC[invntt_fqmul_c; WORD_MUL_SYM]);;


let BARRED_VEC_LANE_STMT =
  `!t:int16.
     word_add t
      (word_mul
        (word_subword
          (word_ishr (word_add (word_mul (word_sx t) (word 20159))
                               (word 33554432)) 26:int32) (0,16))
        (word 62207)) =
     barred t`;;

let BARRED_VEC_LANE = assume_spec BARRED_VEC_LANE_STMT;;


let INV_STORE_FACTS_TAC sn =
  let pat = vsubst [mk_var(sn,`:armstate`),`s:armstate`]
    `read (memory :> bytes128 a) s = x` in
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE(ONCE_DEPTH_CONV NTT_LANE_CONV) o
    REWRITE_RULE[BARRED_VEC_LANE] o
    CONV_RULE(DEPTH_CONV NTT_LIN_CONV) o
    CONV_RULE(TOP_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) o
    REWRITE_RULE[WORD_ZX_ZX_SX_16] o
    CONV_RULE (SIMD_SIMPLIFY_CONV []) o CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (fun th -> can (term_match [] pat) (concl th))));;


let INV_LOHI_FACTS z start len m i hyp =
  let mk lemma k =
    let th = SPECL [z; start; len; m; i; mk_small_numeral k] lemma in
    let ant = lhand(concl th) in
    let th' = MP th (CONJ hyp (EQT_ELIM(NUM_REDUCE_CONV (rand ant)))) in
    CONV_RULE(DEPTH_CONV NTT_LIN_CONV) th' in
  map (mk INVNTT_BLOCK_C_LO8) (0--7) @ map (mk INVNTT_BLOCK_C_HI8) (0--7);;


let INV_JOIN_TAC =
  MATCH_MP_TAC INVNTT_BLOCK_JOIN THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  CONV_TAC(DEPTH_CONV NTT_LIN_CONV) THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC; NTT_JOIN_FIN_TAC; NTT_JOIN_FIN_TAC; NTT_JOIN_FIN_TAC;
    NTT_JOIN_FIN_TAC];;

let NIS n = ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_EXEC [n];;


(*** Case analysis on the carry flag of the last comparison ***)

let INV_CASE_CF_TAC =
  W(fun (asl,w) ->
    let c = tryfind (fun (_,th) ->
      let t = concl th in
      let l,r = dest_eq t in
      if is_comb l && rand(rator l) = `CF` && not(r = `T` || r = `F`) then r
      else failwith "") asl in
    ASM_CASES_TAC c THENL
     [POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQT_INTRO th]));
      POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQF_INTRO th]))]);;


let INV_ZF_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_disj(concl th) && can (find_term ((=) `ZF`)) (concl th)
    then DISJ_CASES_THEN2
          (fun h -> SUBGOAL_THEN `F` CONTR_TAC THEN MP_TAC h THEN ASM_ARITH_TAC)
          ASSUME_TAC th
    else failwith "INV_ZF_TAC");;

(*** Decide the carry flag when the two compared words are equal ***)
let INV_EQ_CF_TAC =
  W(fun (asl,w) ->
    let c = tryfind (fun (_,th) ->
      let l,r = dest_eq(concl th) in
      if is_comb l && rand(rator l) = `CF` && not(r = `T` || r = `F`) then r
      else failwith "") asl in
    let x = rand(rand(rator c)) and y = rand(rand c) in
    SUBGOAL_THEN (mk_eq(x,y)) (fun eqth ->
      RULE_ASSUM_TAC(REWRITE_RULE[eqth; LE_REFL])) THENL
     [NTT_WORDS_TAC; ALL_TAC]);;


(*** The setup of a vector block of layer n (n >= 2) up to the loop ***)
let INV_VSETUP_TAC n =
  let len = 1 lsl (n + 1) in
  let lenw = mk_small_numeral len in
  let tmlen = `word:num->int64` in
  let wlen = mk_comb(tmlen,lenw) in
  ENSURES_INIT_TAC "s0" THEN
  NIS 1 THEN NTT_CMP_TAC THEN NIS 2 THEN NIS 3 THEN NTT_FOLD_TAC THEN NIS 4 THEN
  NIS 5 THEN NTT_CMP_TAC THEN NIS 6 THEN NIS 7 THEN NIS 8 THEN NTT_VAL_TAC THEN
  REG_NUM_TAC `X26` wlen THEN ZETA_UXTW_TAC `k:num` THEN NIS 9 THEN NIS 10 THEN
  NTT_CMP_TAC THEN NIS 11 THEN NIS 12 THEN NTT_CMP_TAC THEN NIS 13 THEN
  NIS 14 THEN NIS 15 THEN NTT_VAL_TAC THEN REG_NUM_TAC `X28` wlen THEN
  NIS 16 THEN NTT_VAL_TAC THEN NIS 17 THEN NTT_FOLD_SHL_TAC THEN
  MAP_EVERY NIS (18--22) THEN NTT_FOLD_TAC THEN INV_CASE_CF_TAC THENL
   [NIS 23 THEN MAP_EVERY NIS (24--24) THEN REG_WORD_TAC `X25` wlen THEN
    MAP_EVERY NIS (25--28);
    NIS 23 THEN NIS 24 THEN NIS 25 THEN NTT_FOLD_TAC THEN MAP_EVERY NIS (26--29) THEN
    NTT_FOLD_TAC THEN NIS 30 THEN INV_EQ_CF_TAC THEN NIS 31 THEN
    NIS 32 THEN REG_WORD_TAC `X25` wlen THEN MAP_EVERY NIS (33--36)];;

let INV_VFIN_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; ADD_CLAUSES] THEN
  REPEAT CONJ_TAC THEN NTT_MEM_TAC;;

let INV_BODY_START_TAC n =
  let len = 1 lsl (n + 1) in
  let sub t = inv_subst n t in
  let hyp = subst [mk_small_numeral len,`LEN:num`] `8 * (i + 1) <= LEN` in
  let lo_addr = sub `read(memory :> bytes128(word_add a (word(4 * LEN * b + 16 * i)))) s0` in
  let hi_addr = sub `read(memory :> bytes128(word_add a (word(4 * LEN * b + 16 * i + 2 * LEN)))) s0` in
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
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`];;

let INV_VBLOCK_TAC n =
  let len = 1 lsl (n + 1) and nn = 1 lsl (n - 2) in
  let sub t = inv_subst n t in
  let hyp = subst [mk_small_numeral len,`LEN:num`] `8 * (i + 1) <= LEN` in
  let facts = INV_LOHI_FACTS (sub `iword(EL k mlk_zetas):int16`)
                (sub `2 * LEN * b`) (mk_small_numeral len) `m:num->int16`
                `i:num` (ASSUME hyp) in
  let ilt = sub `i < NN` in
  let icases = MP_TAC(ASSUME ilt) THEN SPEC_TAC(`i:num`,`i:num`) THEN
               CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
               CONV_TAC WORD_REDUCE_CONV THEN TRY(CONV_TAC NUM_REDUCE_CONV) THEN REWRITE_TAC[] in
  let memtac = REWRITE_TAC[CHUNK8_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
               CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NTT_LIN_CONV) THEN
               ASM_REWRITE_TAC(facts @ [INVNTT_FQMUL_SYM]) in
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP_TAC (mk_small_numeral nn)
   `pc + mlkem_poly_invntt_tomont_loop4`
   `pc + mlkem_poly_invntt_tomont_loop4_back` (inv_vinv n) THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;
    INV_VSETUP_TAC n THEN INV_VFIN_TAC;

    INV_BODY_START_TAC n THEN
    MAP_EVERY (fun k -> NIS k THEN SIMD_SIMPLIFY_TAC[]) (1--27) THEN
    INV_STORE_FACTS_TAC "s27" THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [icases; NTT_WORDS_TAC; icases; memtac; memtac];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    (if nn = 1 then ASM_ARITH_TAC else
     ENSURES_INIT_TAC "s0" THEN INV_ZF_TAC THEN NIS 1 THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);

    ENSURES_INIT_TAC "s0" THEN INV_ZF_TAC THEN NIS 1 THEN NIS 2 THEN NTT_CMP_TAC THEN
    MAP_EVERY NIS (3--10) THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    W(fun (asl,w) ->
      if is_forall w then INV_JOIN_TAC
      else if can (find_term (fun t -> is_const t && fst(dest_const t) = "word_zx")) w
      then NTT_SMALL_TAC else NTT_WORDS_TAC)];;

let INV_SSETUP_TAC n =
  let len = 1 lsl (n + 1) in
  let wlen = mk_comb(`word:num->int64`,mk_small_numeral len) in
  ENSURES_INIT_TAC "s0" THEN
  NIS 1 THEN NTT_CMP_TAC THEN NIS 2 THEN NIS 3 THEN NTT_FOLD_TAC THEN NIS 4 THEN
  NIS 5 THEN NTT_CMP_TAC THEN NIS 6 THEN NIS 7 THEN NIS 8 THEN NTT_VAL_TAC THEN
  REG_NUM_TAC `X26` wlen THEN ZETA_UXTW_TAC `k:num` THEN NIS 9 THEN NIS 10 THEN
  NTT_CMP_TAC THEN NIS 11 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `~(a <= i /\ i < a:num)`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;;

let INV_COND_TAC n =
  let len = 1 lsl (n+1) in
  let k1 = mk_small_numeral(4*len) and k2 = mk_small_numeral(2*len) in
  let lo = mk_comb(mk_comb(`(+):num->num->num`,mk_comb(mk_comb(`( * ):num->num->num`,k1),`b:num`)),`2 * jj`) in
  let hi = mk_comb(mk_comb(`(+):num->num->num`,k2),lo) in
  let i1 = inv_subst n `2 * LEN * b + jj` and i2 = inv_subst n `(2 * LEN * b + LEN) + jj` in
  let eq1 = ARITH_RULE(mk_eq(mk_comb(mk_comb(`( * ):num->num->num`,`2`),i1),
                             lo)) in
  let eq2 = ARITH_RULE(mk_eq(mk_comb(mk_comb(`( * ):num->num->num`,`2`),i2),
                             hi)) in
  DISCH_THEN(fun th ->
    let c = rand(rator(rator(rhs(concl th)))) in
    SUBGOAL_THEN (mk_neg c) (fun nth ->
      ASSUME_TAC(REWRITE_RULE[eq1; eq2] (REWRITE_RULE[nth] th))) THENL
     [ASM_ARITH_TAC; ALL_TAC]);;


let INV_SBODY_START_TAC n =
  let i1 = inv_subst n `2 * LEN * b + jj` and i2 = inv_subst n `(2 * LEN * b + LEN) + jj` in
  let i1 = subst [mk_small_numeral(4 * (1 lsl n) * 1),`FOUR:num`] i1 in
  X_GEN_TAC `jj:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && free_in `m:num->int16` (concl th)
    then MP_TAC(SPEC i1 th) THEN MP_TAC(SPEC i2 th) THEN
         ASSUME_TAC(BETA_RULE(MATCH_MP (SPEC
           (mk_abs(`i:num`, mk_conj(mk_neg(mk_eq(`i:num`,i1)),mk_neg(mk_eq(`i:num`,i2)))))
           (MESON[] `!R P Q. (!i:num. P i ==> Q i)
                             ==> (!i. P i /\ R i ==> Q i)`)) th))
    else failwith "") THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN INV_COND_TAC n THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN INV_COND_TAC n;;

(*** Lemmas for the scalar block ***)
let INV_SXFROM_ADD_ZX = prove(`!x y:int16. word_sxfrom 15 (word_subword (word_add (word_zx x) (word_zx y):int32) (0,16)):int32 = word_sx (word_add x y)`, BITBLAST_TAC);;

let INV_ZX_ADD_ZX = prove(`!x y:int16 z:int32. word_zx(word_add (word_add (word_zx x:int32) (word_zx y)) z):int16 = word_zx(word_add (word_sx(word_add x y):int32) z)`, BITBLAST_TAC);;

let INV_SXFROM_SUB_ZX = prove(`!x y:int16. word_sxfrom 15 (word_subword (word_sub (word_zx x) (word_zx y):int32) (0,16)):int32 = word_sx (word_sub x y)`, BITBLAST_TAC);;

let WORD_ZX_USHR_16 = prove(`!x:int32. word_zx(word_ushr x 16):int16 = word_subword x (16,16)`, BITBLAST_TAC);;

let INV_MONTRED_STORE = prove(`!t:int32. word_zx(word_ushr (word_add t (word_mul (word_ishr (word_mul t (word 4076929024)) 16) (word 4294963967))) 16):int16 = montred_scalar t`, GEN_TAC THEN REWRITE_TAC[WORD_ZX_USHR_16] THEN ONCE_REWRITE_TAC[WORD_ADD_SYM] THEN MATCH_ACCEPT_TAC(SPEC_ALL NTT_LANE));;


(*** Drop the register facts and the MAYCHANGE assumption ***)
let INV_DROP_REGS_TAC =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),_)),_) -> is_const c
    | Comb(Comb(Const("<=>",_),Comb(Comb(Const("read",_),c),_)),_) -> is_const c
    | _ -> false))) THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (term_match [] `MAYCHANGE x y z`) (concl th))));;


(*** Normalize the addresses of the stores of the last step ***)
let INV_NORM_STORES_TAC = RULE_ASSUM_TAC(fun th ->
  match concl th with
    Comb(Comb(Const("=",_),l),_) when can (term_match [] `read (memory :> bytes16 (word_add a (word x))) s`) l ->
      CONV_RULE(LAND_CONV(DEPTH_CONV NTT_LIN_CONV)) th
  | _ -> th);;


let INV_SBODY_TAC n =
  let i1 = inv_subst n `2 * LEN * b + jj` and i2 = inv_subst n `(2 * LEN * b + LEN) + jj` in
  INV_SBODY_START_TAC n THEN
  NIS 1 THEN NTT_FOLD_SHL_TAC THEN NIS 2 THEN NIS 3 THEN NTT_CMP_TAC THEN
  MAP_EVERY NIS (4--20) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  INV_NORM_STORES_TAC THEN
  CONJ_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC (mk_eq(`i:num`,i1)) THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN CONV_TAC(DEPTH_CONV NTT_LIN_CONV) THEN
    ASM_REWRITE_TAC[] THEN INV_DROP_REGS_TAC THEN MLKEM_NATIVE_W_SIMP_TAC THEN
    REWRITE_TAC[INV_SXFROM_ADD_ZX; INV_ZX_ADD_ZX; BARRED_SCALAR; invntt_block_c] THEN
    REPEAT COND_CASES_TAC THEN TRY(ASM_ARITH_TAC) THEN
    REWRITE_TAC[WORD_ADD_SYM; ADD_AC];
    ALL_TAC] THEN
  ASM_CASES_TAC (mk_eq(`i:num`,i2)) THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN CONV_TAC(DEPTH_CONV NTT_LIN_CONV) THEN
    ASM_REWRITE_TAC[] THEN INV_DROP_REGS_TAC THEN MLKEM_NATIVE_W_SIMP_TAC THEN
    REWRITE_TAC[WORD_ADD_0; INV_SXFROM_SUB_ZX; INV_MONTRED_STORE; invntt_block_c; invntt_fqmul_c] THEN
    REPEAT COND_CASES_TAC THEN TRY(ASM_ARITH_TAC) THEN REWRITE_TAC[ADD_SUB];
    ALL_TAC] THEN
  INV_DROP_REGS_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) && free_in `m:num->int16` (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;;


let INV_SBLOCK_TAC n =
  let len = 1 lsl (n + 1) in
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP_TAC (mk_small_numeral len)
   `pc + mlkem_poly_invntt_tomont_loop5`
   `pc + mlkem_poly_invntt_tomont_loop5_back` (inv_sinv n) THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;
    INV_SSETUP_TAC n;
    INV_SBODY_TAC n;
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
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[invntt_block_c] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC];;

let INVNTT_BLOCK_STMTS = map inv_block_goal (0--6);;

let INV_BLOCK_THMS = map assume_spec INVNTT_BLOCK_STMTS;;

(* ------------------------------------------------------------------------- *)
(* The lemma for one layer.                                                  *)
(* ------------------------------------------------------------------------- *)

(*** The statement of the lemma for layer n, with L = 7 - n and
 *** len = 2^(n+1) coefficients in each half of a block
 ***)

let inv_layer_inv_tm =
  let (_,bd) = strip_forall inv_block_goal_tm in
  let (_,ens) = dest_imp bd in
  let (_,args) = strip_comb ens in
  let p = el 1 args in
  let (s,body) = dest_abs p in
  let cs = filter (fun c -> not(can (find_term (fun t -> t = `PC`)) c))
                  (conjuncts body) in
  let body' = list_mk_conj cs in
  let body'' = subst [`(2 EXP LW - 1) - b`,`k:num`;
                      `invntt_blocks_c LW b r`,`m:num->int16`] body' in
  mk_abs(`b:num`,mk_abs(s,body''));;


let inv_layer_inv n = inv_subst n inv_layer_inv_tm;;


let inv_layer_tm =
  `!a zetas pc (r:num->int16).
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size); (word zetas,256)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_clang17_O2_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop2) /\
               read X0 s = a /\ read X8 s = word zetas /\ read X9 s = word LW /\
               read X10 s = word 20159 /\ read X11 s = word 256 /\
               read X12 s = word 4076929024 /\ read X13 s = word 4294967295 /\
               read X14 s = word 33554432 /\ read X15 s = word 4294963967 /\
               read Q0 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
               read Q1 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
               read Q2 s = word 0xf3010000f3010000f3010000f3010000 /\
               read Q3 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               (!j. j < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * j)))) s =
                        iword(EL j mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        r i))
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_clang17_O2_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3_exit) /\
               read X0 s = a /\ read X8 s = word zetas /\ read X9 s = word LW /\
               read X10 s = word 20159 /\ read X11 s = word 256 /\
               read X12 s = word 4076929024 /\ read X13 s = word 4294967295 /\
               read X14 s = word 33554432 /\ read X15 s = word 4294963967 /\
               read Q0 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
               read Q1 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
               read Q2 s = word 0xf3010000f3010000f3010000f3010000 /\
               read Q3 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               (!j. j < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * j)))) s =
                        iword(EL j mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        invntt_blocks_c LW NB r i))
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X16; X17; X18; X19;
                      X20; X21; X22; X23; X24; X25; X26; X27; X28; X29;
                      X30] ,,
           MAYCHANGE [Q4; Q5; Q6; Q7; Q16; Q17; Q18] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,512)])`;;


let inv_layer_goal n = inv_subst n inv_layer_tm;;

(*** The proof of the lemma for layer n, from the block lemmas in
 *** INV_BLOCK_THMS (indexed by n) ***)

let INV_LAYER_TAC n =
  let l = 7 - n in
  let nb = 1 lsl (l - 1) in
  let blk = List.nth INV_BLOCK_THMS n in
  let ltm = mk_small_numeral l in
  let kk = mk_small_numeral((1 lsl l) - 1) in
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [ltm,`l:num`; `i:num`,`b:num`] (SPEC_ALL(CONJUNCT2 invntt_blocks_c)))) in
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP_TAC (mk_small_numeral nb)
   `pc + mlkem_poly_invntt_tomont_loop3`
   `pc + mlkem_poly_invntt_tomont_loop3_test` (inv_layer_inv n) THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV;

    (*** The head of the layer, up to the first block ***)

    ENSURES_INIT_TAC "s0" THEN MAP_EVERY NIS (1--17) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0; CONJUNCT1 invntt_blocks_c;
                WORD_NEG_0; WORD_ADD_0] THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN ASM_REWRITE_TAC[];

    (*** One block ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`a:int64`; `zetas:num`; `pc:num`; `i:num`;
                  mk_comb(mk_comb(`(-):num->num->num`,kk),`i:num`);
                  mk_comb(mk_comb(mk_comb(`invntt_blocks_c`,ltm),`i:num`),`r:num->int16`)]
                 blk) THEN
    ASM_REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(ENSURES_WEAKEN_TAC) THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[sth] THEN CONV_TAC(DEPTH_CONV NTT_LIN_CONV) THEN
      ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN ARITH_TAC;
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

let INVNTT_LAYER_STMTS = map inv_layer_goal (0--6);;

let INV_LAYER_THMS = map assume_spec INVNTT_LAYER_STMTS;;

(* ------------------------------------------------------------------------- *)
(* All the layers.                                                           *)
(* ------------------------------------------------------------------------- *)

(*** All seven layers, from the head of the layer loop for layer 7 ***)

let inv_layers_tm =
  `!a zetas pc (x:num->int16).
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size); (word zetas,256)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_clang17_O2_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop2) /\
               read X0 s = a /\ read X8 s = word zetas /\ read X9 s = word 7 /\
               read X10 s = word 20159 /\ read X11 s = word 256 /\
               read X12 s = word 4076929024 /\ read X13 s = word 4294967295 /\
               read X14 s = word 33554432 /\ read X15 s = word 4294963967 /\
               read Q0 s = word 0x4ebf4ebf4ebf4ebf4ebf4ebf4ebf4ebf /\
               read Q1 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
               read Q2 s = word 0xf3010000f3010000f3010000f3010000 /\
               read Q3 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
               (!j. j < 128
                    ==> read(memory :> bytes16(word_add (word zetas)
                                                        (word(2 * j)))) s =
                        iword(EL j mlk_zetas)) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        x i))
          (\s. read PC s = word(pc + mlkem_poly_invntt_tomont_loop2_exit) /\
               (!i. i < 256
                    ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                        invntt_layers_c 7 x i))
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X9; X16; X17; X18; X19;
                      X20; X21; X22; X23; X24; X25; X26; X27; X28; X29;
                      X30] ,,
           MAYCHANGE [Q4; Q5; Q6; Q7; Q16; Q17; Q18] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,512)])`;;


(*** The assertions of the layer lemma n, with the layer input r replaced ***)

let inv_layer_states n r_tm =
  let (_,bd) = strip_forall(inv_layer_goal n) in
  let (_,ens) = dest_imp bd in
  let (_,args) = strip_comb ens in
  let p = el 1 args and q = el 2 args in
  let lc = mk_small_numeral(7 - n) and nb = mk_small_numeral(1 lsl (6 - n)) in
  let blocks = mk_comb(mk_comb(mk_comb(`invntt_blocks_c`,lc),nb),`r:num->int16`) in
  let q' = subst [mk_comb(mk_comb(`invntt_layers_c`,mk_small_numeral(n+1)),`x:num->int16`),blocks] q in
  subst [r_tm,`r:num->int16`] p, subst [r_tm,`r:num->int16`] q';;


let inv_lhead n =
  fst(inv_layer_states n
       (mk_comb(mk_comb(`invntt_layers_c`,mk_small_numeral n),`x:num->int16`)));;

let inv_lend n =
  snd(inv_layer_states n
       (mk_comb(mk_comb(`invntt_layers_c`,mk_small_numeral n),`x:num->int16`)));;


let INV_LAYER_APPLY_TAC n =
  let sth = CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ADD1]
    (INST [mk_small_numeral n,`n:num`] (SPEC_ALL(CONJUNCT2 invntt_layers_c)))) in
  MP_TAC(SPECL [`a:int64`; `zetas:num`; `pc:num`;
                mk_comb(mk_comb(`invntt_layers_c`,mk_small_numeral n),`x:num->int16`)]
              (List.nth INV_LAYER_THMS n)) THEN
  ASM_REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(ENSURES_WEAKEN_TAC) THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[CONJUNCT1 invntt_layers_c];
    GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[sth];
    REWRITE_TAC[SOME_FLAGS] THEN SUBSUMED_MAYCHANGE_TAC];;


(*** From the end of layer n to the head of layer n + 1 or the exit ***)

let INV_LAYER_BACK_TAC n =
  ENSURES_INIT_TAC "s0" THEN NIS 1 THEN W32_DECIDE_FLAGS_TAC THEN NIS 2 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV);;


let INV_LAYERS_TAC =
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun n ->
    ENSURES_SEQUENCE_TAC `pc + mlkem_poly_invntt_tomont_loop3_exit` (inv_lend n) THEN
    CONJ_TAC THENL [INV_LAYER_APPLY_TAC n; ALL_TAC] THEN
    if n = 6 then ALL_TAC else
    ENSURES_SEQUENCE_TAC `pc + mlkem_poly_invntt_tomont_loop2` (inv_lhead (n + 1)) THEN
    CONJ_TAC THENL [INV_LAYER_BACK_TAC n; ALL_TAC]) (0--6) THEN
  INV_LAYER_BACK_TAC 6;;

let INVNTT_LAYERS_STMT = inv_layers_tm;;

let INVNTT_LAYERS = assume_spec INVNTT_LAYERS_STMT;;

(* ------------------------------------------------------------------------- *)
(* The scaling loop.                                                         *)
(* ------------------------------------------------------------------------- *)

(*** The scaling loop ***)

let CHUNK16_INPUT_SPLIT_STMT =
  `!P i. i < 16
         ==> ((!j. 16 * i <= j /\ j < 256 ==> P j) <=>
              (!j. 16 * (i + 1) <= j /\ j < 256 ==> P j) /\
              (!k. k < 16 ==> P(16 * i + k)))`;;


let CHUNK16_OUTPUT_SPLIT_STMT =
  `!P i. (!j. j < 16 * (i + 1) ==> P j) <=>
         (!j. j < 16 * i ==> P j) /\ (!k. k < 16 ==> P(16 * i + k))`;;


let CHUNK16_ADDR_STMT =
  `!a i k. word_add a (word(2 * (16 * i + k))):int64 =
           word_add (word_add a (word(32 * i))) (word(2 * k))`;;


let ADDR_NORM_CONV =
  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
  REWRITE_CONV[GSYM ADD_ASSOC] THENC NUM_REDUCE_CONV;;


let INVNTT_SCALE_FACTOR_STMT =
  `!x:int16.
     word_ishr (word_mul (word_sx x) (word 3634429952)) 16:int32 =
     word_sx (word_mul (word_subword (word_mul (word_sx x) (word 1441):int32)
                                     (0,16))
                       (word 62209):int16)`;;


let INVNTT_SCALE_MONTRED_STMT =
  `!x:int16.
     word_subword
      (word_add
        (word_mul
          (word_ishr (word_mul (word_shl (word_sx x:int32) 0)
                               (word 3634429952)) 16)
          (word 4294963967))
        (word_mul (word_sx x) (word 1441):int32)) (16,16):int16 =
     montred_neon(word_mul (word_sx x) (word 1441))`;;


let INVNTT_SCALE_STMT =
  `!a (x:num->int16) pc.
    nonoverlapping (a,512) (word pc,libmlkem_size)
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_clang17_O2_mc /\
           read PC s = word (pc + mlkem_poly_invntt_tomont) /\
           read X0 s = a /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = word (pc + mlkem_poly_invntt_tomont_loop1_exit) /\
           read X0 s = a /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    invntt_scale_c x i))
      (MAYCHANGE [PC; X8; X9; X10] ,,
       MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18] ,,
       MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
       MAYCHANGE [memory :> bytes(a,512)])`;;

let CHUNK16_INPUT_SPLIT = assume_spec CHUNK16_INPUT_SPLIT_STMT;;

let CHUNK16_OUTPUT_SPLIT = assume_spec CHUNK16_OUTPUT_SPLIT_STMT;;

let CHUNK16_ADDR = assume_spec CHUNK16_ADDR_STMT;;

let INVNTT_SCALE_FACTOR = assume_spec INVNTT_SCALE_FACTOR_STMT;;

let INVNTT_SCALE_MONTRED = assume_spec INVNTT_SCALE_MONTRED_STMT;;

let INVNTT_SCALE = assume_spec INVNTT_SCALE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The computation of the C code gives the inverse NTT.                      *)
(* ------------------------------------------------------------------------- *)

(* The computation of the C code gives the inverse NTT, within the same      *)
(* bounds as the hand-written kernel. In fact all the coefficients stay      *)
(* below 3329 in absolute value, because of the reductions in every layer.   *)
(* ------------------------------------------------------------------------- *)

let INVNTT_BLOCKS_C_CLOSED_STMT =
  `!l b r i.
     invntt_blocks_c l b r i =
     if i < 2 * 2 EXP (8 - l) * b
     then let z = iword(EL (2 EXP l - 1 - i DIV (2 * 2 EXP (8 - l)))
                           mlk_zetas) in
          if i MOD (2 * 2 EXP (8 - l)) < 2 EXP (8 - l)
          then barred(word_add (r i) (r(i + 2 EXP (8 - l))))
          else invntt_fqmul_c z (word_sub (r i) (r(i - 2 EXP (8 - l))))
     else r i`;;

let INVNTT_BLOCKS_C_CLOSED = assume_spec INVNTT_BLOCKS_C_CLOSED_STMT;;

let INVNTT_LAYERS_C_STEP_STMT =
  `!n x i.
     n < 7 /\ i < 256
     ==> invntt_layers_c (SUC n) x i =
         let z = iword(EL (2 EXP (7 - n) - 1 -
                           i DIV (2 * 2 EXP (8 - (7 - n)))) mlk_zetas) in
         if i MOD (2 * 2 EXP (8 - (7 - n))) < 2 EXP (8 - (7 - n))
         then barred(word_add (invntt_layers_c n x i)
                        (invntt_layers_c n x (i + 2 EXP (8 - (7 - n)))))
         else invntt_fqmul_c z
                (word_sub (invntt_layers_c n x i)
                          (invntt_layers_c n x (i - 2 EXP (8 - (7 - n)))))`;;

let INVNTT_LAYERS_C_STEP = assume_spec INVNTT_LAYERS_C_STEP_STMT;;

let MLK_ZETAS_ELS =
  map (fun k -> (REWRITE_CONV[mlk_zetas] THENC EL_CONV)
                 (mk_comb(mk_comb(`EL:num->int list->int`,mk_small_numeral k),
                          `mlk_zetas`))) (0--127);;

(*** The equation for coefficient i after layer n + 1, starting from the ***)
(*** scaled coefficients.                                                ***)

let INVNTT_LAYER_EQUATION =
  let conv =
    NUM_REDUCE_CONV THENC TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV(CONJUNCT1 invntt_layers_c :: invntt_scale_c ::
                 MONTRED_NEON_SCALAR :: MLK_ZETAS_ELS) THENC
    ONCE_DEPTH_CONV WORD_IWORD_CONV THENC REWRITE_CONV[invntt_fqmul_c] THENC
    DEPTH_CONV WORD_RED_CONV in
  fun n i ->
    let th = SPECL [mk_small_numeral n; `invntt_scale_c x`;
                    mk_small_numeral i] INVNTT_LAYERS_C_STEP in
    let th' = MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))) in
    CONV_RULE(BINOP_CONV conv) th';;

(*** The congruences and bounds for all the layers, in order ***)

let INVNTT_LAYERS_CONGBOUND =
  MLKEM_NATIVE_LOCAL_CONGBOUND_RULE undefined
   (map (fun (n,i) -> SYM(INVNTT_LAYER_EQUATION n i))
        (List.concat (map (fun n -> map (fun i -> (n,i)) (0--255)) (0--6))));;

let INVNTT_FINAL_TAC =
  W(fun (asl,w) ->
    let tm = find_term
      (can (term_match [] `invntt_layers_c 7 (invntt_scale_c x) i`)) w in
    let th = apply INVNTT_LAYERS_CONGBOUND tm in
    if not(fst(dest_const(repeat rator w)) = "int_le") then
      MP_TAC(CONJUNCT1 th) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_TRANS) THEN
      CONV_TAC(ONCE_DEPTH_CONV INVERSE_NTT_CONV) THEN
      REWRITE_TAC[GSYM INT_REM_EQ; o_THM] THEN CONV_TAC INT_REM_DOWN_CONV THEN
      REWRITE_TAC[INT_REM_EQ] THEN INT_LINEAR_CONG_TAC
    else
      MP_TAC(CONJUNCT2 th) THEN INT_ARITH_TAC);;

let INVNTT_LAYERS_C_CORRECT_STMT =
  `!x i. i < 256
         ==> (ival(invntt_layers_c 7 (invntt_scale_c x) i) ==
              inverse_ntt (ival o x) i) (mod &3329) /\
             abs(ival(invntt_layers_c 7 (invntt_scale_c x) i)) <= &26624`;;

let INVNTT_LAYERS_C_CORRECT = assume_spec INVNTT_LAYERS_C_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!a x pc stackpointer returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    aligned 16 stackpointer /\
    nonoverlapping (a,512) (word_sub stackpointer (word 96),96) /\
    ALLPAIRS nonoverlapping
     [(a,512); (word_sub stackpointer (word 96),96)]
     [(word pc,libmlkem_size)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_clang17_O2_mc /\
           read PC s = word (pc + mlkem_poly_invntt_tomont) /\
           read SP s = stackpointer /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [a] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    x i))
      (\s. read PC s = returnaddress /\
           !i. i < 256
               ==> let zi =
                     read(memory :> bytes16(word_add a (word(2 * i)))) s in
                   (ival zi == inverse_ntt (ival o x) i) (mod &3329) /\
                   abs(ival zi) <= &26624)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
       MAYCHANGE [memory :> bytes(a,512);
                  memory :> bytes(word_sub stackpointer (word 96),96)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(* ------------------------------------------------------------------------- *)
(* The statements for the safety of the blocks, layers and scaling loop.     *)
(* ------------------------------------------------------------------------- *)

(*** The statement of the safety lemma for one block of layer n ***)

let inv_block_safe_tm =
  `exists f_ev_blk.
   forall e a zetas pc b sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size); (word zetas,256); (sp,96)] /\
     b < NB
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_clang17_O2_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3) /\
               read X0 s = a /\ read X1 s = word LEN /\ read X2 s = word((2 * NB - 1) - b) /\
               read X3 s = word(2 * LEN) /\ read X4 s = word(4 * LEN) /\
               read X5 s = word_neg(word(2 * LEN)) /\
               read X6 s = word(2 * LEN + 2) /\
               read X7 s = word_neg(word(2 * LEN)) /\
               read X8 s = word zetas /\
               read X9 s = word LW /\ read X11 s = word 256 /\
               read X13 s = word 4294967295 /\
               read X16 s = word_neg(word(2 * LEN * b)) /\
               read X17 s = word b /\ read X18 s = word(2 * LEN * b) /\
               read X19 s = word_add a (word(2 * LEN)) /\
               read X20 s = word_add a (word(4 * LEN * b)) /\
               read X21 s = word(2 * LEN * b + 1) /\
               read X22 s = word(2 * LEN * b + LEN) /\
               read SP s = sp /\
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
               read(memory :> bytes64 (word_add sp (word 80))) s = v10 /\
               read(memory :> bytes64 (word_add sp (word 88))) s = v11 /\
               read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_clang17_O2_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3_test) /\
               read X0 s = a /\ read X1 s = word LEN /\
               read X2 s = word(((2 * NB - 1) - b) - 1) /\
               read X3 s = word(2 * LEN) /\ read X4 s = word(4 * LEN) /\
               read X5 s = word_neg(word(2 * LEN)) /\
               read X6 s = word(2 * LEN + 2) /\
               read X7 s = word_neg(word(2 * LEN)) /\
               read X8 s = word zetas /\
               read X9 s = word LW /\ read X11 s = word 256 /\
               read X13 s = word 4294967295 /\
               read X16 s = word_neg(word(2 * LEN * (b + 1))) /\
               read X17 s = word (b + 1) /\
               read X18 s = word(2 * LEN * (b + 1)) /\
               read X19 s = word_add a (word(2 * LEN)) /\
               read X20 s = word_add a (word(4 * LEN * (b + 1))) /\
               read X21 s = word(2 * LEN * (b + 1) + 1) /\
               read X22 s = word(2 * LEN * (b + 1) + LEN) /\
               read SP s = sp /\
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
               read(memory :> bytes64 (word_add sp (word 80))) s = v10 /\
               read(memory :> bytes64 (word_add sp (word 88))) s = v11 /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_blk a zetas pc b /\
                 memaccess_inbounds e2 [a,512; word zetas,256] [a,512])
          (MAYCHANGE [PC; X2; X16; X17; X18; X20; X21; X22; X23; X24; X25;
                      X26; X27; X28; X29; X30] ,,
           MAYCHANGE [Q4; Q5; Q6; Q7; Q16; Q17; Q18] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,512)])`;;

let inv_block_safe_goal n = inv_subst n inv_block_safe_tm;;

let SAFE_ZETA_UXTW_TAC n =
  MP_TAC(SPEC n VAL_WORD_ZX_UXTW) THEN ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC];;

(*** The register state at a block head or after j iterations of the scalar
 *** loop, for the events: the addresses depend on these
 ***)

let inv_safe_sinv_tm =
  `\i s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_clang17_O2_mc /\
        read X0 s = a /\ read X1 s = word LEN /\
        read X2 s = word((2 * NB - 1) - b) /\
        read X3 s = word(2 * LEN) /\ read X4 s = word(4 * LEN) /\
        read X5 s = word_neg(word(2 * LEN)) /\
        read X6 s = word(2 * LEN + 2) /\
        read X7 s = word_neg(word(2 * LEN)) /\
        read X8 s = word zetas /\
        read X9 s = word LW /\ read X11 s = word 256 /\
        read X13 s = word 4294967295 /\
        read X16 s = word_neg(word(2 * LEN * b)) /\
        read X17 s = word b /\ read X18 s = word(2 * LEN * b) /\
        read X19 s = word_add a (word(2 * LEN)) /\
        read X20 s = word_add a (word(4 * LEN * b)) /\
        read X21 s = word(2 * LEN * b + 1) /\
        read X22 s = word(2 * LEN * b + LEN) /\
        read X23 s = word(2 * LEN * b + LEN) /\
        read X25 s = word(2 * LEN * b + i) /\
        read SP s = sp /\
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
        read(memory :> bytes64 (word_add sp (word 80))) s = v10 /\
        read(memory :> bytes64 (word_add sp (word 88))) s = v11`;;

let inv_safe_sinv n = inv_subst n inv_safe_sinv_tm;;

let INV_SBLOCK_SAFE_TAC n =
  let len = 1 lsl (n + 1) in
  let lenw = mk_small_numeral len in
  let tmpl = subst [lenw,`LEN:num`]
   `\(a:int64) (zetas:num) (pc:num) (b:num).
      APPEND (f_ev_exit a zetas pc b)
        (APPEND (ENUMERATEL LEN (\j. f_ev_loop a zetas pc b j))
                (f_ev_setup a zetas pc b)) :(uarch_event)list` in
  let kz = inv_subst n `(2 * NB - 1) - b` in
  let cnd = inv_subst n `(2 * LEN * b + i) + 1 < 2 * LEN * b + LEN` in
  let cnd' = subst [lenw,`LEN:num`] `i + 1 < LEN` in
  CONCRETIZE_F_EVENTS_TAC tmpl THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC lenw `pc + mlkem_poly_invntt_tomont_loop5`
   `pc + mlkem_poly_invntt_tomont_loop5_exit` (inv_safe_sinv n) THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The head of the block, to the scalar loop ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    NIS 1 THEN NTT_CMP_TAC THEN NIS 2 THEN NIS 3 THEN NTT_FOLD_TAC THEN
    NIS 4 THEN NIS 5 THEN NTT_CMP_TAC THEN NIS 6 THEN NIS 7 THEN NIS 8 THEN
    NTT_VAL_TAC THEN REG_NUM_TAC `X26` (mk_comb(`word:num->int64`,lenw)) THEN
    SAFE_ZETA_UXTW_TAC kz THEN NIS 9 THEN NIS 10 THEN NTT_CMP_TAC THEN
    NIS 11 THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    NIS 1 THEN NTT_FOLD_SHL_TAC THEN NIS 2 THEN NIS 3 THEN NTT_CMP_TAC THEN
    MAP_EVERY NIS (4--21) THEN
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

let inv_safe_vinv_tm =
  `\i s. aligned_bytes_loaded s (word pc) mlkem_native_libmlkem_clang17_O2_mc /\
        read X0 s = a /\ read X1 s = word LEN /\
        read X2 s = word((2 * NB - 1) - b) /\
        read X3 s = word(2 * LEN) /\ read X4 s = word(4 * LEN) /\
        read X5 s = word_neg(word(2 * LEN)) /\
        read X6 s = word(2 * LEN + 2) /\
        read X7 s = word_neg(word(2 * LEN)) /\
        read X8 s = word zetas /\
        read X9 s = word LW /\ read X11 s = word 256 /\
        read X13 s = word 4294967295 /\
        read X16 s = word_neg(word(2 * LEN * b)) /\
        read X17 s = word b /\ read X18 s = word(2 * LEN * b) /\
        read X19 s = word_add a (word(2 * LEN)) /\
        read X20 s = word_add a (word(4 * LEN * b)) /\
        read X21 s = word(2 * LEN * b + 1) /\
        read X22 s = word(2 * LEN * b + LEN) /\
        read X26 s = word LEN /\ read X27 s = word LEN /\
        read X28 s = word(LEN - 8 * i) /\
        read X29 s = word_add a (word(4 * LEN * b + 16 * i)) /\
        read SP s = sp /\
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
        read(memory :> bytes64 (word_add sp (word 80))) s = v10 /\
        read(memory :> bytes64 (word_add sp (word 88))) s = v11`;;

let inv_safe_vinv n = inv_subst n inv_safe_vinv_tm;;

(*** The condition of the check for overlap ***)

let inv_safe_cond n =
  inv_subst n
   `val(word_add (word_add (word_add a (word (2 * LEN + 2)))
                           (word (4 * LEN * b))) (word (2 * LEN - 2)):int64) <=
    val(word_add a (word (4 * LEN * b)):int64)`;;

let INV_SAFE_CASE_TAC =
  W(fun (asl,w) ->
    let c = tryfind (fun (_,th) ->
      let t = concl th in
      let l,r = dest_eq t in
      if is_comb l && rand(rator l) = `CF` && not(r = `T` || r = `F`) then r
      else failwith "") asl in
    ASM_CASES_TAC c THENL
     [POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQT_INTRO th]) THEN ASSUME_TAC th);
      POP_ASSUM(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[EQF_INTRO th]) THEN ASSUME_TAC th)]);;

let INV_VSAFE_FRAME_TAC n =
  let nn = 1 lsl (n - 2) in
  let nnw = mk_small_numeral nn in
  let tmpl0 = subst [nnw,`NN:num`]
   `\(a:int64) (zetas:num) (pc:num) (b:num).
      APPEND (f_ev_exit a zetas pc b)
        (APPEND (ENUMERATEL NN (\i. f_ev_loop a zetas pc b i))
          (if CONDX then f_ev_setup1 a zetas pc b else f_ev_setup2 a zetas pc b))
      :(uarch_event)list` in
  let tmpl = let (vs,body) = strip_abs tmpl0 in
             list_mk_abs(vs,subst [inv_safe_cond n,`CONDX:bool`] body) in
  CONCRETIZE_F_EVENTS_TAC tmpl THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC nnw `pc + mlkem_poly_invntt_tomont_loop4`
   `pc + mlkem_poly_invntt_tomont_loop4_exit` (inv_safe_vinv n);;

let INV_VSAFE_SETUP_TAC n =
  let len = 1 lsl (n + 1) in
  let lenw = mk_small_numeral len in
  let wlen = mk_comb(`word:num->int64`,lenw) in
  let kz = inv_subst n `(2 * NB - 1) - b` in
  let setup_fin =
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC in
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  NIS 1 THEN NTT_CMP_TAC THEN NIS 2 THEN NIS 3 THEN NTT_FOLD_TAC THEN NIS 4 THEN
  NIS 5 THEN NTT_CMP_TAC THEN NIS 6 THEN NIS 7 THEN NIS 8 THEN NTT_VAL_TAC THEN
  REG_NUM_TAC `X26` wlen THEN SAFE_ZETA_UXTW_TAC kz THEN NIS 9 THEN NIS 10 THEN
  NTT_CMP_TAC THEN NIS 11 THEN NIS 12 THEN NTT_CMP_TAC THEN NIS 13 THEN
  NIS 14 THEN NIS 15 THEN NTT_VAL_TAC THEN REG_NUM_TAC `X28` wlen THEN
  NIS 16 THEN NTT_VAL_TAC THEN NIS 17 THEN NTT_FOLD_SHL_TAC THEN
  MAP_EVERY NIS (18--22) THEN NTT_FOLD_TAC THEN INV_SAFE_CASE_TAC THENL
   [NIS 23 THEN NIS 24 THEN REG_WORD_TAC `X25` wlen THEN
    MAP_EVERY NIS (25--28) THEN setup_fin;
    NIS 23 THEN NIS 24 THEN NIS 25 THEN NTT_FOLD_TAC THEN
    MAP_EVERY NIS (26--29) THEN NTT_FOLD_TAC THEN NIS 30 THEN
    INV_EQ_CF_TAC THEN NIS 31 THEN NIS 32 THEN REG_WORD_TAC `X25` wlen THEN
    MAP_EVERY NIS (33--36) THEN setup_fin];;

let INV_VSAFE_BODY_TAC n =
  let len = 1 lsl (n + 1) in
  let flagc = inv_subst n `~(val(word_sub (word (LEN - 8 * i)) (word 8):int64) = 0) <=> i + 1 < NN` in
  let ilt = inv_subst n `i < NN` in
  let icases = MP_TAC(ASSUME ilt) THEN SPEC_TAC(`i:num`,`i:num`) THEN
               CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
               CONV_TAC WORD_REDUCE_CONV THEN TRY(CONV_TAC NUM_REDUCE_CONV) THEN
               REWRITE_TAC[] in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY NIS (1--28) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN flagc SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM WORD_SUB; VAL_WORD; DIMINDEX_64] THEN
    NTT_SMALL_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [icases; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let INV_VSAFE_EXIT_TAC n =
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  NIS 1 THEN MAP_EVERY NIS (2--9) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [NTT_SMALL_TAC; NTT_WORDS_TAC; NTT_WORDS_TAC; NTT_WORDS_TAC;
    NTT_WORDS_TAC; NTT_WORDS_TAC; NTT_WORDS_TAC; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let INV_VBLOCK_SAFE_TAC n =
  INV_VSAFE_FRAME_TAC n THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC; INV_VSAFE_SETUP_TAC n; INV_VSAFE_BODY_TAC n;
    INV_VSAFE_EXIT_TAC n];;

(*** The events of the blocks of each layer ***)

let INVNTT_BLOCK_SAFE_STMTS = map inv_block_safe_goal (0--6);;

let INV_BLOCK_SAFE_THMS = map assume_spec INVNTT_BLOCK_SAFE_STMTS;;

let INV_BLOCK_EVENTS =
  map (fun n ->
        new_specification ["invntt_clang17_O2_block_events_" ^ string_of_int n]
                          (el n INV_BLOCK_SAFE_THMS)) (0--6);;

(*** The registers at the head of block b of layer n, for the layer lemma ***)

let inv_safe_linv_tm =
  let (_,bd) = strip_forall(snd(dest_exists(inv_block_safe_tm))) in
  let (_,ens) = dest_imp bd in
  let (_,args) = strip_comb ens in
  let p = el 1 args in
  let (s,body) = dest_abs p in
  let cs = filter (fun c -> not(can (find_term (fun t -> t = `PC`)) c) &&
                            not(can (find_term (fun t -> t = `events`)) c))
                  (conjuncts body) in
  mk_abs(`b:num`,mk_abs(s,list_mk_conj cs));;

let inv_safe_linv n = inv_subst n inv_safe_linv_tm;;

(*** The statement of the safety lemma for layer n ***)

let inv_layer_safe_tm =
  `exists f_ev_lay.
   forall e a zetas pc sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11.
     ALL (nonoverlapping (a,512)) [(word pc,libmlkem_size); (word zetas,256); (sp,96)]
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_clang17_O2_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop2) /\
               read X0 s = a /\ read X8 s = word zetas /\
               read X9 s = word LW /\ read X11 s = word 256 /\
               read X13 s = word 4294967295 /\
               read SP s = sp /\
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
               read(memory :> bytes64 (word_add sp (word 80))) s = v10 /\
               read(memory :> bytes64 (word_add sp (word 88))) s = v11 /\
               read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_clang17_O2_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop3_exit) /\
               read X0 s = a /\ read X8 s = word zetas /\
               read X9 s = word LW /\ read X11 s = word 256 /\
               read X13 s = word 4294967295 /\
               read SP s = sp /\
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
               read(memory :> bytes64 (word_add sp (word 80))) s = v10 /\
               read(memory :> bytes64 (word_add sp (word 88))) s = v11 /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_lay a zetas pc /\
                 memaccess_inbounds e2 [a,512; word zetas,256] [a,512])
          (MAYCHANGE [PC; X1; X2; X3; X4; X5; X6; X7; X16; X17; X18; X19;
                      X20; X21; X22; X23; X24; X25; X26; X27; X28; X29;
                      X30] ,,
           MAYCHANGE [Q4; Q5; Q6; Q7; Q16; Q17; Q18] ,,
           MAYCHANGE SOME_FLAGS ,,
           MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(a,512)])`;;

let inv_layer_safe_goal n = inv_subst n inv_layer_safe_tm;;

let inv_layer_safe_template n =
  let l = 7 - n in
  let nbw = mk_small_numeral(1 lsl (l - 1)) in
  let blk = mk_const("invntt_clang17_O2_block_events_" ^ string_of_int n,[]) in
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

let INV_LSAFE_TEST_TAC n =
  let l = 7 - n in
  let nbw = mk_small_numeral(1 lsl (l - 1)) in
  let want = subst [nbw,`NB:num`] `i + 1 < NB` in
  let cnd = inv_subst n `256 <= 2 * LEN * (i + 1)` in
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  NIS 1 THEN NTT_VAL_TAC THEN NIS 2 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV NTT_LIN_CONV) THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN (mk_eq(cnd,mk_neg want)) SUBST_ALL_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
                  ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let INV_LAYER_SAFE_TAC n =
  let l = 7 - n in
  let nbw = mk_small_numeral(1 lsl (l - 1)) in
  let linv = inv_safe_linv n in
  let ev_inst ev = SPECL ([ev; `a:int64`; `zetas:num`; `pc:num`; `i:num`; `sp:int64`] @
                          map (fun k -> mk_var("v" ^ string_of_int k,`:int64`)) (0--11))
                         (el n INV_BLOCK_EVENTS) in
  let mid = rand(concl((BETA_CONV THENC DEPTH_CONV NTT_LIN_CONV)(mk_comb(linv,`i + 1`)))) in
  CONCRETIZE_F_EVENTS_TAC (inv_layer_safe_template n) THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC nbw `pc + mlkem_poly_invntt_tomont_loop3`
   `pc + mlkem_poly_invntt_tomont_loop3_exit` linv THEN
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
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_invntt_tomont_loop3_test` mid THEN
    CONJ_TAC THENL [EVENTS_LEMMA_TAC ev_inst; INV_LSAFE_TEST_TAC n];

    (*** The exit ***)

    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[APPEND; APPEND_NIL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND; APPEND_NIL]) THEN FIRST_X_ASSUM ACCEPT_TAC];;

(*** The scaling loop ***)

let INVNTT_SCALE_SAFE_STMT =
  `exists f_ev_scale.
   forall e a pc sp r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30.
     nonoverlapping (a,512) (word pc,libmlkem_size)
     ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_clang17_O2_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont) /\
               read X0 s = a /\ read SP s = sp /\
               read X19 s = r19 /\ read X20 s = r20 /\ read X21 s = r21 /\ read X22 s = r22 /\ read X23 s = r23 /\ read X24 s = r24 /\ read X25 s = r25 /\ read X26 s = r26 /\ read X27 s = r27 /\ read X28 s = r28 /\ read X29 s = r29 /\ read X30 s = r30 /\
               read events s = e)
          (\s. aligned_bytes_loaded s (word pc)
                 mlkem_native_libmlkem_clang17_O2_mc /\
               read PC s = word(pc + mlkem_poly_invntt_tomont_loop1_exit) /\
               read X0 s = a /\ read SP s = sp /\
               read X19 s = r19 /\ read X20 s = r20 /\ read X21 s = r21 /\ read X22 s = r22 /\ read X23 s = r23 /\ read X24 s = r24 /\ read X25 s = r25 /\ read X26 s = r26 /\ read X27 s = r27 /\ read X28 s = r28 /\ read X29 s = r29 /\ read X30 s = r30 /\
               exists e2.
                 read events s = APPEND e2 e /\
                 e2 = f_ev_scale a pc /\
                 memaccess_inbounds e2 [a,512] [a,512])
          (MAYCHANGE [PC; X8; X9; X10] ,,
           MAYCHANGE [Q0; Q1; Q2; Q3; Q4; Q5; Q6; Q7; Q16; Q17; Q18] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
           MAYCHANGE [memory :> bytes(a,512)])`;;

let INVNTT_SCALE_SAFE_TAC =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (pc:num).
      APPEND ([]:(uarch_event)list)
       (APPEND (ENUMERATEL 16 (\i. f_ev_loop a pc i)) (f_ev_prol a pc))
      :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `16` `pc + mlkem_poly_invntt_tomont_loop1`
   `pc + mlkem_poly_invntt_tomont_loop1_exit`
   `\i s. aligned_bytes_loaded s (word pc)
            mlkem_native_libmlkem_clang17_O2_mc /\
          read X0 s = a /\ read X8 s = word(32 * i) /\ read SP s = sp /\
          read X19 s = r19 /\ read X20 s = r20 /\ read X21 s = r21 /\ read X22 s = r22 /\ read X23 s = r23 /\ read X24 s = r24 /\ read X25 s = r25 /\ read X26 s = r26 /\ read X27 s = r27 /\ read X28 s = r28 /\ read X29 s = r29 /\ read X30 s = r30` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_EXEC (1--30) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(val(word_add (word(32 * i)) (word 18446744073709551136):int64) = 0) <=>
      i + 1 < 16`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      ASM_CASES_TAC `i = 15` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 16 /\ ~(i = 15)
        ==> 32 * i + 18446744073709551136 < 18446744073709551616`] THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 32`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[APPEND; APPEND_NIL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[APPEND; APPEND_NIL]) THEN FIRST_X_ASSUM ACCEPT_TAC];;

(*** The events of the layers and of the scaling loop ***)

let INVNTT_LAYER_SAFE_STMTS = map inv_layer_safe_goal (0--6);;

let INV_LAYER_SAFE_THMS = map assume_spec INVNTT_LAYER_SAFE_STMTS;;

let INV_LAYER_EVENTS =
  map (fun n ->
        new_specification ["invntt_clang17_O2_layer_events_" ^ string_of_int n]
                          (el n INV_LAYER_SAFE_THMS)) (0--6);;

let INVNTT_SCALE_SAFE = assume_spec INVNTT_SCALE_SAFE_STMT;;

let INVNTT_SCALE_EVENTS =
  new_specification ["invntt_clang17_O2_scale_events"] INVNTT_SCALE_SAFE;;

(*** The events of the whole code, as the events of the scaling loop, the
 *** setup of the frame and the constants, the layers with the code between
 *** them, and the return. The stack pointer after the frame is allocated is
 *** the parameter sp.
 ***)

let invntt_top_template =
  let lay n = list_mk_comb
   (mk_const("invntt_clang17_O2_layer_events_" ^ string_of_int n,[]),
    [`a:int64`; `pc + rodata_mlk_zetas`; `pc:num`])
  and fev nm =
    list_mk_comb
     (mk_var(nm,`:int64->num->int64->int64->(uarch_event)list`),
      [`a:int64`;`pc:num`;`sp:int64`;`returnaddress:int64`]) in
  let app x y = list_mk_icomb "APPEND" [x;y] in
  let rec chain n acc =
    if n = 7 then acc else
    let acc' = app (lay n) acc in
    chain (n + 1)
      (if n = 6 then acc' else app (fev ("f_ev_back" ^ string_of_int n)) acc') in
  let start = app (fev "f_ev_setup") `invntt_clang17_O2_scale_events a pc` in
  list_mk_abs([`a:int64`;`pc:num`;`sp:int64`;`returnaddress:int64`],
              app (fev "f_ev_fin") (chain 0 start));;

(*** The stack after the frame is allocated, and the states between the
 *** pieces
 ***)

let invntt_safe_stack_tm =
  let slot k v =
    if k = 0 then
      subst [v,`V:int64`]
       `read(memory :> bytes64 stackpointer) s = V`
    else
      subst [v,`V:int64`; mk_small_numeral(8 * k),`K:num`]
       `read(memory :> bytes64(word_add stackpointer (word K))) s = V` in
  let vals = [`x29_init:int64`; `returnaddress:int64`; `x28_init:int64`;
              `x27_init:int64`; `x26_init:int64`; `x25_init:int64`;
              `x24_init:int64`; `x23_init:int64`; `x22_init:int64`;
              `x21_init:int64`; `x20_init:int64`; `x19_init:int64`] in
  list_mk_conj(`read SP s = stackpointer` ::
               map2 slot (0--11) vals);;

let invntt_safe_layer_tm n =
  mk_abs(`s:armstate`,
    list_mk_conj
     [subst [mk_small_numeral(7 - n),`L:num`]
        `read X0 s = a /\ read X8 s = word(pc + rodata_mlk_zetas) /\
         read X9 s = word L /\ read X11 s = word 256 /\
         read X13 s = word 4294967295`;
      invntt_safe_stack_tm]);;

let invntt_safe_scaleend_tm =
  `\s. read X0 s = a /\ read SP s = word_add stackpointer (word 96) /\
       read X19 s = x19_init /\ read X20 s = x20_init /\
       read X21 s = x21_init /\ read X22 s = x22_init /\
       read X23 s = x23_init /\ read X24 s = x24_init /\
       read X25 s = x25_init /\ read X26 s = x26_init /\
       read X27 s = x27_init /\ read X28 s = x28_init /\
       read X29 s = x29_init /\ read X30 s = returnaddress`;;

let invntt_layer_events_inst n ev =
  SPECL ([ev; `a:int64`; `pc + rodata_mlk_zetas`; `pc:num`;
          `stackpointer:int64`;
          `x29_init:int64`; `returnaddress:int64`; `x28_init:int64`;
          `x27_init:int64`; `x26_init:int64`; `x25_init:int64`;
          `x24_init:int64`; `x23_init:int64`; `x22_init:int64`;
          `x21_init:int64`; `x20_init:int64`; `x19_init:int64`])
        (el n INV_LAYER_EVENTS);;

let invntt_scale_events_inst ev =
  SPECL [ev; `a:int64`; `pc:num`; `word_add stackpointer (word 96):int64`;
         `x19_init:int64`; `x20_init:int64`; `x21_init:int64`;
         `x22_init:int64`; `x23_init:int64`; `x24_init:int64`;
         `x25_init:int64`; `x26_init:int64`; `x27_init:int64`;
         `x28_init:int64`; `x29_init:int64`; `returnaddress:int64`]
        INVNTT_SCALE_EVENTS;;

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

let INV_SAFE_SIM_TAC n =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY (fun i ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_EXEC [i] THEN
    MLKEM_NATIVE_ADRP_TAC THEN TRY W32_DECIDE_FLAGS_TAC) (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let INV_SAFE_SETUP_TAC =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY (fun i ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_EXEC [i] THEN
    MLKEM_NATIVE_ADRP_TAC) (1--20) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; DISCHARGE_SAFETY_PROPERTY_TAC];;

let INV_SAFE_FIN_TAC =
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  TRY STRIP_EXISTS_ASSUM_TAC THEN
  MAP_EVERY (fun i ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_EXEC [i] THEN
    TRY W32_DECIDE_FLAGS_TAC) (1--9) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let INV_SAFE_TOP_TAC =
  CONCRETIZE_F_EVENTS_TAC invntt_top_template THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `nonoverlapping_modulo (2 EXP 64) (val (a:int64),512)
                          (pc + rodata_mlk_zetas,256)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2 EXP 64`; `val(a:int64)`; `512`; `pc:num`;
                   `libmlkem_size:num`;
                   `val(a:int64)`; `512`; `pc + rodata_mlk_zetas`; `256`]
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
    "x27_init",`X27`; "x28_init",`X28`; "x29_init",`X29`] THEN

  (*** The return after the last layer ***)

  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlkem_poly_invntt_tomont_loop3_exit` (invntt_safe_layer_tm 6) THEN
  CONJ_TAC THENL [ALL_TAC; INV_SAFE_FIN_TAC] THEN

  (*** The layers, with the code between them ***)

  MAP_EVERY (fun n ->
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mlkem_poly_invntt_tomont_loop2` (invntt_safe_layer_tm n) THEN
    CONJ_TAC THENL
     [ALL_TAC;
      EVENTS_LEMMA_TAC (invntt_layer_events_inst n) THEN MEMACCESS_WIDEN_TAC] THEN
    if n = 0 then ALL_TAC else
    ENSURES_EVENTS_SEQUENCE_TAC
     `pc + mlkem_poly_invntt_tomont_loop3_exit` (invntt_safe_layer_tm (n - 1)) THEN
    CONJ_TAC THENL [ALL_TAC; INV_SAFE_SIM_TAC 2]) (rev(0--6)) THEN

  (*** The frame and the constants, after the scaling ***)

  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlkem_poly_invntt_tomont_loop1_exit` invntt_safe_scaleend_tm THEN
  CONJ_TAC THENL
   [ALL_TAC; INV_SAFE_SETUP_TAC] THEN

  (*** The scaling ***)

  MP_TAC(invntt_scale_events_inst `e:(uarch_event)list`) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN ENSURES_WEAKEN_TAC THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `e2:(uarch_event)list` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; MEMACCESS_WIDEN_TAC];
    REWRITE_TAC[SOME_FLAGS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    SUBSUMED_MAYCHANGE_TAC];;


let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + rodata_mlk_zetas):int64`,`256`]
    ~keep_maychanges:true
    (assoc "mlkem_reduce" subroutine_signatures)
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_EXEC;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e a pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       nonoverlapping (a,512) (word_sub stackpointer (word 96),96) /\
       ALLPAIRS nonoverlapping
        [a,512; word_sub stackpointer (word 96),96]
        [word pc,libmlkem_size]
       ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mlkem_native_libmlkem_clang17_O2_mc /\
                read PC s = word (pc + mlkem_poly_invntt_tomont) /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [a] s /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events a pc (word_sub stackpointer (word 96))
                                returnaddress /\
                  memaccess_inbounds e2
                   [a,512; word_sub stackpointer (word 96),96;
                    word (pc + rodata_mlk_zetas),256]
                   [a,512; word_sub stackpointer (word 96),96])
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
            MAYCHANGE [memory :> bytes(a,512);
                       memory :> bytes(word_sub stackpointer (word 96),
                                       96)])`;;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_INVNTT_TOMONT_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
