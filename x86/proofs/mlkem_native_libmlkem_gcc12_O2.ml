(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The code and read-only data of mlkem-native's libmlkem.so for x86-64      *)
(* compiled by gcc 12 with -O2 (see mlkem_native/README.md), as one image,   *)
(* and tools to transfer the results for the individual functions to the     *)
(* same code in the image. The code refers to other code and data in the     *)
(* image only by displacements from the instruction pointer, so the image    *)
(* works in the same way wherever it is loaded, at an address pc, and the    *)
(* functions in it are then at pc + <address>, where <address> is the        *)
(* address of the function in the binary. The theorems about the image only  *)
(* assume that pc is a multiple of 16, since the vectors of constants read   *)
(* by SSE instructions must be aligned. (The dynamic loader puts it at a     *)
(* multiple of 4096.)                                                        *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

let mlkem_native_libmlkem_gcc12_O2_mc = define_from_elf
  "mlkem_native_libmlkem_gcc12_O2_mc"
  "x86/mlkem_native/mlkem_native_libmlkem_gcc12_O2.o";;

let LENGTH_MLKEM_NATIVE_LIBMLKEM_GCC12_O2_MC =
  CONV_RULE(RAND_CONV LENGTH_CONV)
   (AP_TERM `LENGTH:byte list->num` mlkem_native_libmlkem_gcc12_O2_mc);;

(* ------------------------------------------------------------------------- *)
(* Decoding all the code in the image would take several minutes, and the    *)
(* header and the data in it are not instructions, so the decoding theorems  *)
(* for the simulation are only made for the given ranges of addresses        *)
(* [lo,hi), which are those of the code being simulated. Otherwise this is   *)
(* the same as X86_MK_EXEC_RULE.                                             *)
(* ------------------------------------------------------------------------- *)

let X86_MK_EXEC_RANGES_RULE =
  let pth = (UNDISCH_ALL o prove)
   (`i = i' ==> pc + n = pc' ==>
     bytes_loaded s (word pc) l ==> decode_len l (n,i) l' ==>
     x86_decode s (word pc) (n,i') /\ bytes_loaded s (word pc') l'`,
    REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN
    MATCH_ACCEPT_TAC X86_DECODE_CONS)
  and pth_pc = (UNDISCH o ARITH_RULE) `n + m:num = p ==> (pc + n) + m = pc + p`
  and ei,ei' = `i:instruction`,`i':instruction`
  and pl,el,el' = `(+):num->num->num`,`l:byte list`,`l':byte list`
  and en,em,ep,epc,epc' = `n:num`,`m:num`,`p:num`,`pc:num`,`pc':num`
  and len_tm = `LENGTH:byte list->num` in
  let offset_of pc = match pc with
    | Comb(Comb(Const("+",_),_),a) -> dest_small_numeral a
    | _ -> 0 in
  let rec go hi th =
    let l = rand (concl th) in
    let th1 = DECODE_LEN_THM l in
    let (n,i),l' = (dest_pair o rand F_F I) (dest_comb (concl th1)) in
    let th2 = REWRITE_CONV X86_INSTRUCTION_ALIASES i in
    let i' = rhs (concl th2) in
    let pc = rand (lhand (concl th)) in
    let th3,pcofs = match pc with
    | Comb(Comb(Const("+",_),pc),a) ->
      let th = NUM_ADD_CONV (mk_comb (mk_comb (pl, a), n)) in
      PROVE_HYP th (INST [pc,epc; a,en; n,em; rhs (concl th),ep] pth_pc),a
    | _ -> REFL (mk_comb (mk_comb (pl, pc), n)),`0` in
    let pc' = rhs (concl th3) in
    let th' = (PROVE_HYP th2 o PROVE_HYP th3 o PROVE_HYP th o PROVE_HYP th1)
      (INST [i,ei; i',ei'; pc,epc; n,en; pc',epc'; l,el; l',el'] pth) in
    let dth,bth = CONJ_PAIR th' in
    if offset_of pc' >= hi then [dth,pcofs]
    else (dth,pcofs)::(go hi bth) in
  fun mc_def ranges ->
    let lenth = TRANS (AP_TERM len_tm mc_def)
                      (LENGTH_CONV (mk_comb(len_tm,rhs(concl mc_def)))) in
    let dth = AP_TERM `bytes_loaded s (word pc)` mc_def in
    let th0 = EQ_MP dth (ASSUME (lhs (concl dth))) in
    let decodes = itlist (fun (lo,hi) acc ->
      go hi (BYTES_LOADED_OFFSET_RULE lo th0) @ acc) ranges [] in
    let arr = Array.make (dest_small_numeral (rhs (concl lenth))) None in
    List.iter (fun (th,pcofs) ->
        arr.(dest_small_numeral pcofs) <-
          Some ((GENL [`s:x86state`; `pc:num`] o DISCH_ALL) th))
      decodes;
    lenth,arr;;

(* ------------------------------------------------------------------------- *)
(* Addresses in the image: a RIP-relative displacement from code in the      *)
(* image to data in it is within range wherever the image is.                *)
(* ------------------------------------------------------------------------- *)

let RIPREL32_WITHIN_BOUNDS_IN_IMAGE = prove
 (`!pc a b. a < 2 EXP 31 /\ b < 2 EXP 31
            ==> riprel32_within_bounds (pc + a) (pc + b)`,
  REWRITE_TAC[riprel32_within_bounds; GSYM INT_OF_NUM_ADD] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_POW] THEN INT_ARITH_TAC);;

let IMAGE_INT_SUB_LEMMA = prove
 (`!p a b c. &(p + a) - (&(p + b) + c):int = &a - (&b + c)`,
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Given the definition of the code of a function, as it is in the image     *)
(* at address v, and the addresses d1,...,dk in the image of the data that   *)
(* the code refers to with relocations (if any), which are the extra         *)
(* arguments of the definition, give                                         *)
(*                                                                           *)
(* |- !s pc. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc      *)
(*           ==> bytes_loaded s (word(pc + v))                               *)
(*                 (<mc> (pc + v) (pc + d1) ... (pc + dk))                   *)
(*                                                                           *)
(* The relocated displacements are then constants, the same as in the image, *)
(* wherever it is.                                                           *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_IMAGE_CODE_RULE =
  let pc_tm = `pc:num` and plus_tm = `(+):num->num->num` in
  let conv =
    GEN_REWRITE_CONV TOP_DEPTH_CONV [IMAGE_INT_SUB_LEMMA] THENC
    NUM_REDUCE_CONV THENC INT_REDUCE_CONV THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [NUM_OF_INT_OF_NUM] THENC
    NUM_REDUCE_CONV in
  fun mc_def v ds ->
    let inst =
      if ds = [] then mc_def else
      let offs = map (mk_binop plus_tm pc_tm o mk_small_numeral) (v::ds) in
      CONV_RULE (RAND_CONV conv) (SPECL offs mc_def) in
    BYTES_LOADED_SUBPROGRAM_RULE mlkem_native_libmlkem_gcc12_O2_mc inst v;;

(* ------------------------------------------------------------------------- *)
(* Likewise for a table of data that is at address d in the image, give      *)
(*                                                                           *)
(* |- !s pc. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc      *)
(*           ==> bytes_loaded s (word(pc + d)) <data>                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_IMAGE_DATA_RULE data_def d =
  BYTES_LOADED_SUBPROGRAM_RULE mlkem_native_libmlkem_gcc12_O2_mc data_def d;;

(* ------------------------------------------------------------------------- *)
(* Prove the version of a theorem for a function in the image, given the     *)
(* theorem for the function with the variables for the addresses of the      *)
(* code and of the data instantiated to pc + v and pc + d1, ..., and its     *)
(* other variables free with the same names as in the goal, and the          *)
(* theorems from the two rules above for its code and data. The hypotheses   *)
(* about the addresses of the code and data, such as the bounds for the      *)
(* RIP-relative displacements and the alignment of vectors of constants,     *)
(* follow from those for the image.                                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_IMAGE_TAC =
  let pth = ONCE_REWRITE_RULE[IMP_CONJ_ALT] ENSURES_PRECONDITION_THM in
  fun th loadths ->
    REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
    REPEAT STRIP_TAC THEN MP_TAC th THEN ANTS_TAC THENL
     [REWRITE_TAC[GSYM ADD_ASSOC; ALL] THEN
      CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      FIRST
       [MATCH_MP_TAC RIPREL32_WITHIN_BOUNDS_IN_IMAGE THEN
        CONV_TAC NUM_REDUCE_CONV;
        REWRITE_TAC[WORD_ADD] THEN
        CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[WORD_ADD] THEN NONOVERLAPPING_TAC];
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP pth) THEN
      X_GEN_TAC `s:x86state` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC loadths];;

(* ------------------------------------------------------------------------- *)
(* The same for a theorem of constant time and memory safety, of the form    *)
(* |- ?f_events. !e ... . P ==> ensures x86 (...) (... f_events ...) (...). *)
(* The function of the events in the image is that of the function with the  *)
(* instantiations, as a function of the arguments of f_events in the goal.   *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_IMAGE_SAFE_TAC th inst loadths =
  let f = fst(dest_exists(concl th)) in
  let app v tm = find_term (fun t -> fst(strip_comb t) = v) tm in
  X_CHOOSE_THEN f (fun fth ->
    let fth' = INST inst (SPEC_ALL fth) in
    W(fun (asl,w) ->
      let f',wbod = dest_exists w in
      let xs = snd(strip_comb(app f' wbod)) in
      let zs = map (genvar o type_of) xs in
      let wit = list_mk_abs(zs,subst (zip zs xs) (app f (concl fth'))) in
      EXISTS_TAC wit THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      MLKEM_NATIVE_IMAGE_TAC fth' loadths)) th;;

(* ------------------------------------------------------------------------- *)
(* Vectors of polynomials. As in common/fips203.ml, a vector of k            *)
(* polynomials is given by its 256 * k coefficients, those of polynomial j   *)
(* being \i. x(256 * j + i). POLYVEC_SPLIT_TAC k splits an assumption        *)
(* !i. i < 256 * k ==> P i into one for each polynomial, POLYVEC_JOIN_TAC k  *)
(* reduces such a goal to the cases for the polynomials, and                 *)
(* POLYVEC_CASES_TAC reduces a goal !j. j < k ==> Q j to Q 0, ...,           *)
(* Q (k - 1), with the indices and offsets evaluated in each case.           *)
(* ------------------------------------------------------------------------- *)

let POLYVEC_SPLIT = prove
 (`!k j P. (!i. i < 256 * k ==> P i) /\ j < k
           ==> !i. i < 256 ==> P(256 * j + i)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  TRANS_TAC LTE_TRANS `256 * (j + 1)` THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let POLYVEC_JOIN = prove
 (`!k P. (!j. j < k ==> !i. i < 256 ==> P(256 * j + i))
         ==> !i. i < 256 * k ==> P i`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i DIV 256`) THEN
  ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
  DISCH_THEN(MP_TAC o SPEC `i MOD 256`) THEN
  REWRITE_TAC[MOD_LT_EQ; ARITH_EQ; DIVISION_SIMP]);;

let POLYVEC_INDEX_CONV =
  TOP_DEPTH_CONV BETA_CONV THENC
  REWRITE_CONV[LEFT_ADD_DISTRIB; MULT_ASSOC] THENC NUM_REDUCE_CONV THENC
  REWRITE_CONV[ADD_CLAUSES];;

let POLYVEC_SPLIT_TAC k =
  let kt = mk_small_numeral k in
  let sth = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) (SPEC kt POLYVEC_SPLIT) in
  let jths = map (fun j ->
    let jt = mk_small_numeral j in
    jt,EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool` jt kt)))
    (0--(k-1)) in
  let n = mk_small_numeral(256 * k) in
  FIRST_X_ASSUM(fun th ->
    let i,bod = dest_forall(concl th) in
    if rand(lhand bod) <> n then failwith "POLYVEC_SPLIT_TAC" else
    MAP_EVERY (fun (jt,jth) ->
      ASSUME_TAC(CONV_RULE POLYVEC_INDEX_CONV
        (MATCH_MP (SPEC jt sth) (CONJ th jth)))) jths);;

let POLYVEC_CASES_TAC =
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC POLYVEC_INDEX_CONV;;

let POLYVEC_JOIN_TAC k =
  let kt = mk_small_numeral k in
  MATCH_MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
                (SPEC kt POLYVEC_JOIN)) THEN
  POLYVEC_CASES_TAC;;

(* ------------------------------------------------------------------------- *)
(* Decide the test at the end of an iteration of a loop over the             *)
(* polynomials, which compares a pointer with its final value, both offsets  *)
(* from the same base, after the conditional jump. This evaluates the        *)
(* condition in the resulting instruction pointer and in the events.         *)
(* ------------------------------------------------------------------------- *)

let PTR_DECIDE_RIP_TAC =
  let wth = WORD_RULE
   `word_sub (word_add a x) (word_add a y):int64 = word_sub x y` in
  let pat = `val(word_sub (word_add a x) (word_add a y):int64) = 0` in
  let is_test t =
    let t' = if is_neg t then rand t else t in
    can (term_match [] pat) t' in
  let tconv = REWRITE_CONV[wth] THENC WORD_REDUCE_CONV THENC
              NUM_REDUCE_CONV in
  let conv t =
    if is_cond t && is_test(lhand(rator t)) then
      (RATOR_CONV(LAND_CONV tconv) THENC REWRITE_CONV[]) t
    else failwith "PTR_DECIDE_RIP_TAC" in
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (can conv)) (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV conv) th else th);;

(* ------------------------------------------------------------------------- *)
(* ALIGNED_OFFSETS_TAC a k [n1; ...] adds aligned k (word_add a (word ni))   *)
(* to the assumptions for each ni, a multiple of k, given aligned k a there, *)
(* e.g. for the polynomials of an aligned vector.                            *)
(* ------------------------------------------------------------------------- *)

let ALIGNED_OFFSETS_TAC a k ns =
  MAP_EVERY (fun n ->
    let tm = list_mk_comb(`aligned:num->int64->bool`,
       [mk_small_numeral k;
        mk_comb(mk_comb(`word_add:int64->int64->int64`,a),
                mk_comb(`word:num->int64`,mk_small_numeral n))]) in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC]) ns;;

(* ------------------------------------------------------------------------- *)
(* For a vector instruction with a memory operand at base + index, the       *)
(* address is computed as word_add a (word(1 * n)) when the index register   *)
(* is word n, so INDEX_ADDR_TAC restates the assumptions about the 128-bit   *)
(* words at word_add a (word(16 * i)), and their alignment, in that form.    *)
(* ------------------------------------------------------------------------- *)

let INDEX_ADDR_TAC =
  let pth = ARITH_RULE `16 * i = 1 * 16 * i` in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if can (term_match []
          `read (memory :> bytes128 (word_add a (word(16 * i)))) s = v`) c ||
       can (term_match [] `aligned 16 (word_add a (word(16 * i)):int64)`) c
    then ONCE_REWRITE_RULE[pth] th else th);;

(* ------------------------------------------------------------------------- *)
(* Byte arrays. As in mlkem_decode in common/fips203.ml, the contents of a   *)
(* byte array are given as a number n, and READ_MEMORY_BYTES8_OF_NUM,        *)
(* READ_MEMORY_BYTES16_OF_NUM and READ_MEMORY_BYTES32_OF_NUM give its 8-,    *)
(* 16- and 32-bit parts. BYTES_BITBLAST_TAC proves a goal of bit operations  *)
(* on such bytes word((n DIV 2 EXP k) MOD 256) by bit-blasting with them as  *)
(* atoms.                                                                    *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES8_OF_NUM = prove
 (`!a:int64 m n k s:x86state.
        read (memory :> bytes(a,m)) s = n /\ k < m
        ==> read (memory :> bytes8(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 256)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES8_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP (8 * 1)`; READ_BYTES_DIV;
              READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES16_OF_NUM = prove
 (`!a:int64 m n k s:x86state.
        read (memory :> bytes(a,m)) s = n /\ k + 2 <= m
        ==> read (memory :> bytes16(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 65536)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `65536 = 2 EXP (8 * 2)`; READ_BYTES_DIV;
              READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES32_OF_NUM = prove
 (`!a:int64 m n k s:x86state.
        read (memory :> bytes(a,m)) s = n /\ k + 4 <= m
        ==> read (memory :> bytes32(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 4294967296)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES32_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP (8 * 4)`; READ_BYTES_DIV;
              READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

(*** A byte array from its bytes, and a byte array as a single word ***)

let READ_MEMORY_BYTES_OF_BYTES8 = prove
 (`!a:int64 n x s:x86state.
        (!j. j < n
             ==> read (memory :> bytes8(word_add a (word j))) s =
                 word((x DIV 2 EXP (8 * j)) MOD 256))
        ==> read (memory :> bytes(a,n)) s = x MOD 2 EXP (8 * n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1];
    REPEAT STRIP_TAC] THEN
  REWRITE_TAC[ADD1; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE;
              READ_BYTES_BYTES8] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `s:x86state`]) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `j < n ==> j < SUC n`];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[LT] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL; LEFT_ADD_DISTRIB; MULT_CLAUSES; EXP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; MOD_MULT_MOD] THEN ARITH_TAC);;

let READ_MEMORY_WBYTES_VAL = prove
 (`!a:int64 (x:N word) s:x86state.
        read (memory :> wbytes a) s = x <=>
        read (memory :> bytes(a,dimindex(:N) DIV 8)) s = val x`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM VAL_EQ] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES]);;

(*** The case of a Keccak state, and its wbytes form from its bytes ***)

let READ_MEMORY_WBYTES_1600 =
  CONV_RULE(DEPTH_CONV DIMINDEX_CONV THENC ONCE_DEPTH_CONV NUM_DIV_CONV)
   (INST_TYPE [`:1600`,`:N`] READ_MEMORY_WBYTES_VAL);;

let KECCAK_STATE_WBYTES_TAC sv =
  let pat = subst [sv,`S:1600 word`]
   `read (memory :> bytes (a,200)) s = val(S:1600 word)` in
  FIRST_ASSUM(fun th ->
    if can (term_match [sv] pat) (concl th)
    then ASSUME_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600] th)
    else NO_TAC);;

let BYTES_BITBLAST_TAC (asl,w) =
  let bts = setify (find_terms (fun t ->
     type_of t = `:byte` &&
     can (term_match [] `word(x MOD 256):byte`) t) w) in
  let vs = map (fun _ -> genvar `:byte`) bts in
  let th = BITBLAST_RULE (subst (zip vs bts) w) in
  ACCEPT_TAC (INST (zip bts vs) th) (asl,w);;

(*** Splitting off the first m values of a sum of n + m values ***)

let NSUM_LT_ADD = prove
 (`!f m n. nsum {i | i < m + n} f =
           nsum {i | i < m} f + nsum {i | i < n} (\i. f(m + i))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; NSUM_CLAUSES_NUMSEG_LT; ADD_ASSOC]);;

(*** Coefficients loaded with sign extension, when known to be small ***)

let WORD_SX_SMALL = prove
 (`!y:int16. val y < 32768 ==> (word_sx y:int32) = word_zx y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_SX_ZX_GEN; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `~bit 15 (y:int16)` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[BIT_VAL] THEN
    ASM_SIMP_TAC[DIV_LT; ARITH_RULE `2 EXP 15 = 32768`] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[WORD_OR_0]]);;

let MOD_32_64 = prove
 (`!x. x MOD 4294967296 MOD 18446744073709551616 = x MOD 4294967296`,
  GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL [`x:num`; `4294967296`] MOD_LT_EQ) THEN ARITH_TAC);;

(*** The truncation of a 64-bit value to 32 bits by a 32-bit LEA ***)

let WORD_SX_64_32 = prove
 (`!x:int64. word_sx x:int32 = word_zx x`,
  BITBLAST_TAC);;

(*** Unsigned 32-bit arguments word n, as the code zero-extends them,
 *** including those loaded from the stack as 32-bit words
 ***)

let WORD_ZX_32_SMALL = prove
 (`!n. n < 2 EXP 32
       ==> word_zx(word_zx(word n:int64):int32):int64 = word n /\
           val(word_zx(word n:int64):int32) = n /\
           word_zx(word n:int32):int64 = word n`,
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN TRY(ONCE_REWRITE_TAC[GSYM VAL_EQ]) THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `n < 4294967296 ==> n < 18446744073709551616`]);;

let ARGS_32_TAC ns =
  MAP_EVERY (fun n ->
    MP_TAC(SPEC n WORD_ZX_32_SMALL) THEN
    ANTS_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))]) ns;;

(*** Bit fields of numbers and of words made from them ***)

let DIV_MOD_EXP_LOW = prove
 (`!x m k l. k + l <= m
             ==> ((x MOD 2 EXP m) DIV 2 EXP k) MOD 2 EXP l =
                 (x DIV 2 EXP k) MOD 2 EXP l`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `k + l <= m ==> MIN m (k + l) = k + l`]);;

let WORD_SUBWORD_WORD = prove
 (`!x k l. k + l <= dimindex(:N)
           ==> word_subword (word x:N word) (k,l):M word =
               word((x DIV 2 EXP k) MOD 2 EXP l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_subword; VAL_WORD] THEN
  AP_TERM_TAC THEN ASM_SIMP_TAC[DIV_MOD_EXP_LOW]);;

(* ------------------------------------------------------------------------- *)
(* Constants in the image. MLKEM_NATIVE_IMAGE_CONST_RULE d k gives           *)
(*                                                                           *)
(* |- !s pc. bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc      *)
(*           ==> read (memory :> bytes<k> (word(pc + d))) s = word v         *)
(*                                                                           *)
(* for the k-bit value v (k = 8, 16, 32, 64 or 128) at address d in the      *)
(* image, and MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE n d k gives the same with *)
(* the address in the form that the simulation gives for a RIP-relative      *)
(* operand in an instruction ending at n, word(val(word(pc + n)) + (d - n)). *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_WBYTES_LOADED = prove
 (`!(a:int64) (l:byte list) s:x86state.
        bytes_loaded s a l /\ LENGTH l = dimindex(:N) DIV 8
        ==> read (memory :> wbytes a) s:N word = word(num_of_bytelist l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bytes_loaded] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM WORD_VAL] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[]);;

let MLKEM_NATIVE_IMAGE_CONST_RULE =
  let rec take n l =
    if n = 0 then [] else
    match l with h::t -> h::take (n - 1) t | [] -> failwith "take" in
  let rec drop n l =
    if n = 0 then l else
    match l with _::t -> drop (n - 1) t | [] -> failwith "drop" in
  let imagel = dest_list(rhs(concl mlkem_native_libmlkem_gcc12_O2_mc)) in
  let wbths = [8,BYTES8_WBYTES; 16,BYTES16_WBYTES; 32,BYTES32_WBYTES;
               64,BYTES64_WBYTES; 128,BYTES128_WBYTES] in
  let bl_tm = `bytes_loaded s (word pc) mlkem_native_libmlkem_gcc12_O2_mc` in
  fun d k ->
    let l = mk_list(take (k / 8) (drop d imagel),`:byte`) in
    let th1 = UNDISCH(SPEC_ALL(BYTES_LOADED_SUBPROGRAM_RULE
                mlkem_native_libmlkem_gcc12_O2_mc (REFL l) d)) in
    let a = rand(rator(concl th1)) in
    let lth = ISPECL [a; l; `s:x86state`]
               (INST_TYPE [mk_finty(Num.num_of_int k),`:N`]
                          READ_MEMORY_WBYTES_LOADED) in
    let lenth = prove(rand(lhand(concl lth)),
      REWRITE_TAC[LENGTH] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV) in
    let th2 = MP lth (CONJ th1 lenth) in
    let th3 = CONV_RULE(RAND_CONV(RAND_CONV
      (REWRITE_CONV[num_of_bytelist] THENC DEPTH_CONV WORD_RED_CONV THENC
       NUM_REDUCE_CONV))) th2 in
    let th4 = REWRITE_RULE[GSYM(assoc k wbths)] th3 in
    GENL [`s:x86state`; `pc:num`] (DISCH bl_tm th4);;

let WORD_VAL_ADD_64 = prove
 (`!x n. word(val(word x:int64) + n):int64 = word(x + n)`,
  REWRITE_TAC[WORD_ADD; WORD_VAL]);;

let MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE next target k =
  let th = MLKEM_NATIVE_IMAGE_CONST_RULE target k in
  let disp = target - next in
  let lt = mk_comb(`word:num->int64`,
    mk_binop `(+):num->num->num`
     (mk_comb(`val:int64->num`,
        mk_comb(`word:num->int64`,
          mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral next))))
     (mk_small_numeral disp)) in
  let eth = (REWRITE_CONV[WORD_VAL_ADD_64; GSYM ADD_ASSOC] THENC
             NUM_REDUCE_CONV) lt in
  REWRITE_RULE[GSYM eth] th;;

(*** MLKEM_NATIVE_IMAGE_RIPREL_ALIGNED_TAC n d adds the alignment of such an
 *** address, for an aligned SSE load of a vector at a multiple d of 16,
 *** given that of pc
 ***)

let MLKEM_NATIVE_IMAGE_RIPREL_ALIGNED_TAC next target =
  let tm = subst [mk_small_numeral next,`n:num`;
                  mk_small_numeral (target - next),`d:num`]
    `aligned 16 (word (val (word (pc + n):int64) + d):int64)` in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [REWRITE_TAC[WORD_VAL_ADD_64; GSYM ADD_ASSOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[WORD_ADD] THEN
    CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC];;
