(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the FULL proofs of the packing glue of signatures and keys of   *)
(* mldsa-native (packing.c): the copies of byte strings that the compiler    *)
(* has inlined as 128-bit loads and stores (mld_pack_sig_c,                  *)
(* mld_pack_sk_rho_key_tr, mld_unpack_sk), the tail calls at offsets         *)
(* computed from an index (mld_pack_sig_z, mld_unpack_pk_t1), and the        *)
(* packing and unpacking of the hints (mld_pack_sig_h,                       *)
(* mld_sig_unpack_hints).                                                    *)
(* ========================================================================= *)

needs "common/layout.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "arm/proofs/utils/mldsa_native_polyvec.ml";;
needs "common/mldsa_native_hints.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(* ------------------------------------------------------------------------- *)
(* Byte strings copied with 128-bit loads and stores. The inputs are facts   *)
(* !j. j < n ==> read (bytes8 (word_add a (word j))) s0 = b j: before the    *)
(* simulation, GLUE_LOAD128_TAC a offs adds the facts for the 128-bit words  *)
(* at a + off for each offset off in offs, with the bytes of b. After it,    *)
(* GLUE_STORE_TAC r splits each fact about a 32-, 64- or 128-bit word stored *)
(* at r or at word_add r e into the facts for its bytes, with the addresses  *)
(* normalized, and GLUE_BYTES_FINAL_TAC proves a goal                        *)
(* !j. j < n ==> read (bytes8 (word_add r (word(m + j)))) s = ... from them. *)
(* ------------------------------------------------------------------------- *)

let GLUE_LOAD128_TAC =
  let pat = `!j. j < n ==> read(memory :> bytes8(word_add a (word j))) s0 =
                           (b:num->byte) j` in
  fun (a:term) (offs:int list) ->
    W(fun (asl,w) ->
      let th = snd(find (fun (_,th) ->
                 try let i = term_match [] pat (concl th) in
                     instantiate i `a:int64` = a
                 with Failure _ -> false) asl) in
      let lanes = CONJUNCTS(CONV_RULE(EXPAND_CASES_CONV THENC
                                      REWRITE_CONV[WORD_ADD_0]) th) in
      MAP_EVERY (fun off ->
        let addr = if off = 0 then a else
                   subst [a,`a:int64`; mk_small_numeral off,`n:num`]
                         `word_add (a:int64) (word n)` in
        ASSUME_TAC(REWRITE_RULE lanes (READ_MEMORY_MERGE_CONV 4
          (subst [addr,`A:int64`] `read (memory :> bytes128 A) s0`))))
       offs);;

let GLUE_STORE_TAC (r:term) =
  let ok a = (a = r) ||
             (try lhand a = r && fst(dest_const(rator(rator a))) = "word_add"
              with Failure _ -> false)
  and levels = ["bytes32",2; "bytes64",3; "bytes128",4] in
  REPEAT(FIRST_X_ASSUM(fun th ->
    let c = concl th in
    try let l,_ = dest_eq c in
        let comp = rand(rator l) and st = rand l in
        let bytesf,addr = dest_comb(rand comp) in
        let n = assoc (fst(dest_const bytesf)) levels in
        if ok addr && not(st = `s0:armstate`) then
          STRIP_ASSUME_TAC
           (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
             (CONV_RULE(SIMD_SIMPLIFY_CONV [])
               (CONV_RULE(READ_MEMORY_SPLIT_CONV n) th)))
        else NO_TAC
    with Failure _ -> NO_TAC));;

let GLUE_BYTES_FINAL_TAC =
  CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
           REWRITE_CONV[WORD_ADD_0]) THEN
  ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Part of a byte string given by a fact !j. j < m ==> read (bytes8          *)
(* (word_add a (word j))) s = b j, e.g. for the precondition of a callee:    *)
(* GLUE_SLICE_TAC tm proves and assumes tm, of the form !j. j < n ==> read   *)
(* (bytes8 (word_add a (word(e + j)))) s = b(e' + j) with e + j and e' + j   *)
(* equal up to the association of the additions.                             *)
(* ------------------------------------------------------------------------- *)

let GLUE_SLICE_TAC tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[GSYM ADD_ASSOC] THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN SIMPLE_ARITH_TAC);
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* The address of a tail call, computed from an index with 32-bit            *)
(* operations: GLUE_REG_TAC reg tm replaces the value v of the 64-bit        *)
(* register reg in the assumptions by tm, proving v = tm with WORD_SMALL_TAC *)
(* from the bound on the index in the assumptions.                           *)
(* ------------------------------------------------------------------------- *)

let GLUE_REG_TAC (reg:term) (tm:term) =
  let rd = `read:(armstate,int64)component->armstate->int64` in
  FIRST_ASSUM(fun th ->
    try let l,r = dest_eq(concl th) in
        if rator l = mk_comb(rd,reg) then
          SUBGOAL_THEN (mk_eq(r,tm)) SUBST_ALL_TAC THENL
           [WORD_SMALL_TAC; ALL_TAC]
        else NO_TAC
    with Failure _ -> NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The loop of mld_pack_sig_h, as one loop over the positions p of the       *)
(* vector (coefficient p MOD 256 of polynomial p DIV 256). With hint bits h, *)
(* the code goes through glue_hint_steps omega n h of the n positions: all   *)
(* of them if there are at most omega hints, else up to the first that does  *)
(* not fit (glue_hint_fail omega h p), where it returns.                     *)
(* ------------------------------------------------------------------------- *)

let glue_hint_fail = new_definition
 `glue_hint_fail omega (h:num->bool) p <=>
    h p /\ mld_hint_count h p = omega`;;

let glue_hint_steps = new_definition
 `glue_hint_steps omega n (h:num->bool) =
    if mld_hint_count h n <= omega then n
    else (minimal p. glue_hint_fail omega h p) + 1`;;

let GLUE_HINT_FAIL_EXISTS = prove
 (`!h omega n. ~(mld_hint_count h n <= omega)
               ==> ?p. p < n /\ glue_hint_fail omega h p`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[mld_hint_count; LE_0; glue_hint_fail] THEN
  ASM_CASES_TAC `mld_hint_count h n <= omega` THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[LT] THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[glue_hint_fail] THEN MESON_TAC[LT]]);;

let GLUE_HINT_STEPS = prove
 (`!h omega n.
        let np = glue_hint_steps omega n h in
        np <= n /\
        (0 < n ==> 0 < np) /\
        (mld_hint_count h n <= omega ==> np = n) /\
        (!p. p < np ==> mld_hint_count h p <= omega) /\
        (!p. p < np
             ==> (glue_hint_fail omega h p <=>
                  p + 1 = np /\ ~(mld_hint_count h n <= omega)))`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[glue_hint_steps] THEN
  ASM_CASES_TAC `mld_hint_count h n <= omega` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[LE_REFL; glue_hint_fail] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MLD_HINT_COUNT_MONO; LT_IMP_LE; LE_TRANS]; ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`h:num->bool`; `p + 1`; `n:num`] MLD_HINT_COUNT_MONO) THEN
    ASM_REWRITE_TAC[MLD_HINT_COUNT_ADD1] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`h:num->bool`; `omega:num`; `n:num`] GLUE_HINT_FAIL_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?p. glue_hint_fail omega (h:num->bool) p` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN BETA_TAC THEN
  ABBREV_TAC `m = minimal p. glue_hint_fail omega (h:num->bool) p` THEN
  REWRITE_TAC[glue_hint_fail] THEN STRIP_TAC THEN
  SUBGOAL_THEN `m < n` ASSUME_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM NOT_LT] THEN ASM_MESON_TAC[glue_hint_fail];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. p <= m ==> mld_hint_count h p <= omega` ASSUME_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[mld_hint_count; LE_0] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[glue_hint_fail]] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ARITH_TAC;
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    REWRITE_TAC[EQ_ADD_RCANCEL] THEN EQ_TAC THENL
     [STRIP_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM NOT_LT] THEN ASM_MESON_TAC[glue_hint_fail];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The tests of the code for the hint of a coefficient a0 with high part a1: *)
(* a0 + gamma2 <= 2 * gamma2 as unsigned 32-bit numbers (a0 is within        *)
(* [-gamma2, gamma2], glue_hint_inr_88/32), with the flags of the comparison *)
(* as the simulation gives them (GLUE_FLAGS_LS, GLUE_INR_VAL), and then      *)
(* a1 <> 0 and a0 = -gamma2 with a conditional comparison (GLUE_CCMP_EQ).    *)
(* ------------------------------------------------------------------------- *)

let glue_hint_inr_88 = new_definition
 `glue_hint_inr_88 (a:int32) <=> -- &95232 <= ival a /\ ival a <= &95232`;;

let glue_hint_inr_32 = new_definition
 `glue_hint_inr_32 (a:int32) <=> -- &261888 <= ival a /\ ival a <= &261888`;;

let GLUE_FLAGS_LS = prove
 (`!v:int32 c.
        c < 2 EXP 32
        ==> (~(&(val v) - &c:int = &(val(word_sub v (word c))) /\
               ~(val(word_sub v (word c)) = 0)) <=>
             val v <= c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word c:int32) = c` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN MATCH_MP_TAC MOD_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM VAL_EQ] THEN
  ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_32] THEN
  MP_TAC(ISPEC `v:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
  DISCH_TAC THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN ASM_ARITH_TAC;
    REWRITE_TAC[INT_ARITH `&a - &c:int = &b <=> &a:int = &b + &c`;
                INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ASM_ARITH_TAC]);;

let GLUE_INR_VAL = prove
 (`!a:int32 g.
        2 * g < 2 EXP 31
        ==> (val(word_add a (word g)) <= 2 * g <=>
             -- &g <= ival a /\ ival a <= &g)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ADD_CASES; INT_IVAL; DIMINDEX_32; VAL_WORD] THEN
  MP_TAC(ISPEC `a:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `g MOD 4294967296 = g` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[INT_ARITH `-- &g:int <= &x - &n <=> &n:int <= &x + &g`;
              INT_ARITH `&x - &n:int <= &g <=> &x:int <= &g + &n`;
              INT_ARITH `-- &g:int <= &x`; INT_OF_NUM_ADD; INT_OF_NUM_LE] THEN
  ASM_ARITH_TAC);;

let GLUE_INR_88 = prove
 (`!a:int32. val(word_add a (word 95232)) <= 190464 <=> glue_hint_inr_88 a`,
  GEN_TAC THEN REWRITE_TAC[glue_hint_inr_88] THEN
  MP_TAC(SPECL [`a:int32`; `95232`] GLUE_INR_VAL) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let GLUE_INR_32 = prove
 (`!a:int32. val(word_add a (word 261888)) <= 523776 <=> glue_hint_inr_32 a`,
  GEN_TAC THEN REWRITE_TAC[glue_hint_inr_32] THEN
  MP_TAC(SPECL [`a:int32`; `261888`] GLUE_INR_VAL) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let GLUE_CCMP_EQ = prove
 (`!a0:int32 a1:int32 m.
        (if ~(val(word_sub a1 (word 0)) = 0)
         then val(word_sub a0 (word m)) = 0 else F) <=>
        ~(a1 = word 0) /\ a0 = word m`,
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; WORD_SUB_0] THEN MESON_TAC[]);;

(*** The hint bit when a0 is out of range, and when it is within it ***)

let GLUE_HINT_OUT_88 = prove
 (`!a0 a1. ~glue_hint_inr_88 a0 ==> mld_make_hint_88 a0 a1`,
  REWRITE_TAC[glue_hint_inr_88; mld_make_hint_88] THEN INT_ARITH_TAC);;

let GLUE_HINT_OUT_32 = prove
 (`!a0 a1. ~glue_hint_inr_32 a0 ==> mld_make_hint_32 a0 a1`,
  REWRITE_TAC[glue_hint_inr_32; mld_make_hint_32] THEN INT_ARITH_TAC);;

let GLUE_HINT_INR_88 = prove
 (`!a0 a1. glue_hint_inr_88 a0
           ==> (mld_make_hint_88 a0 a1 <=>
                ~(a1 = word 0) /\ a0 = word 4294872064)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[glue_hint_inr_88; mld_make_hint_88] THEN
  SUBGOAL_THEN `(a0:int32) = word 4294872064 <=> ival a0 = -- &95232`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IVAL_EQ] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `a1:int32 = word 0` THEN ASM_REWRITE_TAC[] THEN
  INT_ARITH_TAC);;

let GLUE_HINT_INR_32 = prove
 (`!a0 a1. glue_hint_inr_32 a0
           ==> (mld_make_hint_32 a0 a1 <=>
                ~(a1 = word 0) /\ a0 = word 4294705408)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[glue_hint_inr_32; mld_make_hint_32] THEN
  SUBGOAL_THEN `(a0:int32) = word 4294705408 <=> ival a0 = -- &261888`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IVAL_EQ] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `a1:int32 = word 0` THEN ASM_REWRITE_TAC[] THEN
  INT_ARITH_TAC);;

(*** The hint bit of position i, from the coefficient of w0 and the one of ***)
(*** w1 that the code unpacks into the scratch polynomial ***)

let GLUE_POLYVEC_HINT_88 = prove
 (`!x b i. mld_polyvec_make_hint_88 x b i <=>
           mld_make_hint_88 (x i)
            (mld_polyw1_unpack_88 (\t. b(192 * i DIV 256 + t)) (i MOD 256))`,
  REWRITE_TAC[mld_polyvec_make_hint_88; mld_polyvec_unpack; mld_polyvec]);;

let GLUE_POLYVEC_HINT_32 = prove
 (`!x b i. mld_polyvec_make_hint_32 x b i <=>
           mld_make_hint_32 (x i)
            (mld_polyw1_unpack_32 (\t. b(128 * i DIV 256 + t)) (i MOD 256))`,
  REWRITE_TAC[mld_polyvec_make_hint_32; mld_polyvec_unpack; mld_polyvec]);;

(*** The range test as the simulation gives it ***)

let GLUE_RANGE_88 = prove
 (`!a:int32.
     ~(&(val(word_add a (word 95232))) - &190464:int =
       &(val(word_sub (word_add a (word 95232)) (word 190464))) /\
       ~(val(word_sub (word_add a (word 95232)) (word 190464)) = 0)) <=>
     glue_hint_inr_88 a`,
  GEN_TAC THEN REWRITE_TAC[GSYM GLUE_INR_88] THEN
  MATCH_MP_TAC GLUE_FLAGS_LS THEN CONV_TAC NUM_REDUCE_CONV);;

let GLUE_RANGE_32 = prove
 (`!a:int32.
     ~(&(val(word_add a (word 261888))) - &523776:int =
       &(val(word_sub (word_add a (word 261888)) (word 523776))) /\
       ~(val(word_sub (word_add a (word 261888)) (word 523776)) = 0)) <=>
     glue_hint_inr_32 a`,
  GEN_TAC THEN REWRITE_TAC[GSYM GLUE_INR_32] THEN
  MATCH_MP_TAC GLUE_FLAGS_LS THEN CONV_TAC NUM_REDUCE_CONV);;

(*** The comparison of the count with omega, and the tests of the index ***)
(*** of the coefficient after its increment ***)

let GLUE_W32_EQ = prove
 (`!n m. n < 2 EXP 32 /\ m < 2 EXP 32
         ==> (val(word_sub (word_zx (word n:int64):int32) (word m)) = 0 <=>
              n = m)`,
  REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  ASM_SIMP_TAC[WORD_ZX_64_32_SMALL] THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM VAL_EQ; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]);;

let GLUE_J_TEST = prove
 (`!j. j < 256
       ==> (val(word_add (word j) (word 18446744073709551361):int64) = 0 <=>
            ~(j < 255))`,
  REPEAT STRIP_TAC THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand)
                     VAL_WORD_ADD_COMPLEMENT_EQ_0 (lhand w))) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

(*** The position after i, in the same polynomial or the next one ***)

let GLUE_MOD_NEXT = prove
 (`!i. (i MOD 256 < 255
        ==> (i + 1) MOD 256 = i MOD 256 + 1 /\ (i + 1) DIV 256 = i DIV 256) /\
       (~(i MOD 256 < 255)
        ==> (i + 1) MOD 256 = 0 /\ (i + 1) DIV 256 = i DIV 256 + 1 /\
            256 * (i DIV 256 + 1) = i + 1)`,
  GEN_TAC THEN MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  ABBREV_TAC `q = i DIV 256` THEN ABBREV_TAC `r = i MOD 256` THEN
  STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q:num` THEN ASM_ARITH_TAC;
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `r + 1` THEN ASM_ARITH_TAC;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `q + 1` THEN ASM_ARITH_TAC;
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(*** The number of positions after the step for position i ***)

let GLUE_HINT_NEXT = prove
 (`!h omega n i.
        i < glue_hint_steps omega n h
        ==> (glue_hint_fail omega h i
             ==> glue_hint_steps omega n h = i + 1 /\
                 ~(mld_hint_count h n <= omega)) /\
            (~glue_hint_fail omega h i /\ i + 1 < n
             ==> i + 1 < glue_hint_steps omega n h /\
                 ~(i + 1 = glue_hint_steps omega n h)) /\
            (~glue_hint_fail omega h i /\ i + 1 = n
             ==> glue_hint_steps omega n h = i + 1 /\
                 mld_hint_count h n <= omega)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`h:num->bool`; `omega:num`; `n:num`] GLUE_HINT_STEPS) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `np = glue_hint_steps omega n h` THEN STRIP_TAC THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `mld_hint_count h n <= omega` THEN
  ASM_SIMP_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The proof of a FULL theorem for mld_pack_sig_h. Its loop over the         *)
(* polynomials, with the unpacking of w1 into the scratch polynomial, and    *)
(* the loop over their coefficients are one loop over the positions i, from  *)
(* the head of the inner loop (label loop2) to the next head or to the end   *)
(* (join3), whose iteration for i goes through one of the paths of the code: *)
(* the range test of the coefficient of w0 (glue_hint_inr_88/32), the test   *)
(* of the hint bit for those within the range, the test of the count of the  *)
(* hints so far against omega (glue_hint_fail) and the tests of the index    *)
(* (i MOD 256 < 255) and of the polynomial (i DIV 256 < k - 1). The events   *)
(* template has one function for each path. GLUE_PSH_RUN_TAC prm 1 simulates *)
(* the iteration from the head, splitting the goal at each branch on these   *)
(* predicates (GLUE_PSH_DECIDE_TAC), and proves the invariant for i + 1 at   *)
(* the end of each path (GLUE_PSH_FINAL_TAC). The parameters prm give the    *)
(* code, the hint bits and the constants of the parameter set.               *)
(* ------------------------------------------------------------------------- *)

type glue_psh =
 { psh_exec : thm * thm option array;
   psh_fn : string;
   psh_callee : string;
   psh_hintf : term;
   psh_inrf : term;
   psh_unpackf : term;
   psh_range : thm;
   psh_inr : thm;
   psh_out : thm;
   psh_unfold : thm;
   psh_omega : int;
   psh_k : int;
   psh_wbytes : int;
   psh_sigh : int;
   psh_gamma : int };;

let glue_psh_hint prm =
  list_mk_comb(prm.psh_hintf,[`x:num->int32`; `b:num->byte`]);;

let glue_psh_vars =
  [`x:num->int32`; `b:num->byte`; `sig:int64`; `w0:int64`; `w1p:int64`;
   `scratch:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`;
   `i:num`];;

let glue_psh_inst prm tm =
  let n = mk_small_numeral in
  vsubst [glue_psh_hint prm,`H:num->bool`;
          prm.psh_hintf,`HF:(num->int32)->(num->byte)->num->bool`;
          prm.psh_inrf,`IF:int32->bool`;
          prm.psh_unpackf,`UNPACK:(num->byte)->num->int32`;
          n prm.psh_omega,`OM:num`;
          n (256 * prm.psh_k),`NN:num`; n prm.psh_k,`KK:num`;
          n (prm.psh_k - 1),`K1:num`; n prm.psh_wbytes,`WB:num`;
          n (prm.psh_wbytes * prm.psh_k),`WK:num`;
          n (1024 * prm.psh_k),`XK:num`;
          n prm.psh_sigh,`SH:num`; n (prm.psh_sigh + prm.psh_omega),`ST:num`;
          n prm.psh_gamma,`GA:num`; n (2 * prm.psh_gamma),`G2:num`;
          n (4294967296 - prm.psh_gamma),`GN:num`]
         tm;;

(*** Specialize an assumption !p. P p ==> Q p, matching pat, to tm ***)

let GLUE_ASM_SPEC_TAC pat tm =
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && can (term_match [] pat) (concl th) then
      MP_TAC(SPEC tm th) THEN ANTS_TAC THENL
       [SIMPLE_ARITH_TAC ORELSE (ASM_REWRITE_TAC[] THEN NO_TAC); DISCH_TAC]
    else NO_TAC);;

(*** Equations of words formed from small numbers, as WORD_SMALL_TAC of ***)
(*** utils/mldsa_native.ml does, also for bytes and for numbers such as ***)
(*** i MOD 256, removing those MOD that the bounds allow ***)

let GLUE_MOD_LT_TAC =
  W(fun (asl,w) ->
    let tms = find_terms
     (fun t -> is_binary "MOD" t && is_numeral(rand t) &&
               not(is_numeral(lhand t))) w in
    FIRST(map (fun t ->
      MP_TAC(SPECL [lhand t; rand t] MOD_LT) THEN
      ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC])
     (sort free_in (setify tms))));;

let GLUE_WORD_SMALL_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SUB_CASES; VAL_WORD_ZX_GEN;
              VAL_WORD; VAL_WORD_SHL; DIMINDEX_8; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(GLUE_MOD_LT_TAC ORELSE
         (COND_CASES_TAC THEN TRY(FIRST_ASSUM(fun th ->
            if is_neg(concl th) then
              (MP_TAC th THEN SIMPLE_ARITH_TAC) else NO_TAC)))) THEN
  SIMPLE_ARITH_TAC;;

(*** The PC in the current state, and its offset in the function ***)

let glue_current_pc (asl,w) =
  let s = rand w in
  rhs(concl(snd(find (fun (_,th) ->
    try lhs(concl th) = mk_comb(`read PC`,s) with Failure _ -> false) asl)));;

let glue_pc_offset base t =
  try dest_small_numeral(rand(rand t)) - base with Failure _ -> -1;;

(*** Split on p, deciding the branch and the events in each case ***)

let GLUE_PSH_CASES_TAC (p:term) =
  let pcev th =
    let c = concl th in
    is_eq c &&
    (can (term_match [] `read PC s`) (lhs c) ||
     can (term_match [] `read events s`) (lhs c)) in
  ASM_CASES_TAC p THEN
  POP_ASSUM(fun cth ->
    let eq = if is_neg(concl cth) then EQF_INTRO cth else EQT_INTRO cth in
    RULE_ASSUM_TAC(fun th -> if pcev th then REWRITE_RULE[eq] th else th) THEN
    ASSUME_TAC cth);;

let GLUE_PSH_DECIDE_TAC prm =
  let inst = glue_psh_inst prm in
  let hi = inst `(H:num->bool) i`
  and fl = inst `glue_hint_fail OM H i`
  and cnt = inst `mld_hint_count H i`
  and lastp = inst `i DIV 256 < K1` in
  let pcev th =
    let c = concl th in
    is_eq c &&
    (can (term_match [] `read PC s`) (lhs c) ||
     can (term_match [] `read events s`) (lhs c)) in
  let canon eq =
    RULE_ASSUM_TAC(fun th ->
      if pcev th then REWRITE_RULE[eq; NOT_CLAUSES] th else th) in
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; prm.psh_range;
                              GLUE_CCMP_EQ]) THEN
  W(fun (asl,w) ->
    let c0,_ = dest_cond(glue_current_pc (asl,w)) in
    let c = if is_neg c0 then rand c0 else c0 in
    let occurs t = can (find_term ((=) t)) c in
    if is_comb c && is_const(rator c) &&
       mem (fst(dest_const(rator c))) ["glue_hint_inr_88"; "glue_hint_inr_32"]
    then
      GLUE_PSH_CASES_TAC c THENL
       [ALL_TAC;
        SUBGOAL_THEN hi ASSUME_TAC THENL
         [REWRITE_TAC[prm.psh_unfold] THEN MATCH_MP_TAC prm.psh_out THEN
          FIRST_ASSUM ACCEPT_TAC;
          ALL_TAC]]
    else if is_conj c then
      SUBGOAL_THEN (mk_iff(c,hi)) canon THENL
       [REWRITE_TAC[prm.psh_unfold] THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC prm.psh_inr THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      GLUE_PSH_CASES_TAC hi THENL
       [ALL_TAC;
        SUBGOAL_THEN (mk_neg fl) ASSUME_TAC THENL
         [REWRITE_TAC[glue_hint_fail] THEN ASM_REWRITE_TAC[]; ALL_TAC]]
    else if occurs cnt then
      SUBGOAL_THEN (mk_iff(c,fl)) canon THENL
       [REWRITE_TAC[glue_hint_fail; ASSUME hi] THEN
        MATCH_MP_TAC GLUE_W32_EQ THEN CONV_TAC NUM_REDUCE_CONV THEN
        SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      GLUE_PSH_CASES_TAC fl THENL
       [ALL_TAC;
        SUBGOAL_THEN (inst `mld_hint_count H i < OM`) ASSUME_TAC THENL
         [UNDISCH_TAC (mk_neg fl) THEN
          REWRITE_TAC[glue_hint_fail; ASSUME hi] THEN SIMPLE_ARITH_TAC;
          ALL_TAC]]
    else if occurs `i MOD 256` then
      canon(MP (SPEC `i MOD 256` GLUE_J_TEST) (ASSUME `i MOD 256 < 256`))
      THEN GLUE_PSH_CASES_TAC `i MOD 256 < 255` THENL
       [MP_TAC(CONJUNCT1(SPEC `i:num` GLUE_MOD_NEXT));
        MP_TAC(CONJUNCT2(SPEC `i:num` GLUE_MOD_NEXT))] THEN
      (ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC])
    else
      SUBGOAL_THEN (mk_iff(c,mk_neg lastp)) canon THENL
       [REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN GLUE_WORD_SMALL_TAC;
        ALL_TAC] THEN
      GLUE_PSH_CASES_TAC lastp);;

(*** The facts for the iteration for position i, before the simulation ***)

let GLUE_PSH_PREP_TAC prm =
  let inst = glue_psh_inst prm in
  GLUE_ASM_SPEC_TAC `!p. p < n ==> mld_hint_count h p <= m` `i:num` THEN
  SUBGOAL_THEN `i MOD 256 < 256` ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN (inst `i DIV 256 < KK`) ASSUME_TAC THENL
   [SUBGOAL_THEN (inst `i < NN`) MP_TAC THENL
     [SIMPLE_ARITH_TAC; ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word(i MOD 256):int64) = i MOD 256` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC (inst `mld_hint_count H i`) VAL_WORD_ZX_UXTW) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPEC (inst `mld_hint_count H i`) WORD_ZX_ZX_SMALL) THEN
  ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `read(memory :> bytes32(word_add w0
                    (word(1024 * i DIV 256 + 4 * i MOD 256)))) s0 =
    (x:num->int32) i`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `1024 * i DIV 256 + 4 * i MOD 256 = 4 * i` SUBST1_TAC THENL
     [MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN ARITH_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in `scratch:int64` (concl th) then
      ASSUME_TAC(MP (SPEC `i MOD 256` th) (ASSUME `i MOD 256 < 256`))
    else NO_TAC) THEN
  SUBGOAL_THEN
   (inst `!t. t < OM /\ ~(t = mld_hint_count H i)
              ==> read(memory :> bytes8(word_add sig (word(SH + t)))) s0 =
                  mld_hint_index H i t`)
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   (inst `!t. t < KK /\ ~(t = i DIV 256)
              ==> read(memory :> bytes8(word_add sig (word(ST + t)))) s0 =
                  if t < i DIV 256
                  then word(mld_hint_count H (256 * (t + 1)))
                  else word 0`)
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** The registers for the next polynomial, and the call of the function ***)
(*** unpacking its w1, in the state before the call (step n) ***)

let GLUE_PSH_REGS_TAC prm =
  let inst = glue_psh_inst prm in
  GLUE_REG_TAC `X28` (inst `word_add w1p (word(WB * (i DIV 256 + 1))):int64`)
  THEN GLUE_REG_TAC `X21` `word_add w0 (word(1024 * (i DIV 256 + 1))):int64`
  THEN GLUE_REG_TAC `X23`
        (inst `word_add sig (word(ST + (i DIV 256 + 1))):int64`);;

let GLUE_PSH_CALL_TAC prm (b':term) (slice:term) n =
  let sv = mk_var("s"^string_of_int(n-1),`:armstate`) in
  SUBGOAL_THEN (vsubst [sv,`s:armstate`] slice) ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc prm.psh_exec "H_UNPACK"
   [`read X0 s`; `read X1 s`; b'; `pc:num`; `read X30 s`] glue_psh_vars n;;

(*** The end of an iteration: the next position, and the invariant for it ***)

let GLUE_PSH_NEXT_TAC prm =
  let inst = glue_psh_inst prm in
  let fl = inst `glue_hint_fail OM H i` in
  let th0 = SPECL [glue_psh_hint prm; mk_small_numeral prm.psh_omega;
                   mk_small_numeral(256 * prm.psh_k); `i:num`]
                  GLUE_HINT_NEXT in
  let arith =
    MP_TAC(SPECL [`i:num`; `256`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    SIMPLE_ARITH_TAC in
  W(fun (asl,w) ->
    let has t = exists (fun (_,th) -> concl th = t) asl in
    MP_TAC(MP th0 (ASSUME(lhand(concl th0)))) THEN
    if has fl then
      DISCH_THEN(MP_TAC o C MP (ASSUME fl) o CONJUNCT1) THEN STRIP_TAC
    else if has (mk_neg `i MOD 256 < 255`) &&
            has (mk_neg(inst `i DIV 256 < K1`)) then
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; arith];
                      STRIP_TAC]
    else
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; arith];
                      STRIP_TAC]);;

let GLUE_PSH_INDEX_TAC =
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN GLUE_WORD_SMALL_TAC;
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];;

let GLUE_PSH_TALLY_TAC =
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN ASM_CASES_TAC `t = i DIV 256` THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE `k < k + 1`; MLD_HINT_COUNT_ADD1] THEN
    GLUE_WORD_SMALL_TAC;
    SUBGOAL_THEN `t < i DIV 256 + 1 <=> t < i DIV 256` SUBST1_TAC THENL
     [SIMPLE_ARITH_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];;

let GLUE_PSH_RET_TAC =
  REWRITE_TAC[mld_pack_hints_ret] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;;

let GLUE_PSH_FINAL_TAC prm =
  GLUE_PSH_NEXT_TAC prm THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[MLD_HINT_COUNT_ADD1; MLD_HINT_INDEX_ADD1; LT_REFL;
                  ADD_CLAUSES] THEN
  REPEAT CONJ_TAC THEN
  TRY(GLUE_WORD_SMALL_TAC THEN NO_TAC) THEN
  TRY(GLUE_PSH_INDEX_TAC THEN NO_TAC) THEN
  TRY(GLUE_PSH_TALLY_TAC THEN NO_TAC) THEN
  TRY(GLUE_PSH_RET_TAC THEN NO_TAC) THEN
  PATH_DISCHARGE_TAC;;

(*** The simulation of the iteration from step n, with the address of the ***)
(*** store of the index in the events as in the facts for the memory ***)

let GLUE_PSH_EVENTS_TAC =
  let pat = `word_zx(word_zx(word n:int64):int32):int64` in
  FIRST_ASSUM(fun eth ->
    if is_eq(concl eth) && can (term_match [] pat) (lhs(concl eth)) then
      RULE_ASSUM_TAC(fun th ->
        let c = concl th in
        if is_eq c && can (term_match [] `read events s`) (lhs c)
        then REWRITE_RULE[eth] th else th)
    else NO_TAC);;


let rec GLUE_PSH_RUN_TAC prm n (asl,w) =
  let inst = glue_psh_inst prm in
  let base = layout prm.psh_fn in
  let lbl l = layout(prm.psh_fn ^ "_" ^ l) - base in
  let pct = glue_current_pc (asl,w) in
  let off = glue_pc_offset base pct in
  if n > 1 && (off = lbl "loop2" || off = lbl "join3") then
    GLUE_PSH_FINAL_TAC prm (asl,w)
  else if off + base = layout prm.psh_callee then
    (GLUE_PSH_CALL_TAC prm
       (inst `\t. (b:num->byte)(WB * (i DIV 256 + 1) + t)`)
       (inst `!j. j < WB
                  ==> read(memory :> bytes8
                        (word_add w1p (word(WB * (i DIV 256 + 1) + j)))) s =
                      (b:num->byte)(WB * (i DIV 256 + 1) + j)`) n THEN
     GLUE_PSH_RUN_TAC prm (n + 1)) (asl,w)
  else
    ((if off = lbl "loop1" then GLUE_PSH_REGS_TAC prm else ALL_TAC) THEN
     ARM_STEPS_TAC prm.psh_exec [n] THEN TRY GLUE_PSH_EVENTS_TAC THEN
     (fun g -> if is_cond(glue_current_pc g) then GLUE_PSH_DECIDE_TAC prm g
               else ALL_TAC g) THEN
     GLUE_PSH_RUN_TAC prm (n + 1)) (asl,w);;

let GLUE_PSH_BODY_TAC prm =
  let inst = glue_psh_inst prm in
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[ASSUME(inst `i < glue_hint_steps OM NN H`)] THEN
  FULL_INIT_TAC THEN GLUE_PSH_PREP_TAC prm THEN GLUE_PSH_RUN_TAC prm 1;;

(*** The return: the hints from the facts for all positions when the count ***)
(*** is at most omega ***)

let GLUE_PSH_BYTES_TAC prm =
  let inst = glue_psh_inst prm in
  let cnt_ok = inst `mld_hint_count H NN <= OM` in
  REWRITE_TAC[mld_pack_hints_ret] THEN CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THENL [ALL_TAC; CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[]]
  THEN DISCH_THEN(K ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && lhand(concl th) = cnt_ok && is_conj(rand(concl th))))
  THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) && lhand(concl th) = cnt_ok && is_eq(rand(concl th))))
  THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST_ALL_TAC] THEN
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN REWRITE_TAC[mld_pack_hints] THEN
  COND_CASES_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN (inst `SH + t = ST + (t - OM)`) SUBST1_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN (inst `t - OM < KK`) ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC (inst `t - OM`) o check (fun th ->
      is_forall(concl th) && free_in (inst `ST:num`) (concl th))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]];;

let GLUE_PSH_EXIT_TAC prm =
  REWRITE_TAC[LT_REFL] THEN FULL_INIT_TAC THEN
  ARM_STEPS_TAC prm.psh_exec (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [GLUE_PSH_BYTES_TAC prm; DISCHARGE_SAFETY_PROPERTY_TAC];;

(*** The events template: one function for each path of an iteration ***)

let glue_psh_template prm = glue_psh_inst prm
 `\(x:num->int32) (b:num->byte) (sig:int64) (w0:int64) (w1p:int64)
   (scratch:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
   APPEND
    (f_ev_epil x b sig w0 w1p scratch pc stackpointer returnaddress)
    (APPEND
      (ENUMERATEL (glue_hint_steps OM NN (HF x b))
        (\p. if glue_hint_fail OM (HF x b) p
             then if IF (x p)
                  then f_ev_f2 x b sig w0 w1p scratch pc stackpointer
                               returnaddress p
                  else f_ev_f1 x b sig w0 w1p scratch pc stackpointer
                               returnaddress p
             else if p MOD 256 < 255
             then if HF x b p
                  then if IF (x p)
                       then f_ev_m2 x b sig w0 w1p scratch pc stackpointer
                                    returnaddress p
                       else f_ev_m1 x b sig w0 w1p scratch pc stackpointer
                                    returnaddress p
                  else f_ev_m3 x b sig w0 w1p scratch pc stackpointer
                               returnaddress p
             else if p DIV 256 < K1
             then if HF x b p
                  then if IF (x p)
                       then f_ev_e2 x b sig w0 w1p scratch pc stackpointer
                                    returnaddress p
                       else f_ev_e1 x b sig w0 w1p scratch pc stackpointer
                                    returnaddress p
                  else f_ev_e3 x b sig w0 w1p scratch pc stackpointer
                               returnaddress p
             else if HF x b p
             then if IF (x p)
                  then f_ev_l2 x b sig w0 w1p scratch pc stackpointer
                               returnaddress p
                  else f_ev_l1 x b sig w0 w1p scratch pc stackpointer
                               returnaddress p
             else f_ev_l3 x b sig w0 w1p scratch pc stackpointer
                          returnaddress p))
      (f_ev_prol x b sig w0 w1p scratch pc stackpointer returnaddress))
   :(uarch_event)list`;;

(*** The invariant at the head for position i: the registers and the ***)
(*** stack, the inputs, the registers and the scratch polynomial for i if ***)
(*** the code goes through it, the hint bytes so far if the code goes ***)
(*** through i or there are at most omega hints, and the return value at ***)
(*** the end ***)

let glue_psh_inv prm = glue_psh_inst prm
 `\i s.
  read SP s = stackpointer /\
  read X20 s = scratch /\ read X22 s = word G2 /\
  read X24 s = word_add w1p (word WK) /\ read X25 s = word GA /\
  read X26 s = word_add sig (word SH) /\ read X27 s = word GN /\
  read (memory :> bytes64 stackpointer) s = x19_init /\
  read (memory :> bytes64 (word_add stackpointer (word 8))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 16))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 24))) s = x22_init /\
  read (memory :> bytes64 (word_add stackpointer (word 32))) s = x23_init /\
  read (memory :> bytes64 (word_add stackpointer (word 40))) s = x24_init /\
  read (memory :> bytes64 (word_add stackpointer (word 48))) s = x25_init /\
  read (memory :> bytes64 (word_add stackpointer (word 56))) s = x26_init /\
  read (memory :> bytes64 (word_add stackpointer (word 64))) s = x27_init /\
  read (memory :> bytes64 (word_add stackpointer (word 72))) s = x28_init /\
  read (memory :> bytes64 (word_add stackpointer (word 80))) s =
    returnaddress /\
  (!q. q < NN
       ==> read(memory :> bytes32(word_add w0 (word(4 * q)))) s = x q) /\
  (!j. j < WK ==> read(memory :> bytes8(word_add w1p (word j))) s = b j) /\
  (i < glue_hint_steps OM NN H
   ==> read X4 s = word(i MOD 256) /\
       read X19 s = word(mld_hint_count H i) /\
       read X21 s = word_add w0 (word(1024 * i DIV 256)) /\
       read X23 s = word_add sig (word(ST + i DIV 256)) /\
       read X28 s = word_add w1p (word(WB * i DIV 256)) /\
       (!j. j < 256
            ==> read(memory :> bytes32(word_add scratch (word(4 * j)))) s =
                UNPACK (\t. b(WB * i DIV 256 + t)) j)) /\
  (i < glue_hint_steps OM NN H \/ mld_hint_count H NN <= OM
   ==> (!t. t < OM
            ==> read(memory :> bytes8(word_add sig (word(SH + t)))) s =
                mld_hint_index H i t) /\
       (!t. t < KK
            ==> read(memory :> bytes8(word_add sig (word(ST + t)))) s =
                if t < i DIV 256 then word(mld_hint_count H (256 * (t + 1)))
                else word 0)) /\
  (i = glue_hint_steps OM NN H
   ==> read X0 s = word_zx(mld_pack_hints_ret OM KK H))`;;

(*** The code before the loop, with the stores of zeros to the hints and ***)
(*** the call for polynomial 0, from step n ***)

let rec GLUE_PSH_PRO_TAC prm n (asl,w) =
  let inst = glue_psh_inst prm in
  let base = layout prm.psh_fn in
  let off = glue_pc_offset base (glue_current_pc (asl,w)) in
  if off = layout(prm.psh_fn ^ "_loop2") - base then
    (ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     REWRITE_TAC[mld_hint_count; mld_hint_index; WORD_ADD_0; ADD_CLAUSES;
                 ETA_AX; CONJUNCT1 LT] THEN
     ASM_SIMP_TAC[ARITH_RULE `0 < n ==> ~(0 = n)`] THEN
     REPEAT CONJ_TAC THEN
     TRY(GLUE_BYTES_FINAL_TAC THEN NO_TAC) THEN
     TRY(FIRST_ASSUM MATCH_ACCEPT_TAC THEN NO_TAC) THEN
     DISCHARGE_SAFETY_PROPERTY_TAC) (asl,w)
  else if off + base = layout prm.psh_callee then
    (GLUE_PSH_CALL_TAC prm `b:num->byte`
      (inst `!j. j < WB
                 ==> read(memory :> bytes8(word_add w1p (word j))) s =
                     (b:num->byte) j`) n THEN
     GLUE_PSH_PRO_TAC prm (n + 1)) (asl,w)
  else
    (ARM_STEPS_TAC prm.psh_exec [n] THEN GLUE_STORE_TAC `sig:int64` THEN
     GLUE_PSH_PRO_TAC prm (n + 1)) (asl,w);;

(*** The whole proof, given the FULL theorem for unpacking w1 ***)

let GLUE_PSH_FULL_TAC prm calleeth =
  let inst = glue_psh_inst prm in
  let np = inst `glue_hint_steps OM NN H` in
  let lbl l =
    mk_binary "+" (`pc:num`,mk_small_numeral(layout(prm.psh_fn ^ "_" ^ l))) in
  ASSUME_CALLEE_SAFETY_TAILED_TAC calleeth "H_UNPACK" THEN
  CONCRETIZE_F_EVENTS_TAC (glue_psh_template prm) THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst prm.psh_exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [glue_psh_hint prm; mk_small_numeral prm.psh_omega;
                mk_small_numeral(256 * prm.psh_k)] GLUE_HINT_STEPS) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  STRIP_TAC THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x25_init" `X25` THEN
  ENSURES_PRESERVED_TAC "x26_init" `X26` THEN
  ENSURES_PRESERVED_TAC "x27_init" `X27` THEN
  ENSURES_PRESERVED_TAC "x28_init" `X28` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC np (lbl "loop2") (lbl "join3")
    (glue_psh_inv prm) THEN
  REPEAT CONJ_TAC THENL
   [SIMPLE_ARITH_TAC;
    FULL_INIT_TAC THEN GLUE_PSH_PRO_TAC prm 1;
    GLUE_PSH_BODY_TAC prm;
    GLUE_PSH_EXIT_TAC prm];;

(*** The num value of a word built from small numbers and bytes ***)

let rec glue_small_val t =
  match t with
    Comb(Const("word",_),n) -> n
  | Comb(Const("word_zx",_),x) -> glue_small_val x
  | Comb(Comb(Const("word_add",_),x),y) ->
      mk_binary "+" (glue_small_val x,glue_small_val y)
  | _ -> if type_of t = `:byte` then mk_comb(`val:byte->num`,t)
         else failwith "glue_small_val";;

let GLUE_VAL_BYTE = prove
 (`!x:byte. val x < 256`,
  GEN_TAC THEN MP_TAC(ISPEC `x:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

(*** Arithmetic with the small numbers, also using the bounds of bytes ***)

let GLUE_ARITH_TAC =
  let numty = `:num` in
  let is_num_relop tm =
    exists (fun op -> is_binary op tm &&
                      (let x,_ = dest_binary op tm in type_of x = numty))
           ["=";"<";"<=";">";">="] in
  let avoiderp tm =
    match tm with Const(n,_) -> mem n ["read"; "write"; "word"] | _ -> false in
  let filtered tm =
    (is_num_relop tm || (is_neg tm && is_num_relop (dest_neg tm))) &&
    not(can (find_term avoiderp) tm) in
  W(fun (asl,w) ->
    let vals = setify(find_terms (fun t ->
      try fst(dest_const(rator t)) = "val" && type_of(rand t) = `:byte`
      with Failure _ -> false) (list_mk_conj(w::map (concl o snd) asl))) in
    let asl' = filter (fun (_,th) -> filtered(concl th)) asl in
    MAP_EVERY (MP_TAC o snd) asl' THEN
    MAP_EVERY (fun t -> MP_TAC(SPEC (rand t) GLUE_VAL_BYTE)) vals THEN
    CONV_TAC ARITH_RULE);;

let GLUE_MOD_LT2_TAC =
  W(fun (asl,w) ->
    let tms = find_terms
     (fun t -> is_binary "MOD" t && is_numeral(rand t) &&
               not(is_numeral(lhand t))) w in
    FIRST(map (fun t ->
      MP_TAC(SPECL [lhand t; rand t] MOD_LT) THEN
      ANTS_TAC THENL [GLUE_ARITH_TAC; DISCH_THEN SUBST1_TAC])
     (sort free_in (setify tms))));;

let GLUE_WORD_SMALL2_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD_SUB_CASES; VAL_WORD_ZX_GEN;
              VAL_WORD; VAL_WORD_SHL; DIMINDEX_8; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT GLUE_MOD_LT2_TAC THEN GLUE_ARITH_TAC;;

(*** The flags of 32-bit comparisons of small numbers, as arithmetic ***)

let GLUE_W32_FLAGS_TAC =
  let pat = `read (c:(armstate,A)component) (s:armstate)` in
  let pcev th =
    let c = concl th in
    (is_eq c || is_iff c) && can (term_match [] pat) (lhs c) in
  let all_concls (asl,w) =
    list_mk_conj(`T` :: filter (fun t -> pcev(ASSUME t))
                                 (map (concl o snd) asl)) in
  let rewr th =
    RULE_ASSUM_TAC(fun th' -> if pcev th' then REWRITE_RULE[th] th' else th') in
  W(fun g ->
    let tms = setify(find_terms
      (can (term_match [] `word_zx(word n:int64):int32`)) (all_concls g)) in
    MAP_EVERY (fun t ->
      TRY(MP_TAC(SPEC (rand(rand t)) WORD_ZX_64_32_SMALL) THEN
          ANTS_TAC THENL [GLUE_ARITH_TAC; DISCH_THEN rewr])) tms) THEN
  W(fun g ->
    let tms = setify(find_terms
      (can (term_match [] `word_sub (word x) (word y):int32`))
      (all_concls g)) in
    MAP_EVERY (fun t ->
      let x = rand(lhand t) and y = rand(rand t) in
      TRY(MP_TAC(SPECL [x;y] WORD_CMP_32_FLAGS) THEN
          ANTS_TAC THENL [CONJ_TAC THEN GLUE_ARITH_TAC; DISCH_THEN rewr]))
     tms) THEN
  W(fun g ->
    let tms = setify(find_terms
      (can (term_match [] `val(word n:int32)`)) (all_concls g)) in
    MAP_EVERY (fun t ->
      let n = rand(rand t) in
      if is_numeral n then ALL_TAC else
      TRY(SUBGOAL_THEN (mk_eq(t,n)) rewr THENL
           [REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN MATCH_MP_TAC MOD_LT THEN
            CONV_TAC NUM_REDUCE_CONV THEN GLUE_ARITH_TAC;
            ALL_TAC])) tms);;

(* ------------------------------------------------------------------------- *)
(* The loops of mld_sig_unpack_hints, for the omega + k bytes b of the       *)
(* hints and polynomial i, with the counts before it (mld_hints_start, s)    *)
(* and up to it (glue_suh_new, w): the code fails at once if                 *)
(* glue_suh_early, else sets the coefficients b j for j from s, in           *)
(* glue_suh_n1 iterations, up to w or up to the first that is not greater    *)
(* than the one before (glue_suh_ok1 says there is none), and then, for the  *)
(* last polynomial, if b w = 0 (w < omega), checks the bytes from w + 1 in   *)
(* glue_suh_n2 iterations, up to omega or the first that is not zero         *)
(* (glue_suh_zeros says the bytes from w are zero). glue_suh_h n gives the   *)
(* coefficients after n iterations of the first loop.                        *)
(* ------------------------------------------------------------------------- *)

let glue_suh_new = new_definition
 `glue_suh_new omega (b:num->byte) i = val(b(omega + i))`;;

let glue_suh_early = new_definition
 `glue_suh_early omega (b:num->byte) i <=>
    glue_suh_new omega b i < mld_hints_start omega b i \/
    omega < glue_suh_new omega b i`;;

let glue_suh_ok1 = new_definition
 `glue_suh_ok1 omega (b:num->byte) i <=>
    !j. mld_hints_start omega b i < j /\ j < glue_suh_new omega b i
        ==> val(b(j - 1)) < val(b j)`;;

let glue_suh_zeros = new_definition
 `glue_suh_zeros omega (b:num->byte) i <=>
    !j. glue_suh_new omega b i <= j /\ j < omega ==> b j = word 0`;;

let glue_suh_n1 = new_definition
 `glue_suh_n1 omega (b:num->byte) i =
    if glue_suh_early omega b i \/
       ~(mld_hints_start omega b i < glue_suh_new omega b i) then 0
    else (minimal j. mld_hints_start omega b i < j /\
                     (j = glue_suh_new omega b i \/
                      val(b j) <= val(b(j - 1)))) -
         mld_hints_start omega b i`;;

let glue_suh_loop2 = new_definition
 `glue_suh_loop2 omega k (b:num->byte) i <=>
    ~glue_suh_early omega b i /\ glue_suh_ok1 omega b i /\ i = k - 1 /\
    glue_suh_new omega b i < omega /\ b(glue_suh_new omega b i) = word 0`;;

let glue_suh_n2 = new_definition
 `glue_suh_n2 omega k (b:num->byte) i =
    if glue_suh_loop2 omega k b i
    then (minimal m. glue_suh_new omega b i < m /\
                     (m = omega \/ ~(b m = word 0))) -
         glue_suh_new omega b i
    else 0`;;

let glue_suh_steps = new_definition
 `glue_suh_steps omega k (b:num->byte) i =
    glue_suh_n1 omega b i + glue_suh_n2 omega k b i`;;

let glue_suh_h = new_definition
 `glue_suh_h omega (b:num->byte) i n q:int32 =
    if ?j. mld_hints_start omega b i <= j /\
           j < mld_hints_start omega b i + n /\ val(b j) = q
    then word 1 else word 0`;;

(*** The return value, and the coefficients so far ***)

let GLUE_SUH_OK = prove
 (`!omega k (b:num->byte) i.
        mld_unpack_hints_ok omega k b i <=>
        ~glue_suh_early omega b i /\ glue_suh_ok1 omega b i /\
        (i = k - 1 ==> glue_suh_zeros omega b i)`,
  REWRITE_TAC[mld_unpack_hints_ok; glue_suh_early; glue_suh_ok1;
              glue_suh_zeros; glue_suh_new; NOT_LT; DE_MORGAN_THM] THEN
  MESON_TAC[]);;

let GLUE_SUH_H_0 = prove
 (`!omega (b:num->byte) i q. glue_suh_h omega b i 0 q = word 0`,
  REWRITE_TAC[glue_suh_h; ADD_CLAUSES] THEN ARITH_TAC);;

let GLUE_SUH_H_ADD1 = prove
 (`!omega (b:num->byte) i n q.
        glue_suh_h omega b i (n + 1) q =
        if val(b(mld_hints_start omega b i + n)) = q then word 1
        else glue_suh_h omega b i n q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[glue_suh_h] THEN
  ABBREV_TAC `s = mld_hints_start omega (b:num->byte) i` THEN
  SUBGOAL_THEN
   `!P. (?j. s <= j /\ j < s + n + 1 /\ P j) <=>
        P(s + n) \/ (?j. s <= j /\ j < s + n /\ P j)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `j:num = s + n` THENL
       [DISJ1_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
        DISJ2_TAC THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC];
      STRIP_TAC THENL
       [EXISTS_TAC `s + n:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]];
    ASM_CASES_TAC `val((b:num->byte)(s + n)) = q` THEN ASM_REWRITE_TAC[]]);;

let GLUE_SUH_H_FULL = prove
 (`!omega (b:num->byte) i n q.
        mld_hints_start omega b i + n = glue_suh_new omega b i
        ==> glue_suh_h omega b i n q = mld_unpack_hints omega b i q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[glue_suh_h; mld_unpack_hints; glue_suh_new]
  THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(*** The number of iterations of the first loop, and the tests in them ***)

let GLUE_SUH_N1 = prove
 (`!omega (b:num->byte) i.
        ~glue_suh_early omega b i /\
        mld_hints_start omega b i < glue_suh_new omega b i
        ==> let s = mld_hints_start omega b i
            and w = glue_suh_new omega b i
            and n1 = glue_suh_n1 omega b i in
            0 < n1 /\ s + n1 <= w /\
            (!p. p + 1 < n1
                 ==> s + p + 1 < w /\ val(b(s + p)) < val(b(s + p + 1))) /\
            (glue_suh_ok1 omega b i <=> s + n1 = w) /\
            (~glue_suh_ok1 omega b i
             ==> s + n1 < w /\ val(b(s + n1)) <= val(b((s + n1) - 1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[glue_suh_n1; glue_suh_ok1] THEN
  ABBREV_TAC `s = mld_hints_start omega (b:num->byte) i` THEN
  ABBREV_TAC `w = glue_suh_new omega (b:num->byte) i` THEN
  SUBGOAL_THEN
   `?j. s < j /\ (j = w \/ val((b:num->byte) j) <= val(b(j - 1)))`
  MP_TAC THENL [EXISTS_TAC `w:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN BETA_TAC THEN
  ABBREV_TAC
   `m = minimal j. s < j /\ (j = w \/ val((b:num->byte) j) <= val(b(j - 1)))`
  THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `m <= w` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. s < j /\ j < m ==> ~(j = w) /\ val((b:num->byte)(j - 1)) < val(b j)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s + p + 1`) THEN
    REWRITE_TAC[ARITH_RULE `(s + p + 1) - 1 = s + p`] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    EQ_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `m:num = w` THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (is_forall o concl) o
        check (fun th -> free_in `w:num` (concl th) &&
                         not(free_in `m:num` (concl th)))) THEN
      ASM_ARITH_TAC;
      DISCH_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        is_forall(concl th) && free_in `m:num` (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
    DISCH_TAC THEN
    SUBGOAL_THEN `~(m:num = w)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC
       `~(!j. s < j /\ j < w ==> val((b:num->byte)(j - 1)) < val(b j))` THEN
      REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        is_forall(concl th) && free_in `m:num` (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `s + m - s = m` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [ASM_MESON_TAC[]; FIRST_ASSUM ACCEPT_TAC]]);;

(*** The number of iterations of the second loop, and the tests in them ***)

let GLUE_SUH_N2 = prove
 (`!omega k (b:num->byte) i.
        glue_suh_loop2 omega k b i
        ==> let w = glue_suh_new omega b i
            and n2 = glue_suh_n2 omega k b i in
            0 < n2 /\ w + n2 <= omega /\
            (!q. q + 1 < n2 ==> w + q + 1 < omega /\ b(w + q + 1) = word 0) /\
            (glue_suh_zeros omega b i <=> w + n2 = omega) /\
            (~glue_suh_zeros omega b i
             ==> w + n2 < omega /\ ~(b(w + n2) = word 0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[glue_suh_n2; glue_suh_zeros] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[glue_suh_loop2]) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC `w = glue_suh_new omega (b:num->byte) i` THEN
  SUBGOAL_THEN `?m. w < m /\ (m = omega \/ ~((b:num->byte) m = word 0))`
  MP_TAC THENL [EXISTS_TAC `omega:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN BETA_TAC THEN
  ABBREV_TAC
   `m = minimal m. w < m /\ (m = omega \/ ~((b:num->byte) m = word 0))` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `m <= omega` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `omega:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. w < j /\ j < m ==> ~(j = omega) /\ (b:num->byte) j = word 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!j. w <= j /\ j < omega ==> (b:num->byte) j = word 0) <=> m = omega`
  ASSUME_TAC THENL
   [EQ_TAC THENL
     [DISCH_TAC THEN ASM_CASES_TAC `m:num = omega` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th ->
        is_forall(concl th) && not(free_in `m:num` (concl th)))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
      DISCH_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      ASM_CASES_TAC `j:num = w` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        is_forall(concl th) && free_in `m:num` (concl th) &&
        not(is_neg(concl th)))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `w + m - w = m` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w + q + 1` o check (fun th ->
      is_forall(concl th) && free_in `m:num` (concl th) &&
      not(is_neg(concl th)))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [ASM_MESON_TAC[]; FIRST_ASSUM ACCEPT_TAC]]);;

let GLUE_SUH_LOOP2_OK = prove
 (`!omega k (b:num->byte) i.
        glue_suh_loop2 omega k b i
        ==> (mld_unpack_hints_ok omega k b i <=> glue_suh_zeros omega b i)`,
  REWRITE_TAC[glue_suh_loop2; GLUE_SUH_OK] THEN MESON_TAC[]);;

(*** The counts and the result in the cases of the tests of the code ***)

let GLUE_SUH_FACTS = prove
 (`!omega k (b:num->byte) i.
      (glue_suh_early omega b i
       ==> glue_suh_n1 omega b i = 0 /\ glue_suh_n2 omega k b i = 0 /\
           ~mld_unpack_hints_ok omega k b i) /\
      (~glue_suh_early omega b i /\
       ~(mld_hints_start omega b i < glue_suh_new omega b i)
       ==> glue_suh_n1 omega b i = 0 /\ glue_suh_ok1 omega b i) /\
      (~glue_suh_ok1 omega b i
       ==> glue_suh_n2 omega k b i = 0 /\ ~mld_unpack_hints_ok omega k b i) /\
      (~glue_suh_early omega b i /\ glue_suh_ok1 omega b i /\ ~(i = k - 1)
       ==> glue_suh_n2 omega k b i = 0 /\ mld_unpack_hints_ok omega k b i) /\
      (~glue_suh_early omega b i /\ glue_suh_ok1 omega b i /\ i = k - 1 /\
       glue_suh_new omega b i = omega
       ==> glue_suh_n2 omega k b i = 0 /\ mld_unpack_hints_ok omega k b i) /\
      (~glue_suh_early omega b i /\ glue_suh_ok1 omega b i /\ i = k - 1 /\
       ~(glue_suh_new omega b i = omega) /\
       ~(b(glue_suh_new omega b i) = word 0)
       ==> glue_suh_n2 omega k b i = 0 /\ ~mld_unpack_hints_ok omega k b i) /\
      (~glue_suh_early omega b i /\ glue_suh_ok1 omega b i /\ i = k - 1 /\
       ~(glue_suh_new omega b i = omega) /\
       b(glue_suh_new omega b i) = word 0
       ==> glue_suh_loop2 omega k b i /\
           (mld_unpack_hints_ok omega k b i <=> glue_suh_zeros omega b i))`,
  REPEAT GEN_TAC THEN
  MP_TAC(REWRITE_CONV[glue_suh_early] `glue_suh_early omega (b:num->byte) i`)
  THEN
  MP_TAC(REWRITE_CONV[glue_suh_ok1] `glue_suh_ok1 omega (b:num->byte) i`) THEN
  MP_TAC(REWRITE_CONV[glue_suh_zeros] `glue_suh_zeros omega (b:num->byte) i`)
  THEN
  MP_TAC(REWRITE_CONV[glue_suh_loop2]
          `glue_suh_loop2 omega k (b:num->byte) i`) THEN
  MP_TAC(REWRITE_CONV[glue_suh_n1] `glue_suh_n1 omega (b:num->byte) i`) THEN
  MP_TAC(REWRITE_CONV[glue_suh_n2] `glue_suh_n2 omega k (b:num->byte) i`) THEN
  MP_TAC(REWRITE_CONV[GLUE_SUH_OK]
          `mld_unpack_hints_ok omega k (b:num->byte) i`) THEN
  SPEC_TAC(`mld_unpack_hints_ok omega k (b:num->byte) i`,`ok:bool`) THEN
  SPEC_TAC(`glue_suh_n2 omega k (b:num->byte) i`,`n2:num`) THEN
  SPEC_TAC(`glue_suh_n1 omega (b:num->byte) i`,`n1:num`) THEN
  SPEC_TAC(`glue_suh_loop2 omega k (b:num->byte) i`,`l2:bool`) THEN
  SPEC_TAC(`glue_suh_zeros omega (b:num->byte) i`,`zs:bool`) THEN
  SPEC_TAC(`glue_suh_ok1 omega (b:num->byte) i`,`o1:bool`) THEN
  SPEC_TAC(`glue_suh_early omega (b:num->byte) i`,`ea:bool`) THEN
  SPEC_TAC(`mld_hints_start omega (b:num->byte) i`,`s:num`) THEN
  SPEC_TAC(`glue_suh_new omega (b:num->byte) i`,`w:num`) THEN
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REPEAT CONJ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  TRY(X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_ARITH_TAC) THEN
  TRY(EXISTS_TAC `w:num` THEN ASM_REWRITE_TAC[LE_REFL] THEN ASM_ARITH_TAC)
  THEN ASM_ARITH_TAC);;

let GLUE_SUH_BOUNDS = prove
 (`!omega (b:num->byte) i.
        mld_hints_start omega b i < 256 /\ glue_suh_new omega b i < 256`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_hints_start; glue_suh_new] THEN
  COND_CASES_TAC THEN REWRITE_TAC[GLUE_VAL_BYTE] THEN ARITH_TAC);;

(*** Arithmetic with the counts, with the number of iterations as a sum ***)

let GLUE_STEPS_ARITH_TAC =
  let isst t =
    try let f,args = strip_comb t in
        fst(dest_const f) = "glue_suh_steps" && length args = 4
    with Failure _ -> false in
  W(fun (asl,w) ->
    let ts = setify(find_terms isst (list_mk_conj(w::map (concl o snd) asl))) in
    MAP_EVERY (fun t -> MP_TAC(REWRITE_CONV[glue_suh_steps] t)) ts THEN
    GLUE_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The proof of a FULL theorem for mld_sig_unpack_hints. The two loops of    *)
(* the code are one loop over the glue_suh_steps = n1 + n2 iterations p      *)
(* (GLUE_ENSURES_WHILE), with the invariant glue_suh_inv whose PC is the     *)
(* head of the first loop for p < n1, that of the second for n1 <= p and one *)
(* of the two returns at the end. The record gives the parameter set, and    *)
(* suh_regs1 the registers at the head of the first loop for the position    *)
(* j, which differ between them. An iteration is proved in the cases of the  *)
(* paths of the code (GLUE_SUH_BODY_TAC), each with its own function in the  *)
(* events template glue_suh_template.                                        *)
(* ------------------------------------------------------------------------- *)

type glue_suh =
 { suh_exec : thm * thm option array;
   suh_fn : string;
   suh_omega : int;
   suh_k : int;
   suh_sigh : int;
   suh_regs1 : term };;

let glue_suh_inst prm tm =
  let n = mk_small_numeral in
  let lbl l = n(layout(prm.suh_fn ^ "_" ^ l)) in
  vsubst [n prm.suh_omega,`OM:num`; n (prm.suh_omega - 1),`OM1:num`;
          n prm.suh_k,`KK:num`; n (prm.suh_k - 1),`K1:num`;
          n prm.suh_sigh,`SH:num`; n (prm.suh_omega + prm.suh_k),`HB:num`;
          lbl "loop1",`L1:num`; lbl "loop2",`L2:num`;
          lbl "join3",`J3:num`; lbl "join6",`J6:num`] tm;;

let glue_suh_vars =
  [`b:num->byte`; `i:num`; `h:int64`; `sig:int64`; `mf:int64`; `pc:num`;
   `stackpointer:int64`; `returnaddress:int64`; `p:num`];;

let glue_suh_pcev =
  let pat = `read (c:(armstate,A)component) (s:armstate)` in
  fun th ->
    let c = concl th in
    (is_eq c || is_iff c) && can (term_match [] pat) (lhs c);;

(*** Register values that are small words, as word n, with the values of   ***)
(*** their UXTW views; byte values named by the equations in the context   ***)

let glue_rassoc e = rand(concl(REWRITE_CONV[GSYM ADD_ASSOC] e));;

let rec glue_base_off t =
  match t with
    Comb(Comb(Const("word_add",_),x),y) ->
      (try let e = glue_small_val y in
           let b,off = glue_base_off x in
           b,Some(match off with
                    None -> e
                  | Some e' -> glue_rassoc(mk_binary "+" (e',e)))
       with Failure _ -> t,None)
  | _ -> t,None;;

let GLUE_SMALL_REGS2_TAC =
  let rd = `read:(armstate,int64)component->armstate->int64` in
  let regs = [`X0`;`X1`;`X2`;`X3`;`X4`;`X5`;`X6`;`X7`;`X19`;`X20`;`X21`;
              `X22`;`X23`] in
  let is_word t = is_comb t && is_const(rator t) &&
                  fst(dest_const(rator t)) = "word" in
  let one reg =
    TRY(FIRST_ASSUM(fun th ->
      let l,r = dest_eq(concl th) in
      if rator l <> mk_comb(rd,reg) || is_word r then NO_TAC else
      try let e = glue_rassoc(glue_small_val r) in
          let tm = mk_comb(`word:num->int64`,e) in
          SUBGOAL_THEN (mk_eq(r,tm)) SUBST_ALL_TAC THENL
           [GLUE_WORD_SMALL2_TAC; ALL_TAC]
      with Failure _ ->
        match glue_base_off r with
          b,Some e ->
            let tm = list_mk_icomb "word_add"
                       [b; mk_comb(`word:num->int64`,e)] in
            if tm = r then NO_TAC else
            SUBGOAL_THEN (mk_eq(r,tm)) SUBST_ALL_TAC THENL
             [GLUE_WORD_SMALL2_TAC; ALL_TAC]
        | _ -> NO_TAC)) in
  let uxtw reg =
    TRY(FIRST_ASSUM(fun th ->
      let l,r = dest_eq(concl th) in
      if rator l <> mk_comb(rd,reg) || not(is_word r) || is_numeral(rand r)
      then NO_TAC else
      let e = rand r in
      let vt = mk_eq(mk_comb(`val:int64->num`,
                 mk_comb(`word_zx:int32->int64`,
                   mk_comb(`word_zx:int64->int32`,r))),e) in
      W(fun (asl,w) ->
        if exists (fun (_,th) -> concl th = vt) asl then NO_TAC else
        MP_TAC(SPEC e VAL_WORD_ZX_UXTW) THEN
        MP_TAC(SPEC e WORD_ZX_ZX_SMALL) THEN
        REWRITE_TAC[ARITH_RULE `n < 2 EXP 32 <=> n < 4294967296`] THEN
        ANTS_TAC THENL [GLUE_ARITH_TAC; STRIP_TAC] THEN
        ANTS_TAC THENL [GLUE_ARITH_TAC; STRIP_TAC]))) in
  MAP_EVERY one regs THEN MAP_EVERY uxtw regs;;

let GLUE_SUH_ATOMS_TAC =
  W(fun (asl,w) ->
    let eqs = filter (fun th ->
      let c = concl th in
      is_eq c &&
      (try fst(dest_const(rator(lhs c))) = "val" &&
           type_of(rand(lhs c)) = `:byte` && not(is_var(rand(lhs c)))
       with Failure _ -> false)) (map snd asl) in
    if eqs = [] then ALL_TAC else
    RULE_ASSUM_TAC(fun th ->
      if glue_suh_pcev th then REWRITE_RULE eqs th else th));;

let GLUE_EVENTS_ZX_TAC =
  let pat = `word_zx(word_zx(word n:int64):int32):int64` in
  W(fun (asl,w) ->
    let eqs = filter (fun th ->
      let c = concl th in
      is_eq c && can (term_match [] pat) (lhs c)) (map snd asl) in
    if eqs = [] then ALL_TAC else
    RULE_ASSUM_TAC(fun th ->
      let c = concl th in
      if is_eq c && can (term_match [] `read events s`) (lhs c)
      then REWRITE_RULE eqs th else th));;

let GLUE_SUH_NORM_TAC =
  GLUE_SMALL_REGS2_TAC THEN GLUE_SUH_ATOMS_TAC THEN GLUE_EVENTS_ZX_TAC THEN
  GLUE_W32_FLAGS_TAC;;

(*** The byte of the hints at index t, at the address as the simulation ***)
(*** normalizes it                                                        ***)

let GLUE_INPUT_AT_TAC prm t =
  let inst = glue_suh_inst prm in
  let pat = inst `!j. j < HB ==> read(memory :> bytes8
                         (word_add sig (word(SH + j)))) s = (b:num->byte) j` in
  FIRST_ASSUM(fun th ->
    if can (term_match [] pat) (concl th) then
      MP_TAC(SPEC t th) THEN ANTS_TAC THENL [GLUE_STEPS_ARITH_TAC; DISCH_TAC]
    else NO_TAC);;

(*** Decide a branch from the facts, or split on one of the predicates of ***)
(*** the events template that it is equivalent to                         ***)

let GLUE_SUH_DECIDE_TAC prm =
  let inst = glue_suh_inst prm in
  let canon eq =
    RULE_ASSUM_TAC(fun th ->
      let c = concl th in
      if is_eq c && (can (term_match [] `read PC s`) (lhs c) ||
                     can (term_match [] `read events s`) (lhs c))
      then REWRITE_RULE[eq; NOT_CLAUSES] th else th) in
  let cands =
   [`0 < i`; inst `glue_suh_early OM (b:num->byte) i`;
    inst `mld_hints_start OM (b:num->byte) i < glue_suh_new OM b i`;
    inst `i < K1`; inst `OM <= glue_suh_new OM (b:num->byte) i`;
    inst `(b:num->byte)(glue_suh_new OM b i) = word 0`] in
  let hook p =
    if p = `0 < i` then
      W(fun (asl,w) ->
        if exists (fun (_,th) -> concl th = `0 < i`) asl then
          SUBGOAL_THEN
           (inst `val((b:num->byte)(i + OM1)) = mld_hints_start OM b i`)
          ASSUME_TAC THENL
           [REWRITE_TAC[mld_hints_start] THEN
            COND_CASES_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
            AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC;
            ALL_TAC]
        else
          SUBGOAL_THEN (inst `word 0:int64 = word(mld_hints_start OM b i)`)
           (fun eq -> FIRST_X_ASSUM(fun th ->
              if concl th = mk_eq(mk_comb(`read X21`,rand w),`word 0:int64`)
              then ASSUME_TAC(TRANS th eq) else NO_TAC)) THENL
           [REWRITE_TAC[mld_hints_start] THEN
            COND_CASES_TAC THENL [REFL_TAC; SIMPLE_ARITH_TAC];
            ALL_TAC])
    else if p = el 1 cands then
      W(fun (asl,w) ->
        if exists (fun (_,th) -> concl th = mk_neg p) asl then
          SUBGOAL_THEN
           (inst `mld_hints_start OM (b:num->byte) i <= glue_suh_new OM b i /\
                  glue_suh_new OM b i <= OM`) STRIP_ASSUME_TAC THENL
           [UNDISCH_TAC (mk_neg p) THEN REWRITE_TAC[glue_suh_early] THEN
            ARITH_TAC;
            ALL_TAC] THEN
          GLUE_INPUT_AT_TAC prm (inst `glue_suh_new OM (b:num->byte) i`)
        else ALL_TAC)
    else ALL_TAC in
  let equiv =
    REWRITE_TAC[glue_suh_early; COND_EXPAND; GSYM VAL_EQ_0] THEN
    GLUE_ARITH_TAC in
  let decide =
    (ASM_REWRITE_TAC[COND_EXPAND; VAL_EQ_0] THEN NO_TAC) ORELSE
    (REWRITE_TAC[COND_EXPAND] THEN GLUE_ARITH_TAC) in
  W(fun (asl,w) ->
    let c0,_ = dest_cond(glue_current_pc (asl,w)) in
    let split p =
      ((SUBGOAL_THEN (mk_iff(c0,p)) canon THENL [equiv; ALL_TAC]) ORELSE
       (SUBGOAL_THEN (mk_iff(c0,mk_neg p)) canon THENL [equiv; ALL_TAC])) THEN
      GLUE_PSH_CASES_TAC p THEN hook p in
    let addcands =
      MAP_EVERY (fun p ->
        W(fun (asl,w) ->
          if exists (fun (_,th) -> concl th = p || concl th = mk_neg p) asl
          then ALL_TAC else
          TRY(SUBGOAL_THEN p ASSUME_TAC THENL [equiv; ALL_TAC]) THEN
          TRY(SUBGOAL_THEN (mk_neg p) ASSUME_TAC THENL [equiv; ALL_TAC])))
       cands in
    ((((SUBGOAL_THEN c0 (canon o EQT_INTRO) THENL [decide; ALL_TAC]) ORELSE
       (SUBGOAL_THEN (mk_neg c0) (canon o EQF_INTRO) THENL [decide; ALL_TAC]))
      THEN addcands) ORELSE
     FIRST (map split cands)));;

(*** The simulation from step n to the next checkpoint (the heads of the  ***)
(*** loops and the two returns), with the call of memset                  ***)

let rec GLUE_SUH_RUN_TAC prm final n (asl,w) =
  let base = layout prm.suh_fn in
  let lbl l = layout(prm.suh_fn ^ "_" ^ l) - base in
  let off = glue_pc_offset base (glue_current_pc (asl,w)) in
  if n > 1 &&
     mem off [lbl "loop1"; lbl "loop2"; lbl "join3"; lbl "join6"] then
    final (asl,w)
  else if off + base = layout "plt_memset" then
    (LIBC_PLT_TAC prm.suh_exec (n - 1) THEN
     LIBC_SAFE_CALL_TAC "H_MEMSET" prm.suh_exec
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
       `read X30 s`] (ref glue_suh_vars) (n + 4) THEN
     GLUE_SUH_RUN_TAC prm final (n + 5)) (asl,w)
  else
    (ARM_STEPS_TAC prm.suh_exec [n] THEN GLUE_SUH_NORM_TAC THEN
     (fun g -> if is_cond(glue_current_pc g) then GLUE_SUH_DECIDE_TAC prm g
               else ALL_TAC g) THEN
     GLUE_SUH_RUN_TAC prm final (n + 1)) (asl,w);;

(*** A loop with any invariant (whose PC may depend on the iteration):    ***)
(*** the invariant iv i for the iterations i <= k, with the events of the ***)
(*** iterations so far, from the template in the postcondition            ***)

let GLUE_ENSURES_WHILE = prove
 (`!k (iv:num->A->bool) P Q C.
        C ,, C = C /\
        ensures step P (iv 0) C /\
        (!i. i < k ==> ensures step (iv i) (iv(i + 1)) C) /\
        ensures step (iv k) Q C
        ==> ensures step P Q C`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC `(iv:num->A->bool) k` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!n. n <= k ==> ensures step P ((iv:num->A->bool) n) C`
   (fun th -> MATCH_MP_TAC th THEN REWRITE_TAC[LE_REFL]) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
  EXISTS_TAC `(iv:num->A->bool) n` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[ADD1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let GLUE_EVENTS_WHILE_TAC (k:term) (iv:term) (asl,w) =
  let _,args = strip_comb w in
  let postcond = el 2 args in
  let sv,_ = dest_abs postcond in
  let ex = find_term (fun t -> is_exists t &&
             fst(dest_var(fst(dest_exists t))) = "e2") postcond in
  let v,bd = dest_exists ex in
  let c1,eqn,c3 = match conjuncts bd with
                    [a;b;c] -> a,b,c | _ -> failwith "GLUE_EVENTS_WHILE_TAC" in
  let _,mid = dest_binary "APPEND" (rhs eqn) in
  let enum,pro = dest_binary "APPEND" mid in
  let fn = rand enum in
  let i = fst(dest_abs iv) in
  let bv,body = dest_abs(snd(dest_abs iv)) in
  let ev_conj = mk_exists(v,list_mk_conj
    [c1; mk_eq(v,list_mk_icomb "APPEND"
              [list_mk_icomb "ENUMERATEL" [i;fn]; pro]); c3]) in
  let new_iv = mk_abs(i,mk_abs(bv,mk_conj(body,vsubst [bv,sv] ev_conj))) in
  (MATCH_MP_TAC GLUE_ENSURES_WHILE THEN
   MAP_EVERY EXISTS_TAC [k; new_iv] THEN
   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
   CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]) (asl,w);;

(*** The invariant at checkpoint p, and the facts at the start ***)

let glue_suh_inv prm =
  let regs1 = vsubst [`mld_hints_start OM (b:num->byte) i + p`,`j:num`]
                     prm.suh_regs1 in
  let body = glue_suh_inst prm (subst [regs1,`REGS1:bool`]
 `aligned_bytes_loaded (s:armstate) (word pc)
     mldsa_native_libmldsa_gcc12_O2_mc /\
   read SP s = stackpointer /\
   read (memory :> bytes64 stackpointer) s = x19_init /\
   read (memory :> bytes64 (word_add stackpointer (word 8))) s = x20_init /\
   read (memory :> bytes64 (word_add stackpointer (word 16))) s = x21_init /\
   read (memory :> bytes64 (word_add stackpointer (word 24))) s = x22_init /\
   read (memory :> bytes64 (word_add stackpointer (word 32))) s = x23_init /\
   read (memory :> bytes64 (word_add stackpointer (word 40))) s =
     returnaddress /\
   read X19 s = sig /\ read X22 s = word_add sig (word SH) /\
   read X23 s = word i /\ read X21 s = word(mld_hints_start OM b i) /\
   (!j. j < HB
        ==> read(memory :> bytes8(word_add sig (word(SH + j)))) s = b j) /\
   read PC s =
     word(if p < glue_suh_steps OM KK b i
          then if p < glue_suh_n1 OM b i then pc + L1 else pc + L2
          else if mld_unpack_hints_ok OM KK b i then pc + J6 else pc + J3) /\
   (p < glue_suh_n1 OM b i
    ==> REGS1 /\ read X6 s = h /\ read X7 s = word 1 /\
        read X20 s = word(glue_suh_new OM b i)) /\
   (glue_suh_n1 OM b i <= p /\ p < glue_suh_steps OM KK b i
    ==> read X20 s = word(glue_suh_new OM b i + (p - glue_suh_n1 OM b i) + 1) /\
        read X0 s = word 0) /\
   (p = glue_suh_steps OM KK b i
    ==> read X0 s = word_zx(mld_unpack_hints_ret OM KK b i)) /\
   (p < glue_suh_steps OM KK b i \/ mld_unpack_hints_ok OM KK b i
    ==> !q. q < 256
            ==> read(memory :> bytes32(word_add h (word(4 * q)))) s =
                glue_suh_h OM b i (MIN (p:num) (glue_suh_n1 OM b i)) q)`) in
  list_mk_abs([`p:num`; `s:armstate`],body);;
let GLUE_SUH_INIT_PREP_TAC prm =
  let inst = glue_suh_inst prm in
  STRIP_ASSUME_TAC(SPECL [mk_small_numeral prm.suh_omega; `b:num->byte`;
                          `i:num`] GLUE_SUH_BOUNDS) THEN
  SUBGOAL_THEN (inst `val((b:num->byte)(i + OM)) = glue_suh_new OM b i`)
  ASSUME_TAC THENL
   [REWRITE_TAC[glue_suh_new] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN
  GLUE_INPUT_AT_TAC prm (inst `i + OM1`) THEN
  GLUE_INPUT_AT_TAC prm (inst `i + OM`);;

(*** Zero coefficients from the zero bytes that memset gives ***)

let GLUE_ZERO32 = prove
 (`!a n s.
        (!j. j < 4 * n
             ==> read(memory :> bytes8(word_add a (word j))) s =
                 word_zx(word 0:int64))
        ==> !q. q < n
                ==> read(memory :> bytes32(word_add a (word(4 * q)))) s =
                    word 0`,
  REPEAT STRIP_TAC THEN
  CONV_TAC(LAND_CONV(READ_MEMORY_MERGE_CONV 2)) THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  SUBGOAL_THEN `4 * q < 4 * n /\ 4 * q + 1 < 4 * n /\ 4 * q + 2 < 4 * n /\
                4 * q + 3 < 4 * n` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[WORD_ADD_0] THEN CONV_TAC WORD_REDUCE_CONV);;

let GLUE_ZERO32_TAC =
  let lem = GEN `a:int64` (CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
              (SPECL [`a:int64`; `256`] GLUE_ZERO32)) in
  TRY(FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP lem th)));;

(*** Decide the conditions and antecedents in the goal from the facts ***)

let GLUE_DECIDE_CONDS_TAC prover =
  W(fun (asl,w) ->
    let ts = find_terms (fun t -> is_cond t || is_imp t) w in
    let cs = setify(map (fun t -> if is_cond t then rand(rator(rator t))
                                  else lhand t) ts) in
    MAP_EVERY (fun c ->
      TRY((SUBGOAL_THEN c MP_TAC THENL
            [prover; DISCH_THEN(fun th -> REWRITE_TAC[EQT_INTRO th])]) ORELSE
          (SUBGOAL_THEN (mk_neg c) MP_TAC THENL
            [prover; DISCH_THEN(fun th -> REWRITE_TAC[EQF_INTRO th])]))) cs);;

let GLUE_SELECT_TAC =
  W(fun (asl,w) ->
    let conds = map (fun t -> rand(rator(rator t))) (find_terms is_cond w) in
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if mem c conds then EQT_INTRO th
      else if is_neg c && mem (rand c) conds then EQF_INTRO th
      else failwith "") asl in
    REWRITE_TAC ths);;

(*** The facts about the counts and the result in the cases of the tests ***)

let GLUE_SUH_COUNTS_TAC prm =
  let om = mk_small_numeral prm.suh_omega
  and kk = mk_small_numeral prm.suh_k in
  let facts = CONV_RULE NUM_REDUCE_CONV
                (SPECL [om; kk; `b:num->byte`; `i:num`] GLUE_SUH_FACTS) in
  let ante = REPEAT CONJ_TAC THEN
             (FIRST_ASSUM ACCEPT_TAC ORELSE GLUE_ARITH_TAC) in
  MAP_EVERY (fun th ->
    TRY(MP_TAC th THEN ANTS_TAC THENL [ante; STRIP_TAC])) (CONJUNCTS facts)
  THEN
  TRY(MP_TAC(SPECL [om; `b:num->byte`; `i:num`] GLUE_SUH_N1) THEN
      ANTS_TAC THENL [ante; ALL_TAC] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC) THEN
  TRY(FIRST_ASSUM(fun th ->
        if can (term_match [] `glue_suh_loop2 omega k (b:num->byte) i`)
               (concl th)
        then MP_TAC(MATCH_MP GLUE_SUH_N2 th) THEN
             CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC
        else NO_TAC));;

(*** The events so far in the goal, from the fact for them ***)

let GLUE_EVENTS_REWRITE_TAC =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_eq c && can (term_match [] `read events s`) (lhs c)
    then REWRITE_TAC[th] else NO_TAC);;

(*** A conjunct of the invariant at a checkpoint ***)

let GLUE_SUH_CONJ_TAC =
  let prover = FIRST_ASSUM ACCEPT_TAC ORELSE GLUE_STEPS_ARITH_TAC in
  GLUE_DECIDE_CONDS_TAC prover THEN
  ASM_REWRITE_TAC[glue_suh_steps; mld_unpack_hints_ret; GLUE_SUH_H_0;
                  ARITH_RULE `MIN 0 n = 0`; VAL_WORD_0; ADD_CLAUSES] THEN
  CONV_TAC(NUM_REDUCE_CONV THENC WORD_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN TRY GLUE_WORD_SMALL2_TAC;;

let GLUE_SUH_INIT_FINAL_TAC prm =
  GLUE_SUH_COUNTS_TAC prm THEN GLUE_ZERO32_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THEN
  W(fun (asl,w) ->
    if is_exists w then
      GLUE_EVENTS_REWRITE_TAC THEN
      REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN GLUE_SELECT_TAC THEN
      DISCHARGE_SAFETY_PROPERTY_TAC
    else GLUE_SUH_CONJ_TAC);;

(*** The counts of iterations are positive only for the cases of the loops ***)

let GLUE_SUH_N1_POS = prove
 (`!omega (b:num->byte) i.
        0 < glue_suh_n1 omega b i
        ==> ~glue_suh_early omega b i /\
            mld_hints_start omega b i < glue_suh_new omega b i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[glue_suh_n1] THEN
  COND_CASES_TAC THENL [ARITH_TAC; ASM_MESON_TAC[]]);;

let GLUE_SUH_N2_POS = prove
 (`!omega k (b:num->byte) i.
        0 < glue_suh_n2 omega k b i ==> glue_suh_loop2 omega k b i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[glue_suh_n2] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(*** The bytes of the hints that an iteration may load, at the addresses  ***)
(*** in the forms that the simulation may give them                      ***)

let GLUE_INPUT_FORMS_TAC prm extra t =
  let inst = glue_suh_inst prm in
  let canon = inst (vsubst [t,`t:num`] `word_add sig (word(SH + t)):int64`) in
  let cands =
    map (fun a -> try rhs(concl(NORMALIZE_RELATIVE_ADDRESS_CONV a))
                  with Failure _ -> a)
     [inst (vsubst [t,`t:num`]
        `word_add (word_add sig (word t)) (word SH):int64`);
      inst (vsubst [t,`t:num`]
        `word_add (word_add sig (word SH)) (word t):int64`);
      inst (vsubst [t,`t:num`] `word_add sig (word(t + SH)):int64`)] @
    map (fun e -> list_mk_icomb "word_add"
                    [`sig:int64`; mk_comb(`word:num->int64`,inst e)]) extra in
  let rass a =
    try let b,w = dest_binary "word_add" a in
        list_mk_icomb "word_add" [b; mk_comb(rator w,glue_rassoc(rand w))]
    with Failure _ -> a in
  let forms = setify(canon :: cands @ map rass cands) in
  GLUE_INPUT_AT_TAC prm t THEN
  MAP_EVERY (fun a ->
    if a = canon then ALL_TAC else
    TRY(FIRST_ASSUM(fun th ->
      let c = concl th in
      if is_eq c && can (term_match [] `read (memory :> bytes8 a) s`) (lhs c)
         && rand(rand(rand(rator(lhs c)))) = canon
      then
        SUBGOAL_THEN (mk_eq(a,canon)) (fun eq -> ASSUME_TAC
          (CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV(REWR_CONV(SYM eq)))) th))
        THENL
         [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
          ALL_TAC]
      else NO_TAC))) forms;;

(*** The facts at the head of an iteration p of the first loop, for the  ***)
(*** position j = s + p: the bytes it loads, and the coefficients other   ***)
(*** than the one it sets                                                 ***)

let GLUE_SUH_PREP1_TAC prm =
  let inst = glue_suh_inst prm in
  let j = inst `mld_hints_start OM (b:num->byte) i + p` in
  GLUE_INPUT_FORMS_TAC prm [] j THEN
  GLUE_INPUT_FORMS_TAC prm
   [`((mld_hints_start OM (b:num->byte) i + p) + SH) + 1`]
   (inst `mld_hints_start OM (b:num->byte) i + p + 1`) THEN
  GLUE_INPUT_FORMS_TAC prm [] (inst `glue_suh_new OM (b:num->byte) i`) THEN
  ASSUME_TAC(SPEC (mk_comb(`b:num->byte`,j)) GLUE_VAL_BYTE) THEN
  SUBGOAL_THEN (subst [j,`j:num`] `val(word(val((b:num->byte) j)):int64) =
                                   val(b j)`) ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(SPEC (mk_comb(`b:num->byte`,j)) GLUE_VAL_BYTE) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (inst `MIN p (glue_suh_n1 OM (b:num->byte) i) = p`)
  ASSUME_TAC THENL
   [REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN GLUE_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
         `!q. q < 256 ==> read(memory :> bytes32(word_add h (word(4 * q)))) s =
                          glue_suh_h omega b i n q`) (concl th)
    then
      SUBGOAL_THEN
       (subst [j,`j:num`]
         (inst `!q. q < 256 /\ ~(q = val((b:num->byte) j))
                    ==> read(memory :> bytes32
                          (word_add h (word(4 * q)))) s0 =
                        glue_suh_h OM b i p q`))
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN MP_TAC(SPEC `q:num` th) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC]
    else NO_TAC);;

(*** The facts at the head of an iteration p of the second loop, for the ***)
(*** position m = w + (p - n1) + 1                                        ***)

let GLUE_SUH_PREP2_TAC prm =
  let inst = glue_suh_inst prm in
  GLUE_INPUT_FORMS_TAC prm []
   (inst `glue_suh_new OM (b:num->byte) i + (p - glue_suh_n1 OM b i) + 1`);;

let GLUE_SUH_STEPS_POS = prove
 (`!omega k (b:num->byte) i.
        0 < glue_suh_steps omega k b i
        ==> mld_hints_start omega b i <= glue_suh_new omega b i /\
            glue_suh_new omega b i <= omega`,
  REPEAT GEN_TAC THEN REWRITE_TAC[glue_suh_steps] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~glue_suh_early omega (b:num->byte) i` MP_TAC THENL
   [ASM_CASES_TAC `0 < glue_suh_n1 omega (b:num->byte) i` THENL
     [ASM_MESON_TAC[GLUE_SUH_N1_POS];
      SUBGOAL_THEN `0 < glue_suh_n2 omega k (b:num->byte) i` MP_TAC THENL
       [ASM_ARITH_TAC;
        DISCH_THEN(MP_TAC o MATCH_MP GLUE_SUH_N2_POS) THEN
        SIMP_TAC[glue_suh_loop2]]];
    REWRITE_TAC[glue_suh_early] THEN ARITH_TAC]);;

(*** The end of an iteration: the invariant for p + 1 ***)

(*** The frame, with the bytes in the addresses of the stores replaced by ***)
(*** variables, so that their bounds are available to the arithmetic      ***)

let GLUE_FRAME_TAC =
  let isv t =
    try fst(dest_const(rator t)) = "val" && type_of(rand t) = `:byte`
    with Failure _ -> false in
  W(fun (asl,w) ->
    let s0,s1 = rand(rator w),rand w in
    let ok c =
      maychange_term c &&
      (try rand(rator c) = s0 && rand c = s1 with Failure _ -> false) in
    let th = snd(find (fun (_,th) -> ok(concl th)) asl) in
    let vs = setify(find_terms isv (concl th)) in
    MP_TAC th THEN
    MAP_EVERY (fun t -> MP_TAC(SPEC (rand t) GLUE_VAL_BYTE)) vs THEN
    MAP_EVERY (fun t -> SPEC_TAC(t,genvar `:num`)) vs THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN MONOTONE_MAYCHANGE_TAC);;

(*** PATH_DISCHARGE_TAC, with the byte values in the addresses of the    ***)
(*** events replaced by variables, so that their bounds are available to ***)
(*** the arithmetic                                                       ***)

let GLUE_GEN_BYTES_TAC =
  let isv t =
    try fst(dest_const(rator t)) = "val" && type_of(rand t) = `:byte` &&
        not(is_var(rand t))
    with Failure _ -> false in
  W(fun (asl,w) ->
    let vs = setify(find_terms isv w) in
    MAP_EVERY (fun t -> MP_TAC(SPEC (rand t) GLUE_VAL_BYTE)) vs THEN
    MAP_EVERY (fun t -> SPEC_TAC(t,genvar `:num`)) vs THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC);;

let GLUE_SELECT_E2_TAC =
  let ise2 th =
    let c = concl th in
    is_eq c && is_var(lhs c) && fst(dest_var(lhs c)) = "e2" in
  W(fun (asl,w) ->
    match filter (ise2 o snd) asl with
      [] -> ALL_TAC
    | (_,th)::_ ->
        let conds = map (fun t -> rand(rator(rator t)))
                        (find_terms is_cond (rhs(concl th))) in
        let ths = mapfilter (fun (_,th) ->
          let c = concl th in
          if mem c conds then EQT_INTRO th
          else if is_neg c && mem (rand c) conds then EQF_INTRO th
          else failwith "") asl in
        RULE_ASSUM_TAC(fun th -> if ise2 th then REWRITE_RULE ths th else th));;

let GLUE_PATH_DISCHARGE_TAC =
  let beta_all =
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) in
  REWRITE_TAC[ENUMERATEL_ADD1] THEN beta_all THEN GLUE_SELECT_TAC THEN
  GLUE_SELECT_E2_TAC THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    if is_conj w then CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]
    else ALL_TAC) THEN
  beta_all THEN
  REWRITE_TAC[NOT_LT] THEN RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  GLUE_GEN_BYTES_TAC THEN DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(*** The coefficients after an iteration: one more set in the first loop ***)

let GLUE_SUH_H_TAC =
  let prover = FIRST_ASSUM ACCEPT_TAC ORELSE GLUE_STEPS_ARITH_TAC ORELSE
               (ASM_REWRITE_TAC[] THEN GLUE_STEPS_ARITH_TAC) in
  GLUE_DECIDE_CONDS_TAC prover THEN REWRITE_TAC[] THEN
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  REWRITE_TAC[MIN] THEN GLUE_DECIDE_CONDS_TAC prover THEN
  REWRITE_TAC[GLUE_SUH_H_ADD1] THEN
  FIRST
   [COND_CASES_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN FIRST_ASSUM ACCEPT_TAC]];
    FIRST_ASSUM(fun th ->
      if is_forall(concl th) && free_in `glue_suh_h` (concl th) then
        MP_TAC(SPEC `q:num` th) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MIN] THEN
        COND_CASES_TAC THEN GLUE_ARITH_TAC
      else NO_TAC)];;

let GLUE_SUH_BODY_CONJ_TAC =
  W(fun (asl,w) ->
    if is_exists w then GLUE_EVENTS_REWRITE_TAC THEN GLUE_PATH_DISCHARGE_TAC
    else if maychange_term w then GLUE_FRAME_TAC
    else if free_in `glue_suh_h` w then GLUE_SUH_H_TAC
    else GLUE_SUH_CONJ_TAC);;

let GLUE_SUH_BODY_FINAL_TAC prm =
  GLUE_SUH_COUNTS_TAC prm THEN
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THEN GLUE_SUH_BODY_CONJ_TAC;;

(*** The iterations of the loops, in the cases of the paths of the code ***)

let GLUE_DECIDE_ASMS_TAC prover =
  let bad t = can (find_term (fun u -> is_const u &&
                                       fst(dest_const u) = "ENUMERATEL")) t in
  let ok th = let c = concl th in
              not(bad c) &&
              can (find_term (fun t -> is_cond t || is_imp t)) c in
  W(fun (asl,w) ->
    let conds = setify(flat(map (fun (_,th) ->
      map (fun t -> if is_cond t then rand(rator(rator t)) else lhand t)
          (find_terms (fun t -> is_cond t || is_imp t) (concl th)))
      (filter (fun (_,th) -> ok th) asl))) in
    let known c = exists (fun (_,th) -> concl th = c || concl th = mk_neg c) in
    MAP_EVERY (fun c ->
      W(fun (asl,w) ->
        if known c asl then ALL_TAC else
        TRY(SUBGOAL_THEN c ASSUME_TAC THENL [prover; ALL_TAC]) THEN
        TRY(SUBGOAL_THEN (mk_neg c) ASSUME_TAC THENL [prover; ALL_TAC])))
     conds THEN
    W(fun (asl,w) ->
      let eqs = mapfilter (fun (_,th) ->
        let c = concl th in
        if mem c conds then EQT_INTRO th
        else if is_neg c && mem (rand c) conds then EQF_INTRO th
        else failwith "") asl in
      RULE_ASSUM_TAC(fun th -> if ok th then REWRITE_RULE eqs th else th) THEN
      REPEAT(FIRST_X_ASSUM(fun th ->
        let c = concl th in
        if is_conj c && can (find_term (fun t ->
             try fst(dest_const(rator(rator t))) = "read" with Failure _ ->
             false)) c && not(bad c)
        then STRIP_ASSUME_TAC th else NO_TAC))));;

let GLUE_SUH_ITER_TAC prm prep =
  let prover = FIRST_ASSUM ACCEPT_TAC ORELSE GLUE_STEPS_ARITH_TAC in
  GLUE_SUH_COUNTS_TAC prm THEN FULL_INIT_TAC THEN
  GLUE_DECIDE_ASMS_TAC prover THEN prep THEN
  GLUE_SUH_RUN_TAC prm (GLUE_SUH_BODY_FINAL_TAC prm) 1;;

let GLUE_SUH_BODY_GEN_TAC prm it1 it2 =
  let inst = glue_suh_inst prm in
  let om = mk_small_numeral prm.suh_omega and kk = mk_small_numeral prm.suh_k in
  let n1 = inst `glue_suh_n1 OM (b:num->byte) i`
  and ok1 = inst `glue_suh_ok1 OM (b:num->byte) i`
  and zs = inst `glue_suh_zeros OM (b:num->byte) i`
  and ok = inst `mld_unpack_hints_ok OM KK (b:num->byte) i` in
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  STRIP_ASSUME_TAC(SPECL [om; `b:num->byte`; `i:num`] GLUE_SUH_BOUNDS) THEN
  MP_TAC(SPECL [om; kk; `b:num->byte`; `i:num`] GLUE_SUH_STEPS_POS) THEN
  ANTS_TAC THENL [GLUE_ARITH_TAC; STRIP_TAC] THEN
  ASM_CASES_TAC (mk_binary "<" (`p:num`,n1)) THENL
   [MP_TAC(SPECL [om; `b:num->byte`; `i:num`] GLUE_SUH_N1_POS) THEN
    ANTS_TAC THENL [GLUE_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(SPECL [om; `b:num->byte`; `i:num`] GLUE_SUH_N1) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
    ASM_CASES_TAC (mk_binary "<" (`p + 1`,n1)) THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (fun th ->
        is_forall(concl th) && free_in n1 (concl th))) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN it1;
      ASM_CASES_TAC ok1 THENL
       [FIRST_ASSUM(fun th ->
          if is_iff(concl th) && lhand(concl th) = ok1 then
            FIRST_ASSUM(fun th1 ->
              if concl th1 = ok1 then ASSUME_TAC(EQ_MP th th1) else NO_TAC)
          else NO_TAC) THEN
        ASM_CASES_TAC (inst `i < K1`) THENL
         [it1;
          ASM_CASES_TAC (inst `OM <= glue_suh_new OM (b:num->byte) i`) THENL
           [it1;
            ASM_CASES_TAC
             (inst `(b:num->byte)(glue_suh_new OM b i) = word 0`) THEN it1]];
        FIRST_X_ASSUM(MP_TAC o check (fun th ->
          is_imp(concl th) && is_neg(lhand(concl th)))) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
        SUBGOAL_THEN (inst `mld_hints_start OM (b:num->byte) i +
                            glue_suh_n1 OM b i =
                            mld_hints_start OM b i + p + 1 /\
                            (mld_hints_start OM b i + glue_suh_n1 OM b i) - 1 =
                            mld_hints_start OM b i + p`)
         (fun th -> RULE_ASSUM_TAC(fun t ->
            if free_in `val:byte->num` (concl t) then REWRITE_RULE[th] t
            else t)) THENL
         [GLUE_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN (inst `~(mld_hints_start OM (b:num->byte) i +
                              glue_suh_n1 OM b i = glue_suh_new OM b i)`)
        ASSUME_TAC THENL [GLUE_ARITH_TAC; ALL_TAC] THEN it1]];
    SUBGOAL_THEN (inst `0 < glue_suh_n2 OM KK (b:num->byte) i`) ASSUME_TAC THENL
     [GLUE_STEPS_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GLUE_SUH_N2_POS) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GLUE_SUH_N2) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
    ASM_CASES_TAC (inst `p + 1 < glue_suh_steps OM KK (b:num->byte) i`) THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC (inst `p - glue_suh_n1 OM (b:num->byte) i`) o
        check (fun th -> is_forall(concl th) &&
                         free_in `glue_suh_n2` (concl th))) THEN
      ANTS_TAC THENL [GLUE_STEPS_ARITH_TAC; STRIP_TAC] THEN it2;
      SUBGOAL_THEN (inst `p - glue_suh_n1 OM (b:num->byte) i + 1 <=
                          glue_suh_n2 OM KK b i /\
                          glue_suh_n2 OM KK b i <=
                          p - glue_suh_n1 OM (b:num->byte) i + 1`)
      STRIP_ASSUME_TAC THENL [GLUE_STEPS_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(fun th ->
        if can (term_match [] `glue_suh_loop2 omega k (b:num->byte) i`)
               (concl th)
        then ASSUME_TAC(MATCH_MP GLUE_SUH_LOOP2_OK th) else NO_TAC) THEN
      ASM_CASES_TAC zs THENL
       [FIRST_ASSUM(fun th ->
          if is_iff(concl th) && lhand(concl th) = zs then
            FIRST_ASSUM(fun th1 ->
              if concl th1 = zs then ASSUME_TAC(EQ_MP th th1) else NO_TAC)
          else NO_TAC) THEN
        FIRST_X_ASSUM(fun th ->
          if is_iff(concl th) && lhand(concl th) = ok then
            FIRST_ASSUM(fun th1 ->
              if concl th1 = zs then ASSUME_TAC(EQ_MP (SYM th) th1)
              else NO_TAC)
          else NO_TAC) THEN
        it2;
        FIRST_X_ASSUM(fun th ->
          if is_iff(concl th) && lhand(concl th) = ok then
            FIRST_ASSUM(fun th1 ->
              if concl th1 = mk_neg zs then
                ASSUME_TAC(REWRITE_RULE[GSYM th] th1)
              else NO_TAC)
          else NO_TAC) THEN
        FIRST_X_ASSUM(MP_TAC o check (fun th ->
          is_imp(concl th) && is_neg(lhand(concl th)) &&
          free_in `glue_suh_zeros` (concl th))) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
        SUBGOAL_THEN (inst `~(glue_suh_new OM (b:num->byte) i +
                              glue_suh_n2 OM KK b i = OM)`)
        ASSUME_TAC THENL [GLUE_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN (inst `glue_suh_new OM (b:num->byte) i +
                            glue_suh_n2 OM KK b i =
                            glue_suh_new OM b i + (p - glue_suh_n1 OM b i) + 1`)
         (fun th -> RULE_ASSUM_TAC(fun t ->
            if is_neg(concl t) && free_in `word 0:byte` (concl t)
            then REWRITE_RULE[th] t else t)) THENL
         [GLUE_STEPS_ARITH_TAC; ALL_TAC] THEN it2]]];;

let GLUE_SUH_BODY_TAC prm =
  GLUE_SUH_BODY_GEN_TAC prm
   (GLUE_SUH_ITER_TAC prm (GLUE_SUH_PREP1_TAC prm))
   (GLUE_SUH_ITER_TAC prm (GLUE_SUH_PREP2_TAC prm));;

(*** The coefficients at the end, when the hints are well formed ***)

let GLUE_SUH_OK_N1 = prove
 (`!omega k (b:num->byte) i.
        mld_unpack_hints_ok omega k b i
        ==> mld_hints_start omega b i + glue_suh_n1 omega b i =
            glue_suh_new omega b i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GLUE_SUH_OK] THEN STRIP_TAC THEN
  ASM_CASES_TAC `mld_hints_start omega (b:num->byte) i <
                 glue_suh_new omega b i` THENL
   [MP_TAC(SPECL [`omega:num`; `b:num->byte`; `i:num`] GLUE_SUH_N1) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    STRIP_TAC THEN ASM_MESON_TAC[];
    UNDISCH_TAC `~glue_suh_early omega (b:num->byte) i` THEN
    ASM_REWRITE_TAC[glue_suh_n1; glue_suh_early] THEN ASM_ARITH_TAC]);;

(*** The return from the checkpoint at the end ***)

let GLUE_SUH_EXIT_TAC prm =
  let inst = glue_suh_inst prm in
  let om = mk_small_numeral prm.suh_omega and kk = mk_small_numeral prm.suh_k in
  let ok = inst `mld_unpack_hints_ok OM KK (b:num->byte) i` in
  ASM_CASES_TAC ok THEN
  ASM_REWRITE_TAC[LT_REFL] THEN FULL_INIT_TAC THEN
  ARM_STEPS_TAC prm.suh_exec (1--4) THEN
  ENSURES_FINAL_STATE_TAC THEN REPEAT CONJ_TAC THEN
  W(fun (asl,w) ->
    if is_exists w then
      GLUE_EVENTS_REWRITE_TAC THEN GLUE_SELECT_TAC THEN
      DISCHARGE_SAFETY_PROPERTY_TAC
    else
      ASM_REWRITE_TAC[mld_unpack_hints_ret] THEN
      CONV_TAC WORD_REDUCE_CONV THEN
      TRY(X_GEN_TAC `q:num` THEN DISCH_TAC THEN
          FIRST_ASSUM(fun th ->
            if is_forall(concl th) && free_in `glue_suh_h` (concl th)
            then MP_TAC(SPEC `q:num` th) THEN
                 ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]
            else NO_TAC) THEN
          SUBGOAL_THEN
           (inst `MIN (glue_suh_steps OM KK (b:num->byte) i)
                      (glue_suh_n1 OM b i) = glue_suh_n1 OM b i`)
          SUBST1_TAC THENL
           [REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN GLUE_STEPS_ARITH_TAC;
            ALL_TAC] THEN
          MATCH_MP_TAC GLUE_SUH_H_FULL THEN
          MATCH_MP_TAC(SPECL [om; kk] GLUE_SUH_OK_N1) THEN
          FIRST_ASSUM ACCEPT_TAC));;

(*** The events template: one function for each path of the code to the ***)
(*** first checkpoint, and for each path of an iteration                 ***)

let glue_suh_template prm = glue_suh_inst prm
 `\(b:num->byte) (i:num) (h:int64) (sig:int64) (mf:int64) (pc:num)
   (stackpointer:int64) (returnaddress:int64).
   APPEND
    (if mld_unpack_hints_ok OM KK b i
     then f_ev_ok b i h sig mf pc stackpointer returnaddress
     else f_ev_bad b i h sig mf pc stackpointer returnaddress)
    (APPEND
      (ENUMERATEL (glue_suh_steps OM KK b i)
        (\p. if p < glue_suh_n1 OM b i
             then if p + 1 < glue_suh_n1 OM b i
                  then f_ev_a b i h sig mf pc stackpointer returnaddress p
                  else if glue_suh_ok1 OM b i
                  then if i < K1
                       then f_ev_ar b i h sig mf pc stackpointer returnaddress p
                       else if OM <= glue_suh_new OM b i
                       then f_ev_ar2 b i h sig mf pc stackpointer
                                     returnaddress p
                       else if b(glue_suh_new OM b i) = word 0
                       then f_ev_at b i h sig mf pc stackpointer returnaddress p
                       else f_ev_az b i h sig mf pc stackpointer returnaddress p
                  else f_ev_af b i h sig mf pc stackpointer returnaddress p
             else if p + 1 < glue_suh_steps OM KK b i
             then f_ev_b b i h sig mf pc stackpointer returnaddress p
             else if glue_suh_zeros OM b i
             then f_ev_be b i h sig mf pc stackpointer returnaddress p
             else f_ev_bf b i h sig mf pc stackpointer returnaddress p))
      (if glue_suh_early OM b i
       then if 0 < i then f_ev_e1 b i h sig mf pc stackpointer returnaddress
            else f_ev_e0 b i h sig mf pc stackpointer returnaddress
       else if mld_hints_start OM b i < glue_suh_new OM b i
       then if 0 < i then f_ev_p1 b i h sig mf pc stackpointer returnaddress
            else f_ev_p0 b i h sig mf pc stackpointer returnaddress
       else if i < K1
       then if 0 < i then f_ev_r1 b i h sig mf pc stackpointer returnaddress
            else f_ev_r0 b i h sig mf pc stackpointer returnaddress
       else if OM <= glue_suh_new OM b i
       then f_ev_r2 b i h sig mf pc stackpointer returnaddress
       else if b(glue_suh_new OM b i) = word 0
       then f_ev_t b i h sig mf pc stackpointer returnaddress
       else f_ev_z b i h sig mf pc stackpointer returnaddress))
   :(uarch_event)list`;;

(*** The whole proof ***)

let GLUE_SUH_FULL_TAC prm =
  let inst = glue_suh_inst prm in
  REPEAT GEN_TAC THEN REWRITE_TAC[memset_ret_full_contract] THEN
  DISCH_THEN(fun th -> ASSUME_CALLEE_SAFETY_TAILED_TAC th "H_MEMSET") THEN
  CONCRETIZE_F_EVENTS_TAC (glue_suh_template prm) THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst prm.suh_exec] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `got_memset:num`] WORD_ADD])
  THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  GLUE_EVENTS_WHILE_TAC (inst `glue_suh_steps OM KK (b:num->byte) i`)
    (glue_suh_inv prm) THEN
  REPEAT CONJ_TAC THENL
   [FULL_INIT_TAC THEN GLUE_SUH_INIT_PREP_TAC prm THEN
    GLUE_SUH_RUN_TAC prm (GLUE_SUH_INIT_FINAL_TAC prm) 1;
    GLUE_SUH_BODY_TAC prm;
    GLUE_SUH_EXIT_TAC prm];;
