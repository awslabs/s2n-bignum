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
needs "common/fips204/properties/mldsa_native_full.ml";;
needs "common/fips204/properties/mldsa_native_polyvec.ml";;
needs "common/mldsa_native_hints.ml";;

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

let glue_psh_vars =
  [`x:num->int32`; `b:num->byte`; `sig:int64`; `w0:int64`; `w1p:int64`;
   `scratch:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`;
   `i:num`];;

(*** Specialize an assumption !p. P p ==> Q p, matching pat, to tm ***)

let GLUE_ASM_SPEC_TAC pat tm =
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && can (term_match [] pat) (concl th) then
      MP_TAC(SPEC tm th) THEN ANTS_TAC THENL
       [SIMPLE_ARITH_TAC ORELSE (ASM_REWRITE_TAC[] THEN NO_TAC); DISCH_TAC]
    else NO_TAC);;

(*** Equations of words formed from small numbers, as WORD_SMALL_TAC of ***)
(*** mldsa_native.ml does, also for bytes and for numbers such as ***)
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

let glue_pc_offset base t =
  try dest_small_numeral(rand(rand t)) - base with Failure _ -> -1;;

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

let glue_suh_vars =
  [`b:num->byte`; `i:num`; `h:int64`; `sig:int64`; `mf:int64`; `pc:num`;
   `stackpointer:int64`; `returnaddress:int64`; `p:num`];;

(*** Register values that are small words, as word n, with the values of   ***)
(*** their UXTW views; byte values named by the equations in the context   ***)

let glue_rassoc e = rand(concl(REWRITE_CONV[GSYM ADD_ASSOC] e));;

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
