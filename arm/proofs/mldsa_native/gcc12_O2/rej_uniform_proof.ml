(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Rejection sampling of coefficients mod q: the proof (see                  *)
(* rej_uniform_spec.ml).                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/rej_uniform_spec.ml";;
needs "arm/proofs/utils/mldsa_native_sampling.ml";;

let REJ_UNIFORM_EXEC = MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The events, which may depend on the buffer b. The loop reads G =          *)
(* mld_rej_uniform_groups groups; iteration i accepts the candidate and      *)
(* stores it (a) or rejects it (r) and goes on to the test of the length,    *)
(* except that the last one returns: at once when the polynomial is full     *)
(* (af), or after the test when the buffer is exhausted (ae, re), from two   *)
(* different RET instructions. The last iteration therefore ends at the      *)
(* return address, and there is nothing after the loop.                      *)
(* ------------------------------------------------------------------------- *)

let REJ_UNIFORM_TEMPLATE =
 `\(a:int64) (offset:num) (buf:int64) (buflen:num) (b:num->byte) (pc:num)
   (returnaddress:int64).
   if offset = 256 then f_ev_full a offset buf buflen b pc returnaddress
   else
    APPEND (f_ev_epil a offset buf buflen b pc returnaddress)
     (APPEND
       (ENUMERATEL (mld_rej_uniform_groups 256 offset b buflen)
         (\i. if i + 1 < mld_rej_uniform_groups 256 offset b buflen
              then if val(mld_rej_uniform_cand b i) < 8380417
                   then f_ev_a a offset buf buflen b pc returnaddress i
                   else f_ev_r a offset buf buflen b pc returnaddress i
              else if val(mld_rej_uniform_cand b i) < 8380417
                   then if offset + LENGTH(mld_rej_uniform_list b i) = 255
                        then f_ev_af a offset buf buflen b pc returnaddress i
                        else f_ev_ae a offset buf buflen b pc returnaddress i
                   else f_ev_re a offset buf buflen b pc returnaddress i))
       (f_ev_prol a offset buf buflen b pc returnaddress))
   :(uarch_event)list`;;

(* ------------------------------------------------------------------------- *)
(* The invariant at the head of the loop after i groups (position in X2 and  *)
(* count in X1), and after the return for i = G (the result in X0).          *)
(* ------------------------------------------------------------------------- *)

let REJ_UNIFORM_INV =
 `\i s. read X9 s = a /\ read X3 s = word buflen /\
        read X8 s = word_zx(word_sub (word 3) (word_zx buf):int32):int64 /\
        read X30 s = returnaddress /\
        (!j. j < buflen
             ==> read(memory :> bytes8(word_add buf (word j))) s = b j) /\
        (!j. offset <= j /\
             j < offset + MIN (256 - offset)
                           (LENGTH(mld_rej_uniform_list b i))
             ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                 EL (j - offset) (mld_rej_uniform_list b i)) /\
        (if i < G
         then read X2 s = word_add buf (word(3 * i)) /\
              read X1 s = word(offset + LENGTH(mld_rej_uniform_list b i))
         else read X0 s =
              word(offset + MIN (256 - offset)
                             (LENGTH(mld_rej_uniform_list b i))))`;;

(* ------------------------------------------------------------------------- *)
(* The facts for iteration i: the count c, the bytes of the group and its    *)
(* candidate tv, whether the loop goes on, and the registers after the first *)
(* ten steps, which load the group and compute the candidate.                *)
(* ------------------------------------------------------------------------- *)

let REJ_UNIFORM_BODY_SETUP_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[ASSUME `i < G`] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i < G`) o
    check (fun th -> is_forall(concl th) &&
                     can (term_match [] `!m. m < G ==> P m`) (concl th))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `3 * i + 3 <= buflen` ASSUME_TAC THENL
   [UNDISCH_TAC `i < buflen DIV 3` THEN ARITH_TAC; ALL_TAC] THEN
  FULL_INIT_TAC THEN
  MAP_EVERY (fun k ->
    let t = subst [k,`k:num`]
      `read (memory :> bytes8 (word_add buf (word (3 * i + k)))) s0 =
       (b:num->byte) (3 * i + k)` in
    SUBGOAL_THEN t (ASSUME_TAC o REWRITE_RULE[ADD_CLAUSES]) THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && free_in `bytes8` (concl th))) THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC]) [`0`;`1`;`2`] THEN
  MP_TAC(MATCH_MP MLD_REJ_UNIFORM_GROUPS_NEXT
   (CONJ (ASSUME `mld_rej_uniform_groups 256 offset (b:num->byte) buflen = G`)
         (ASSUME `i < G`))) THEN
  MP_TAC(ISPECL
   [`word_or (word_or (word_zx((b:num->byte)(3 * i)))
                      (word_shl (word_zx(b(3 * i + 1))) 8))
             (word_shl (word_zx(b(3 * i + 2))) 16):int32`; `8388607`]
    (CONJUNCT1 VAL_WORD_AND_WORD_LE)) THEN
  REWRITE_TAC[GSYM mld_rej_uniform_cand] THEN
  REWRITE_TAC[MLD_REJ_UNIFORM_LIST_SUC; LENGTH_APPEND;
              SAMPLING_LENGTH_COND] THEN
  ABBREV_TAC `c = LENGTH(mld_rej_uniform_list (b:num->byte) i)` THEN
  ABBREV_TAC `tv = val(mld_rej_uniform_cand (b:num->byte) i)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `mld_rej_uniform_cand (b:num->byte) i = word tv` ASSUME_TAC THENL
   [EXPAND_TAC "tv" THEN REWRITE_TAC[WORD_VAL]; ALL_TAC] THEN
  SUBGOAL_THEN `MIN (256 - offset) c = c`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `offset + c < 256` THEN ARITH_TAC; ALL_TAC] THEN
  ARM_STEPS_TAC REJ_UNIFORM_EXEC (1--10) THEN
  SAMPLING_REG_TAC `X4` `word_zx(mld_rej_uniform_cand (b:num->byte) i):int64`
    [mld_rej_uniform_cand] THEN
  RULE_ASSUM_TAC(fun th ->
    if is_eq(concl th) && can (term_match [] `read c s`) (lhs(concl th))
    then REWRITE_RULE
          [ASSUME `mld_rej_uniform_cand (b:num->byte) i = word tv`] th
    else th) THEN
  RULE_ASSUM_TAC(fun th ->
    if is_eq(concl th) &&
       (try mem (rand(rator(lhs(concl th)))) [`X2`;`X7`]
        with Failure _ -> false)
    then REWRITE_RULE[WORD_ZX_ZX_32_64_32; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]
                     th
    else th) THEN
  MP_TAC(SPECL [`buf:int64`; `3 * i + 3`; `3`] MLD_REJ_POS) THEN
  ANTS_TAC THENL
   [SIMPLE_ARITH_TAC;
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  SAMPLING_W64_TAC;;

(*** The coefficients after iteration i: those before, and the new one ***)

let REJ_UNIFORM_STORE_TAC =
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[APPEND] THEN
  ASM_CASES_TAC `j < offset + c` THENL
   [REWRITE_TAC[EL_APPEND;
                ASSUME `LENGTH (mld_rej_uniform_list (b:num->byte) i) = c`] THEN
    SUBGOAL_THEN `j - offset < c` (fun th -> REWRITE_TAC[th]) THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && free_in `bytes32` (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `j = (offset + c) + 0` SUBST_ALL_TAC THENL
   [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  TRY(SUBGOAL_THEN `F` CONTR_TAC THEN SIMPLE_ARITH_TAC THEN NO_TAC) THEN
  REWRITE_TAC[EL_APPEND;
              ASSUME `LENGTH (mld_rej_uniform_list (b:num->byte) i) = c`;
              ARITH_RULE `((offset + c) + k) - offset = c + k`;
              ARITH_RULE `~(c + k < c)`; ARITH_RULE `(c + k) - c = k`] THEN
  CONV_TAC(RAND_CONV SAMPLING_EL_LIST_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];;

(*** One path of the iteration, from the compare of the candidate on ***)

let REJ_UNIFORM_PATH_TAC =
  SAMPLING_RUN_TAC REJ_UNIFORM_EXEC 11
   [`word(pc + mld_rej_uniform_c_loop1):int64`; `returnaddress:int64`] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SAMPLING_W64_TAC THEN SAMPLING_SELECT_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[WORD_VAL] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(AP_TERM_TAC THEN SIMPLE_ARITH_TAC THEN NO_TAC) THEN
  TRY(REJ_UNIFORM_STORE_TAC THEN NO_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `c:num` &&
    can (term_match [] `LENGTH(mld_rej_uniform_list b i)`)
        (lhs(concl th)))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `tv:num` &&
    can (term_match [] `val(mld_rej_uniform_cand b i)`) (lhs(concl th)))) THEN
  SAMPLING_PATH_DISCHARGE_TAC;;

(*** Whether the loop goes on after iteration i, by the cases ***)

let REJ_UNIFORM_IFF_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_iff(concl th) && lhand(concl th) = `i + 1 < G`
    then MP_TAC th else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC;;

let REJ_UNIFORM_LAST_TAC =
  SUBGOAL_THEN `~(i + 1 < buflen DIV 3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_neg(concl th) && is_conj(rand(concl th)))) THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  CONCRETIZE_F_EVENTS_TAC REJ_UNIFORM_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `offset:num`; `buf:int64`;
    `buflen:num`; `b:num->byte`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[SOME_FLAGS; C_ARGUMENTS;
              C_RETURN; NONOVERLAPPING_CLAUSES; ALL; fst REJ_UNIFORM_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The number G of groups read ***)

  REWRITE_TAC[MLD_REJ_UNIFORM_CTR] THEN
  MP_TAC(SPECL [`256`; `offset:num`; `b:num->byte`; `buflen:num`;
    `mld_rej_uniform_groups 256 offset (b:num->byte) buflen`]
    MLD_REJ_UNIFORM_GROUPS) THEN REWRITE_TAC[] THEN
  ABBREV_TAC `G = mld_rej_uniform_groups 256 offset (b:num->byte) buflen` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `offset = 256` THENL
   [SUBGOAL_THEN `G = 0` ASSUME_TAC THENL
     [EXPAND_TAC "G" THEN MATCH_MP_TAC MLD_REJ_UNIFORM_GROUPS_0 THEN
      ASM_REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[SUB_REFL; ARITH_RULE `MIN 0 x = 0`; ADD_CLAUSES;
                    ARITH_RULE `~(i < n /\ n <= i)`; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC REJ_UNIFORM_EXEC (1--2) THEN W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC REJ_UNIFORM_EXEC (3--3) THEN
    TRY SAMPLING_DECIDE_BRANCH_TAC THEN
    ARM_STEPS_TAC REJ_UNIFORM_EXEC (4--5) THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MESON_TAC[NOT_LT]; DISCHARGE_SAFETY_PROPERTY_TAC];
    ALL_TAC] THEN

  (*** The loop over the groups, the last iteration ending at the return ***)

  REWRITE_TAC[ASSUME `~(offset = 256)`] THEN
  SUBGOAL_THEN `offset < 256` ASSUME_TAC THENL
   [UNDISCH_TAC `offset <= 256` THEN UNDISCH_TAC `~(offset = 256)` THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `0 < G` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MATCH_MP_TAC MLD_REJ_UNIFORM_GROUPS_POS THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `G:num` `pc + mld_rej_uniform_c_loop1`
   `val(returnaddress:int64)` REJ_UNIFORM_INV THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `0 < G` THEN ARITH_TAC;

    (*** Initialization ***)

    FULL_INIT_TAC THEN ARM_STEPS_TAC REJ_UNIFORM_EXEC (1--2) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC REJ_UNIFORM_EXEC (3--3) THEN
    TRY SAMPLING_DECIDE_BRANCH_TAC THEN
    ARM_STEPS_TAC REJ_UNIFORM_EXEC (4--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[mld_rej_uniform_list; list_of_seq; FILTER; LENGTH;
                ARITH_RULE `MIN a 0 = 0`; ADD_CLAUSES; MULT_CLAUSES;
                WORD_ADD_0; ARITH_RULE `~(a <= j /\ j < a)`] THEN
    ASM_REWRITE_TAC[] THEN
    TRY(CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, by the cases of the template ***)

    REJ_UNIFORM_BODY_SETUP_TAC THEN
    ASM_CASES_TAC `tv < 8380417` THEN ASM_CASES_TAC `i + 1 < G` THEN
    REJ_UNIFORM_IFF_TAC THENL
     [REJ_UNIFORM_PATH_TAC;
      ASM_CASES_TAC `offset + c = 255` THENL
       [REJ_UNIFORM_PATH_TAC; REJ_UNIFORM_LAST_TAC THEN REJ_UNIFORM_PATH_TAC];
      REJ_UNIFORM_PATH_TAC;
      REJ_UNIFORM_LAST_TAC THEN REJ_UNIFORM_PATH_TAC];

    (*** Nothing after the last iteration ***)

    REWRITE_TAC[LT_REFL] THEN FULL_INIT_TAC THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[WORD_VAL] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      MP_TAC(SPECL [`b:num->byte`; `G:num`; `buflen DIV 3`; `j - offset`]
        EL_MLD_REJ_UNIFORM_LIST_PREFIX) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCHARGE_SAFETY_PROPERTY_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC MLDSA_NATIVE_REJ_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
