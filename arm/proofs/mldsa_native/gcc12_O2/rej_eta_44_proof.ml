(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Rejection sampling of coefficients in [-2,2]: the proof (see              *)
(* rej_eta_44_spec.ml), as that of rej_eta_65_proof.ml.                      *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/rej_eta_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_sampling.ml";;

let REJ_ETA_44_EXEC = MLDSA_NATIVE_REJ_ETA_44_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* The events, by the paths of iteration i as for rej_eta_65_proof.ml.       *)
(* ------------------------------------------------------------------------- *)

let REJ_ETA_44_TEMPLATE =
 `\(a:int64) (offset:num) (buf:int64) (D:bool list) (pc:num)
   (returnaddress:int64).
   if offset = 256 then f_ev_full a offset buf D pc returnaddress
   else
    APPEND (f_ev_epil a offset buf D pc returnaddress)
     (APPEND
       (ENUMERATEL (LENGTH D DIV 2)
         (\i. if EL (2 * i) D
              then if EL (2 * i + 1) D /\
                      offset + LENGTH(FILTER (\x. x) (SUB_LIST(0,2 * i) D)) +
                      1 < 256
                   then f_ev_vv a offset buf D pc returnaddress i
                   else f_ev_vx a offset buf D pc returnaddress i
              else if EL (2 * i + 1) D
                   then f_ev_xv a offset buf D pc returnaddress i
                   else f_ev_xx a offset buf D pc returnaddress i))
       (f_ev_prol a offset buf D pc returnaddress))
   :(uarch_event)list`;;

(* ------------------------------------------------------------------------- *)
(* The invariant at the head of the loop after i bytes.                      *)
(* ------------------------------------------------------------------------- *)

let REJ_ETA_44_INV =
 `\i s. read X8 s = a /\ read X7 s = word 205 /\ read X10 s = word 2 /\
        read X9 s = word_zx(word_sub (word 1) (word_zx buf):int32):int64 /\
        read X30 s = returnaddress /\
        read X2 s = word_add buf (word i) /\
        read X0 s = word(offset + MIN (256 - offset)
                           (LENGTH(FILTER (\x. x) (SUB_LIST(0,2 * i) D)))) /\
        (!j. j < 136
             ==> read(memory :> bytes8(word_add buf (word j))) s = b j) /\
        (!j. offset <= j /\
             j < offset + MIN (256 - offset)
                           (LENGTH(FILTER (\x. x) (SUB_LIST(0,2 * i) D)))
             ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                 EL (j - offset) (mld_rej_eta_list 2 b (2 * i)))`;;

(* ------------------------------------------------------------------------- *)
(* The facts for iteration i, as for rej_eta_65_proof.ml.                    *)
(* ------------------------------------------------------------------------- *)

let REJ_ETA_44_BODY_SETUP_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `i < M` ASSUME_TAC THENL
   [UNDISCH_TAC `i < LENGTH (D:bool list) DIV 2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i < M`) o
    check (fun th -> is_forall(concl th) &&
                     can (term_match [] `!m. m < M ==> P m`) (concl th))) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `2 * i` o
    check (fun th -> is_forall(concl th) &&
                     can (term_match [] `!n. n <= 2 * M ==> P n`)
                         (concl th))) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < M` THEN ARITH_TAC; DISCH_TAC] THEN
  FULL_INIT_TAC THEN
  ABBREV_TAC
   `c = LENGTH(FILTER (\x. x) (SUB_LIST (0,2 * i) (D:bool list)))` THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `c:num`)) THEN
  SUBGOAL_THEN `offset + c < 256` ASSUME_TAC THENL
   [UNDISCH_TAC `offset + LENGTH (mld_rej_eta_list 2 b (2 * i)) < 256` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `MIN (256 - offset) c = c`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [UNDISCH_TAC `offset + c < 256` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `i < 136`) o SPEC `i:num` o
    check (fun th -> is_forall(concl th) && free_in `bytes8` (concl th))) THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `2 * (i + 1)` o
    check (fun th -> is_forall(concl th) &&
                     can (term_match [] `!n. n <= 2 * M ==> P n`)
                         (concl th))) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i < M` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(MATCH_MP MLD_REJ_ETA_BYTES_NEXT
   (CONJ (ASSUME `mld_rej_eta_bytes 2 256 offset (b:num->byte) 136 = M`)
         (ASSUME `i < M`))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `2 * i + 1` o
    check (fun th -> is_forall(concl th) &&
                     can (term_match [] `!k. k < 2 * M ==> P k`)
                         (concl th))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `2 * i` o
    check (fun th -> is_forall(concl th) &&
                     can (term_match [] `!k. k < 2 * M ==> P k`)
                         (concl th))) THEN
  REWRITE_TAC[ARITH_RULE `2 * i < 2 * M <=> i < M`;
              ARITH_RULE `2 * i + 1 < 2 * M <=> i < M`; ASSUME `i < M`] THEN
  REWRITE_TAC[MLD_REJ_ETA_LIST_BYTE; LENGTH_APPEND; SAMPLING_LENGTH_COND;
              MLD_REJ_ETA_VALID_BYTE; mld_rej_eta_coeff;
              ASSUME `LENGTH (mld_rej_eta_list 2 b (2 * i)) = c`] THEN
  MP_TAC(ISPEC `(b:num->byte) i` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ABBREV_TAC `n = val((b:num->byte) i)` THEN REPEAT DISCH_TAC;;

(*** The first steps: the byte, its nibbles and the first compare ***)

let REJ_ETA_44_SIM1_TAC =
  ARM_STEPS_TAC REJ_ETA_44_EXEC (1--5) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_BYTE_NIBBLES]) THEN
  RULE_ASSUM_TAC(fun th ->
    if concl th = `val((b:num->byte) i) = n` then th
    else REWRITE_RULE[ASSUME `val((b:num->byte) i) = n`] th) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
  MP_TAC(SPECL [`buf:int64`; `i:num`; `1`] MLD_REJ_POS) THEN
  ANTS_TAC THENL
   [SIMPLE_ARITH_TAC;
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  ARM_STEPS_TAC REJ_ETA_44_EXEC (6--6) THEN W32_DECIDE_FLAGS_TAC;;

(*** The coefficients after iteration i: those before, and the new ones ***)

let REJ_ETA_44_STORE_TAC =
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[APPEND] THEN
  ASM_CASES_TAC `j < offset + c` THENL
   [REWRITE_TAC[EL_APPEND;
                ASSUME `LENGTH (mld_rej_eta_list 2 b (2 * i)) = c`] THEN
    SUBGOAL_THEN `j - offset < c` (fun th -> REWRITE_TAC[th]) THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && free_in `bytes32` (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `j = (offset + c) + 0 \/ j = (offset + c) + 1`
   (DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [SIMPLE_ARITH_TAC; ALL_TAC; ALL_TAC] THEN
  TRY(SUBGOAL_THEN `F` CONTR_TAC THEN SIMPLE_ARITH_TAC THEN NO_TAC) THEN
  REWRITE_TAC[EL_APPEND; ASSUME `LENGTH (mld_rej_eta_list 2 b (2 * i)) = c`;
              ARITH_RULE `((offset + c) + k) - offset = c + k`;
              ARITH_RULE `~(c + k < c)`; ARITH_RULE `(c + k) - c = k`] THEN
  CONV_TAC(RAND_CONV SAMPLING_EL_LIST_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[];;

(*** One path of the iteration, from the first branch to the loop test ***)

let REJ_ETA_44_PATH_TAC =
  SAMPLING_RUN_TAC REJ_ETA_44_EXEC 7
   [`word(pc + mld_rej_eta_c44_loop1):int64`;
    `word(pc + mld_rej_eta_c44_loop1_exit):int64`] THEN
  SAMPLING_COND_REWRITE_TAC[MLD_REJ_ETA2_COEFF] THEN
  (SAMPLING_LOOP_PC_TAC `LENGTH (D:bool list) DIV 2`
     [SYM(ASSUME `M = LENGTH (D:bool list) DIV 2`)] ORELSE
   SAMPLING_LOOP_EXIT_TAC `LENGTH (D:bool list) DIV 2`
     [SYM(ASSUME `M = LENGTH (D:bool list) DIV 2`)]
     `word(pc + mld_rej_eta_c44_loop1):int64`) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_iff(concl th) && lhand(concl th) = `i + 1 < M`)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SAMPLING_W64_TAC THEN SAMPLING_SELECT_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(AP_TERM_TAC THEN SIMPLE_ARITH_TAC THEN NO_TAC) THEN
  TRY(REJ_ETA_44_STORE_TAC THEN NO_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `c:num` &&
    can (term_match [] `LENGTH(FILTER (\x:bool. x) l)`) (lhs(concl th)))) THEN
  SAMPLING_PATH_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_REJ_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  CONCRETIZE_F_EVENTS_TAC REJ_ETA_44_TEMPLATE THEN REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `offset:num`; `buf:int64`;
    `b:num->byte`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; NONOVERLAPPING_CLAUSES; ALL; fst REJ_ETA_44_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The declassified values D, the number M of bytes read ***)

  REWRITE_TAC[MLD_REJ_ETA_CTR] THEN
  MP_TAC(SPECL [`2`; `256`; `offset:num`; `b:num->byte`; `136`]
    MLD_REJ_ETA_DECLASS) THEN
  MP_TAC(SPECL [`2`; `256`; `offset:num`; `b:num->byte`; `136`;
    `mld_rej_eta_bytes 2 256 offset (b:num->byte) 136`]
    MLD_REJ_ETA_BYTES) THEN REWRITE_TAC[] THEN
  ABBREV_TAC `D = mld_rej_eta_declass 2 256 offset (b:num->byte) 136` THEN
  ABBREV_TAC `M = mld_rej_eta_bytes 2 256 offset (b:num->byte) 136` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `offset = 256` THENL
   [SUBGOAL_THEN `M = 0` ASSUME_TAC THENL
     [EXPAND_TAC "M" THEN MATCH_MP_TAC MLD_REJ_ETA_BYTES_0 THEN
      ASM_REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[SUB_REFL; ARITH_RULE `MIN 0 x = 0`; ADD_CLAUSES;
                    ARITH_RULE `~(i < n /\ n <= i)`; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC REJ_ETA_44_EXEC (1--5) THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [MESON_TAC[NOT_LT]; DISCHARGE_SAFETY_PROPERTY_TAC];
    ALL_TAC] THEN

  (*** The loop over the bytes ***)

  REWRITE_TAC[ASSUME `~(offset = 256)`] THEN
  SUBGOAL_THEN `offset < 256` ASSUME_TAC THENL
   [UNDISCH_TAC `offset <= 256` THEN UNDISCH_TAC `~(offset = 256)` THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `0 < M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC MLD_REJ_ETA_BYTES_POS THEN
    ASM_REWRITE_TAC[ARITH]; ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `l = 2 * M ==> M = l DIV 2`) o
    check (fun th -> concl th = `LENGTH (D:bool list) = 2 * M`)) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `LENGTH (D:bool list) DIV 2`
   `pc + mld_rej_eta_c44_loop1` `pc + mld_rej_eta_c44_loop1_exit`
   REJ_ETA_44_INV THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `M = LENGTH (D:bool list) DIV 2`)) THEN
    UNDISCH_TAC `0 < M` THEN ARITH_TAC;

    (*** Initialization ***)

    FULL_INIT_TAC THEN ARM_STEPS_TAC REJ_ETA_44_EXEC (1--3) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC REJ_ETA_44_EXEC (4--4) THEN SAMPLING_DECIDE_BRANCH_TAC THEN
    ARM_STEPS_TAC REJ_ETA_44_EXEC (5--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_LIST_CLAUSES; FILTER; LENGTH;
                ARITH_RULE `MIN a 0 = 0`; ADD_CLAUSES; WORD_ADD_0;
                ARITH_RULE `~(a <= j /\ j < a)`] THEN
    CONJ_TAC THENL [WORD_SMALL_TAC; DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The loop body, in the paths of the two nibbles of the byte ***)

    REJ_ETA_44_BODY_SETUP_TAC THEN REJ_ETA_44_SIM1_TAC THEN
    SAMPLING_CASES_TAC `EL (2 * i) (D:bool list)` THENL
     [SAMPLING_CASES_TAC
       `EL (2 * i + 1) (D:bool list) /\ offset + c + 1 < 256` THENL
       [REJ_ETA_44_PATH_TAC;
        ASM_CASES_TAC `n DIV 16 < 15` THEN
        ASM_CASES_TAC `offset + c + 1 < 256` THEN
        TRY(FIRST_X_ASSUM(MP_TAC o check (fun th ->
              is_neg(concl th) && is_conj(rand(concl th)) &&
              not(free_in `D:bool list` (concl th)))) THEN
            ASM_REWRITE_TAC[] THEN NO_TAC) THEN
        REJ_ETA_44_PATH_TAC];
      SAMPLING_CASES_TAC `EL (2 * i + 1) (D:bool list)` THEN
      REJ_ETA_44_PATH_TAC];

    (*** The return ***)

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    ARM_STEPS_TAC REJ_ETA_44_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `2 * M` o
      check (fun th -> is_forall(concl th) &&
                       can (term_match [] `!n. n <= 2 * M ==> P n`)
                           (concl th))) THEN
    REWRITE_TAC[LE_REFL; ASSUME `M = LENGTH (D:bool list) DIV 2`] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
                         REWRITE_TAC[th]) THEN
    CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      MP_TAC(SPECL [`2`; `b:num->byte`; `2 * LENGTH (D:bool list) DIV 2`;
                    `2 * 136`; `j - offset`] EL_MLD_REJ_ETA_LIST_PREFIX) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `M <= 136` THEN
          REWRITE_TAC[ASSUME `M = LENGTH (D:bool list) DIV 2`] THEN ARITH_TAC;
          SIMPLE_ARITH_TAC];
        DISCH_THEN SUBST1_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCHARGE_SAFETY_PROPERTY_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_REJ_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_REJ_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC MLDSA_NATIVE_REJ_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_REJ_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_REJ_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC MLDSA_NATIVE_REJ_ETA_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
