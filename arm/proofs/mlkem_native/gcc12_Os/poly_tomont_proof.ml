(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_Os/poly_tomont_spec.ml";;


let TOMONT_LANE = prove
 (TOMONT_LANE_STMT,
  GEN_TAC THEN REWRITE_TAC[INT_CONG_RREM] THEN
  MP_TAC(MLKEM_NATIVE_CONGBOUND_RULE undefined
   `montred_scalar(word_mul (word_sx (x:int16)) (word 1353))`) THEN
  MATCH_MP_TAC(TAUT `(p ==> p') /\ (q ==> q') ==> p /\ q ==> p' /\ q'`) THEN
  CONJ_TAC THENL [ALL_TAC; INT_ARITH_TAC] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(a * b:int == c) (mod n)
    ==> (x == a * y * b) (mod n) ==> (x == c * y) (mod n)`) THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `x:num->int16`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `256` `pc + mlkem_poly_tomont_loop1`
   `pc + mlkem_poly_tomont_loop1_test`
   `\i s. read X0 s = a /\ read X2 s = word i /\
          read X30 s = returnaddress /\
          read X6 s = word 1353 /\ read X5 s = word 4294963969 /\
          read X4 s = word 4294963967 /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          (!j. j < i
               ==> let z_j = read(memory :> bytes16
                                (word_add a (word(2 * j)))) s in
                   (ival z_j == (tomont_3329 (ival o x)) j) (mod &3329) /\
                   abs(ival z_j) <= &3328)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization of the counter and the constants ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[CONJUNCT1 LT; LE_0] THEN CONV_TAC WORD_REDUCE_CONV THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;

    (*** The loop body: one coefficient ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes16 (word_add a (word (2 * i)))) s0 = x i /\
      (!j. i + 1 <= j /\ j < 256
           ==> read (memory :> bytes16 (word_add a (word (2 * j)))) s0 = x j)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; GEN_TAC THEN STRIP_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `val(word i:int64) = i` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_EXEC (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN
    REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    MLKEM_NATIVE_W_SIMP_TAC THEN
    REWRITE_TAC[ADD_CLAUSES; tomont_3329; o_THM;
                WORD_RULE `word_add (word 0) x = x`] THEN
    MP_TAC(SPEC `(x:num->int16) i` TOMONT_LANE) THEN
    REWRITE_TAC[montred_scalar];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_EXEC (1--2) THEN
    SUBGOAL_THEN `~(val(word_sub (word i) (word 256):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 256 ==> i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;


let MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a pc returnaddress)
        (APPEND
          (ENUMERATEL 256 (\i. f_ev_loop a pc returnaddress i))
          (f_ev_prol a pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + mlkem_poly_tomont_loop1`
   `pc + mlkem_poly_tomont_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X0 s = a /\ read X2 s = word i` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_EXEC (1--4) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(word i:int64) = i` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_TOMONT_GCC12_OS_EXEC (1--10) THEN
  SUBGOAL_THEN
   `~(val(word_add (word i) (word 18446744073709551361):int64) = 0) <=>
    i + 1 < 256`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    ASM_CASES_TAC `i = 255` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 256 /\ ~(i = 255)
      ==> i + 18446744073709551361 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
