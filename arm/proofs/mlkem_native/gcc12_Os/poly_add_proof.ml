(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_Os/poly_add_spec.ml";;


let MLKEM_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `b:int64`; `x:num->int16`; `y:num->int16`; `pc:num`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `256` `pc + mlkem_poly_add_loop1`
   `pc + mlkem_poly_add_loop1_test`
   `\i s. read X0 s = r /\ read X1 s = b /\ read X2 s = word(2 * i) /\
          read X30 s = returnaddress /\
          (!j. j < 256
               ==> read(memory :> bytes16(word_add b (word(2 * j)))) s =
                   y j) /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   x j) /\
          (!j. j < i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word_add (x j) (y j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_GCC12_OS_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0] THEN ASM_REWRITE_TAC[];

    (*** The loop body: one coefficient ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes16 (word_add r (word (2 * i)))) s0 = x i /\
      (!j. i + 1 <= j /\ j < 256
           ==> read (memory :> bytes16 (word_add r (word (2 * j)))) s0 = x j)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; GEN_TAC THEN STRIP_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `read (memory :> bytes16 (word_add b (word (2 * i)))) s0 = y i`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_GCC12_OS_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN
    REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MLKEM_NATIVE_W_SIMP_TAC THEN
    REWRITE_TAC[BITBLAST_RULE
     `word_zx(word_add (word_zx (x:int16):int32) (word_zx (y:int16))):int16 =
      word_add x y`];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_GCC12_OS_EXEC (1--2) THEN
    SUBGOAL_THEN `~(val(word_sub (word(2 * i)) (word 512):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 255 ==> 2 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_GCC12_OS_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let MLKEM_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(b:int64) (r:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil b r pc returnaddress)
        (APPEND
          (ENUMERATEL 256 (\i. f_ev_loop b r pc returnaddress i))
          (f_ev_prol b r pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_ADD_GCC12_OS_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + mlkem_poly_add_loop1`
   `pc + mlkem_poly_add_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X0 s = r /\ read X1 s = b /\ read X2 s = word(2 * i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_ADD_GCC12_OS_EXEC (1--1) THEN
    REWRITE_TAC[MULT_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_ADD_GCC12_OS_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_ADD_GCC12_OS_EXEC (1--7) THEN
  SUBGOAL_THEN
   `~(val(word_add (word(2 * i)) (word 18446744073709551106):int64) = 0) <=>
    i + 1 < 256`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    ASM_CASES_TAC `i = 255` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 256 /\ ~(i = 255)
      ==> 2 * i + 18446744073709551106 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
