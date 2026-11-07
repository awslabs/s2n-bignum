(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/clang17_O2/poly_reduce_spec.ml";;


let CONDADD_CLANG17_O2 = prove
 (CONDADD_CLANG17_O2_STMT,
  BITBLAST_TAC);;

let REDUCE_ELEMENT = prove
 (REDUCE_ELEMENT_STMT,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CONDADD_CLANG17_O2; BARRED_SCALAR; BARRED_CONDADD_REM]);;

let MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_CORRECT = prove
 (MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `256` `pc + poly_reduce_loop1`
   `pc + poly_reduce_loop1_test`
   `\i s. read X0 s = a /\ read X8 s = word(2 * i) /\
          read X9 s = word 20159 /\ read X10 s = word 33554432 /\
          read X11 s = word 4294963967 /\
          (!j. j < i
               ==> ival(read(memory :> bytes16(word_add a (word(2 * j)))) s) =
                   ival(x j) rem &3329) /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization of the constants and the offset ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; CONJUNCT1 LT; LE_0] THEN
    ASM_REWRITE_TAC[];

    (*** The loop body: process one coefficient ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read (memory :> bytes16 (word_add a (word (2 * i)))) s0 = x i /\
      (!j. i + 1 <= j /\ j < 256
           ==> read (memory :> bytes16 (word_add a (word (2 * j)))) s0 = x j)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; GEN_TAC THEN STRIP_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_EXEC (1--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN
    REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MLKEM_NATIVE_W_SIMP_TAC THEN
    REWRITE_TAC[CONV_RULE(TOP_DEPTH_CONV let_CONV) REDUCE_ELEMENT];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_EXEC (1--2) THEN
    SUBGOAL_THEN `~(val(word_sub (word (2 * i)) (word 512):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 256 ==> 2 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_SUBROUTINE_CORRECT_STMT,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_EXEC
    MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_CORRECT);;

let MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_SUBROUTINE_SAFE_STMT,
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
              fst MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + poly_reduce_loop1`
   `pc + poly_reduce_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X0 s = a /\
           read X8 s = word(2 * i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_EXEC (1--4) THEN
    CONJ_TAC THENL [REWRITE_TAC[MULT_0; WORD_ADD_0]; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_REDUCE_CLANG17_O2_EXEC (1--15) THEN
  SUBGOAL_THEN
   `~(val(word_add (word (2 * i)) (word 18446744073709551106):int64) = 0) <=>
    i + 1 < 256`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 256 ==> 2 * i < 18446744073709551616`] THEN
    ASM_CASES_TAC `i = 255` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 256 /\ ~(i = 255)
      ==> 2 * i + 18446744073709551106 < 18446744073709551616`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
