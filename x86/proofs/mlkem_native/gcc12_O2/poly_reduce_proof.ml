(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/gcc12_O2/poly_reduce_spec.ml";;


let BARRETT_GCC12_O2 = prove
 (BARRETT_GCC12_O2_STMT,
  BITBLAST_TAC);;

let CONDADD_GCC12_O2 = prove
 (CONDADD_GCC12_O2_STMT,
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN BITBLAST_TAC);;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_CORRECT = prove
 (MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `256` `pc + poly_reduce_loop1` `pc + poly_reduce_loop1_test`
   `\i s. read RCX s = word_add a (word(2 * i)) /\
          read RSI s = word_add a (word 512) /\
          (!j. j < i
               ==> ival(read(memory :> bytes16(word_add a (word(2 * j)))) s) =
                   ival(x j) rem &3329) /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization of the pointers ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC (1--3) THEN
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
    X86_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC (1--17) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN
    REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MLKEM_NATIVE_WORD_SIMP_TAC THEN
    REWRITE_TAC[CONDADD_GCC12_O2] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[BARRETT_GCC12_O2; BARRED_GCC12_O2; BARRED_CONDADD_REM];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add a (word (2 * i)))
                     (word_add a (word 512)):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y) = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 256 ==> 2 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 256` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_CORRECT_STMT,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_CORRECT);;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SAFE = time prove
 (MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SAFE_STMT,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (pc:num).
      APPEND
        (f_ev_epil a pc)
        (APPEND
          (ENUMERATEL 256 (\i. f_ev_loop a pc i))
          (f_ev_prol a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + poly_reduce_loop1` `pc + poly_reduce_loop1_exit`
    `\i s. read RCX s = word_add a (word(2 * i)) /\
           read RSI s = word_add a (word 512)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC (1--3) THEN
    CONJ_TAC THENL [REWRITE_TAC[MULT_0; WORD_ADD_0]; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC (1--0) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC (1--19) THEN
  SUBGOAL_THEN
   `~(val(word_add (word_add a (word (2 * i))) (word 2):int64) =
      val(word_add a (word 512):int64)) <=> i + 1 < 256`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_EQ; GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_EQ; DIMINDEX_64; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 256 ==> 2 * i + 2 < 18446744073709551616`] THEN
    UNDISCH_TAC `i < 256` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_SAFE_STMT,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLKEM_NATIVE_IMAGE_TAC
   (INST [`pc + mlkem_poly_reduce`,`pc:num`]
     (SPEC_ALL MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_CORRECT))
   [MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IN_IMAGE]);;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  MLKEM_NATIVE_IMAGE_SAFE_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_SAFE
   [`pc + mlkem_poly_reduce`,`pc:num`]
   [MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IN_IMAGE]);;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_FULL = time prove
 (MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_FULL_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (pc:num).
      APPEND
        (f_ev_epil a pc)
        (APPEND
          (ENUMERATEL 256 (\i. f_ev_loop a pc i))
          (f_ev_prol a pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + poly_reduce_loop1` `pc + poly_reduce_loop1_exit`
   `\i s. read RCX s = word_add a (word(2 * i)) /\
          read RSI s = word_add a (word 512) /\
          (!j. j < i
               ==> ival(read(memory :> bytes16(word_add a (word(2 * j)))) s) =
                   ival(x j) rem &3329) /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization of the pointers ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; CONJUNCT1 LT; LE_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN
     `read (memory :> bytes16 (word_add a (word (2 * i)))) s0 = x i /\
      (!j. i + 1 <= j /\ j < 256
           ==> read (memory :> bytes16 (word_add a (word (2 * j)))) s0 = x j)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; GEN_TAC THEN STRIP_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC (1--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add (word_add a (word (2 * i))) (word 2))
                     (word_add a (word 512)):int64) = 0) <=>
      i + 1 < 256`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add (word_add a x) y) (word_add a z):int64 =
        word_sub (word_add x y) z`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 256 ==> 2 * i + 2 < 18446744073709551616`] THEN
      UNDISCH_TAC `i < 256` THEN ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN
      REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[] THEN
      MLKEM_NATIVE_WORD_SIMP_TAC THEN
      REWRITE_TAC[CONDADD_GCC12_O2] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[BARRETT_GCC12_O2; BARRED_GCC12_O2; BARRED_CONDADD_REM];
      ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop exit ***)

    REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_FULL = time prove
 (MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_FULL_STMT,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_FULL THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  MLKEM_NATIVE_IMAGE_SAFE_TAC MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_SUBROUTINE_FULL
   [`pc + mlkem_poly_reduce`,`pc:num`]
   [MLKEM_NATIVE_POLY_REDUCE_GCC12_O2_IN_IMAGE]);;
