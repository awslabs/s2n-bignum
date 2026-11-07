(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_O2/basemul_k2_spec.ml";;


let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_CORRECT = prove
 (MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`srcA:int64`; `srcB:int64`; `srcBt:int64`; `dst:int64`;
    `x0:num->int16`; `y0:num->int16`; `y0t:num->int16`;
    `x1:num->int16`; `y1:num->int16`; `y1t:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `128` `pc + basemul_k2_loop1`
   `pc + basemul_k2_loop1_test`
   `\i s. read X4 s = word_add srcA (word(4 * i)) /\
          read X5 s = word_add srcB (word(4 * i)) /\
          read X6 s = word_add srcBt (word(2 * i)) /\
          read X7 s = word_add dst (word(4 * i)) /\
          read X13 s = word_add srcA (word 512) /\
          read X12 s = word 4294963969 /\ read X11 s = word 4294963967 /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcA (word (2 * i)))) s = x0 i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcB  (word (2 * i)))) s = y0 i) /\
          (!i. i < 128
               ==> read(memory :> bytes16
                    (word_add srcBt (word (2 * i)))) s = y0t i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcA (word (512 + 2 * i)))) s = x1 i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcB (word (512 + 2 * i)))) s = y1 i) /\
          (!i. i < 128
               ==> read(memory :> bytes16
                    (word_add srcBt (word (256 + 2 * i)))) s = y1t i) /\
          ((!i. i < 256
                ==> abs(ival(x0 i)) <= &2 pow 12 /\
                    abs(ival(x1 i)) <= &2 pow 12)
           ==> (!j. j < i
                    ==> (ival(read(memory :> bytes16
                           (word_add dst (word (4 * j)))) s) ==
                         basemul2_even (ival o x0) (ival o y0) (ival o y0t)
                                       (ival o x1) (ival o y1) (ival o y1t)
                                       j) (mod &3329) /\
                        (ival(read(memory :> bytes16
                           (word_add dst (word (4 * j + 2)))) s) ==
                         basemul2_odd (ival o x0) (ival o y0) (ival o x1)
                         (ival o y1) j) (mod &3329)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization of pointers and constants ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; CONJUNCT1 LT];

    (*** The loop body, computing two output coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY SPECIALIZE_LOAD_TAC
     [`x0:num->int16`,`2 * i`; `x0:num->int16`,`2 * i + 1`;
      `x1:num->int16`,`2 * i`; `x1:num->int16`,`2 * i + 1`;
      `y0:num->int16`,`2 * i`; `y0:num->int16`,`2 * i + 1`;
      `y1:num->int16`,`2 * i`; `y1:num->int16`,`2 * i + 1`;
      `y0t:num->int16`,`i:num`; `y1t:num->int16`,`i:num`] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC (1--34) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`;
                  ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC]) THEN
    DISCH_TAC THEN X_GEN_TAC `j:num` THEN
    REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MLKEM_NATIVE_W_SIMP_TAC THEN
    REWRITE_TAC[WORD_ADD_0] THEN REWRITE_TAC[GSYM montred_scalar] THEN
    SUBGOAL_THEN
     `abs(ival(x0(2 * i):int16)) <= &2 pow 12 /\
      abs(ival(x1(2 * i):int16)) <= &2 pow 12 /\
      abs(ival(x0(2 * i + 1):int16)) <= &2 pow 12 /\
      abs(ival(x1(2 * i + 1):int16)) <= &2 pow 12`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `i < 128 ==> 2 * i < 256 /\ 2 * i + 1 < 256`];
      ALL_TAC] THEN
    CONJ_TAC THEN MONTRED_SCALAR_CONG_TAC;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add srcA (word (4 * i)))
                     (word_add srcA (word 512)):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y) = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 128 ==> 4 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_SUBROUTINE_CORRECT_STMT,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC
    MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_CORRECT);;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_SUBROUTINE_SAFE_STMT,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(srcA:int64) (srcB:int64) (srcBt:int64) (dst:int64) (pc:num)
      (returnaddress:int64).
      APPEND
        (f_ev_epil srcA srcB srcBt dst pc returnaddress)
        (APPEND
          (ENUMERATEL 128
            (\i. f_ev_loop srcA srcB srcBt dst pc returnaddress i))
          (f_ev_prol srcA srcB srcBt dst pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + basemul_k2_loop1`
   `pc + basemul_k2_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X4 s = word_add srcA (word(4 * i)) /\
           read X5 s = word_add srcB (word(4 * i)) /\
           read X6 s = word_add srcBt (word(2 * i)) /\
           read X7 s = word_add dst (word(4 * i)) /\
           read X13 s = word_add srcA (word 512)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false
        MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC (1--8) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_EXEC (1--36) THEN
  SUBGOAL_THEN
   `~(val(word_sub (word_add (word_add srcA (word (4 * i))) (word 4))
                   (word_add srcA (word 512)):int64) = 0) <=>
    i + 1 < 128`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word_add (word_add a y) z) (word_add a x):int64 =
      word_sub (word_add y z) x`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 128 ==> 4 * i + 4 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`;
                ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLKEM_NATIVE_IMAGE_TAC
   (INST [`pc + mlkem512_polyvec_basemul_acc_montgomery_cached`,`pc:num`]
     (SPEC_ALL MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_SUBROUTINE_CORRECT))
   [MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_IN_IMAGE]);;

let MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  MLKEM_NATIVE_IMAGE_SAFE_TAC MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_SUBROUTINE_SAFE
   [`pc + mlkem512_polyvec_basemul_acc_montgomery_cached`,`pc:num`]
   [MLKEM_NATIVE_BASEMUL_K2_GCC12_O2_IN_IMAGE]);;
