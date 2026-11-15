(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/gcc12_O2/basemul_k3_spec.ml";;


let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_CORRECT = prove
 (MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`srcA:int64`; `srcB:int64`; `srcBt:int64`; `dst:int64`;
    `x0:num->int16`; `y0:num->int16`; `y0t:num->int16`;
    `x1:num->int16`; `y1:num->int16`; `y1t:num->int16`;
    `x2:num->int16`; `y2:num->int16`; `y2t:num->int16`; `pc:num`;
    `stackpointer:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The outer loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `128` `pc + basemul_k3_loop1` `pc + basemul_k3_loop1_test`
   `\i s. read RAX s = word_add srcBt (word(2 * i)) /\
          read R9 s = word_add srcA (word(4 * i)) /\
          read R8 s = word_add (word_add srcB (word(4 * i))) (word 2) /\
          read RDX s = word_add (word_add dst (word(4 * i))) (word 2) /\
          read R14 s = word_add srcBt (word 256) /\
          read RSP s = word_add stackpointer (word 4) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcA (word (2 * i)))) s = x0 i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcB (word (2 * i)))) s = y0 i) /\
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
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcA (word (1024 + 2 * i)))) s = x2 i) /\
          (!i. i < 256
               ==> read(memory :> bytes16
                    (word_add srcB (word (1024 + 2 * i)))) s = y2 i) /\
          (!i. i < 128
               ==> read(memory :> bytes16
                    (word_add srcBt (word (512 + 2 * i)))) s = y2t i) /\
          ((!i. i < 256
                ==> abs(ival(x0 i)) <= &2 pow 12 /\
                    abs(ival(x1 i)) <= &2 pow 12 /\
                    abs(ival(x2 i)) <= &2 pow 12)
           ==> (!j. j < i
                    ==> (ival(read(memory :> bytes16
                           (word_add dst (word (4 * j)))) s) ==
                         basemul3_even
                          (ival o x0) (ival o y0) (ival o y0t)
                          (ival o x1) (ival o y1) (ival o y1t)
                          (ival o x2) (ival o y2) (ival o y2t)
                          j) (mod &3329) /\
                        (ival(read(memory :> bytes16
                           (word_add dst (word (4 * j + 2)))) s) ==
                         basemul3_odd
                          (ival o x0) (ival o y0) (ival o x1)
                          (ival o y1) (ival o x2) (ival o y2)
                          j) (mod &3329)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The initialization is already done ***)

    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; CONJUNCT1 LT];

    (*** The loop body, with the inner loop over the three polynomials
     *** unrolled, computing two output coefficients
     ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    BASEMUL_READ_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC (1--85) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
    DISCH_TAC THEN X_GEN_TAC `j:num` THEN
    REWRITE_TAC[ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC] THEN
    ASM_REWRITE_TAC[] THEN MLKEM_NATIVE_WORD_SIMP_TAC THEN
    REWRITE_TAC[MONTRED_X86_FOLD] THEN
    SUBGOAL_THEN
     `abs(ival(x0(2 * i):int16)) <= &2 pow 12 /\
      abs(ival(x1(2 * i):int16)) <= &2 pow 12 /\
      abs(ival(x2(2 * i):int16)) <= &2 pow 12 /\
      abs(ival(x0(2 * i + 1):int16)) <= &2 pow 12 /\
      abs(ival(x1(2 * i + 1):int16)) <= &2 pow 12 /\
      abs(ival(x2(2 * i + 1):int16)) <= &2 pow 12`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `i < 128 ==> 2 * i < 256 /\ 2 * i + 1 < 256`];
      ALL_TAC] THEN
    CONJ_TAC THEN BASEMUL_CONG_TAC;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add srcBt (word 256))
                     (word_add srcBt (word (2 * i))):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add x y) (word_add x z):int64 = word_sub y z`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 128 ==> 2 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 128` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_SUBROUTINE_CORRECT_STMT,
  GEN_X86_ADD_RETURN_STACK_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC
    MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_CORRECT
    `[R15; R14; R13; R12; RBP; RBX]` 52 (12,7));;

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_SAFE = time prove
 (MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_SAFE_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(srcA:int64) (srcB:int64) (srcBt:int64) (dst:int64) (pc:num)
      (stackpointer:int64).
      APPEND
        (f_ev_epil srcA srcB srcBt dst pc stackpointer)
        (APPEND
          (ENUMERATEL 128
            (\i. f_ev_loop srcA srcB srcBt dst pc stackpointer i))
          (f_ev_prol srcA srcB srcBt dst pc stackpointer))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + basemul_k3_loop1` `pc + basemul_k3_loop1_exit`
    `\i s. read RAX s = word_add srcBt (word(2 * i)) /\
           read R9 s = word_add srcA (word(4 * i)) /\
           read R8 s = word_add (word_add srcB (word(4 * i))) (word 2) /\
           read RDX s = word_add (word_add dst (word(4 * i))) (word 2) /\
           read R14 s = word_add srcBt (word 256) /\
           read RSP s = word_add stackpointer (word 4)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC (1--0) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC (1--0) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN VAL_INT64_TAC `i:num` THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC (1--87) THEN
  SUBGOAL_THEN
   `~(val (word_add srcBt (word 256):int64) =
      val (word_add (word_add srcBt (word (2 * i))) (word 2):int64)) <=>
    i + 1 < 128`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_EQ; GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_EQ; DIMINDEX_64; CONG] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 128 ==> 2 * i + 2 < 2 EXP 64`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 128` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_SUBROUTINE_SAFE_STMT,
  GEN_X86_ADD_RETURN_STACK_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_EXEC
    MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_SAFE
    `[R15; R14; R13; R12; RBP; RBX]` 52 (12,7) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLKEM_NATIVE_IMAGE_TAC
   (INST [`pc + mlkem768_polyvec_basemul_acc_montgomery_cached`,`pc:num`]
     (SPEC_ALL MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_SUBROUTINE_CORRECT))
   [MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_IN_IMAGE]);;

let MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  MLKEM_NATIVE_IMAGE_SAFE_TAC MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_SUBROUTINE_SAFE
   [`pc + mlkem768_polyvec_basemul_acc_montgomery_cached`,`pc:num`]
   [MLKEM_NATIVE_BASEMUL_K3_GCC12_O2_IN_IMAGE]);;
