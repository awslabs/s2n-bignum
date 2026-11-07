(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_O2/poly_decompress_d4_spec.ml";;


let BYTE_NIBBLES = prove
 (BYTE_NIBBLES_STMT,
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN REPEAT STRIP_TAC THEN
  SPEC_TAC(`n DIV 2 EXP k`,`x:num`) THEN GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `256 = 16 * 16`; MOD_MOD; DIV_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `n:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `128` `pc + mlkem_poly_decompress_d4_loop1`
   `pc + mlkem_poly_decompress_d4_loop1_test`
   `\i s. read X0 s = word_add r (word(4 * i)) /\
          read X1 s = word_add a (word i) /\
          read X3 s = word 3329 /\
          read X4 s = word_add r (word 512) /\
          read X30 s = returnaddress /\
          read (memory :> bytes(a,128)) s = n /\
          (!j. j < 2 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((3329 * (n DIV 2 EXP (4 * j)) MOD 2 EXP 4 + 8)
                        DIV 16))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body, for one byte and two coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`a:int64`; `128`; `n:num`; `i:num`; `s0:armstate`]
                 READ_MEMORY_BYTES8_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC (1--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC];
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE
     `j < 2 * (i + 1) <=> j < 2 * i \/ j = 2 * i \/ j = 2 * i + 1`] THEN
    REWRITE_TAC[TAUT `(p \/ q \/ r ==> s) <=>
                      (p ==> s) /\ (q ==> s) /\ (r ==> s)`;
                FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `2 * 2 * i = 4 * i`;
                ARITH_RULE `2 * (2 * i + 1) = 4 * i + 2`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `4 * 2 * i = 8 * i`;
                ARITH_RULE `4 * (2 * i + 1) = 8 * i + 4`] THEN
    REWRITE_TAC[BYTE_NIBBLES] THEN

    (*** Check all values of the byte ***)

    MP_TAC(SPECL [`n DIV 2 EXP (8 * i)`; `256`] MOD_LT_EQ) THEN
    REWRITE_TAC[ARITH_EQ] THEN
    SPEC_TAC(`(n DIV 2 EXP (8 * i)) MOD 256`,`m:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV));

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC (2--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `bytes16` (concl th)))]);;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a r pc returnaddress)
        (APPEND
          (ENUMERATEL 128 (\i. f_ev_loop a r pc returnaddress i))
          (f_ev_prol a r pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + mlkem_poly_decompress_d4_loop1`
   `pc + mlkem_poly_decompress_d4_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X0 s = word_add r (word(4 * i)) /\
           read X1 s = word_add a (word i) /\
           read X4 s = word_add r (word 512)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC (1--3) THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O2_EXEC (1--15) THEN
  SUBGOAL_THEN
   `~(val(word_sub (word_add r (word 512))
                   (word_add (word_add r (word (4 * i))) (word 4)):int64) =
      0) <=>
    i + 1 < 128`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word_add a x) (word_add (word_add a y) z):int64 =
      word_sub x (word_add y z)`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 128 ==> 4 * i + 4 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) THEN
  TRY(CONJ_TAC THENL
   [REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC]; ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
