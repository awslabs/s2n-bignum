(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_tomsg_spec.ml";;


let COMPRESS_D1_ARITH = prove
 (COMPRESS_D1_ARITH_STMT,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`4 * v + 3329`; `6658`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`(4 * v + 3329) MOD 6658`,`r:num`) THEN
  SPEC_TAC(`(4 * v + 3329) DIV 6658`,`q:num`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `(1073741824 + v * 1290168) - q * 2147483648` THEN
  ASM_ARITH_TAC);;

let TOMSG_BIT = prove
 (TOMSG_BIT_STMT,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WORD_SX_SMALL; ARITH_RULE `y < 3329 ==> y < 32768`] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_32_64; MOD_MOD_REFL] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 4294967296`] THEN
  SUBGOAL_THEN `((4 * val(y:int16) + 3329) DIV 6658) MOD 2 < 4294967296`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [MATCH_MP_TAC(ARITH_RULE `x < 2 ==> x < 4294967296`) THEN
    REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2147483648 * 2`; GSYM DIV_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[COMPRESS_D1_ARITH]);;

let NSUM_BYTE = prove
 (NSUM_BYTE_STMT,
  REWRITE_TAC[EXP_ADD; GSYM NSUM_LMUL] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[MULT_AC]);;

let MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `x:num->int16`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[SOME_FLAGS; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The outer loop, over the bytes, with the test as a separate step ***)

  ENSURES_WHILE_UP_TAC `32` `pc + mlkem_poly_tomsg_loop1`
   `pc + mlkem_poly_tomsg_loop1_test`
   `\i s. read X3 s = word i /\
          read X4 s = r /\
          read X6 s = a /\
          read X7 s = word 1073741824 /\
          read X8 s = word 1290168 /\
          read X30 s = returnaddress /\
          (!j. j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          ((!j. j < 256 ==> val(x j) < 3329)
           ==> read(memory :> bytes(r,i)) s =
               nsum {j | j < 8 * i}
                (\j. ((4 * val(x j) + 3329) DIV 6658) MOD 2 * 2 EXP j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_MONO_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; NSUM_CLAUSES_NUMSEG_LT;
                READ_MEMORY_BYTES_TRIVIAL];

    (*** The loop body, for eight coefficients and one byte ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun jt ->
      FIRST_ASSUM(MP_TAC o SPEC jt o check (is_forall o concl)) THEN
      ANTS_TAC THENL [UNDISCH_TAC `i < 32` THEN ARITH_TAC; DISCH_TAC])
     tomsg_indices THEN
    TOMSG_BODY_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

    (*** Split off the new byte and the bits for it ***)

    REWRITE_TAC[READ_MEMORY_BYTES_SNOC] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`; NSUM_LT_ADD;
                EQ_ADD_LCANCEL] THEN
    REWRITE_TAC[BETA_RULE(ISPECL
     [`\j. ((4 * val((x:num->int16) j) + 3329) DIV 6658) MOD 2`; `8 * i`]
     NSUM_BYTE)] THEN
    REWRITE_TAC[EQ_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[NUMSEG_LT; ARITH_EQ] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_NSUM_CONV) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN

    (*** The compression of each coefficient ***)

    MAP_EVERY (fun jt ->
      MP_TAC(SPEC (mk_comb(`x:num->int16`,jt)) TOMSG_BIT) THEN
      ANTS_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check
         (can (term_match []
                `!j. j < 256 ==> val((x:num->int16) j) < 3329`) o
          concl)) THEN
        UNDISCH_TAC `i < 32` THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC]) tomsg_indices THEN

    (*** Check all combinations of the bits ***)

    MAP_EVERY (fun jt ->
      let ft = vsubst [mk_comb(`x:num->int16`,jt),`y:int16`]
                `((4 * val(y:int16) + 3329) DIV 6658) MOD 2` in
      MP_TAC(SPECL [lhand ft; `2`] MOD_LT_EQ) THEN REWRITE_TAC[ARITH_EQ] THEN
      SPEC_TAC(ft,genvar `:num`)) (rev tomsg_indices) THEN
    CONV_TAC(TOP_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV));

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_MONO_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_MONO_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_MONO_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_MONO_EXEC (2--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (is_imp o concl))]);;

let MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a r pc returnaddress)
        (APPEND
          (ENUMERATEL 32 (\i. f_ev_loop a r pc returnaddress i))
          (f_ev_prol a r pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              SOME_FLAGS; ALL;
              fst MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_MONO_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem_poly_tomsg_loop1`
   `pc + mlkem_poly_tomsg_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X3 s = word i /\
           read X4 s = r /\
           read X6 s = a` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_MONO_EXEC (1--6) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_MONO_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  TOMSG_BODY_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_GCC12_O2_MONO_EXEC (94--95) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `~(val(word_add (word i) (word 18446744073709551585):int64) = 0) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    ASM_CASES_TAC `i = 31` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 32 /\ ~(i = 31)
      ==> i + 18446744073709551585 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
