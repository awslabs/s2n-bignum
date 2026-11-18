(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_O2/poly_mulcache_compute_spec.ml";;


let MLK_ZETAS_MULCACHE = prove
 (MLK_ZETAS_MULCACHE_STMT,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[mlk_zetas] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[BITREVERSE7_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let MLK_ZETAS_MULCACHE_IVAL = prove
 (MLK_ZETAS_MULCACHE_IVAL_STMT,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MLK_ZETAS_MULCACHE) THEN
  SUBGOAL_THEN
   `ival(iword(EL (64 + i) mlk_zetas):int16) = EL (64 + i) mlk_zetas`
  SUBST1_TAC THENL [MATCH_MP_TAC IVAL_IWORD; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;

let WORD_ZX_NEG_SX = prove
 (WORD_ZX_NEG_SX_STMT,
  BITBLAST_TAC);;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_CORRECT = prove
 (MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`dst:int64`; `src:int64`; `zetas:num`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step. The ***)
  (*** constant parts of the pointers are kept apart so that address  ***)
  (*** offsets in loads and stores are simplified.                    ***)

  ENSURES_WHILE_UP_TAC `64` `pc + poly_mulcache_compute_loop1`
   `pc + poly_mulcache_compute_loop1_test`
   `\i s. read X5 s = word_add (word_add (word zetas) (word(2 * i)))
                               (word 128) /\
          read X8 s = word_add (word zetas) (word 256) /\
          read X2 s = word_add (word_add src (word(8 * i))) (word 2) /\
          read X4 s = word_add (word_add dst (word(4 * i))) (word 2) /\
          read X7 s = word 4294963969 /\ read X6 s = word 4294963967 /\
          (!k. k < 128
               ==> read(memory :> bytes16(word_add (word zetas)
                                                   (word(2 * k)))) s =
                   iword(EL k mlk_zetas)) /\
          (!i. i < 256
                ==> read(memory :> bytes16(word_add src (word (2 * i)))) s =
                    x i) /\
          (!j. j < 2 * i
               ==> let z_j = read(memory :> bytes16
                                (word_add dst (word (2 * j)))) s in
                   (ival z_j == (mulcache (ival o x)) j) (mod &3329) /\
                   abs(ival z_j) <= &3328)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, including the address of the table ***)

    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLK_ZETAS_LOADED) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--2) THEN
    FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP ADRP_ADD_FOLD) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (3--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body, computing two output coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY MSPEC_TAC
     [`mlk_zetas`,`64 + i`; `x:num->int16`,`4 * i + 1`;
      `x:num->int16`,`4 * i + 3`] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--18) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`;
                  ARITH_RULE `8 * (i + 1) = 8 * i + 8`;
                  ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC]) THEN
    X_GEN_TAC `j:num` THEN
    REWRITE_TAC[ARITH_RULE
     `j < 2 * (i + 1) <=> j < 2 * i \/ j = 2 * i \/ j = 2 * i + 1`] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check
       (fun th -> is_forall(concl th) &&
                  can (find_term (fun t -> try fst(dest_const t) = "mulcache"
                                           with _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC; ALL_TAC] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `2 * 2 * i = 4 * i`;
                ARITH_RULE `2 * (2 * i + 1) = 4 * i + 2`] THEN
    ASM_REWRITE_TAC[] THEN MLKEM_NATIVE_W_SIMP_TAC THEN
    REWRITE_TAC[WORD_ADD_0; SXFROM_15_SUBWORD; WORD_ZX_NEG_SX] THEN
    REWRITE_TAC[GSYM SXFROM_15_SUBWORD] THEN
    REWRITE_TAC[GSYM montred_scalar] THEN
    MULCACHE_OUTPUT_TAC;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add (word zetas) (word 256))
                     (word_add (word_add (word zetas) (word (2 * i)))
                               (word 128)):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add (word_add a y) z):int64 =
        word_sub x (word_add y z)`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 64 ==> 2 * i + 128 < 18446744073709551616`] THEN
      ASM_ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                can (find_term (fun t -> try fst(dest_const t) = "mulcache"
                                         with _ -> false)) (concl th)))]);;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_CORRECT_STMT,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_CORRECT);;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_SAFE_STMT,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(src:int64) (dst:int64) (zetas:num) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil src dst zetas pc returnaddress)
        (APPEND
          (ENUMERATEL 64 (\i. f_ev_loop src dst zetas pc returnaddress i))
          (f_ev_prol src dst zetas pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `64` `pc + poly_mulcache_compute_loop1`
   `pc + poly_mulcache_compute_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X5 s = word_add (word_add (word zetas) (word(2 * i)))
                                (word 128) /\
           read X8 s = word_add (word zetas) (word 256) /\
           read X2 s = word_add (word_add src (word(8 * i))) (word 2) /\
           read X4 s = word_add (word_add dst (word(4 * i))) (word 2)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--2) THEN
    FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP ADRP_ADD_FOLD) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (3--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--20) THEN
  SUBGOAL_THEN
   `~(val(word_sub (word_add (word zetas) (word 256))
                   (word_add (word_add (word zetas) (word (2 * i))) (word 130))
          :int64) = 0) <=>
    i + 1 < 64`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word_add a x) (word_add (word_add a y) z):int64 =
      word_sub x (word_add y z)`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 64 ==> 2 * i + 130 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`;
                ARITH_RULE `8 * (i + 1) = 8 * i + 8`;
                ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLKEM_NATIVE_IMAGE_TAC
   (INST [`pc + mlkem_poly_mulcache_compute`,`pc:num`;
          `pc + rodata_mlk_zetas`,`zetas:num`]
     (SPEC_ALL MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_CORRECT))
   [MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IN_IMAGE;
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_ZETAS_IN_IMAGE]);;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  MLKEM_NATIVE_IMAGE_SAFE_TAC
   MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_SAFE
   [`pc + mlkem_poly_mulcache_compute`,`pc:num`;
    `pc + rodata_mlk_zetas`,`zetas:num`]
   [MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IN_IMAGE;
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_ZETAS_IN_IMAGE]);;
