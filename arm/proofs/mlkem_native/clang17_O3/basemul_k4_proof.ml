(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/clang17_O3/basemul_k4_spec.ml";;


let BASEMUL_ALIAS = prove
 (BASEMUL_ALIAS_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP NONOVERLAPPING_ALIAS_CHECK) THEN
  REWRITE_TAC[VAL_WORD_SUB_FLAG; VAL_WORD_SUB_EQ_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

let WORD_ISHR_16_SUBWORD = prove
 (WORD_ISHR_16_SUBWORD_STMT,
  BITBLAST_TAC);;

let BASEMUL_LANE = prove
 (BASEMUL_LANE_STMT,
  GEN_TAC THEN REWRITE_TAC[GSYM MONTRED_NEON_SCALAR; montred_neon] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_ISHR_16_SUBWORD] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_MUL; VAL_WORD;
              DIMINDEX_16; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(t:int32)`,`v:num`) THEN GEN_TAC THEN
  REWRITE_TAC[MOD_MOD_REFL; DIV_1] THEN
  REWRITE_TAC[ARITH_RULE `v * 4076929024 = 65536 * v * 62209`;
              ARITH_RULE `4294967296 = 65536 * 65536`] THEN
  REWRITE_TAC[MOD_MULT2] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ; MOD_MOD_REFL] THEN
  REWRITE_TAC[MOD_MOD; ARITH_EQ; MOD_MULT_LMOD]);;

let BASEMUL_LOOP_FLAG = prove
 (BASEMUL_LOOP_FLAG_STMT,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  ASM_CASES_TAC `i = 15` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `i < 16 /\ ~(i = 15)
    ==> 32 * i + 18446744073709551136 < 18446744073709551616`] THEN
  SIMPLE_ARITH_TAC);;

let BM_ADDR_AB_GEN = prove
 (BM_ADDR_AB_GEN_STMT,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let BM_ADDR_CD_GEN = prove
 (BM_ADDR_CD_GEN_STMT,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let BM_ADDR_E = prove
 (BM_ADDR_E_STMT,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let BM_ADDR_F = prove
 (BM_ADDR_F_STMT,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`srcA:int64`; `srcB:int64`; `srcBt:int64`; `dst:int64`;
    `x0:num->int16`; `y0:num->int16`; `y0t:num->int16`;
    `x1:num->int16`; `y1:num->int16`; `y1t:num->int16`;
    `x2:num->int16`; `y2:num->int16`; `y2t:num->int16`;
    `x3:num->int16`; `y3:num->int16`; `y3t:num->int16`;
    `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The vector loop, with the loop test at the end of the body ***)

  ENSURES_WHILE_UP2_TAC `16`
   `pc + mlkem1024_polyvec_basemul_acc_montgomery_cached_loop1`
   `pc + mlkem1024_polyvec_basemul_acc_montgomery_cached_loop1_exit`
   basemul_k4_inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The checks for overlap, which go to the vector code, and the
     *** setup of the pointers and the constants
     ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_EXEC (1--13) THEN
    BASEMUL_ALIAS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_EXEC (14--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; CONJUNCT1 LT];

    (*** The loop body, computing 8 pairs of output coefficients from
     *** 256-bit and 128-bit loads of the inputs
     ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    BM_LOAD_TAC `x0:num->int16` 16 16 (BM_ADDR_AB 0) THEN
    BM_LOAD_TAC `y0:num->int16` 16 16 (BM_ADDR_AB 0) THEN
    BM_LOAD_TAC `y0t:num->int16` 8 8 (BM_ADDR_CD 0) THEN
    BM_LOAD_TAC `x1:num->int16` 16 16 (BM_ADDR_AB 512) THEN
    BM_LOAD_TAC `y1:num->int16` 16 16 (BM_ADDR_AB 512) THEN
    BM_LOAD_TAC `y1t:num->int16` 8 8 (BM_ADDR_CD 256) THEN
    BM_LOAD_TAC `x2:num->int16` 16 16 (BM_ADDR_AB 1024) THEN
    BM_LOAD_TAC `y2:num->int16` 16 16 (BM_ADDR_AB 1024) THEN
    BM_LOAD_TAC `y2t:num->int16` 8 8 (BM_ADDR_CD 512) THEN
    BM_LOAD_TAC `x3:num->int16` 16 16 (BM_ADDR_AB 1536) THEN
    BM_LOAD_TAC `y3:num->int16` 16 16 (BM_ADDR_AB 1536) THEN
    BM_LOAD_TAC `y3t:num->int16` 8 8 (BM_ADDR_CD 768) THEN
    MAP_EVERY (fun t -> MP_TAC(READ_MEMORY_MERGE_CONV 4 t))
     [`read(memory :> bytes256(word_add srcA (word(32 * i)))) s0`;
      `read(memory :> bytes256(word_add srcB (word(32 * i)))) s0`;
      `read(memory :> bytes256(word_add srcA (word(32 * i + 512)))) s0`;
      `read(memory :> bytes256(word_add srcB (word(32 * i + 512)))) s0`;
      `read(memory :> bytes256(word_add srcA (word(32 * i + 1024)))) s0`;
      `read(memory :> bytes256(word_add srcB (word(32 * i + 1024)))) s0`;
      `read(memory :> bytes256(word_add srcA (word(32 * i + 1536)))) s0`;
      `read(memory :> bytes256(word_add srcB (word(32 * i + 1536)))) s0`] THEN
    MAP_EVERY (fun t -> MP_TAC(READ_MEMORY_MERGE_CONV 3 t))
     [`read(memory :> bytes128(word_add srcBt (word(16 * i)))) s0`;
      `read(memory :> bytes128(word_add srcBt (word(16 * i + 256)))) s0`;
      `read(memory :> bytes128(word_add srcBt (word(16 * i + 512)))) s0`;
      `read(memory :> bytes128(word_add srcBt (word(16 * i + 768)))) s0`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
    MAP_EVERY BASEMUL_STEP_TAC (1--74) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
        CONV_RULE (SIMD_SIMPLIFY_CONV []) o
        CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
        check (fun th ->
          can (term_match [] `read (memory :> bytes256 a) s74 = x`)
              (concl th) && free_in `dst:int64` (concl th)))) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[BASEMUL_LOOP_FLAG] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 32`;
                  ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC]) THEN

    (*** The output pairs j < 8 * i, from the invariant, and the new ones
     *** 8 * i + k for k < 8
     ***)

    DISCH_TAC THEN
    MAP_EVERY (fun c ->
      FIRST_ASSUM(MP_TAC o SPEC (subst [mk_small_numeral c,`c:num`]
                                     `16 * i + c`) o
                  check (fun th -> is_forall(concl th) &&
                                   free_in `abs:int->int` (concl th))) THEN
      ANTS_TAC THENL [UNDISCH_TAC `i < 16` THEN ARITH_TAC; STRIP_TAC])
     (0--15) THEN
    X_GEN_TAC `j:num` THEN
    ASM_CASES_TAC `j < 8 * i` THEN ASM_REWRITE_TAC[] THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `?k. k < 8 /\ j = 8 * i + k` STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `j - 8 * i` THEN
      MAP_EVERY UNDISCH_TAC [`j < 8 * (i + 1)`; `~(j < 8 * i)`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `j:num`)) THEN
    UNDISCH_TAC `k < 8` THEN SPEC_TAC(`k:num`,`k:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[BM_ADDR_E; BM_ADDR_F] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN BM_CONG_TAC;

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    ASM_REWRITE_TAC[]]);;

let MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(srcA:int64) (srcB:int64) (srcBt:int64) (dst:int64) (pc:num)
      (returnaddress:int64).
      APPEND
        (f_ev_epil srcA srcB srcBt dst pc returnaddress)
        (APPEND
          (ENUMERATEL 16
            (\i. f_ev_loop srcA srcB srcBt dst pc returnaddress i))
          (f_ev_prol srcA srcB srcBt dst pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `16`
   `pc + mlkem1024_polyvec_basemul_acc_montgomery_cached_loop1`
   `pc + mlkem1024_polyvec_basemul_acc_montgomery_cached_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X0 s = dst /\ read X1 s = srcA /\ read X2 s = srcB /\
           read X3 s = word_add srcBt (word(16 * i)) /\
           read X8 s = word(32 * i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The checks for overlap and the setup ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_EXEC (1--13) THEN
    BASEMUL_ALIAS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_EXEC (14--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_EXEC (1--74) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[BASEMUL_LOOP_FLAG] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 32`;
                  ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop exit and the return ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;
