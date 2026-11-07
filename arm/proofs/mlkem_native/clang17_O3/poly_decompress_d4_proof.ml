(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/clang17_O3/poly_decompress_d4_spec.ml";;


let D4_LANES = prove
 (D4_LANES_STMT,
  GEN_TAC THEN
  SUBGOAL_THEN
   `!v. v < 256
        ==> word_ushr
             (word_add (word 8)
               (word_mul (word_shl (word_zx (word_and (word 15) (word v:byte)))
                                   0)
                         (word 3329))) 4:int16 =
            word((3329 * v MOD 16 + 8) DIV 16) /\
            word_ushr
             (word_add (word 8)
               (word_mul (word_shl (word_zx (word_ushr (word v:byte) 4)) 0)
                         (word 3329))) 4:int16 =
            word((3329 * v DIV 16 + 8) DIV 16)`
   (MP_TAC o SPEC `val(b:byte)`) THENL
   [CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV));
    REWRITE_TAC[WORD_VAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    ARITH_TAC]);;

let D4_NIBBLES = prove
 (D4_NIBBLES_STMT,
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN REPEAT STRIP_TAC THEN
  SPEC_TAC(`n DIV 2 EXP k`,`x:num`) THEN GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `256 = 16 * 16`; MOD_MOD; DIV_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let D4_LANES2 = prove
 (D4_LANES2_STMT,
  GEN_TAC THEN
  SUBGOAL_THEN
   `!v. v < 256
        ==> word((val(word_mul (word_zx (word_shl (word_zx (word_ushr
                (word v:byte) 4):int16) 0):int32) (word 3329)) + 8) DIV 16):
            int16 = word((3329 * v DIV 16 + 8) DIV 16) /\
            word((val(word_mul (word_zx (word_shl (word_zx (word_and
                (word 15) (word v:byte)):int16) 0):int32) (word 3329)) + 8)
                 DIV 16):int16 = word((3329 * v MOD 16 + 8) DIV 16)`
   (MP_TAC o SPEC `val(b:byte)`) THENL
   [CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV));
    REWRITE_TAC[WORD_VAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    ARITH_TAC]);;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_DECOMPRESS_D4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `n:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  D4_INPUT_TAC THEN

  (*** The overlap check, and the vector code ***)

  D4_CHECK_TAC (fun off ->
    MAP_EVERY (fun k ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_CLANG17_O3_EXEC [k + off] THEN
      SIMD_SIMPLIFY_TAC[]) (1--219)) THEN
  D4_STORES_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Each coefficient from its 4-bit field ***)

  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[D4_NIBBLES] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 4 = 16`]);;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_DECOMPRESS_D4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (returnaddress:int64).
      (if val(word_add a (word 128):int64) <= val r
       then f_ev1 a r pc returnaddress
       else f_ev2 a r pc returnaddress):(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_DECOMPRESS_D4_CLANG17_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  D4_CHECK_TAC (fun off ->
    MAP_EVERY (fun k ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_CLANG17_O3_EXEC [k + off])
     (1--219)) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
