(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/clang17_O3/poly_add_spec.ml";;


let MOD_2N_CASES = prove
 (MOD_2N_CASES_STMT,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN
  MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC);;

let ALIAS_CHECK_512 = prove
 (ALIAS_CHECK_512_STMT,
  let n = `18446744073709551616` in
  let wit_tac i j =
    MAP_EVERY EXISTS_TAC [i; j] THEN
    REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    W(fun (asl,w) -> let l,r = dest_eq w in
       MP_TAC(SPECL [lhand l; n] MOD_2N_CASES) THEN
       MP_TAC(SPECL [lhand r; n] MOD_2N_CASES)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC in
  let wrap_tacs =
   [wit_tac `0` `(m + 18446744073709551616) - p`;
    wit_tac `(p + 18446744073709551616) - m` `0`] in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; nonoverlapping_modulo] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `r:int64` VAL_BOUND_64) THEN
  MP_TAC(ISPEC `b:int64` VAL_BOUND_64) THEN
  SPEC_TAC(`val(r:int64)`,`m:num`) THEN SPEC_TAC(`val(b:int64)`,`p:num`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `!x. x < 2 EXP 64
        ==> (x + 512) MOD 18446744073709551616 =
            if x + 512 < 18446744073709551616 then x + 512
            else (x + 512) - 18446744073709551616`
  (fun th -> ASM_SIMP_TAC[th]) THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_2N_CASES THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM DE_MORGAN_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_neg(concl th) && is_exists(rand(concl th)))) THEN
  REWRITE_TAC[CONG] THEN
  ASM_CASES_TAC `p + 512 < 18446744073709551616` THEN
  ASM_CASES_TAC `m + 512 < 18446744073709551616` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_REWRITE_TAC[] THEN
  (ASM_CASES_TAC `m:num <= p` THENL
    [FIRST(wit_tac `p - m:num` `0` :: wrap_tacs);
     FIRST(wit_tac `0` `m - p:num` :: wrap_tacs)]));;

let MLKEM_NATIVE_POLY_ADD_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_ADD_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `b:int64`; `x:num->int16`; `y:num->int16`; `pc:num`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_SEQUENCE_TAC `pc + mlkem_poly_add_join1`
   `\s. read X0 s = r /\ read X1 s = b /\ read X30 s = returnaddress /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                 x i) /\
        (!i. i < 256
             ==> read(memory :> bytes16(word_add b (word(2 * i)))) s =
                 y i)` THEN
  CONJ_TAC THENL
   [

    (*** The check for overlap, which goes to the vectorized code ***)

    ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`r:int64`; `b:int64`] ALIAS_CHECK_512) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES]; DISCH_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_CLANG17_O3_EXEC (1--3) THEN
    ASM_CASES_TAC ALIAS_CHECK_1 THENL
     [USE_CASE_TAC ALIAS_CHECK_1 THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      USE_CASE_TAC (mk_neg ALIAS_CHECK_1) THEN
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_CLANG17_O3_EXEC (4--6) THEN
      USE_CASE_TAC ALIAS_CHECK_2 THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    ALL_TAC] THEN

  (*** The vectorized code, with the 32 blocks of 8 coefficients of each
   *** input as 128-bit words, and the 32 blocks of the result split again
   ***)

  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun v ->
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_forall(concl th) && free_in v (concl th))) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC) [`r:int64`; `b:int64`] THEN
  MAP_EVERY (fun v ->
    MAP_EVERY (fun k ->
      let a = if k = 0 then v else
              mk_comb(mk_comb(`word_add:int64->int64->int64`,v),
                      mk_comb(`word:num->int64`,mk_small_numeral(16 * k))) in
      MP_TAC(READ_MEMORY_MERGE_CONV 3
        (subst [a,`a:int64`] `read(memory :> bytes128 a) s0`))) (0--31))
   [`r:int64`; `b:int64`] THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
  MAP_EVERY (fun n ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_CLANG17_O3_EXEC [n] THEN
    SIMD_SIMPLIFY_TAC[]) (1--81) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE (SIMD_SIMPLIFY_CONV []) o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (fun th -> can (term_match [] `read (memory :> bytes128 a) s81 = x`)
                         (concl th)))) THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[WORD_ADD_SYM]);;

let MLKEM_NATIVE_POLY_ADD_CLANG17_O3_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_ADD_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(b:int64) (r:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_vec b r pc returnaddress)
        (if ~(val r <= val (word_add b (word 512)) /\
              ~(val (word_sub (word_add b (word 512)) r) = 0))
         then f_ev_check1 b r pc returnaddress
         else f_ev_check2 b r pc returnaddress)
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_ADD_CLANG17_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_add_join1`
   `\s. read X0 s = r /\ read X1 s = b /\ read X30 s = returnaddress` THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`r:int64`; `b:int64`] ALIAS_CHECK_512) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES]; DISCH_TAC] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_CLANG17_O3_EXEC (1--3) THEN
    ASM_CASES_TAC ALIAS_CHECK_1 THENL
     [USE_CASE_TAC ALIAS_CHECK_1 THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      USE_CASE_TAC (mk_neg ALIAS_CHECK_1) THEN
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_CLANG17_O3_EXEC (4--6) THEN
      USE_CASE_TAC ALIAS_CHECK_2 THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC];
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_ADD_CLANG17_O3_EXEC (1--81) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
