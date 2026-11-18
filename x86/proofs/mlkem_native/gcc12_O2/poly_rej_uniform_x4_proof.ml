(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/gcc12_O2/poly_rej_uniform_x4_spec.ml";;


let REJX4_SAMPLE_SUC = prove
 (REJX4_SAMPLE_SUC_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[REJ_FIELDS_SUC; REJ_SAMPLE_APPEND] THEN
  MAP_EVERY (fun (t,v) -> SPEC_TAC(t,v))
   [`REJ_SAMPLE(wordlist_of_num 112 (num_of_bytelist
      (list_of_seq (\i. (f:num->byte)((504 + 168 * j) + i)) 168)))`,
    `l2:int16 list`;
    `REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
      (num_of_bytelist(list_of_seq (f:num->byte) (504 + 168 * j))))`,
    `l1:int16 list`] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `LENGTH(l1:int16 list) <= 256` THENL
   [ASM_SIMP_TAC[SUB_LIST_APPEND_RIGHT; SUB_LIST_REFL;
                 ARITH_RULE `x <= 256 ==> MIN 256 x = x`];
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
    ASM_SIMP_TAC[SUB_LIST_APPEND_LEFT; LT_IMP_LE; SUB_REFL;
                 ARITH_RULE `256 < x ==> MIN 256 x = 256`] THEN
    REWRITE_TAC[SUB_LIST_CLAUSES; APPEND_NIL]]);;

let REJX4_FRAME_ADDRESS = prove
 (REJX4_FRAME_ADDRESS_STMT,
  let lemma = prove
   (`!x:int64. word_and x (word 18446744073709551584) =
               word_sub x (word(val x MOD 32))`,
    GEN_TAC THEN
    SUBGOAL_THEN `val(x:int64) MOD 32 = val(word_and x (word 31):int64)`
    SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD_AND_MASK_WORD; ARITH_RULE `31 = 2 EXP 5 - 1`] THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 5 = 32`];
      REWRITE_TAC[WORD_VAL] THEN
      W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w))]) in
  GEN_TAC THEN REWRITE_TAC[lemma] THEN
  MP_TAC(SPECL [`val(word_add a (word 3368):int64)`; `32`] MOD_LT_EQ) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`val(word_add a (word 3368):int64) MOD 32`,`k:num`) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(INST [`456`,`x:num`; `k:num`,`y:num`]
    (INST_TYPE [`:64`,`:N`] WORD_SUB2)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `k < 32` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC WORD_RULE);;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REJX4_INTRO_TAC THEN REJX4_SETUP_TAC THEN REJX4_ABSORBED_TAC THEN
  REJX4_MINIMAL_TAC THEN

  (*** The first three blocks of each and the samples from them ***)

  ENSURES_SEQUENCE_TAC `pc + mlkem_poly_rej_uniform_x4_sampled` REJX4_A2 THEN CONJ_TAC THENL
   [ENSURES_SEQUENCE_TAC `pc + mlkem_poly_rej_uniform_x4_after_mlk_rej_uniform_c_4` REJX4_A1 THEN CONJ_TAC THENL
     [REJX4_PART1_TAC;
      ASM_CASES_TAC `k0 = 0` THENL [REJX4_NOLOOP_TAC; REJX4_LOOP_TAC]];
    REJX4_PART3_TAC]);;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  PREJ4_SAFE_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_rej_uniform_x4_sampled` REJX4_A2 THEN CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_rej_uniform_x4_after_mlk_rej_uniform_c_4` REJX4_A1 THEN CONJ_TAC THENL
     [PREJ4_SAFE_PART1_TAC;
      ASM_CASES_TAC `k0 = 0` THENL
       [PREJ4_SAFE_NOLOOP_TAC; PREJ4_SAFE_LOOP_TAC]];
    PREJ4_SAFE_PART3_TAC]);;
