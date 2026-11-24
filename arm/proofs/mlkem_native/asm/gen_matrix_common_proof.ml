(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/asm/gen_matrix_common_spec.ml";;

(* The proofs run at the same time with the parallel backend of
   common/par.ml, and one after the other without it *)

let proof_futures =
 [prove_async
 (GM_ZERO_END_STMT,
  GM_ZERO_TAC MLKEM_GEN_MATRIX_EXEC (gm_pc "end" 0) (gm_pc "end" 20) 96 800);
  prove_async
 (MLKEM_GEN_MATRIX_SAMPLEPOLY_STMT,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MLKEM_REJ_BLOCKS) THEN
  SUBGOAL_THEN
   `val(word l:int64) = l /\
    word_add (word_add stackpointer (word 128))
             (word_add (word (0 + l * 504)) (word 896)):int64 =
    word_add stackpointer (word(1024 + 504 * l)) /\
    word_add (word_add stackpointer (word 128))
             (word_add (word (0 + l * 200)) (word 96)):int64 =
    word_add stackpointer (word(224 + 200 * l)) /\
    word_shl (word e:int64) 9 = word(512 * e)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      UNDISCH_TAC `l < 4` THEN ARITH_TAC;
      REWRITE_TAC[GSYM WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[GSYM WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[WORD_SHL_WORD] THEN AP_TERM_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  let NORM_TAC =
    RULE_ASSUM_TAC(REWRITE_RULE
     [ASSUME `val(word l:int64) = l`; WORD_ADD_0;
      ASSUME `word_add (word_add stackpointer (word 128))
                       (word_add (word (0 + l * 504)) (word 896)):int64 =
              word_add stackpointer (word(1024 + 504 * l))`;
      ASSUME `word_add (word_add stackpointer (word 128))
                       (word_add (word (0 + l * 200)) (word 96)):int64 =
              word_add stackpointer (word(224 + 200 * l))`;
      ASSUME `word_shl (word e:int64) 9 = word(512 * e)`]) in
  ENSURES_SEQUENCE_TAC (gm_pc_tm(gm_pc "rejloop" 40)) (samplepoly_inv `3`) THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--9) THEN
    NORM_TAC THEN
    ARM_SUBROUTINE_SIM_TAC
     (mlkem_native2_image_mc,MLKEM_GEN_MATRIX_EXEC,
      layout "mlkem_rej_uniform_alt_VARIABLE_TIME",mlkem_rej_uniform_alt_mc,
      MLKEM_REJ_UNIFORM_BUF_OUT)
     [`read X0 s`; `read X2 s`; `read X4 s`; `b:byte list`;
      `pc + mlkem_rej_uniform_alt_VARIABLE_TIME`; `read SP s`;
      `read X30 s`] 10 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `N = mlkem_rej_blocks b - 3` THEN
  SUBGOAL_THEN `mlkem_rej_blocks b = 3 + N` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `N = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
    SUBGOAL_THEN `LENGTH(mlkem_rej_out b 3) = 256` ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `mlkem_rej_blocks b = 3`)) THEN
      ASM_SIMP_TAC[LENGTH_MLKEM_REJ_OUT_BLOCKS];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(mlkem_rej_out b 3) = 256`]) THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SAMPLEPOLY_POST THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[ASSUME `LENGTH(mlkem_rej_out b 3) = 256`];
    ALL_TAC] THEN
  ENSURES_WHILE_UP_TAC `N:num` (gm_pc_tm(gm_pc "rejloop" 48))
   (gm_pc_tm(gm_pc "rejloop" 40))
   (mk_abs(`t:num`,samplepoly_inv `3 + t`)) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** The test, the first time ***)

    REWRITE_TAC[ADD_CLAUSES] THEN
    SUBGOAL_THEN `LENGTH(mlkem_rej_out b 3) < 256` ASSUME_TAC THENL
     [MATCH_MP_TAC LENGTH_MLKEM_REJ_OUT_LT THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `val(word(LENGTH(mlkem_rej_out b 3)):int64) =
                  LENGTH(mlkem_rej_out b 3)` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LT];

    (*** The body: another block from the lane, and its fields ***)

    X_GEN_TAC `t:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `nonoverlapping (word_add a (word(512 * e)),
                      2 * LENGTH(mlkem_rej_out b (3 + t)))
                     (stackpointer:int64,3216)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC NONOVERLAPPING_SHORTER THEN EXISTS_TAC `512` THEN
      REWRITE_TAC[ARITH_RULE `2 * l <= 512 <=> l <= 256`;
                  LENGTH_MLKEM_REJ_OUT_LE] THEN
      ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
      ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--7) THEN NORM_TAC THEN
    TO_WBYTES_TAC `word_add stackpointer (word(224 + 200 * l)):int64` 7 THEN
    RC_TAC `c:int64` 7 THEN
    ARM_SUBROUTINE_SIM_TAC
     (mlkem_native2_image_mc,MLKEM_GEN_MATRIX_EXEC,
      layout "sha3_keccak_f1600",sha3_keccak_f1600_mc,
      SHA3_KECCAK_F1600_SUBROUTINE_CORRECT_F1600)
     [`read X0 s`; `read X1 s`; `keccak_squeeze (3 + t) (A:1600 word)`;
      `pc + sha3_keccak_f1600`; `read SP s`; `read X30 s`] 8 THEN
    FROM_WBYTES_TAC 8 THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (9--17) THEN NORM_TAC THEN
    SUBGOAL_THEN
     `read (memory :> bytes(word_add stackpointer (word(224 + 200 * l)),
                            168)) s17 =
      num_of_bytelist(list_of_seq (\j. shake128 b (168 * (3 + t) + j)) 168)`
    ASSUME_TAC THENL
     [MP_TAC(SPECL [`word_add stackpointer (word(224 + 200 * l)):int64`;
                    `200`; `168`;
                    `val(keccak_f1600(keccak_squeeze (3 + t)
                                       (A:1600 word)))`;
                    `s17:armstate`] READ_MEMORY_BYTES_PREFIX) THEN
      ASM_REWRITE_TAC[ARITH_RULE `168 <= 200`] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ARITH_RULE `(3 + t) + 1 = SUC(3 + t)`; keccak_squeeze] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    ARM_SUBROUTINE_SIM_TAC
     (mlkem_native2_image_mc,MLKEM_GEN_MATRIX_EXEC,
      layout "mlkem_rej_uniform_alt_VARIABLE_TIME",mlkem_rej_uniform_alt_mc,
      MLKEM_REJ_UNIFORM_BLOCK_OUT)
     [`read X0 s`; `read X2 s`; `read X4 s`; `b:byte list`; `3 + t`;
      `pc + mlkem_rej_uniform_alt_VARIABLE_TIME`; `read SP s`;
      `read X30 s`] 18 THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC [19] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `3 + t + 1 = (3 + t) + 1`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `(3 + t) + 1 = SUC(3 + t)`; keccak_squeeze];

    (*** The test, the later times ***)

    X_GEN_TAC `t:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `LENGTH(mlkem_rej_out b (3 + t)) < 256` ASSUME_TAC THENL
     [MATCH_MP_TAC LENGTH_MLKEM_REJ_OUT_LT THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `val(word(LENGTH(mlkem_rej_out b (3 + t))):int64) =
                  LENGTH(mlkem_rej_out b (3 + t))` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[GSYM NOT_LT];

    (*** The exit, with the 256 coefficients ***)

    SUBGOAL_THEN `LENGTH(mlkem_rej_out b (3 + N)) = 256` ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `mlkem_rej_blocks b = 3 + N`)) THEN
      ASM_SIMP_TAC[LENGTH_MLKEM_REJ_OUT_BLOCKS];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ASSUME `LENGTH(mlkem_rej_out b (3 + N)) = 256`]) THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SAMPLEPOLY_POST THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[ASSUME `LENGTH(mlkem_rej_out b (3 + N)) = 256`]]);
  prove_async
 (GM_ABSORB_FULL_0_6_STMT,
 GM_ABSORB_FULL_PROOF_TAC 0 6);
  prove_async
 (GM_ABSORB_FULL_1_6_STMT,
 GM_ABSORB_FULL_PROOF_TAC 1 6);
  prove_async
 (GM_ABSORB_FULL_1_31_STMT,
 GM_ABSORB_FULL_PROOF_TAC 1 31);
  prove_async
 (GM_ABSORB_LAST_0_120_STMT,
 GM_ABSORB_LAST_PROOF_TAC 0 120 6);
  prove_async
 (GM_ABSORB_LAST_1_120_STMT,
 GM_ABSORB_LAST_PROOF_TAC 1 120 31);
  prove_async
 (GM_ABSORB_LAST_0_96_STMT,
 GM_ABSORB_LAST_PROOF_TAC 0 96 6);
  prove_async
 (GM_ABSORB_LAST_1_96_STMT,
 GM_ABSORB_LAST_PROOF_TAC 1 96 6);
  prove_async
 (GM_ABSORB_LAST_1_32_STMT,
 GM_ABSORB_LAST_PROOF_TAC 1 32 31);
  prove_async
 (GM_ABSORB_LAST_0_72_STMT,
 GM_ABSORB_LAST_PROOF_TAC 0 72 6);
  prove_async
 (GM_ABSORB_LAST_1_72_STMT,
 GM_ABSORB_LAST_PROOF_TAC 1 72 6);
  prove_async
 (GM_ABSORB_LAST_1_104_STMT,
 GM_ABSORB_LAST_PROOF_TAC 1 104 31)];;

let [GM_ZERO_END;
     MLKEM_GEN_MATRIX_SAMPLEPOLY;
     GM_ABSORB_FULL_0_6;
     GM_ABSORB_FULL_1_6;
     GM_ABSORB_FULL_1_31;
     GM_ABSORB_LAST_0_120;
     GM_ABSORB_LAST_1_120;
     GM_ABSORB_LAST_0_96;
     GM_ABSORB_LAST_1_96;
     GM_ABSORB_LAST_1_32;
     GM_ABSORB_LAST_0_72;
     GM_ABSORB_LAST_1_72;
     GM_ABSORB_LAST_1_104] =
  map par_await proof_futures;;
