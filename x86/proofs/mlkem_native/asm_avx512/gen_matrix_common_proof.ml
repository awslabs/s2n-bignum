(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/asm_avx512/gen_matrix_common_spec.ml";;

let GM_ZERO_COUNTER = prove
 (GM_ZERO_COUNTER_STMT,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV)));;

let GM_ZERO_END = prove
 (GM_ZERO_END_STMT,
  REWRITE_TAC[SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ENSURES_WHILE_UP2_TAC `6` `pc + mlkem_gen_matrix_zeroloop`
   (gm_pc_tm(gm_pc "zeroloop" 30))
   `\i s. read RDI s = word_add stackpointer (word(128 * i)) /\
          read RCX s = word(6 - i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    X86_SIM_TAC MLKEM_GEN_MATRIX_AVX512_EXEC (1--3) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0];
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    X86_SIM_TAC MLKEM_GEN_MATRIX_AVX512_EXEC (1--7) THEN
    ASM_SIMP_TAC[GM_ZERO_COUNTER] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; CONV_TAC WORD_RULE];
    X86_SIM_TAC MLKEM_GEN_MATRIX_AVX512_EXEC [1]]);;

let MLKEM_GEN_MATRIX_AVX512_SAMPLEPOLY = prove
 (MLKEM_GEN_MATRIX_AVX512_SAMPLEPOLY_STMT,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MLKEM_REJ_BLOCKS) THEN
  SUBGOAL_THEN `aligned 32 (word_add a (word(512 * (idx + l))):int64)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `512 * n = 32 * (16 * n)`] THEN
    ASM_SIMP_TAC[ALIGNED_BLOCK];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val(word l:int64) = l /\
    val(word_mul (word l) (word 504):int64) = 504 * l /\
    val(word_mul (word l) (word 200):int64) = 200 * l /\
    val(word_shl (word_add (word idx) (word l)) 9:int64) = 512 * (idx + l)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM WORD_MUL; GSYM WORD_ADD; WORD_SHL_WORD; VAL_WORD;
                DIMINDEX_64] THEN
    REPEAT CONJ_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o lhand o snd) THEN
    (ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN ARITH_TAC]);
    ALL_TAC] THEN

  (*** The addresses of the polynomial, buffer and lane as stated ***)

  let NORM_TAC =
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ASSUME `val(word l:int64) = l`;
      ASSUME `val(word_mul (word l) (word 504):int64) = 504 * l`;
      ASSUME `val(word_mul (word l) (word 200):int64) = 200 * l`;
      ASSUME `val(word_shl (word_add (word idx) (word l)) 9:int64) =
              512 * (idx + l)`]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [WORD_RULE
       `word_add (word_add (x:int64) (word 40)) (word (504 * l + 800)) =
        word_add x (word(840 + 504 * l))`;
      WORD_RULE
       `word_add (word_add (x:int64) (word 40)) (word (200 * l)) =
        word_add x (word(40 + 200 * l))`]) in

  (*** The exit with the 256 entries of m blocks, and mlkem_unpack ***)

  let EXIT_TAC m =
    SUBGOAL_THEN (subst [m,`m:num`] `LENGTH(mlkem_rej_out b m) = 256`)
    ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_MLKEM_REJ_OUT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ASSUME (subst [m,`m:num`] `LENGTH(mlkem_rej_out b m) = 256`);
      ARITH_RULE `2 * 256 = 512`]) THEN
    X86_STEPS_TAC MLKEM_GEN_MATRIX_AVX512_EXEC (1--6) THEN NORM_TAC THEN
    X86_SUBROUTINE_SIM_TAC
     (mlkem_native2_avx512_image_mc,MLKEM_GEN_MATRIX_AVX512_EXEC,
      layout "mlkem_unpack",mlkem_unpack_mc,MLKEM_UNPACK_SAMPLE_NTT)
     ([`read RDI s`; `b:byte list`; m; `pc + mlkem_unpack`] @
      return_args) 7 THEN
    ENSURES_FINAL_STATE_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]) THEN
    ASM_REWRITE_TAC[] in

  (*** The first call, on the three blocks in the buffer ***)

  ENSURES_SEQUENCE_TAC (gm_pc_tm(gm_pc "rejloop" 46)) (samplepoly_inv `3`) THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_GEN_MATRIX_AVX512_EXEC (1--9) THEN
    NORM_TAC THEN
    X86_SUBROUTINE_SIM_TAC
     (mlkem_native2_avx512_image_mc,MLKEM_GEN_MATRIX_AVX512_EXEC,
      layout "mlkem_rej_uniform_alt_VARIABLE_TIME",mlkem_rej_uniform_alt_mc,
      MLKEM_REJ_UNIFORM_BUF_OUT)
     ([`read RDI s`; `read RDX s`; `read R8 s`; `b:byte list`;
       `pc + mlkem_rej_uniform_alt_VARIABLE_TIME`] @ return_args) 10 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `N = mlkem_rej_blocks b - 3` THEN
  SUBGOAL_THEN `mlkem_rej_blocks b = 3 + N` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `256 <= CARD {j | j < 112 * (3 + N) /\
                     mlkem_xof_field (shake128 b) j < 3329}`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `mlkem_rej_blocks b = 3 + N`
                            then SUBST1_TAC(SYM th) THEN ASSUME_TAC th
                            else NO_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `N = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN EXIT_TAC `3`;
    ALL_TAC] THEN

  (*** Otherwise the loop over the further blocks ***)

  ENSURES_WHILE_UP_TAC `N:num` (gm_pc_tm(gm_pc "rejloop" 54))
   (gm_pc_tm(gm_pc "rejloop" 46))
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
    X86_STEPS_TAC MLKEM_GEN_MATRIX_AVX512_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The body: another block from the lane, and its fields ***)

    X_GEN_TAC `t:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `nonoverlapping (word_add a (word(512 * (idx + l))),
                      2 * LENGTH(mlkem_rej_out b (3 + t)))
                     (stackpointer:int64,3072)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC NONOVERLAPPING_SHORTER THEN EXISTS_TAC `512` THEN
      REWRITE_TAC[ARITH_RULE `2 * l <= 512 <=> l <= 256`;
                  LENGTH_MLKEM_REJ_OUT_LE] THEN
      ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
      ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_GEN_MATRIX_AVX512_EXEC (1--5) THEN NORM_TAC THEN
    TO_WBYTES_TAC `word_add stackpointer (word(40 + 200 * l)):int64` 5 THEN
    RC_TAC `c:int64` 5 THEN
    X86_SUBROUTINE_SIM_TAC
     (mlkem_native2_avx512_image_mc,MLKEM_GEN_MATRIX_AVX512_EXEC,0,
      mlkem_native2_avx512_image_mc,
      SHA3_KECCAK_F1600_AVX512_IMAGE_CORRECT_F1600)
     ([`read RDI s`; `read RSI s`; `keccak_squeeze (3 + t) (A:1600 word)`;
       `pc:num`] @ return_args) 6 THEN
    FROM_WBYTES_TAC 6 THEN
    X86_STEPS_TAC MLKEM_GEN_MATRIX_AVX512_EXEC (7--15) THEN NORM_TAC THEN
    SUBGOAL_THEN
     `read (memory :> bytes(word_add stackpointer (word(40 + 200 * l)),168))
           s15 =
      num_of_bytelist(list_of_seq (\j. shake128 b (168 * (3 + t) + j)) 168)`
    ASSUME_TAC THENL
     [MP_TAC(SPECL [`word_add stackpointer (word(40 + 200 * l)):int64`;
                    `200`; `168`;
                    `val(keccak_f1600(keccak_squeeze (3 + t) (A:1600 word)))`;
                    `s15:x86state`] READ_MEMORY_BYTES_PREFIX) THEN
      ASM_REWRITE_TAC[ARITH_RULE `168 <= 200`] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ARITH_RULE `(3 + t) + 1 = SUC(3 + t)`; keccak_squeeze] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    X86_SUBROUTINE_SIM_TAC
     (mlkem_native2_avx512_image_mc,MLKEM_GEN_MATRIX_AVX512_EXEC,
      layout "mlkem_rej_uniform_alt_VARIABLE_TIME",mlkem_rej_uniform_alt_mc,
      MLKEM_REJ_UNIFORM_BLOCK_OUT)
     ([`read RDI s`; `read RDX s`; `read R8 s`; `b:byte list`; `3 + t`;
       `pc + mlkem_rej_uniform_alt_VARIABLE_TIME`] @ return_args) 16 THEN
    X86_STEPS_TAC MLKEM_GEN_MATRIX_AVX512_EXEC [17] THEN
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
    X86_STEPS_TAC MLKEM_GEN_MATRIX_AVX512_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The exit, with the 256 coefficients ***)

    EXIT_TAC `3 + N`]);;

let GM_ABSORB_FULL_0_6 = prove
 (GM_ABSORB_FULL_0_6_STMT,
  GM_ABSORB_FULL_PROOF_TAC 0 6);;

let GM_ABSORB_FULL_1_6 = prove
 (GM_ABSORB_FULL_1_6_STMT,
  GM_ABSORB_FULL_PROOF_TAC 1 6);;

let GM_ABSORB_FULL_1_31 = prove
 (GM_ABSORB_FULL_1_31_STMT,
  GM_ABSORB_FULL_PROOF_TAC 1 31);;

let GM_ABSORB_LAST_0_120_6 = prove
 (GM_ABSORB_LAST_0_120_6_STMT,
  GM_ABSORB_LAST_PROOF_TAC 0 120 6);;

let GM_ABSORB_LAST_0_96_6 = prove
 (GM_ABSORB_LAST_0_96_6_STMT,
  GM_ABSORB_LAST_PROOF_TAC 0 96 6);;

let GM_ABSORB_LAST_0_72_6 = prove
 (GM_ABSORB_LAST_0_72_6_STMT,
  GM_ABSORB_LAST_PROOF_TAC 0 72 6);;

let GM_ABSORB_LAST_1_120_6 = prove
 (GM_ABSORB_LAST_1_120_6_STMT,
  GM_ABSORB_LAST_PROOF_TAC 1 120 6);;

let GM_ABSORB_LAST_1_96_6 = prove
 (GM_ABSORB_LAST_1_96_6_STMT,
  GM_ABSORB_LAST_PROOF_TAC 1 96 6);;

let GM_ABSORB_LAST_1_72_6 = prove
 (GM_ABSORB_LAST_1_72_6_STMT,
  GM_ABSORB_LAST_PROOF_TAC 1 72 6);;

let GM_ABSORB_LAST_1_120_31 = prove
 (GM_ABSORB_LAST_1_120_31_STMT,
  GM_ABSORB_LAST_PROOF_TAC 1 120 31);;

let GM_ABSORB_LAST_1_32_31 = prove
 (GM_ABSORB_LAST_1_32_31_STMT,
  GM_ABSORB_LAST_PROOF_TAC 1 32 31);;

let GM_ABSORB_LAST_1_104_31 = prove
 (GM_ABSORB_LAST_1_104_31_STMT,
  GM_ABSORB_LAST_PROOF_TAC 1 104 31);;
