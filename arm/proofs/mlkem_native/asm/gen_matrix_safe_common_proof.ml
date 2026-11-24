(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/asm/gen_matrix_safe_common_spec.ml";;

let MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_FULL_BYTES = prove
 (MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_FULL_BYTES_STMT,
  X_CHOOSE_TAC `f:int64->int64->int64->int64->int64->(12 word)list->num->
                  int64->int64->(uarch_event)list`
    MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_FULL THEN
  EXISTS_TAC `f:int64->int64->int64->int64->int64->(12 word)list->num->
                int64->int64->(uarch_event)list` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `res:int64`; `n:int64`; `buf:int64`;
    `buflen:int64`; `table:int64`; `curlist:int16 list`;
    `inlist:(12 word)list`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPECL [`table:int64`; `4096`; `4096`; `mlkem_rej_uniform_table`]
    (INST_TYPE [`:8`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  REWRITE_TAC[DIMINDEX_8; LENGTH_MLKEM_REJ_UNIFORM_TABLE] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`buf:int64`; `LENGTH(inlist:(12 word)list)`;
                 `val(buflen:int64)`; `inlist:(12 word)list`]
    (INST_TYPE [`:12`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  ASM_REWRITE_TAC[DIMINDEX_CONV `dimindex(:12)`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`res:int64`; `val(n:int64)`; `2 * val(n:int64)`;
                 `curlist:int16 list`]
    (INST_TYPE [`:16`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH_RULE `16 * n = 8 * 2 * n`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN rej_full_post_tac);;

let MLKEM_REJ_UNIFORM_BUF_OUT_FULL = prove
 (MLKEM_REJ_UNIFORM_BUF_OUT_FULL_STMT,
  X_CHOOSE_TAC `f:int64->int64->int64->int64->int64->(12 word)list->num->
                  int64->int64->(uarch_event)list`
    MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_FULL_BYTES THEN
  EXISTS_TAC
   `\(res:int64) (buf:int64) (table:int64) (b:byte list) (pc:num)
     (sp:int64) (ra:int64).
      (f:int64->int64->int64->int64->int64->(12 word)list->num->
          int64->int64->(uarch_event)list)
       res (word 0) buf (word 504) table
       (wordlist_of_num 336
          (num_of_bytelist(list_of_seq (shake128 b) 504))) pc sp ra` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ISPECL
   [`e:(uarch_event)list`; `res:int64`; `word 0:int64`; `buf:int64`;
    `word 504:int64`; `table:int64`; `[]:int16 list`;
    `wordlist_of_num 336
       (num_of_bytelist(list_of_seq (shake128 b) 504)):(12 word)list`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[LENGTH_WORDLIST_OF_NUM; LENGTH] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[NUM_OF_WORDLIST_OF_NUM_BYTES; LENGTH_LIST_OF_SEQ;
               ARITH_RULE `8 * 504 = 12 * 336`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; num_of_wordlist] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; GSYM MLKEM_REJ_OUT_BUF]);;

let MLKEM_REJ_UNIFORM_BLOCK_OUT_FULL = prove
 (MLKEM_REJ_UNIFORM_BLOCK_OUT_FULL_STMT,
  X_CHOOSE_TAC `f:int64->int64->int64->int64->int64->(12 word)list->num->
                  int64->int64->(uarch_event)list`
    MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_FULL_BYTES THEN
  EXISTS_TAC
   `\(res:int64) (buf:int64) (table:int64) (b:byte list) (m:num) (pc:num)
     (sp:int64) (ra:int64).
      (f:int64->int64->int64->int64->int64->(12 word)list->num->
          int64->int64->(uarch_event)list)
       res (word(LENGTH(mlkem_rej_out b m))) buf (word 168) table
       (wordlist_of_num 112
          (num_of_bytelist
            (list_of_seq (\j. shake128 b (168 * m + j)) 168))) pc sp ra` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o ISPECL
   [`e:(uarch_event)list`; `res:int64`;
    `word(LENGTH(mlkem_rej_out b m)):int64`; `buf:int64`;
    `word 168:int64`; `table:int64`; `mlkem_rej_out b m`;
    `wordlist_of_num 112
       (num_of_bytelist(list_of_seq (\j. shake128 b (168 * m + j)) 168)):
     (12 word)list`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`]) THEN
  SUBGOAL_THEN `val(word(LENGTH(mlkem_rej_out b m)):int64) =
                LENGTH(mlkem_rej_out b m)` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(SPECL [`b:byte list`; `m:num`] LENGTH_MLKEM_REJ_OUT_LE) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LENGTH_WORDLIST_OF_NUM; LENGTH_MLKEM_REJ_OUT_LE] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[NUM_OF_WORDLIST_OF_NUM_BYTES; LENGTH_LIST_OF_SEQ;
               ARITH_RULE `8 * 168 = 12 * 112`] THEN
  REWRITE_TAC[MLKEM_REJ_OUT_BLOCK]);;

let MLKEM_GEN_MATRIX_SAMPLEPOLY_SAFE = prove
 (MLKEM_GEN_MATRIX_SAMPLEPOLY_SAFE_STMT,
  let sp_inv m = vsubst [`ei:num`,`e:num`] (samplepoly_inv m) in
  let NORM_TAC =
    RULE_ASSUM_TAC(REWRITE_RULE
     [ASSUME `val(word l:int64) = l`; WORD_ADD_0;
      ASSUME `word_add (word_add stackpointer (word 128))
                       (word_add (word (0 + l * 504)) (word 896)):int64 =
              word_add stackpointer (word(1024 + 504 * l))`;
      ASSUME `word_add (word_add stackpointer (word 128))
                       (word_add (word (0 + l * 200)) (word 96)):int64 =
              word_add stackpointer (word(224 + 200 * l))`;
      ASSUME `word_shl (word ei:int64) 9 = word(512 * ei)`]) in
  let REJ0_TAC =
    GM_SAFE_CALL_TAC gsp_vars "H_REJ0"
     (layout "mlkem_rej_uniform_alt_VARIABLE_TIME",mlkem_rej_uniform_alt_mc)
     [`e:(uarch_event)list`; `read X0 s`; `read X2 s`; `read X4 s`;
      `b:byte list`; `pc + mlkem_rej_uniform_alt_VARIABLE_TIME`;
      `read SP s`; `read X30 s`] 10 in
  ASSUME_CALLEE_TAILED_TAC MLKEM_REJ_UNIFORM_BUF_OUT_FULL "H_REJ0" THEN
  ASSUME_CALLEE_TAILED_TAC MLKEM_REJ_UNIFORM_BLOCK_OUT_FULL "H_REJ1" THEN
  ASSUME_CALLEE_TAILED_TAC SHA3_KECCAK_F1600_SUBROUTINE_FULL_F1600
    "H_K1" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(b:byte list) (a:int64) (c:int64) (l:num) (ei:num) (stackpointer:int64)
     (pc:num).
      if mlkem_rej_blocks b - 3 = 0
      then f_ev_skip b a c l ei stackpointer pc
      else APPEND (f_ev_exit b a c l ei stackpointer pc)
             (APPEND (ENUMERATEL (mlkem_rej_blocks b - 3)
                       (\i. f_ev_loop b a c l ei stackpointer pc i))
                     (f_ev_enter b a c l ei stackpointer pc))
      :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN REPEAT GEN_TAC THEN
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
    word_shl (word ei:int64) 9 = word(512 * ei)`
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
  ASM_CASES_TAC `mlkem_rej_blocks b - 3 = 0` THEN ASM_REWRITE_TAC[] THENL
   [(*** No more blocks: the three in the buffer suffice ***)
    SUBGOAL_THEN `LENGTH(mlkem_rej_out b 3) = 256` ASSUME_TAC THENL
     [SUBGOAL_THEN `mlkem_rej_blocks b = 3` (SUBST1_TAC o SYM) THENL
       [ASM_ARITH_TAC; ASM_SIMP_TAC[LENGTH_MLKEM_REJ_OUT_BLOCKS]];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--9) THEN
    NORM_TAC THEN REJ0_TAC THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (11--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `mlkem_rej_blocks b - 3`
   (gm_pc_tm(gm_pc "rejloop" 48)) (gm_pc_tm(gm_pc "rejloop" 116))
   (mk_abs(`i:num`,sp_inv `3 + i`)) THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** The buffer, and the test the first time ***)

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
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--9) THEN
    NORM_TAC THEN REJ0_TAC THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (11--12) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ENUMERATEL; APPEND; GSYM NOT_LT] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The body: another block from the lane, its fields, the test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `nonoverlapping (word_add a (word(512 * ei)),
                      2 * LENGTH(mlkem_rej_out b (3 + i)))
                     (stackpointer:int64,3216)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC NONOVERLAPPING_SHORTER THEN EXISTS_TAC `512` THEN
      REWRITE_TAC[ARITH_RULE `2 * l <= 512 <=> l <= 256`;
                  LENGTH_MLKEM_REJ_OUT_LE] THEN
      ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
      ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(256 <= LENGTH(mlkem_rej_out b ((3 + i) + 1)) <=>
       ~(i + 1 < mlkem_rej_blocks b - 3)) /\
      val(word(LENGTH(mlkem_rej_out b ((3 + i) + 1))):int64) =
      LENGTH(mlkem_rej_out b ((3 + i) + 1))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_CASES_TAC `i + 1 < mlkem_rej_blocks b - 3` THEN
        ASM_REWRITE_TAC[NOT_LE] THENL
         [MATCH_MP_TAC LENGTH_MLKEM_REJ_OUT_LT THEN ASM_REWRITE_TAC[] THEN
          ASM_ARITH_TAC;
          SUBGOAL_THEN `(3 + i) + 1 = mlkem_rej_blocks b` SUBST1_TAC THENL
           [ASM_ARITH_TAC; ASM_SIMP_TAC[LENGTH_MLKEM_REJ_OUT_BLOCKS]] THEN
          ARITH_TAC];
        REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
        MP_TAC(SPECL [`b:byte list`; `(3 + i) + 1`]
                     LENGTH_MLKEM_REJ_OUT_LE) THEN
        ARITH_TAC];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--7) THEN NORM_TAC THEN
    TO_WBYTES_TAC `word_add stackpointer (word(224 + 200 * l)):int64` 7 THEN
    RC_TAC `c:int64` 7 THEN
    GM_SAFE_CALL_TAC (gsp_vars @ [`i:num`]) "H_K1"
     (layout "sha3_keccak_f1600",sha3_keccak_f1600_mc)
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`;
      `keccak_squeeze (3 + i) (A:1600 word)`;
      `pc + sha3_keccak_f1600`; `read SP s`; `read X30 s`] 8 THEN
    FROM_WBYTES_TAC 8 THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (9--17) THEN NORM_TAC THEN
    SUBGOAL_THEN
     `read (memory :> bytes(word_add stackpointer (word(224 + 200 * l)),
                            168)) s17 =
      num_of_bytelist(list_of_seq (\j. shake128 b (168 * (3 + i) + j)) 168)`
    ASSUME_TAC THENL
     [MP_TAC(SPECL [`word_add stackpointer (word(224 + 200 * l)):int64`;
                    `200`; `168`;
                    `val(keccak_f1600(keccak_squeeze (3 + i)
                                       (A:1600 word)))`;
                    `s17:armstate`] READ_MEMORY_BYTES_PREFIX) THEN
      ASM_REWRITE_TAC[ARITH_RULE `168 <= 200`] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ARITH_RULE `(3 + i) + 1 = SUC(3 + i)`; keccak_squeeze] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    GM_SAFE_CALL_TAC (gsp_vars @ [`i:num`]) "H_REJ1"
     (layout "mlkem_rej_uniform_alt_VARIABLE_TIME",mlkem_rej_uniform_alt_mc)
     [`e:(uarch_event)list`; `read X0 s`; `read X2 s`; `read X4 s`;
      `b:byte list`; `3 + i`; `pc + mlkem_rej_uniform_alt_VARIABLE_TIME`;
      `read SP s`; `read X30 s`] 18 THEN
    ARM_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (19--21) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `3 + i + 1 = (3 + i) + 1`] THEN
    ASM_REWRITE_TAC[COND_SWAP] THEN
    ASM_REWRITE_TAC[ARITH_RULE `(3 + i) + 1 = SUC(3 + i)`; keccak_squeeze] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN COND_CASES_TAC THEN
      REWRITE_TAC[];
      ALL_TAC] THEN
    (fun gl -> allowed_vars_e := `i:num` :: !allowed_vars_e; ALL_TAC gl) THEN
    REWRITE_TAC[GSYM ADD1; ENUMERATEL] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The exit ***)

    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_GEN_MATRIX_EXEC [] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let GM_ZERO_END_SAFE = prove
 (GM_ZERO_END_SAFE_STMT,
  GM_ZERO_SAFE_TAC MLKEM_GEN_MATRIX_EXEC (gm_pc "end" 0) (gm_pc "end" 20)
    96 800);;

let GM_ABSORB_FULL_SAFE_0_6 = prove
 (GM_ABSORB_FULL_SAFE_0_6_STMT,
  GM_ABSORB_FULL_SAFE_PROOF_TAC);;

let GM_ABSORB_FULL_SAFE_1_6 = prove
 (GM_ABSORB_FULL_SAFE_1_6_STMT,
  GM_ABSORB_FULL_SAFE_PROOF_TAC);;

let GM_ABSORB_FULL_SAFE_1_31 = prove
 (GM_ABSORB_FULL_SAFE_1_31_STMT,
  GM_ABSORB_FULL_SAFE_PROOF_TAC);;

let GM_ABSORB_LAST_SAFE_0_120_6 = prove
 (GM_ABSORB_LAST_SAFE_0_120_6_STMT,
  GM_ABSORB_LAST_SAFE_PROOF_TAC 120);;

let GM_ABSORB_LAST_SAFE_1_120_31 = prove
 (GM_ABSORB_LAST_SAFE_1_120_31_STMT,
  GM_ABSORB_LAST_SAFE_PROOF_TAC 120);;

let GM_ABSORB_LAST_SAFE_0_96_6 = prove
 (GM_ABSORB_LAST_SAFE_0_96_6_STMT,
  GM_ABSORB_LAST_SAFE_PROOF_TAC 96);;

let GM_ABSORB_LAST_SAFE_1_96_6 = prove
 (GM_ABSORB_LAST_SAFE_1_96_6_STMT,
  GM_ABSORB_LAST_SAFE_PROOF_TAC 96);;

let GM_ABSORB_LAST_SAFE_1_32_31 = prove
 (GM_ABSORB_LAST_SAFE_1_32_31_STMT,
  GM_ABSORB_LAST_SAFE_PROOF_TAC 32);;

let GM_ABSORB_LAST_SAFE_0_72_6 = prove
 (GM_ABSORB_LAST_SAFE_0_72_6_STMT,
  GM_ABSORB_LAST_SAFE_PROOF_TAC 72);;

let GM_ABSORB_LAST_SAFE_1_72_6 = prove
 (GM_ABSORB_LAST_SAFE_1_72_6_STMT,
  GM_ABSORB_LAST_SAFE_PROOF_TAC 72);;

let GM_ABSORB_LAST_SAFE_1_104_31 = prove
 (GM_ABSORB_LAST_SAFE_1_104_31_STMT,
  GM_ABSORB_LAST_SAFE_PROOF_TAC 104);;

let GM_ABSORB_FULL_FULL_0_6 = prove
 (GM_ABSORB_FULL_FULL_0_6_STMT,
  GM_ABSORB_FULL_FULL_PROOF_TAC 0 6);;

let GM_ABSORB_LAST_FULL_0_120_6 = prove
 (GM_ABSORB_LAST_FULL_0_120_6_STMT,
  GM_ABSORB_LAST_FULL_PROOF_TAC 0 120 6);;

let GM_ABSORB_LAST_FULL_0_96_6 = prove
 (GM_ABSORB_LAST_FULL_0_96_6_STMT,
  GM_ABSORB_LAST_FULL_PROOF_TAC 0 96 6);;

let GM_ABSORB_LAST_FULL_0_72_6 = prove
 (GM_ABSORB_LAST_FULL_0_72_6_STMT,
  GM_ABSORB_LAST_FULL_PROOF_TAC 0 72 6);;
