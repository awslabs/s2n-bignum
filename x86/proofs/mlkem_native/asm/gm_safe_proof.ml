(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/asm/gm_safe_spec.ml";;

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

let MLKEM_UNPACK_NOIBT_SUBROUTINE_SAFE_FRAMED = time prove
 (MLKEM_UNPACK_NOIBT_SUBROUTINE_SAFE_FRAMED_STMT,
  X86_PROMOTE_RETURN_NOSTACK_TAC mlkem_unpack_tmc MLKEM_UNPACK_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_GEN_MATRIX_SAMPLEPOLY_SAFE = prove
 (MLKEM_GEN_MATRIX_SAMPLEPOLY_SAFE_STMT,
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
  let REJ0_TAC =
    GM_SAFE_CALL_TAC gsp_vars "H_REJ0"
     (layout "mlkem_rej_uniform_alt_VARIABLE_TIME",mlkem_rej_uniform_alt_mc)
     ([`e:(uarch_event)list`; `read RDI s`; `read RDX s`; `read R8 s`;
       `b:byte list`; `pc + mlkem_rej_uniform_alt_VARIABLE_TIME`] @
      return_args) 10 in
  let UNPACK_TAC vars k =
    GM_SAFE_CALL_TAC vars "H_UNPACK" (layout "mlkem_unpack",mlkem_unpack_mc)
     ([`e:(uarch_event)list`; `read RDI s`; `pc + mlkem_unpack`] @
      return_args) k in
  ASSUME_CALLEE_TAILED_TAC MLKEM_REJ_UNIFORM_BUF_OUT_FULL "H_REJ0" THEN
  ASSUME_CALLEE_TAILED_TAC MLKEM_REJ_UNIFORM_BLOCK_OUT_FULL "H_REJ1" THEN
  ASSUME_CALLEE_TAILED_TAC SHA3_KECCAK_F1600_ALT2_IMAGE_FULL_F1600 "H_K1" THEN
  ASSUME_CALLEE_TAILED_TAC MLKEM_UNPACK_SUBROUTINE_SAFE_FRAMED "H_UNPACK" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(b:byte list) (a:int64) (c:int64) (idx:num) (l:num)
     (stackpointer:int64) (pc:num).
      if mlkem_rej_blocks b - 3 = 0
      then f_ev_skip b a c idx l stackpointer pc
      else APPEND (f_ev_exit b a c idx l stackpointer pc)
             (APPEND (ENUMERATEL (mlkem_rej_blocks b - 3)
                       (\i. f_ev_loop b a c idx l stackpointer pc i))
                     (f_ev_enter b a c idx l stackpointer pc))
      :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN REPEAT GEN_TAC THEN
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
  ASM_CASES_TAC `mlkem_rej_blocks b - 3 = 0` THEN ASM_REWRITE_TAC[] THENL
   [(*** No more blocks: the three in the buffer suffice ***)
    SUBGOAL_THEN `LENGTH(mlkem_rej_out b 3) = 256` ASSUME_TAC THENL
     [SUBGOAL_THEN `mlkem_rej_blocks b = 3` (SUBST1_TAC o SYM) THENL
       [ASM_ARITH_TAC; ASM_SIMP_TAC[LENGTH_MLKEM_REJ_OUT_BLOCKS]];
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--9) THEN
    NORM_TAC THEN REJ0_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [ASSUME `LENGTH(mlkem_rej_out b 3) = 256`]) THEN
    X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (11--16) THEN NORM_TAC THEN
    UNPACK_TAC gsp_vars 17 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FRESH_E2_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `mlkem_rej_blocks b - 3`
   (gm_pc_tm(gm_pc "rejloop" 54)) (gm_pc_tm(gm_pc "rejloop" 131))
   (mk_abs(`i:num`,samplepoly_inv `3 + i`)) THEN
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
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--9) THEN
    NORM_TAC THEN REJ0_TAC THEN
    X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (11--12) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ENUMERATEL; APPEND] THEN
    FRESH_E2_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The body: another block from the lane, its fields, the test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `nonoverlapping (word_add a (word(512 * (idx + l))),
                      2 * LENGTH(mlkem_rej_out b (3 + i)))
                     (stackpointer:int64,3072)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC NONOVERLAPPING_SHORTER THEN EXISTS_TAC `512` THEN
      REWRITE_TAC[ARITH_RULE `2 * l <= 512 <=> l <= 256`;
                  LENGTH_MLKEM_REJ_OUT_LE] THEN
      ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
      ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(LENGTH(mlkem_rej_out b ((3 + i) + 1)) < 256 <=>
       i + 1 < mlkem_rej_blocks b - 3) /\
      val(word(LENGTH(mlkem_rej_out b ((3 + i) + 1))):int64) =
      LENGTH(mlkem_rej_out b ((3 + i) + 1))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_CASES_TAC `i + 1 < mlkem_rej_blocks b - 3` THEN
        ASM_REWRITE_TAC[NOT_LT] THENL
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
    X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--5) THEN NORM_TAC THEN
    TO_WBYTES_TAC `word_add stackpointer (word(40 + 200 * l)):int64` 5 THEN
    RC_TAC `c:int64` 5 THEN
    GM_SAFE_CALL_TAC (gsp_vars @ [`i:num`]) "H_K1"
     (0,mlkem_native2_image_mc)
     ([`e:(uarch_event)list`; `read RDI s`; `read RSI s`;
       `keccak_squeeze (3 + i) (A:1600 word)`; `pc:num`] @ return_args) 6 THEN
    FROM_WBYTES_TAC 6 THEN
    X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (7--15) THEN NORM_TAC THEN
    SUBGOAL_THEN
     `read (memory :> bytes(word_add stackpointer (word(40 + 200 * l)),168))
           s15 =
      num_of_bytelist(list_of_seq (\j. shake128 b (168 * (3 + i) + j)) 168)`
    ASSUME_TAC THENL
     [MP_TAC(SPECL [`word_add stackpointer (word(40 + 200 * l)):int64`;
                    `200`; `168`;
                    `val(keccak_f1600(keccak_squeeze (3 + i)
                                       (A:1600 word)))`;
                    `s15:x86state`] READ_MEMORY_BYTES_PREFIX) THEN
      ASM_REWRITE_TAC[ARITH_RULE `168 <= 200`] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[ARITH_RULE `(3 + i) + 1 = SUC(3 + i)`; keccak_squeeze] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    GM_SAFE_CALL_TAC (gsp_vars @ [`i:num`]) "H_REJ1"
     (layout "mlkem_rej_uniform_alt_VARIABLE_TIME",mlkem_rej_uniform_alt_mc)
     ([`e:(uarch_event)list`; `read RDI s`; `read RDX s`; `read R8 s`;
       `b:byte list`; `3 + i`; `pc + mlkem_rej_uniform_alt_VARIABLE_TIME`] @
      return_args) 16 THEN
    X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (17--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `3 + i + 1 = (3 + i) + 1`] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[ARITH_RULE `(3 + i) + 1 = SUC(3 + i)`; keccak_squeeze] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM NOT_LT; COND_SWAP] THEN COND_CASES_TAC THEN
      REWRITE_TAC[];
      ALL_TAC] THEN
    (fun gl -> allowed_vars_e := `i:num` :: !allowed_vars_e; ALL_TAC gl) THEN
    REWRITE_TAC[GSYM ADD1; ENUMERATEL] THEN
    FRESH_E2_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The exit, with the 256 coefficients, and mlkem_unpack ***)

    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_GEN_MATRIX_EXEC (1--4) THEN NORM_TAC THEN
    UNPACK_TAC gsp_vars 5 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FRESH_E2_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC]);;

let GM_ZERO_END_SAFE = prove
 (GM_ZERO_END_SAFE_STMT,
  REWRITE_TAC[SOME_FLAGS] THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(stackpointer:int64) (pc:num).
      APPEND (f_ev_epil stackpointer pc)
             (APPEND (ENUMERATEL 6 (\i. f_ev_loop stackpointer pc i))
                     (f_ev_prol stackpointer pc)) :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `pc:num`] THEN
  DISCH_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `6` `pc + mlkem_gen_matrix_zeroloop`
   (gm_pc_tm(gm_pc "zeroloop" 30))
   `\i s. read RDI s = word_add stackpointer (word(128 * i)) /\
          read RCX s = word(6 - i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_GEN_MATRIX_EXEC (1--3) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_GEN_MATRIX_EXEC (1--7) THEN
    ASM_SIMP_TAC[GM_ZERO_COUNTER] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false MLKEM_GEN_MATRIX_EXEC [1] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let gm_absorb_full_safe_ths =
  map (fun (j,ds) ->
         (j,ds),time prove(gm_absorb_full_safe_tm j ds,
                           GM_ABSORB_FULL_SAFE_PROOF_TAC))
      [1,6; 1,31];;

let gm_absorb_last_safe_ths =
  map (fun (j,t,ds) ->
         (j,t,ds),time prove(gm_absorb_last_safe_tm j t ds,
                             GM_ABSORB_LAST_SAFE_PROOF_TAC t))
      [1,120,6; 1,96,6; 1,72,6; 1,120,31; 1,32,31; 1,104,31];;

let gm_absorb_full_full_ths =
  map (fun (j,ds) ->
         (j,ds),GM_BLOCK_RULE(time prove(gm_absorb_full_full_tm j ds,
                                         GM_ABSORB_FULL_FULL_PROOF_TAC j ds)))
      [0,6];;

let gm_absorb_last_full_ths =
  map (fun (j,t,ds) ->
         (j,t,ds),
         GM_BLOCK_RULE(time prove(gm_absorb_last_full_tm j t ds,
                                  GM_ABSORB_LAST_FULL_PROOF_TAC j t ds)))
      [0,120,6; 0,96,6; 0,72,6];;
