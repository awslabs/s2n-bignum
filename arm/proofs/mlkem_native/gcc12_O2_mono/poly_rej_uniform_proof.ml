(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_rej_uniform_spec.ml";;


let REJ_SPONGE = prove
 (REJ_SPONGE_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[shake128] THEN
  MATCH_MP_TAC KECCAK_SPONGE_BLOCK THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let REJ_XOF_BLOCKS = prove
 (REJ_XOF_BLOCKS_STMT,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; list_of_seq; num_of_bytelist;
                NSUM_CLAUSES_NUMSEG_LT];
    ASM_REWRITE_TAC[ARITH_RULE `168 * SUC n = 168 * n + 168`;
                    NUM_OF_BYTELIST_LIST_OF_SEQ_ADD;
                    NSUM_CLAUSES_NUMSEG_LT]]);;

let REJ_SHAKE128_BLOCKS = prove
 (REJ_SHAKE128_BLOCKS_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[REJ_XOF_BLOCKS] THEN
  MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC REJ_SPONGE THEN
  REWRITE_TAC[LE_REFL]);;

let KECCAK_SQUEEZE_ADD = prove
 (KECCAK_SQUEEZE_ADD_STMT,
  INDUCT_TAC THEN ASM_REWRITE_TAC[keccak_squeeze; ADD_CLAUSES]);;

let REJ_NSUM_1 = prove
 (REJ_NSUM_1_STMT,
  REWRITE_TAC[num_CONV `1`; NSUM_CLAUSES_NUMSEG_LT; ADD_CLAUSES]);;

let REJ_WORDLIST_APPEND = prove
 (REJ_WORDLIST_APPEND_STMT,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD; REJ_WORDLIST_OF_NUM_ADD] THEN
  REWRITE_TAC[DIMINDEX_12] THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPEC `list_of_seq (f:num->byte) m` NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; GSYM(NUM_REDUCE_CONV `2 EXP 8`);
              GSYM EXP_MULT] THEN
  SPEC_TAC(`num_of_bytelist(list_of_seq (f:num->byte) m)`,`x:num`) THEN
  SPEC_TAC(`num_of_bytelist(list_of_seq (\i. (f:num->byte)(m + i)) 168)`,
           `y:num`) THEN
  REPEAT STRIP_TAC THEN BINOP_TAC THENL
   [GEN_REWRITE_TAC BINOP_CONV [GSYM WORDLIST_OF_NUM_MOD] THEN
    REWRITE_TAC[DIMINDEX_12] THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[ARITH_RULE `x + n * y:num = y * n + x`] THEN
    REWRITE_TAC[MOD_MULT_ADD];
    AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[ARITH_RULE `x + n * y:num = y * n + x`] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES]]);;

let REJ_FIELDS_SUC = prove
 (REJ_FIELDS_SUC_STMT,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `504 + 168 * (j + 1) = (504 + 168 * j) + 168`;
              ARITH_RULE `336 + 112 * (j + 1) = (336 + 112 * j) + 112`] THEN
  MATCH_MP_TAC REJ_WORDLIST_APPEND THEN ARITH_TAC);;

let REJ_FIELDS_PREFIX = prove
 (REJ_FIELDS_PREFIX_STMT,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [REWRITE_TAC[LE] THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `[]:(12 word)list` THEN REWRITE_TAC[APPEND_NIL];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[LE] THEN
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXISTS_TAC `[]:(12 word)list` THEN
      REWRITE_TAC[APPEND_NIL];
      FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_TAC `t:(12 word)list`) THEN
      REWRITE_TAC[ADD1; REJ_FIELDS_SUC] THEN
      ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN MESON_TAC[]]]);;

let REJ_COUNT_MONO = prove
 (REJ_COUNT_MONO_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(12 word)list` SUBST1_TAC o
             MATCH_MP(SPEC `f:num->byte` REJ_FIELDS_PREFIX)) THEN
  REWRITE_TAC[REJ_SAMPLE_APPEND; LENGTH_APPEND; LE_ADD]);;

let REJ_SAMPLE_FINAL = prove
 (REJ_SAMPLE_FINAL_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `t:(12 word)list` SUBST1_TAC o
    MATCH_MP(SPEC `f:num->byte` REJ_FIELDS_PREFIX))
   ASSUME_TAC) THEN
  REWRITE_TAC[REJ_SAMPLE_APPEND] THEN
  MATCH_MP_TAC SUB_LIST_APPEND_LEFT THEN ASM_REWRITE_TAC[]);;

let REJ_SAMPLE_SUC = prove
 (REJ_SAMPLE_SUC_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REJ_FIELDS_SUC; REJ_SAMPLE_APPEND] THEN
  ASM_SIMP_TAC[SUB_LIST_APPEND_RIGHT; SUB_LIST_REFL]);;

let REJ_WORDLIST_FROM_BYTES = prove
 (REJ_WORDLIST_FROM_BYTES_STMT,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[wordlist_from_memory; DIMINDEX_12] THEN
  SUBGOAL_THEN `(12 * n + 7) DIV 8 = m` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `7` THEN ASM_ARITH_TAC);;

let REJ_BYTES16_OF_WORDLIST = prove
 (REJ_BYTES16_OF_WORDLIST_STMT,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `n:num`; `2 * n`; `l:int16 list`; `s:armstate`]
         WORDLIST_FROM_MEMORY_EQ_ALT) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH_RULE `16 * n = 8 * 2 * n`] THEN
  DISCH_THEN SUBST1_TAC THEN SIMP_TAC[]);;

let REJ_WORDLIST_OF_BYTES16 = prove
 (REJ_WORDLIST_OF_BYTES16_STMT,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `LENGTH(l:int16 list)`; `2 * LENGTH(l:int16 list)`;
                 `l:int16 list`; `s:armstate`]
                WORDLIST_FROM_MEMORY_EQ_ALT) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH_RULE `16 * n = 8 * 2 * n`] THEN
  DISCH_THEN SUBST1_TAC THEN SIMP_TAC[]);;

let REJ_BYTES16_APPEND_N = prove
 (REJ_BYTES16_APPEND_N_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
   (fun th -> concl th = `LENGTH(l1:int16 list) = n`)) THEN
  REWRITE_TAC[GSYM LENGTH_APPEND] THEN
  MATCH_MP_TAC READ_BYTES16_APPEND THEN ASM_REWRITE_TAC[]);;

let REJ_HI_LEMMA = prove
 (REJ_HI_LEMMA_STMT,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word_zx(word c:int64):int32) = c` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[MOD_LT; ARITH_RULE
     `c < 4294967296 ==> c < 18446744073709551616`];
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
  ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC(TAUT `~a /\ ~b ==> ((a /\ c) <=> b)`) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC(INT_ARITH `x < &255 /\ &0 <= y ==> ~(x - &255:int = y)`) THEN
    REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN ASM_ARITH_TAC]);;

let REJ_ALIGNED_16_32 = prove
 (REJ_ALIGNED_16_32_STMT,
  CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`x:int64`; `4`] (CONJUNCT1 WORD_AND_MASK_WORD));
    MP_TAC(ISPECL [`x:int64`; `5`] (CONJUNCT1 WORD_AND_MASK_WORD))] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 16 < 16`; ARITH_RULE `x MOD 32 < 32`;
           ARITH_RULE `x < 16 ==> x < 2 EXP 64`;
           ARITH_RULE `x < 32 ==> x < 2 EXP 64`]);;

let READ_MEMORY_BYTES_EXTEND = prove
 (READ_MEMORY_BYTES_EXTEND_STMT,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MOD_MULT_MOD] THEN
  ARITH_TAC);;

let READ_MEMORY_BYTES128_OF_NUM = prove
 (READ_MEMORY_BYTES128_OF_NUM_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE
   `340282366920938463463374607431768211456 = 2 EXP (8 * 16)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES_OF_BYTES128 = prove
 (READ_MEMORY_BYTES_OF_BYTES128_STMT,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int128->num`) THEN
  REWRITE_TAC[VAL_READ_WBYTES; VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let READ_BYTES_FROM_CHUNKS128 = prove
 (READ_BYTES_FROM_CHUNKS128_STMT,
  INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; READ_COMPONENT_COMPOSE;
                READ_BYTES_TRIVIAL];
    FIRST_X_ASSUM(fun ih ->
      MAP_EVERY X_GEN_TAC [`a:int64`; `x:num`; `s:armstate`] THEN
      DISCH_TAC THEN
      MP_TAC(SPECL [`a:int64`; `x:num`; `s:armstate`] ih) THEN
      ANTS_TAC THENL
       [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]];
        DISCH_TAC]) THEN
    MP_TAC(SPECL [`a:int64`; `16 * n`; `16`; `x:num`; `s:armstate`]
            READ_MEMORY_BYTES_EXTEND) THEN
    REWRITE_TAC[ARITH_RULE `16 * SUC n = 16 * n + 16`;
                ARITH_RULE `128 * SUC n = 8 * (16 * n + 16)`] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[ARITH_RULE `8 * (16 * n) = 128 * n`];
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
        is_forall(concl th) && can (term_match [] `!k. k < SUC n ==> P`)
                                   (concl th))) THEN
      REWRITE_TAC[LT] THEN
      DISCH_THEN(MP_TAC o MATCH_MP READ_MEMORY_BYTES_OF_BYTES128) THEN
      REWRITE_TAC[ARITH_RULE `8 * 16 = 128`;
                  ARITH_RULE `8 * (16 * n) = 128 * n`; MOD_MOD_REFL]]]);;

let READ_MEMORY_BYTES64_OF_NUM = prove
 (READ_MEMORY_BYTES64_OF_NUM_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 EXP (8 * 8)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES_OF_BYTES64 = prove
 (READ_MEMORY_BYTES_OF_BYTES64_STMT,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[BYTES64_WBYTES; READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int64->num`) THEN
  REWRITE_TAC[VAL_READ_WBYTES; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let ZX_ZX_64_128 = prove
 (ZX_ZX_64_128_STMT, BITBLAST_TAC);;

let KSQ_SUC = prove
 (KSQ_SUC_STMT, REWRITE_TAC[GSYM ADD1; keccak_squeeze]);;

let NSUM_LT_STEP = prove
 (NSUM_LT_STEP_STMT, REWRITE_TAC[GSYM ADD1; NSUM_CLAUSES_NUMSEG_LT]);;

let GENMAT3_COPY168 = prove
 (GENMAT3_COPY168_STMT,
  MAP_EVERY X_GEN_TAC [`st:int64`; `q:int64`; `V:1600 word`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP_TAC `21` `pc + mlkem768_gen_matrix_loop3`
   `pc + mlkem768_gen_matrix_loop3_test`
   `\j s. read X0 s = word_add st (word(8 * j)) /\
          read X19 s = word_add q (word(8 * j)) /\
          read X20 s = st /\ read X22 s = word_add q (word 168) /\
          read (memory :> wbytes st) s = (V:1600 word) /\
          read (memory :> bytes(q,8 * j)) s =
          val (V:1600 word) MOD 2 EXP (8 * (8 * j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; READ_COMPONENT_COMPOSE;
                READ_BYTES_TRIVIAL; EXP; MOD_1];

    (*** The body: one 8-byte word ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `read (memory :> wbytes st) s0 = (V:1600 word)`)
             (concl th)
      then ASSUME_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600] th)
      else NO_TAC) THEN
    MP_TAC(SPECL [`st:int64`; `200`; `val(V:1600 word)`; `8 * i`;
                  `s0:armstate`] READ_MEMORY_BYTES64_OF_NUM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN
      CONV_TAC WORD_RULE;
      ASM_REWRITE_TAC[READ_MEMORY_WBYTES_1600];
      MP_TAC(SPECL [`q:int64`; `8 * i`; `8`; `val(V:1600 word)`;
                    `s2:armstate`] READ_MEMORY_BYTES_EXTEND) THEN
      REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`;
                  ARITH_RULE `8 * (8 * i + 8) = 8 * (8 * i) + 64`] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[ARITH_RULE `8 * 8 * i = 8 * (8 * i)`];
        FIRST_ASSUM(fun th ->
          if can (term_match [] `read (memory :> bytes64 (word_add q (word (8 * i)))) s2 = x`) (concl th)
          then MP_TAC(MATCH_MP READ_MEMORY_BYTES_OF_BYTES64
                       (REWRITE_RULE[ZX_ZX_64_128] th))
          else NO_TAC) THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[MOD_MOD_REFL; ARITH_RULE `8 * 8 * i = 8 * (8 * i)`]]];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit and the update of X22 ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (2--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]]);;

let GENMAT3_SQ3 = prove
 (GENMAT3_SQ3_STMT,
  MAP_EVERY X_GEN_TAC [`st:int64`; `buf:int64`; `S:1600 word`; `bp:int64`;
                       `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; ALL; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP2_TAC `3` `pc + mlkem768_gen_matrix_loop2`
   `pc + mlkem768_gen_matrix_loop2_exit`
   `\t s. read SP s = word_add bp (word 256) /\ read X20 s = st /\ read X21 s = buf /\
          read X22 s = word_add buf (word(168 * (t + 1))) /\
          read X23 s = word(3 - t) /\
          read (memory :> wbytes st) s = keccak_squeeze t (S:1600 word) /\
          read (memory :> bytes(buf,168 * t)) s =
          nsum {i | i < t}
           (\i. 2 EXP (8 * 168 * i) *
                val(keccak_squeeze (i + 1) (S:1600 word)) MOD 2 EXP (8 * 168))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0; WORD_ADD_0; keccak_squeeze;
                READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL;
                CONJUNCT1 NSUM_CLAUSES_NUMSEG_LT];

    (*** The body ***)

    X_GEN_TAC `t:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--2) THEN
    LOCAL_GM3_PERMUTE_TAC
     [`read X0 s`; `keccak_squeeze t (S:1600 word)`; `pc:num`; `read SP s`;
      `read X30 s`] 3 THEN
    SUBGOAL_THEN
     `word_add buf (word (168 * (t + 1))):int64 =
      word_add (word_add buf (word (168 * t))) (word 168)`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `168 * (t + 1) = 168 * t + 168`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    LOCAL_GM3_COPY168_TAC
     [`st:int64`; `word_add buf (word(168 * t)):int64`;
      `keccak_f1600 (keccak_squeeze t (S:1600 word))`; `pc:num`] 4 THENL
     [CONV_TAC WORD_RULE; ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (5--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `t < 3` THEN SPEC_TAC(`t:num`,`t:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[ARITH_EQ];
      REWRITE_TAC[ARITH_RULE `168 * t + 336 = 168 * ((t + 1) + 1)`];
      UNDISCH_TAC `t < 3` THEN SPEC_TAC(`t:num`,`t:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[ARITH_EQ];
      REWRITE_TAC[KSQ_SUC];
      REWRITE_TAC[NSUM_LT_STEP; ARITH_RULE `168 * (t + 1) = 168 * t + 168`;
                  READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[KSQ_SUC]] ;

    (*** The exit ***)

    ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]]);;

let GENMAT3_COPY168U = prove
 (GENMAT3_COPY168U_STMT,
  MAP_EVERY X_GEN_TAC [`st:int64`; `buf:int64`; `V:1600 word`; `c19:int64`;
                       `y:int64`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> wbytes st) s0 = (V:1600 word)`)
           (concl th)
    then ASSUME_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600] th)
    else NO_TAC) THEN
  MAP_EVERY (fun k ->
    MP_TAC(SPECL [`st:int64`; `200`; `val(V:1600 word)`;
                  mk_small_numeral(16 * k); `s0:armstate`]
                 READ_MEMORY_BYTES128_OF_NUM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[WORD_ADD_0])) (0--9) THEN
  MP_TAC(SPECL [`st:int64`; `200`; `val(V:1600 word)`; `160`; `s0:armstate`]
               READ_MEMORY_BYTES64_OF_NUM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[READ_MEMORY_WBYTES_1600];
    MP_TAC(SPECL [`10`; `buf:int64`; `val(V:1600 word)`; `s16:armstate`]
                 READ_BYTES_FROM_CHUNKS128) THEN
    ANTS_TAC THENL
     [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    MP_TAC(SPECL [`buf:int64`; `160`; `8`; `val(V:1600 word)`; `s16:armstate`]
                 READ_MEMORY_BYTES_EXTEND) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(fun th ->
        if can (term_match [] `read (memory :> bytes64 (word_add buf (word 160))) s16 = x`) (concl th)
        then MP_TAC(MATCH_MP READ_MEMORY_BYTES_OF_BYTES64 th) else NO_TAC) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]]]);;

let GM3_BYTES16 = prove
 (GM3_BYTES16_STMT,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let GM3_INPUT = prove
 (GM3_INPUT_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; NUM_OF_BYTELIST_APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `34 = 32 + 2`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[GM3_BYTES16; num_of_bytelist; VAL_WORD; DIMINDEX_8;
                  DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC);;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_MONO_IN_MLKEM768_GEN_MATRIX = prove
 (MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_MONO_IN_MLKEM768_GEN_MATRIX_STMT,
  MAP_EVERY X_GEN_TAC
   [`entry:int64`; `buf:int64`; `rho:byte list`; `inp:byte list`; `k:num`;
    `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`; `bp:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL; ALLPAIRS;
              PAIRWISE; NONOVERLAPPING_CLAUSES; GSYM REJ_SAMPLE] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (LABEL_TAC "H_MEMSET" o REWRITE_RULE[memset_contract])
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `LENGTH(inp:byte list) = 34` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `APPEND rho [word 2:byte; word 2] = inp`)) THEN
    ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  REJ_ABSORBED_TAC THEN REJ_MINIMAL_TAC THEN

  (*** Up to the loop of the first three blocks ***)

  ENSURES_SEQUENCE_TAC `pc + mlkem768_gen_matrix_loop2` GM3_M1 THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--8) THEN
    LOCAL_GM3_ABSORB_TAC
     [`read X0 s`; `168`; `read X2 s`; `34`; `31`;
      `num_of_bytelist(inp:byte list)`; `pc:num`; `read SP s`;
      `read X30 s`] 9 THENL
     [MP_TAC(SPECL [`word_add buf (word 512):int64`; `rho:byte list`;
                    `s8:armstate`] GM3_INPUT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
        ASM_REWRITE_TAC[];
        STRIP_TAC THEN ASM_REWRITE_TAC[]];
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (*** The first three blocks ***)

  ENSURES_SEQUENCE_TAC `pc + mlkem768_gen_matrix_loop2_exit` GM3_M2 THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    LOCAL_GM3_SQ3_TAC
     [`word_add buf (word 768):int64`; `buf:int64`; `S0:1600 word`;
      `bp:int64`; `pc:num`] 1 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (*** The first sampling, from the three blocks ***)

  ENSURES_SEQUENCE_TAC `pc + mlkem768_gen_matrix_after_mlk_rej_uniform_c_1`
   GM3_A1 THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--6) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_add (word_sub x (word 4096)) (word 4096):int64 = x`]) THEN
    REJ_INPUT0_TAC `s6:armstate` THEN
    LOCAL_GM3_REJ_TAC
     [`read X0 s`; `0`; `read X2 s`; `504`;
      `wordlist_of_num 336
        (num_of_bytelist(list_of_seq (shake128 inp) 504)):(12 word)list`;
      `pc:num`; `read X30 s`] 7 THEN
    REJ_POST_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; MULT_CLAUSES; SUB_0; WORD_ADD_0;
                                LENGTH_SUB_LIST]) THEN
    FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REJ_BYTES16_OF_WORDLIST o check
     (can (term_match [] `wordlist_from_memory(a,n) s = l:int16 list`) o
      concl)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (*** The branch after the first sampling, the loop of further blocks ***)

  ENSURES_SEQUENCE_TAC `pc + mlkem768_gen_matrix_loop4_exit` GM3_A2 THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `k0 = 0` THENL
     [(*** No more block needed ***)
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `k0 = 0`)) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN
      SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,REJ_C0),`256`))
       (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`shake128 inp`; `0`; `k:num`] REJ_SAMPLE_FINAL) THEN
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
      ASM_REWRITE_TAC[];

      (*** The loop, if one more block is needed ***)

      SUBGOAL_THEN (mk_binop `(<):num->num->bool` REJ_C0 `256`) ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (is_forall o concl)) THEN
        REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; NOT_LE] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,REJ_C0),REJ_C0))
       (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [REWRITE_TAC[ARITH_RULE `MIN a b = b <=> b <= a`] THEN
        ASM_SIMP_TAC[LT_IMP_LE];
        ALL_TAC] THEN
      ENSURES_WHILE_UP2_TAC `k0:num` `pc + mlkem768_gen_matrix_loop4`
       `pc + mlkem768_gen_matrix_loop4_exit` GM3_INV THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];

        (*** Initialization, after not branching round the loop ***)

        ENSURES_INIT_TAC "s0" THEN
        RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
        ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--3) THEN
        REJ_ARGS_32_TAC REJ_C0 THEN REJ_HI_TAC REJ_C0 THEN
        SUBGOAL_THEN (mk_neg(mk_binop `(<):num->num->bool` `255` REJ_C0))
         (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
         [FIRST_ASSUM(fun th ->
            if is_binary "<" (concl th) && lhand(concl th) = REJ_C0
            then MP_TAC th THEN ARITH_TAC else NO_TAC);
          ALL_TAC] THEN
        ENSURES_FINAL_STATE_TAC THEN
        REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
        REJ_MIN_TAC THEN ASM_REWRITE_TAC[];

        (*** The body: one more block ***)

        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        SUBGOAL_THEN (mk_binop `(<):num->num->bool` (rej_count `i:num`) `256`)
        ASSUME_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl)) THEN
          ASM_REWRITE_TAC[NOT_LE];
          ALL_TAC] THEN
        REJ_MIN_TAC THEN ENSURES_INIT_TAC "s0" THEN
        ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--2) THEN
        KECCAK_STATE_AT_TAC `word_add buf (word 768):int64` THEN
        LOCAL_GM3_PERMUTE_TAC
         [`read X0 s`; `keccak_squeeze (3 + i) (S0:1600 word)`; `pc:num`;
          `read SP s`; `read X30 s`] 3 THEN
        RULE_ASSUM_TAC(REWRITE_RULE[GSYM(SPECL [`3 + i`; `S0:1600 word`]
                                          KSQ_SUC)]) THEN
        ABBREV_TAC (mk_eq(`ci:num`,rej_count `i:num`)) THEN
        SUBGOAL_THEN `ci <= 256` ASSUME_TAC THENL
         [UNDISCH_TAC `ci < 256` THEN ARITH_TAC; ALL_TAC] THEN
        LOCAL_GM3_COPYU_TAC
         [`word_add buf (word 768):int64`; `buf:int64`;
          `keccak_squeeze (3 + i + 1) (S0:1600 word)`; `read X19 s`;
          `read X25 s`; `pc:num`] 4 THENL
         [REWRITE_TAC[ADD_ASSOC]; ALL_TAC] THEN
        ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (5--5) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600;
                                    ARITH_RULE `(3 + i) + 1 = 3 + (i + 1)`]) THEN
        REJ_ARGS_32_TAC `ci:num` THEN REJ_BLOCK_TAC `s5:armstate` THEN
        LOCAL_GM3_REJ_TAC
         [`read X0 s`; `ci:num`; `read X2 s`; `168`; rej_block `i:num`;
          `pc:num`; `read X30 s`] 6 THEN
        REJ_COMBINE_TAC "s6" THEN
        ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (7--9) THEN
        REJ_ARGS_32_TAC REJ_CN THEN REJ_HI_TAC REJ_CN THEN REJ_LS_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600;
                                    ARITH_RULE `(3 + i) + 1 = 3 + (i + 1)`]) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        COND_CASES_TAC THEN REWRITE_TAC[];

        (*** The exit ***)

        ENSURES_INIT_TAC "s0" THEN
        SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,rej_count `k0:num`),`256`))
         (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
         [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
        MP_TAC(ISPECL [`shake128 inp`; `k0:num`; `k:num`] REJ_SAMPLE_FINAL) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (*** Releasing the state, zeroing the buffer ***)

  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(fun th ->
    if can (term_match []
             (vsubst [mk_small_numeral(layout "got_memset"),`n:num`]
                `read (memory :> bytes64 (word (pc + n))) s = (g:int64)`))
           (concl th)
    then ASSUME_TAC(REWRITE_RULE[WORD_ADD] th) else NO_TAC) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--12) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC 12 THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_GENMAT3_REJ_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 17 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   (mk_eq(mk_comb(`LENGTH:(16 word)list->num`,rej_l1 `k:num`),`256`))
  ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST; SUB_0;
                ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    if concl th = mk_eq(mk_comb(`LENGTH:(16 word)list->num`,rej_l1 `k:num`),
                        `256`)
    then GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM th]
    else NO_TAC) THEN
  MATCH_MP_TAC REJ_WORDLIST_OF_BYTES16 THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[]);;

let GENMAT3_COPY168_FULL = prove
 (GENMAT3_COPY168_FULL_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(st:int64) (q:int64) (pc:num).
      APPEND
        (f_ev_epil st q pc)
        (APPEND
          (ENUMERATEL 21 (\i. f_ev_loop st q pc i))
          (f_ev_prol st q pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`st:int64`; `q:int64`; `V:1600 word`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `21` `pc + mlkem768_gen_matrix_loop3`
   `pc + mlkem768_gen_matrix_loop3_exit`
   `\j s. read X0 s = word_add st (word(8 * j)) /\
          read X19 s = word_add q (word(8 * j)) /\
          read X20 s = st /\ read X22 s = word_add q (word 168) /\
          read (memory :> wbytes st) s = (V:1600 word) /\
          read (memory :> bytes(q,8 * j)) s =
          val (V:1600 word) MOD 2 EXP (8 * (8 * j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; READ_COMPONENT_COMPOSE;
                READ_BYTES_TRIVIAL; EXP; MOD_1] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The body: one 8-byte word and the test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `read (memory :> wbytes st) s0 = (V:1600 word)`)
             (concl th)
      then ASSUME_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600] th)
      else NO_TAC) THEN
    MP_TAC(SPECL [`st:int64`; `200`; `val(V:1600 word)`; `8 * i`;
                  `s0:armstate`] READ_MEMORY_BYTES64_OF_NUM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add (word_add q (word (8 * i))) (word 8))
                     (word_add q (word 168)):int64) = 0) <=> i + 1 < 21`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add (word_add a x) y) (word_add a z):int64 =
        word_sub (word_add x y) z`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 21 ==> 8 * i + 8 < 18446744073709551616`] THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN
      CONV_TAC WORD_RULE; ALL_TAC]) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[READ_MEMORY_WBYTES_1600]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(SPECL [`q:int64`; `8 * i`; `8`; `val(V:1600 word)`;
                    `s4:armstate`] READ_MEMORY_BYTES_EXTEND) THEN
      REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`;
                  ARITH_RULE `8 * (8 * i + 8) = 8 * (8 * i) + 64`] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[ARITH_RULE `8 * 8 * i = 8 * (8 * i)`];
        FIRST_ASSUM(fun th ->
          if can (term_match [] `read (memory :> bytes64 (word_add q (word (8 * i)))) s4 = x`) (concl th)
          then MP_TAC(MATCH_MP READ_MEMORY_BYTES_OF_BYTES64
                       (REWRITE_RULE[ZX_ZX_64_128] th))
          else NO_TAC) THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[MOD_MOD_REFL; ARITH_RULE `8 * 8 * i = 8 * (8 * i)`]];
      ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The exit and the update of X22 ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let GENMAT3_COPY168U_FULL = prove
 (GENMAT3_COPY168U_FULL_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(st:int64) (buf:int64) (pc:num). f_ev_all st buf pc :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`st:int64`; `buf:int64`; `V:1600 word`; `c19:int64`;
                       `y:int64`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> wbytes st) s0 = (V:1600 word)`)
           (concl th)
    then ASSUME_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600] th)
    else NO_TAC) THEN
  MAP_EVERY (fun k ->
    MP_TAC(SPECL [`st:int64`; `200`; `val(V:1600 word)`;
                  mk_small_numeral(16 * k); `s0:armstate`]
                 READ_MEMORY_BYTES128_OF_NUM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[WORD_ADD_0])) (0--9) THEN
  MP_TAC(SPECL [`st:int64`; `200`; `val(V:1600 word)`; `160`; `s0:armstate`]
               READ_MEMORY_BYTES64_OF_NUM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--16) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[READ_MEMORY_WBYTES_1600]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`10`; `buf:int64`; `val(V:1600 word)`; `s16:armstate`]
                 READ_BYTES_FROM_CHUNKS128) THEN
    ANTS_TAC THENL
     [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    MP_TAC(SPECL [`buf:int64`; `160`; `8`; `val(V:1600 word)`; `s16:armstate`]
                 READ_MEMORY_BYTES_EXTEND) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(fun th ->
        if can (term_match [] `read (memory :> bytes64 (word_add buf (word 160))) s16 = x`) (concl th)
        then MP_TAC(MATCH_MP READ_MEMORY_BYTES_OF_BYTES64 th) else NO_TAC) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]];
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let GENMAT3_SQ3_FULL = prove
 (GENMAT3_SQ3_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERM" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC GENMAT3_COPY168_FULL "H_COPY" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(st:int64) (buf:int64) (bp:int64) (pc:num).
      APPEND
        (f_ev_epil st buf bp pc)
        (APPEND
          (ENUMERATEL 3 (\t. f_ev_loop st buf bp pc t))
          (f_ev_prol st buf bp pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`st:int64`; `buf:int64`; `S:1600 word`; `bp:int64`;
                       `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; ALL; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `3` `pc + mlkem768_gen_matrix_loop2`
   `pc + mlkem768_gen_matrix_loop2_exit`
   `\t s. read SP s = word_add bp (word 256) /\ read X20 s = st /\ read X21 s = buf /\
          read X22 s = word_add buf (word(168 * (t + 1))) /\
          read X23 s = word(3 - t) /\
          read (memory :> wbytes st) s = keccak_squeeze t (S:1600 word) /\
          read (memory :> bytes(buf,168 * t)) s =
          nsum {i | i < t}
           (\i. 2 EXP (8 * 168 * i) *
                val(keccak_squeeze (i + 1) (S:1600 word)) MOD 2 EXP (8 * 168))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; SUB_0; WORD_ADD_0; keccak_squeeze;
                READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL;
                CONJUNCT1 NSUM_CLAUSES_NUMSEG_LT] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The body ***)

    X_GEN_TAC `t:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (1--2) THEN
    GM3SQ_SAFE_CALL_TAC "H_PERM"
     [`e:(uarch_event)list`; `read X0 s`; `keccak_squeeze t (S:1600 word)`;
      `pc:num`; `read SP s`; `read X30 s`] 3 THEN
    SUBGOAL_THEN
     `word_add buf (word (168 * (t + 1))):int64 =
      word_add (word_add buf (word (168 * t))) (word 168)`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `168 * (t + 1) = 168 * t + 168`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    GM3SQ_SAFE_CALL_SIDE_TAC "H_COPY"
     [`e:(uarch_event)list`; `st:int64`; `word_add buf (word(168 * t)):int64`;
      `keccak_f1600 (keccak_squeeze t (S:1600 word))`; `pc:num`] 4 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_GENMAT3_REJ_EXEC (5--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `t < 3` THEN SPEC_TAC(`t:num`,`t:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[ARITH_EQ];
      REWRITE_TAC[ARITH_RULE `168 * t + 336 = 168 * ((t + 1) + 1)`];
      UNDISCH_TAC `t < 3` THEN SPEC_TAC(`t:num`,`t:num`) THEN
      CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[ARITH_EQ];
      REWRITE_TAC[KSQ_SUC];
      REWRITE_TAC[NSUM_LT_STEP; ARITH_RULE `168 * (t + 1) = 168 * t + 168`;
                  READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[KSQ_SUC];
      GM3_LOOP_DISCHARGE_TAC];

    (*** The exit ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_MONO_IN_MLKEM768_GEN_MATRIX_FULL = prove
 (MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O2_MONO_IN_MLKEM768_GEN_MATRIX_FULL_STMT, GM3F_MAIN_TAC);;
