(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/asm/rej_full_spec.ml";;

let LENGTH_REJ_OUT_LEN = prove
 (LENGTH_REJ_OUT_LEN_STMT,
  REWRITE_TAC[rej_out; rej_len; LENGTH_SUB_LIST; LENGTH_APPEND; SUB_0]);;

let REJ_EV_SEQ = prove
 (REJ_EV_SEQ_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC REJ_TRANS THEN
  EXISTS_TAC
   `\s. bytes_loaded s (word pc) (BUTLAST mlkem_rej_uniform_alt_tmc) /\
        read RIP s = word(pc + off2) /\ (Q:x86state->bool) s /\
        read events s = APPEND ev1 e /\
        memaccess_inbounds (ev1:(uarch_event)list) rd wr` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `memaccess_inbounds (ev1:(uarch_event)list) rd wr` THEN
  ASM_REWRITE_TAC[ENSURES_FALSE_PRE; MEMACCESS_INBOUNDS_APPEND;
                  GSYM APPEND_ASSOC]);;

let REJ_EV_LOOP24_EXIT = prove
 (REJ_EV_LOOP24_EXIT_STMT,
  let EXIT_SIM_TAC n =
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (1--n) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [EXISTS_TAC `p:num` THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    REJ_EV_CLOSE_TAC in
  REJ_EV_TEST_PRE_TAC THEN
  ASM_CASES_TAC `buflen < 24 * (p + 1)` THEN REJ_EV_TEST_SETUP_TAC THENL
   [SUBGOAL_THEN `buflen - 24 * p < 24` ASSUME_TAC THENL
     [ASM_ARITH_TAC; EXIT_SIM_TAC 2];
    SUBGOAL_THEN `~(buflen - 24 * p < 24) /\ 256 <= c` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; EXIT_SIM_TAC 4]]);;

let REJ_EV_LOOP48_EXIT_A = prove
 (REJ_EV_LOOP48_EXIT_A_STMT,
  REJ_EV_TEST_PRE_TAC THEN
  ASM_CASES_TAC `buflen < 24 * (p + 2)` THEN REJ_EV_TEST_SETUP_TAC THENL
   [SUBGOAL_THEN `buflen - 24 * p < 48` ASSUME_TAC THENL
     [ASM_ARITH_TAC; REJ_EV_TEST_SIM_TAC 2];
    SUBGOAL_THEN `~(buflen - 24 * p < 48) /\ 224 < c` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; REJ_EV_TEST_SIM_TAC 4]]);;

let REJ_EV_LOOP48_ENTER_A = prove
 (REJ_EV_LOOP48_ENTER_A_STMT,
  REJ_EV_TEST_PRE_TAC THEN REJ_EV_TEST_SETUP_TAC THEN
  SUBGOAL_THEN `~(buflen - 24 * p < 48) /\ ~(224 < c)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; REJ_EV_TEST_SIM_TAC 5]);;

let REJ_EV_LOOP48_EXIT_B = prove
 (REJ_EV_LOOP48_EXIT_B_STMT,
  REJ_EV_TEST_PRE_TAC THEN
  ASM_CASES_TAC `buflen < 24 * (p + 2)` THEN REJ_EV_TEST_SETUP_TAC THENL
   [SUBGOAL_THEN `buflen - 24 * p < 48` ASSUME_TAC THENL
     [ASM_ARITH_TAC; REJ_EV_TEST_SIM_TAC 2];
    SUBGOAL_THEN `~(buflen - 24 * p < 48) /\ 224 < c /\ ~(c <= 224)`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; REJ_EV_TEST_SIM_TAC 4]]);;

let REJ_EV_LOOP48_ENTER_B = prove
 (REJ_EV_LOOP48_ENTER_B_STMT,
  REJ_EV_TEST_PRE_TAC THEN REJ_EV_TEST_SETUP_TAC THEN
  SUBGOAL_THEN `~(buflen - 24 * p < 48) /\ ~(224 < c) /\ c <= 224`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; REJ_EV_TEST_SIM_TAC 4]);;

let REJ_EV_LOOP24_DIRECT = prove
 (REJ_EV_LOOP24_DIRECT_STMT,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REJ_EV_META_TAC THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  REWRITE_TAC[rej_st; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_TAC THEN
  ABBREV_TAC `out = rej_out curlist inlist p` THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`] THEN
  ABBREV_TAC
   `chk = word((num_of_wordlist(inlist:(12 word)list) DIV 2 EXP (8 * 24 * p))
               MOD 2 EXP 192):192 word` THEN
  SUBGOAL_THEN
   `!j. j < 16
        ==> EL (16 * p + j) inlist =
            word_subword (chk:192 word) (12 * j,12):12 word`
  (LABEL_TAC "chunk") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "chk" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REJ_CHUNK_EL_192 THEN
    MAP_EVERY UNDISCH_TAC
     [`j < 16`; `8 * buflen = 12 * LENGTH(inlist:(12 word)list)`;
      `24 * (p + 1) <= buflen`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `buflen - 24 * p < 2 EXP 64 /\ ~(buflen - 24 * p < 24)`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `buflen - 24 * p` THEN
  SUBGOAL_THEN `c < 2 EXP 64 /\ ~(256 <= c) /\ ~(240 < c) /\ c < 241`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `c:num` THEN
  SUBGOAL_THEN
   `(c < 240 \/ val (word_sub (word c:int64) (word 240)) = 0) <=> ~(240 < c)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_JOIN_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`buf:int64`; `buflen:num`;
                `num_of_wordlist(inlist:(12 word)list)`;
                `24 * p`; `s0:x86state`] CHUNK_LOADS24) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `24 * (p + 1) <= buflen` THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN

  (*** The 16 candidates, the masks and the counts ***)

  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (1--12) THEN
  REJ_CANDIDATES_TAC 1 THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC REJ_PACK_FOLD) (13--16) THEN
  REJ_MASK_SIMPLIFY_TAC 16 THEN REJ_MASK_ABBREV_TAC 16 ["m0"; "m1"] THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n])
            (17--25) THEN
  REJ_INDEX_TAC `R9` 25 `m0:byte` THEN REJ_INDEX_TAC `R10` 25 `m1:byte` THEN
  REJ_COUNT_TAC `R11` 25 `m0:byte` THEN REJ_COUNT_TAC `RAX` 25 `m1:byte` THEN

  (*** The table entries and the compaction ***)

  ASSUME_TAC(WORD_RULE `!x. word (1 * val(word x:int64)):int64 = word x`) THEN
  REJ_TAB_TAC "tab0" `m0:byte` 25 THEN REJ_TAB_TAC "tab1" `m1:byte` 25 THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (26--28) THEN
  REJ_GROUP_TAC `YMM0` 28 THEN
  REJ_LIST_ABBREV_TAC `YMM0` 28 ["lis0"; "lis1"] ["len0"; "len1"] THEN
  REJ_COUNTS_TAC THEN

  (*** The stores and the updates of the pointer and the count ***)

  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (29--31) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ZX_JOIN]) THEN REJ_STORE_LEN_TAC THEN
  SUBGOAL_THEN `len0 < 2 EXP 64 /\ len1 < 2 EXP 64 /\ len0 + len1 < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`len0 <= 8`; `len1 <= 8`] THEN ARITH_TAC;
    ALL_TAC] THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [32] THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [MATCH_MP REJ_ADDR_NORM (ASSUME `len0 < 2 EXP 64`)]) THEN
  REJ_STORE_LEN_TAC THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (33--36) THEN

  (*** The new result list ***)

  SUBGOAL_THEN
   `rej_out curlist inlist (p + 1) = APPEND (APPEND out lis0) lis1`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`curlist:int16 list`; `inlist:(12 word)list`; `p:num`; `1`]
      REJ_OUT_STEP) THEN
    REWRITE_TAC[ASSUME `rej_out curlist inlist p = out`;
                ASSUME `LENGTH(out:int16 list) = c`] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `c < 241` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; ARITH_RULE `16 * 1 = 16`] THEN
    AP_TERM_TAC THEN
    REJ_SAMPLE_EXPAND_TAC SUB_LIST_EXPAND_16 ["lis0"; "lis1"] ["chunk"]
     [`8 * buflen = 12 * LENGTH(inlist:(12 word)list)`;
      `24 * (p + 1) <= buflen`];
    ALL_TAC] THEN

  (*** The final state ***)

  SUBGOAL_THEN `c + len0 <= 248` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`c < 241`; `len0 <= 8`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[ASSUME
   `rej_out curlist inlist (p + 1) = APPEND (APPEND out lis0) lis1`;
   LENGTH_APPEND] THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`;
              ASSUME `LENGTH(lis0:int16 list) = len0`;
              ASSUME `LENGTH(lis1:int16 list) = len1`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    SUBGOAL_THEN `buflen - 24 * p = (buflen - 24 * (p + 1)) + 24`
    SUBST1_TAC THENL
     [UNDISCH_TAC `24 * (p + 1) <= buflen` THEN ARITH_TAC;
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC];
    REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    SIMP_TAC[MOD_LT; ASSUME `len0 + len1 < 2 EXP 64`] THEN CONV_TAC WORD_RULE;
    REJ_EV_TAC;
    REJ_MI_TAC]);;

let REJ_EV_COPY_ENTRY = prove
 (REJ_EV_COPY_ENTRY_STMT,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REJ_EV_META_TAC THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  REWRITE_TAC[rej_cst; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    REWRITE_TAC[th; SUB_0; ADD_CLAUSES; MULT_CLAUSES; SUB_LIST_CLAUSES;
                APPEND_NIL; WORD_ADD_0]) THEN
  SUBGOAL_THEN `m < 2 EXP 64` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `m:num` THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_JOIN_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (1--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REJ_EV_CLOSE_TAC);;

let REJ_EV_COPY_STEP = prove
 (REJ_EV_COPY_STEP_STMT,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REJ_EV_META_TAC THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  REWRITE_TAC[rej_cst; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_TAC THEN
  ABBREV_TAC `out = rej_out curlist inlist p` THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_JOIN_CONV) THEN
  SUBGOAL_THEN `i < LENGTH(L:int16 list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i < 2 EXP 64 /\ i + 1 < 2 EXP 64 /\ m < 2 EXP 64`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `i:num` THEN VAL_INT64_TAC `i + 1` THEN
  VAL_INT64_TAC `m:num` THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`stk:int64`; `L:int16 list`; `i:num`; `s0:x86state`]
    READ_BYTES16_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (1--5) THEN
  FIRST_X_ASSUM(MP_TAC o REJ_COPY_SIMP_RULE o check (can (term_match
    [`res:int64`]
    `read (memory :> bytes16 (word_add res (word (2 * n)))) s5 = x`) o
    concl)) THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_INC]) THEN
  MP_TAC(SPECL [`res:int64`; `c + i:num`;
                `APPEND out (SUB_LIST(0,i) L):int16 list`;
                `EL i L:int16`; `s5:x86state`] REJ_STORE16) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_SUB_LIST; SUB_0] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC(ARITH_RULE `i < l ==> MIN i l = i`) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_ADD; ASSUME `val(word(i + 1):int64) = i + 1`]) THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [6] THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_SIMP_TAC[SUB_LIST_SNOC] THEN
  REWRITE_TAC[APPEND_ASSOC; ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN
  REJ_EV_CLOSE_TAC);;

let REJ_EV_COPY_LAST = prove
 (REJ_EV_COPY_LAST_STMT,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REJ_EV_META_TAC THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  REWRITE_TAC[rej_cst; rej_st; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  ABBREV_TAC `out = rej_out curlist inlist p` THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_SUB_LIST; SUB_0] THEN
  ASM_SIMP_TAC[ARITH_RULE `m <= l ==> MIN m l = m`] THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> concl th = `i + 1 = m`)) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_JOIN_CONV) THEN
  SUBGOAL_THEN `i < LENGTH(L:int16 list)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i < 2 EXP 64 /\ i + 1 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `i:num` THEN VAL_INT64_TAC `i + 1` THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`stk:int64`; `L:int16 list`; `i:num`; `s0:x86state`]
    READ_BYTES16_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (1--5) THEN
  FIRST_X_ASSUM(MP_TAC o REJ_COPY_SIMP_RULE o check (can (term_match
    [`res:int64`]
    `read (memory :> bytes16 (word_add res (word (2 * n)))) s5 = x`) o
    concl)) THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_INC]) THEN
  MP_TAC(SPECL [`res:int64`; `c + i:num`;
                `APPEND out (SUB_LIST(0,i) L):int16 list`;
                `EL i L:int16`; `s5:x86state`] REJ_STORE16) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_SUB_LIST; SUB_0] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC(ARITH_RULE `i < l ==> MIN i l = i`) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [GSYM WORD_ADD; ASSUME `val(word(i + 1):int64) = i + 1`; LT_REFL]) THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (6--7) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_SIMP_TAC[SUB_LIST_SNOC] THEN
  REWRITE_TAC[APPEND_ASSOC; ADD_ASSOC] THEN ASM_REWRITE_TAC[] THEN
  REJ_EV_CLOSE_TAC);;

let REJ_DOWN_INDUCT = prove
 (REJ_DOWN_INDUCT_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "last") (LABEL_TAC "step")) THEN
  SUBGOAL_THEN `!d i. i + d + 1 = m ==> P i` ASSUME_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN USE_THEN "last" MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      X_GEN_TAC `d:num` THEN DISCH_THEN(LABEL_TAC "ih") THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN USE_THEN "step" MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "ih" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `m - i - 1` THEN
    ASM_ARITH_TAC]);;

let REJ_EV_COPY_LOOP = prove
 (REJ_EV_COPY_LOOP_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC REJ_DOWN_INDUCT THEN
  CONJ_TAC THEN X_GEN_TAC `i:num` THENL
   [DISCH_TAC THEN MATCH_MP_TAC REJ_EV_COPY_LAST THEN ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_TAC `ev2:(uarch_event)list`))] THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                `inlist:(12 word)list`; `stk:int64`; `pc:num`;
                `p:num`; `c:num`; `L:int16 list`; `m:num`; `i:num`]
    REJ_EV_COPY_STEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `ev1:(uarch_event)list`) THEN
  EXISTS_TAC `APPEND (ev2:(uarch_event)list) ev1` THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  STRIP_TAC THEN MATCH_MP_TAC REJ_EV_SEQ THEN
  MAP_EVERY EXISTS_TAC
   [`0x26b`;
    `rej_cst res buf buflen table inlist stk p
             (rej_out curlist inlist p) L m (i + 1)`] THEN
  ASM_SIMP_TAC[]);;

let REJ_EV_LASTCOPY = prove
 (REJ_EV_LASTCOPY_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `m = 0` THENL
   [REJ_EV_META_TAC THEN
    MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
    REWRITE_TAC[rej_cst; rej_st; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                NONOVERLAPPING_CLAUSES; ALL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    ASM_REWRITE_TAC[SUB_0; ADD_CLAUSES; MULT_CLAUSES; SUB_LIST_CLAUSES;
                    APPEND_NIL] THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_JOIN_CONV) THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REJ_EV_CLOSE_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                `inlist:(12 word)list`; `stk:int64`; `pc:num`;
                `p:num`; `c:num`; `L:int16 list`; `m:num`]
    REJ_EV_COPY_LOOP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < m <=> ~(m = 0)`] THEN
  DISCH_THEN(X_CHOOSE_TAC `ev2:(uarch_event)list`) THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                `inlist:(12 word)list`; `stk:int64`; `pc:num`;
                `p:num`; `c:num`; `L:int16 list`; `m:num`]
    REJ_EV_COPY_ENTRY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `ev1:(uarch_event)list`) THEN
  EXISTS_TAC `APPEND (ev2:(uarch_event)list) ev1` THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  STRIP_TAC THEN MATCH_MP_TAC REJ_EV_SEQ THEN
  MAP_EVERY EXISTS_TAC
   [`0x26b`;
    `rej_cst res buf buflen table inlist stk p
             (rej_out curlist inlist p) L m 0`] THEN
  ASM_SIMP_TAC[]);;

let REJ_EV_LOOP24_HEAD = prove
 (REJ_EV_LOOP24_HEAD_STMT,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REJ_EV_META_TAC THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  REWRITE_TAC[rej_st; rej_cst; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_TAC THEN
  ABBREV_TAC `out = rej_out curlist inlist p` THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`] THEN
  REWRITE_TAC[SUB_0; ADD_CLAUSES; MULT_CLAUSES; SUB_LIST_CLAUSES; APPEND_NIL;
              WORD_ADD_0] THEN
  ABBREV_TAC
   `chk = word((num_of_wordlist(inlist:(12 word)list) DIV 2 EXP (8 * 24 * p))
               MOD 2 EXP 192):192 word` THEN
  SUBGOAL_THEN
   `!j. j < 16
        ==> EL (16 * p + j) inlist =
            word_subword (chk:192 word) (12 * j,12):12 word`
  (LABEL_TAC "chunk") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "chk" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REJ_CHUNK_EL_192 THEN
    MAP_EVERY UNDISCH_TAC
     [`j < 16`; `8 * buflen = 12 * LENGTH(inlist:(12 word)list)`;
      `24 * (p + 1) <= buflen`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `buflen - 24 * p < 2 EXP 64 /\ ~(buflen - 24 * p < 24)`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `buflen - 24 * p` THEN
  SUBGOAL_THEN `c < 2 EXP 64 /\ ~(256 <= c) /\ 240 < c /\ c < 256`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `c:num` THEN
  SUBGOAL_THEN
   `(c < 240 \/ val (word_sub (word c:int64) (word 240)) = 0) <=> ~(240 < c)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_JOIN_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`buf:int64`; `buflen:num`;
                `num_of_wordlist(inlist:(12 word)list)`;
                `24 * p`; `s0:x86state`] CHUNK_LOADS24) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `24 * (p + 1) <= buflen` THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (1--12) THEN
  REJ_CANDIDATES_TAC 1 THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC REJ_PACK_FOLD) (13--16) THEN
  REJ_MASK_SIMPLIFY_TAC 16 THEN REJ_MASK_ABBREV_TAC 16 ["m0"; "m1"] THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n])
            (17--25) THEN
  REJ_INDEX_TAC `R9` 25 `m0:byte` THEN REJ_INDEX_TAC `R10` 25 `m1:byte` THEN
  REJ_COUNT_TAC `R11` 25 `m0:byte` THEN REJ_COUNT_TAC `RAX` 25 `m1:byte` THEN
  ASSUME_TAC(WORD_RULE `!x. word (1 * val(word x:int64)):int64 = word x`) THEN
  REJ_TAB_TAC "tab0" `m0:byte` 25 THEN REJ_TAB_TAC "tab1" `m1:byte` 25 THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (26--28) THEN
  REJ_GROUP_TAC `YMM0` 28 THEN
  REJ_LIST_ABBREV_TAC `YMM0` 28 ["lis0"; "lis1"] ["len0"; "len1"] THEN
  REJ_COUNTS_TAC THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (29--31) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ZX_JOIN]) THEN
  MP_TAC(SPECL [`stk:int64`; `lis0:int16 list`; `s31:x86state`]
    REJ_STORE0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `len0 < 2 EXP 64 /\ len1 < 2 EXP 64 /\ len0 + len1 < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`len0 <= 8`; `len1 <= 8`] THEN ARITH_TAC;
    ALL_TAC] THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [32] THEN
  VAL_INT64_TAC `len0:num` THEN VAL_INT64_TAC `len1:num` THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word len0:int64) = len0`]) THEN
  REJ_STORE_AT_TAC `stk:int64` THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (33--37) THEN
  SUBGOAL_THEN `L:int16 list = APPEND lis0 lis1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `REJ_SAMPLE (SUB_LIST(16 * p,16) inlist) = L`)) THEN
    REJ_SAMPLE_EXPAND_TAC SUB_LIST_EXPAND_16 ["lis0"; "lis1"] ["chunk"]
     [`8 * buflen = 12 * LENGTH(inlist:(12 word)list)`;
      `24 * (p + 1) <= buflen`];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(L:int16 list) = len0 + len1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_APPEND]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match []
    `read R11 s37 = (if a then b else c)`) o concl)) THEN
  MP_TAC(SPECL [`len0:num`; `len1:num`; `c:num`] REJ_CMOVA) THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`len0 <= 8`; `len1 <= 8`; `c < 256`] THEN
    ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM(ASSUME `LENGTH(L:int16 list) = len0 + len1`)] THEN
  REWRITE_TAC[ASSUME `MIN (LENGTH(L:int16 list)) (256 - c) = m`] THEN
  DISCH_TAC THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (38--39) THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match [`stk:int64`]
    `read (memory :> bytes (stk,n)) s39 =
     num_of_wordlist(APPEND l1 l2)`) o concl)) THEN
  REWRITE_TAC[ASSUME `LENGTH(lis1:int16 list) = len1`] THEN DISCH_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[ASSUME `L:int16 list = APPEND lis0 lis1`; LENGTH_APPEND] THEN
  REWRITE_TAC[ASSUME `LENGTH(lis0:int16 list) = len0`;
              ASSUME `LENGTH(lis1:int16 list) = len1`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    SUBGOAL_THEN `buflen - 24 * p = (buflen - 24 * (p + 1)) + 24`
    SUBST1_TAC THENL
     [UNDISCH_TAC `24 * (p + 1) <= buflen` THEN ARITH_TAC;
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    REWRITE_TAC[WORD_ADD];
    REJ_EV_TAC;
    REJ_MI_TAC]);;

let REJ_EV_LOOP24_LAST = prove
 (REJ_EV_LOOP24_LAST_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `L = REJ_SAMPLE (SUB_LIST(16 * p,16) (inlist:(12 word)list))` THEN
  ABBREV_TAC `m = MIN (LENGTH(L:int16 list)) (256 - c)` THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                `inlist:(12 word)list`; `stk:int64`; `pc:num`;
                `p:num`; `c:num`; `L:int16 list`; `m:num`]
    REJ_EV_LOOP24_HEAD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `ev1:(uarch_event)list`) THEN
  MP_TAC(ISPECL [`inlist:(12 word)list`; `16 * p`; `16`]
    LENGTH_REJ_SAMPLE_CHUNK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                `inlist:(12 word)list`; `stk:int64`; `pc:num`;
                `p:num`; `c:num`; `L:int16 list`; `m:num`]
    REJ_EV_LASTCOPY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "m" THEN ASM_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `ev2:(uarch_event)list`)] THEN
  EXISTS_TAC `APPEND (ev2:(uarch_event)list) ev1` THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `rej_out curlist inlist (p + 1) =
    APPEND (rej_out curlist inlist p) (SUB_LIST(0,m) L)`
  ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `LENGTH(rej_out curlist inlist p) = c`)) THEN
    MATCH_MP_TAC REJ_OUT_LAST THEN
    ASM_REWRITE_TAC[LENGTH_REJ_OUT];
    ALL_TAC] THEN
  MATCH_MP_TAC REJ_EV_SEQ THEN
  MAP_EVERY EXISTS_TAC
   [`0x262`;
    `rej_cst res buf buflen table inlist stk p
             (rej_out curlist inlist p) L m 0`] THEN
  ASM_SIMP_TAC[]);;

let REJ_EV_LOOP48_BODY = prove
 (REJ_EV_LOOP48_BODY_STMT,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REJ_EV_META_TAC THEN
  MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
  REWRITE_TAC[rej_st; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_TAC THEN
  ABBREV_TAC `out = rej_out curlist inlist p` THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`] THEN
  ABBREV_TAC
   `chk = word((num_of_wordlist(inlist:(12 word)list) DIV 2 EXP (8 * 24 * p))
               MOD 2 EXP 384):384 word` THEN
  SUBGOAL_THEN
   `!j. j < 32
        ==> EL (16 * p + j) inlist =
            word_subword (chk:384 word) (12 * j,12):12 word`
  (LABEL_TAC "chunk") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "chk" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REJ_CHUNK_EL_384 THEN
    MAP_EVERY UNDISCH_TAC
     [`j < 32`; `8 * buflen = 12 * LENGTH(inlist:(12 word)list)`;
      `24 * (p + 2) <= buflen`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `buflen - 24 * p < 2 EXP 64` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `buflen - 24 * p` THEN
  SUBGOAL_THEN `c < 2 EXP 64 /\ c < 225` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `c:num` THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_JOIN_CONV) THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(SPECL [`buf:int64`; `buflen:num`;
                `num_of_wordlist(inlist:(12 word)list)`;
                `24 * p`; `s0:x86state`] CHUNK_LOADS48) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `24 * (p + 2) <= buflen` THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (1--14) THEN
  REJ_CANDIDATES_TAC 2 THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC REJ_PACK_FOLD48) (15--18) THEN
  REJ_MASK48_SIMPLIFY_TAC 18 THEN
  REJ_MASK_ABBREV_TAC 18 ["m0"; "m1"; "m2"; "m3"] THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n])
            (19--29) THEN
  REJ_INDEX_TAC `R9` 29 `m0:byte` THEN REJ_INDEX_TAC `R10` 29 `m1:byte` THEN
  REJ_INDEX_TAC `R11` 29 `m2:byte` THEN REJ_INDEX_TAC `RAX` 29 `m3:byte` THEN
  ASSUME_TAC(WORD_RULE `!x. word (1 * val(word x:int64)):int64 = word x`) THEN
  REJ_TAB_TAC "tab0" `m0:byte` 29 THEN REJ_TAB_TAC "tab1" `m1:byte` 29 THEN
  REJ_TAB_TAC "tab2" `m2:byte` 29 THEN REJ_TAB_TAC "tab3" `m3:byte` 29 THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[]) (30--35) THEN
  REJ_GROUP_TAC `YMM0` 35 THEN REJ_GROUP_TAC `YMM7` 35 THEN
  REJ_LIST_ABBREV_TAC `YMM0` 35 ["lis0"; "lis2"] ["len0"; "len2"] THEN
  REJ_LIST_ABBREV_TAC `YMM7` 35 ["lis1"; "lis3"] ["len1"; "len3"] THEN
  MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n])
            (36--39) THEN
  REJ_COUNT_TAC `R9` 39 `m0:byte` THEN REJ_COUNT_TAC `R10` 39 `m1:byte` THEN
  REJ_COUNT_TAC `R11` 39 `m2:byte` THEN REJ_COUNT_TAC `RAX` 39 `m3:byte` THEN
  REJ_COUNTS_TAC THEN
  SUBGOAL_THEN
   `len0 < 2 EXP 64 /\ len0 + len1 < 2 EXP 64 /\
    (len0 + len1) + len2 < 2 EXP 64 /\
    ((len0 + len1) + len2) + len3 < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`len0 <= 8`; `len1 <= 8`; `len2 <= 8`; `len3 <= 8`]
    THEN ARITH_TAC;
    ALL_TAC] THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [40] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ZX_JOIN]) THEN REJ_STORE_LEN_TAC THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [41] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ZX_JOIN;
    MATCH_MP REJ_ADDR_NORM (ASSUME `len0 < 2 EXP 64`)]) THEN
  REJ_STORE_LEN_TAC THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [42] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN
  VAL_INT64_TAC `len0 + len1` THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [43] THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_ASSOC;
    MATCH_MP REJ_ADDR_NORM (ASSUME `len0 + len1 < 2 EXP 64`)]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_SUM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_ASSOC]) THEN REJ_STORE_LEN_TAC THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [44] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN
  VAL_INT64_TAC `(len0 + len1) + len2` THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [45] THEN
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REJ_ADDR_SUM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_ASSOC]) THEN REJ_STORE_LEN_TAC THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [46] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM WORD_ADD]) THEN
  VAL_INT64_TAC `((len0 + len1) + len2) + len3` THEN
  X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (47--48) THEN
  SUBGOAL_THEN
   `rej_out curlist inlist (p + 2) =
    APPEND (APPEND (APPEND (APPEND out lis0) lis1) lis2) lis3`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`curlist:int16 list`; `inlist:(12 word)list`; `p:num`; `2`]
      REJ_OUT_STEP) THEN
    REWRITE_TAC[ASSUME `rej_out curlist inlist p = out`;
                ASSUME `LENGTH(out:int16 list) = c`] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `c < 225` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM APPEND_ASSOC; ARITH_RULE `16 * 2 = 32`] THEN
    AP_TERM_TAC THEN
    REJ_SAMPLE_EXPAND_TAC SUB_LIST_EXPAND_32
     ["lis0"; "lis1"; "lis2"; "lis3"] ["chunk"]
     [`8 * buflen = 12 * LENGTH(inlist:(12 word)list)`;
      `24 * (p + 2) <= buflen`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `c + len0 <= 248 /\ (c + len0) + len1 <= 248 /\
    ((c + len0) + len1) + len2 <= 248`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`c < 225`; `len0 <= 8`; `len1 <= 8`; `len2 <= 8`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[ASSUME
   `rej_out curlist inlist (p + 2) =
    APPEND (APPEND (APPEND (APPEND out lis0) lis1) lis2) lis3`;
   LENGTH_APPEND] THEN
  REWRITE_TAC[ASSUME `LENGTH(out:int16 list) = c`;
              ASSUME `LENGTH(lis0:int16 list) = len0`;
              ASSUME `LENGTH(lis1:int16 list) = len1`;
              ASSUME `LENGTH(lis2:int16 list) = len2`;
              ASSUME `LENGTH(lis3:int16 list) = len3`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC WORD_RULE;
    SUBGOAL_THEN `buflen - 24 * p = (buflen - 24 * (p + 2)) + 48`
    SUBST1_TAC THENL
     [UNDISCH_TAC `24 * (p + 2) <= buflen` THEN ARITH_TAC;
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC];
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    REJ_EV_TAC;
    REJ_MI_TAC]);;

let REJ_EV_LOOP24_ALL = prove
 (REJ_EV_LOOP24_ALL_STMT,
  let EXIT_TAC =
    MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                  `inlist:(12 word)list`; `stk:int64`; `pc:num`;
                  `p:num`; `rej_len k (inlist:(12 word)list) p`]
      REJ_EV_LOOP24_EXIT) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `ev1:(uarch_event)list`) THEN
    EXISTS_TAC `ev1:(uarch_event)list` THEN
    MAP_EVERY X_GEN_TAC [`curlist:int16 list`; `e:(uarch_event)list`] THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LENGTH_REJ_OUT_LEN] in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; LE_EXISTS] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` MP_TAC) THEN
  SUBGOAL_THEN `24 divides buflen` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MESON_TAC[DIVIDES_RMUL; DIVIDES_REFL]; ALL_TAC] THEN
  UNDISCH_TAC `buflen = 24 * t` THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  SPEC_TAC(`p:num`,`p:num`) THEN SPEC_TAC(`d:num`,`d:num`) THEN
  INDUCT_TAC THEN X_GEN_TAC `p:num` THEN DISCH_TAC THENL
   [EXIT_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `256 <= rej_len k (inlist:(12 word)list) p` THENL
   [EXIT_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p + 1` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `ev2:(uarch_event)list`) THEN
  ASM_CASES_TAC `rej_len k (inlist:(12 word)list) p <= 240` THENL
   [MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                  `inlist:(12 word)list`; `stk:int64`; `pc:num`;
                  `p:num`; `rej_len k (inlist:(12 word)list) p`]
      REJ_EV_LOOP24_DIRECT);
    MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                  `inlist:(12 word)list`; `stk:int64`; `pc:num`;
                  `p:num`; `rej_len k (inlist:(12 word)list) p`]
      REJ_EV_LOOP24_LAST)] THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_TAC `ev1:(uarch_event)list`) THEN
   REJ_EV_SEQ_TAC `0x198`
    `rej_st res buf buflen table curlist inlist stk (p + 1)`));;

let REJ_EV_LOOP48_ALL = prove
 (REJ_EV_LOOP48_ALL_STMT,
  let BLOCK_TAC th =
    MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                  `inlist:(12 word)list`; `stk:int64`; `pc:num`;
                  `p:num`; `rej_len k (inlist:(12 word)list) p`] th) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `ev1:(uarch_event)list`)
  and LOOP24_TAC =
    MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                  `inlist:(12 word)list`; `stk:int64`; `pc:num`;
                  `t:num`; `k:num`; `p:num`] REJ_EV_LOOP24_ALL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `ev2:(uarch_event)list`) in

  (*** The body, then the rest from the test at its end for p + 2 ***)

  let BODY_REST_TAC =
    SUBGOAL_THEN (rej_ev_to_end 0x9c `p:num`)
     (X_CHOOSE_TAC `ev2:(uarch_event)list`) THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `d - 2` o check (is_forall o concl)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `p + 2`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `ev2:(uarch_event)list` o CONJUNCT1) THEN
      BLOCK_TAC REJ_EV_LOOP48_BODY THEN
      REJ_EV_SEQ_TAC `0x185`
       `rej_st res buf buflen table curlist inlist stk (p + 2)`;
      ALL_TAC] in

  REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; LE_EXISTS] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` MP_TAC) THEN
  SUBGOAL_THEN `24 divides buflen` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MESON_TAC[DIVIDES_RMUL; DIVIDES_REFL]; ALL_TAC] THEN
  SPEC_TAC(`p:num`,`p:num`) THEN SPEC_TAC(`d:num`,`d:num`) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `d:num` THEN DISCH_TAC THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC
   `buflen < 24 * (p + 2) \/ 224 < rej_len k (inlist:(12 word)list) p`
  THENL
   [(*** To the loop by 24 bytes, from either test ***)

    LOOP24_TAC THEN CONJ_TAC THENL
     [BLOCK_TAC REJ_EV_LOOP48_EXIT_B;
      BLOCK_TAC REJ_EV_LOOP48_EXIT_A] THEN
    REJ_EV_SEQ_TAC `0x198`
     `rej_st res buf buflen table curlist inlist stk p`;

    (*** Through the body, from either test ***)

    BODY_REST_TAC THEN CONJ_TAC THENL
     [BLOCK_TAC REJ_EV_LOOP48_ENTER_B;
      BLOCK_TAC REJ_EV_LOOP48_ENTER_A] THEN
    REJ_EV_SEQ_TAC `0x9c`
     `rej_st res buf buflen table curlist inlist stk p`]);;

let REJ_FULL_CORE0 = prove
 (REJ_FULL_CORE0_STMT,
  MAP_EVERY X_GEN_TAC [`res:int64`; `n:int64`; `buf:int64`] THEN
  W64_GEN_TAC `buflen:num` THEN
  MAP_EVERY X_GEN_TAC
   [`table:int64`; `inlist:(12 word)list`; `pc:num`;
    `stackpointer:int64`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `t:num` (ASSUME_TAC o SYM) o
    REWRITE_RULE[divides] o
    check (fun th -> concl th = `24 divides buflen`)) THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `buflen:num`; `table:int64`;
                `inlist:(12 word)list`;
                `word_sub stackpointer (word 32):int64`; `pc:num`;
                `t:num`; `val(n:int64)`; `0`] REJ_EV_LOOP48_ALL) THEN
  ASM_REWRITE_TAC[LE_0] THEN
  DISCH_THEN(X_CHOOSE_TAC `ev:(uarch_event)list` o CONJUNCT2) THEN
  EXISTS_TAC `ev:(uarch_event)list` THEN
  MAP_EVERY X_GEN_TAC [`e:(uarch_event)list`; `curlist:int16 list`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o
    SPECL [`curlist:int16 list`; `e:(uarch_event)list`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN] THEN
  MP_TAC(ISPECL
   [`table:int64`; `4096`; `4096`; `mlkem_rej_uniform_table`]
   (INST_TYPE [`:8`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  REWRITE_TAC[DIMINDEX_8] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL
   [`buf:int64`; `LENGTH(inlist:(12 word)list)`;
    `buflen:num`; `inlist:(12 word)list`]
   (INST_TYPE [`:12`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  ASM_REWRITE_TAC[DIMINDEX_CONV `dimindex(:12)`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL
   [`res:int64`; `val(n:int64)`; `2 * val(n:int64)`; `curlist:int16 list`]
   (INST_TYPE [`:16`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH_RULE `16 * n = 8 * 2 * n`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN GLOBALIZE_PRECONDITION_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  ENSURES_SEQUENCE_TAC `pc + 0x284`
   `\s. rej_end res buf buflen table curlist inlist
                (word_sub stackpointer (word 32)) s /\
        read events s = APPEND ev e /\
        memaccess_inbounds ev
         [buf,buflen; table,4096; word_sub stackpointer (word 32),32]
         [word_sub stackpointer (word 32),32; res,512]` THEN
  CONJ_TAC THENL
   [ENSURES_SEQUENCE_TAC `pc + 0x82`
     `\s. rej_st res buf buflen table curlist inlist
                 (word_sub stackpointer (word 32)) 0 s /\
          read events s = e` THEN
    CONJ_TAC THENL
     [(*** The setup, which has no events ***)

      REWRITE_TAC[rej_st] THEN
      ASM_SIMP_TAC[REJ_OUT_0; LE_REFL] THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; WORD_VAL] THEN
      CONV_TAC(ONCE_DEPTH_CONV WORD_JOIN_CONV) THEN
      ENSURES_INIT_TAC "s0" THEN
      MAP_EVERY (fun n -> X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC [n] THEN
                          SIMD_SIMPLIFY_TAC[]) (1--22) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

      (*** The loops ***)

      FIRST_X_ASSUM(MP_TAC o
        check (fun th -> can (find_term ((=) `rej_end`)) (concl th))) THEN
      REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]];

    (*** The end, with the result as in MLKEM_REJ_UNIFORM_ALT_CORE ***)

    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    REWRITE_TAC[rej_end; rej_st] THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC o
                  check (is_exists o concl)) THEN
    MP_TAC(SPECL [`curlist:int16 list`; `inlist:(12 word)list`; `buflen:num`;
                  `q:num`] REJ_OUT_FINAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    X86_STEPS_TAC MLKEM_REJ_UNIFORM_ALT_TMC_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN
    REWRITE_TAC[GSYM REJ_SAMPLE] THEN
    FIRST_ASSUM(fun th ->
      if can (term_match [] `rej_out a b c = SUB_LIST(0,256) l`) (concl th)
      then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    MP_TAC(ISPECL
     [`res:int64`; `LENGTH(rej_out curlist inlist q)`;
      `2 * LENGTH(rej_out curlist inlist q)`; `rej_out curlist inlist q`]
     (INST_TYPE [`:16`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
    REWRITE_TAC[DIMINDEX_16; ARITH_RULE `16 * n = 8 * 2 * n`] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
     EXISTS_TAC `ev:(uarch_event)list` THEN ASM_REWRITE_TAC[])]);;

let MLKEM_REJ_UNIFORM_ALT_CORE_FULL = prove
 (MLKEM_REJ_UNIFORM_ALT_CORE_FULL_STMT,
  MP_TAC(REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] REJ_FULL_CORE0) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `res:int64`; `n:int64`; `buf:int64`;
    `buflen:int64`; `table:int64`; `curlist:int16 list`;
    `inlist:(12 word)list`; `pc:num`; `stackpointer:int64`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`res:int64`; `n:int64`; `buf:int64`; `buflen:int64`; `table:int64`;
    `inlist:(12 word)list`; `pc:num`; `stackpointer:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`e:(uarch_event)list`; `curlist:int16 list`]) THEN
  ASM_REWRITE_TAC[]);;

let MLKEM_REJ_UNIFORM_ALT_NOIBT_SUBROUTINE_FULL = time prove
 (MLKEM_REJ_UNIFORM_ALT_NOIBT_SUBROUTINE_FULL_STMT,
  let TWEAK_CONV =
    TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV[wordlist_from_memory] in
  let execth = X86_MK_EXEC_RULE mlkem_rej_uniform_alt_tmc in

  (*** The events of the core, then the load of the return address and the
   *** jump to it
   ***)

  X_CHOOSE_THEN
   `core_events:int64->int64->int64->int64->int64->(12 word)list->num->
                int64->(uarch_event)list`
   (LABEL_TAC "core" o
    REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] o
    CONV_RULE TWEAK_CONV o X86_CORE_PROMOTE)
   MLKEM_REJ_UNIFORM_ALT_CORE_FULL THEN
  EXISTS_TAC
   `\(res:int64) (n:int64) (buf:int64) (buflen:int64) (table:int64)
     (inlist:(12 word)list) (pc:num) (stackpointer:int64)
     (returnaddress:int64).
       CONS (EventJump (word(pc + 0x28f):int64,returnaddress))
        (CONS (EventLoad (stackpointer,8))
          (core_events res n buf buflen table inlist pc stackpointer))` THEN
  CONV_TAC TWEAK_CONV THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN] THEN
  STRIP_TAC THEN
  REMOVE_THEN "core" (MP_TAC o SPECL
   [`e:(uarch_event)list`; `res:int64`; `n:int64`; `buf:int64`;
    `buflen:int64`; `table:int64`; `curlist:int16 list`;
    `inlist:(12 word)list`; `pc:num`; `stackpointer:int64`]) THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; C_RETURN] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC th) THEN
  X86_BIGSTEP_TAC execth "s1" THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  REPEAT STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC execth [2] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** The load of the return address is in the region from
   *** word_sub stackpointer (word 32), the events of the core within the
   *** smaller regions of the core theorem
   ***)

  EXISTS_TAC
   `CONS (EventJump (word(pc + 0x28f):int64,returnaddress:int64))
     (CONS (EventLoad (stackpointer:int64,8))
       ((core_events:int64->int64->int64->int64->int64->(12 word)list->
                     num->int64->(uarch_event)list)
        res n buf buflen table inlist pc stackpointer))` THEN
  ASM_REWRITE_TAC[APPEND] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RAND_CONV)
   [MESON[APPEND] `CONS (a:uarch_event) (CONS b l) = APPEND [a; b] l`] THEN
  GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN CONJ_TAC THENL
   [DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN
    DISJ2_TAC THEN DISJ2_TAC THEN
    SUBGOAL_THEN
     `stackpointer:int64 =
      word_add (word_sub stackpointer (word 32)) (word 32)`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th])
    THENL [CONV_TAC WORD_RULE; CONTAINED_TAC];
    DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC]);;

let MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_FULL = time prove
 (MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_FULL_STMT,
  let TWEAK_CONV =
    TOP_DEPTH_CONV let_CONV THENC
    REWRITE_CONV[wordlist_from_memory] in
  CONV_TAC TWEAK_CONV THEN
  MATCH_ACCEPT_TAC(ADD_IBT_RULE
   (CONV_RULE TWEAK_CONV MLKEM_REJ_UNIFORM_ALT_NOIBT_SUBROUTINE_FULL)));;
