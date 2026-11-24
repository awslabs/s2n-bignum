(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/asm/hash_g_spec.ml";;

let MLKEM_HASH_G_BLOCK = prove
 (MLKEM_HASH_G_BLOCK_STMT,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `A = keccak_absorb 72 (keccak_padded 72 6 m) i` THEN
  ABBREV_TAC
   `B = (num_of_bytelist m DIV 2 EXP (8 * 72 * i)) MOD 2 EXP (8 * 72)` THEN
  SUBGOAL_THEN `~(val(word(LENGTH(m:byte list) - 72 * i):int64) < 72)`
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o lhand o rand o snd) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  (*** The lanes of the state after the block is XORed in ***)

  SUBGOAL_THEN
   `!j. j < 25
        ==> word_subword (word_xor (A:1600 word) (word B)) (64 * j,64):int64 =
            if j < 9
            then word_xor (word_subword A (64 * j,64))
                  (word((num_of_bytelist m DIV
                         2 EXP (8 * (72 * i + 8 * j))) MOD 2 EXP 64))
            else word_subword A (64 * j,64)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`A:1600 word`; `B:num`; `9`; `j:num`] KECCAK_XOR_LANE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "B" THEN
      REWRITE_TAC[ARITH_RULE `64 * 9 = 8 * 72`; MOD_LT_EQ; EXP_EQ_0;
                  ARITH_EQ];
      DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN EXPAND_TAC "B" THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC KECCAK_BLOCK_LANE THEN
    UNDISCH_TAC `j < 9` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The lanes of the state and the words of the block in memory, and
   *** the 256-bit loads of them as joins of their lanes
   ***)

  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[READ_MEMORY_WBYTES_LANES] o
    check (can (term_match [] `read (memory :> wbytes a) s = (x:1600 word)`) o
           concl)) THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
                     ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. j < 9
        ==> read (memory :> bytes64(word_add (word_add inp (word(72 * i)))
                                             (word(8 * j)))) s0 =
            word((num_of_bytelist m DIV 2 EXP (8 * (72 * i + 8 * j))) MOD
                 2 EXP 64)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    MATCH_MP_TAC READ_MEMORY_BYTES64_OF_NUM THEN
    EXISTS_TAC `LENGTH(m:byte list)` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`j < 9`; `72 * (i + 1) <= LENGTH(m:byte list)`] THEN
    ARITH_TAC;
    CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES] THEN STRIP_TAC] THEN
  READ_MEMORY_MERGE256_TAC `s0:x86state`
   [`stackpointer:int64`; `word_add stackpointer (word 32):int64`;
    `word_add inp (word(72 * i)):int64`;
    `word_add (word_add inp (word(72 * i))) (word 32):int64`] THEN
  READ_MEMORY_NORMALIZE_TAC `inp:int64` THEN

  (*** The XOR of the block into the state, and the permutation ***)

  X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--12) THEN
  READ_MEMORY_SPLIT256_TAC `s12:x86state`
   [`stackpointer:int64`; `word_add stackpointer (word 32):int64`] THEN
  X86_STEPS_TAC MLKEM_HASH_G_EXEC [13] THEN
  SUBGOAL_THEN
   `read (memory :> wbytes stackpointer) s13 = word_xor (A:1600 word) (word B)`
  ASSUME_TAC THENL
   [REWRITE_TAC[READ_MEMORY_WBYTES_LANES] THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && can (find_term ((=) `B:num`)) (concl th)
      then SIMP_TAC[th] else NO_TAC) THEN
    CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
             ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE
     `18446744073709551616 = 2 EXP 64`]) THEN
    REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 EXP 64`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[WORD_XOR_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `wordlist_from_memory(c,24) s13 = round_constants`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WORDLIST_FROM_MEMORY_ROUND_CONSTANTS]; ALL_TAC] THEN
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,MLKEM_HASH_G_EXEC,0,
    mlkem_native2_image_mc,SHA3_KECCAK_F1600_ALT2_IMAGE_CORRECT_F1600)
   [`read RDI s`; `read RSI s`; `word_xor (A:1600 word) (word B)`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] 14 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x (word 8)) (word 8):int64 = x`]) THEN
  X86_STEPS_TAC MLKEM_HASH_G_EXEC (15--17) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `72 * (i + 1) = 72 * i + 72`; WORD_ADD;
                WORD_ADD_ASSOC];
    SUBGOAL_THEN
     `LENGTH(m:byte list) - 72 * i = (LENGTH m - 72 * (i + 1)) + 72`
    SUBST1_TAC THENL
     [UNDISCH_TAC `72 * (i + 1) <= LENGTH(m:byte list)` THEN ARITH_TAC;
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    REWRITE_TAC[GSYM ADD1; keccak_absorb] THEN ASM_REWRITE_TAC[ADD1] THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[keccak_padded] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC KECCAK_BLOCK_FULL THEN
    ASM_REWRITE_TAC[]]);;

let MLKEM_HASH_G_WORDS = prove
 (MLKEM_HASH_G_WORDS_STMT,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o
    check (fun th -> concl th = `LENGTH(m:byte list) = 72 * q + t`)) THEN
  SUBGOAL_THEN `t < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `t < 72` THEN ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `t:num` THEN
  SUBGOAL_THEN `word_ushr (word t:int64) 3 = word(t DIV 8)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `t < 72` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t DIV 8 < 9` ASSUME_TAC THENL
   [UNDISCH_TAC `t < 72` THEN ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `t DIV 8` THEN
  SUBGOAL_THEN `val(word t:int64) < 72` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `t DIV 8 = 0` THENL
   [ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; EXP; MOD_1; WORD_XOR_0;
                    WORD_ADD_0];
    ALL_TAC] THEN
  ENSURES_WHILE_PUP_TAC `t DIV 8` `pc + mlkem_hash_g_lastwords`
   (pc_plus "mlkem_hash_g_lastwords" 18)
   `\k s. (read RSP s = stackpointer /\
           read RDI s = word_add stackpointer (word(8 * k)) /\
           read RCX s = word(t DIV 8 - k) /\
           read RBP s = word_add inp (word(72 * q + 8 * k)) /\
           read R12 s = word t /\
           read R13 s = c /\
           read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
           read (memory :> bytes(c,192)) s =
           num_of_wordlist round_constants /\
           read (memory :> wbytes stackpointer) s =
           word_xor (A:1600 word)
            (word((num_of_bytelist m DIV 2 EXP (8 * 72 * q)) MOD
                  2 EXP (64 * k)))) /\
          (read ZF s <=> k = t DIV 8)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(*** The entry, past the test for no whole words ***)

    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; EXP; MOD_1; WORD_XOR_0;
                    WORD_ADD_0; SUB_0];

    (*** The loop body, for word and lane k ***)

    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `k < 25 /\ (72 * q + 8 * k) + 8 <= LENGTH(m:byte list)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`k < t DIV 8`; `t < 72`;
                             `72 * q + t = LENGTH(m:byte list)`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] o
      REWRITE_RULE[READ_MEMORY_WBYTES_LANES] o
      check (can (term_match []
        `read (memory :> wbytes a) s = (x:1600 word)`) o concl)) THEN
    DISCH_THEN(fun th ->
      ASSUME_TAC(MP (SPEC `k:num` th) (ASSUME `k < 25`)) THEN
      ASSUME_TAC(RESTRICT_RULE `k:num` th)) THEN
    MP_TAC(SPECL [`inp:int64`; `LENGTH(m:byte list)`; `num_of_bytelist m`;
                  `72 * q + 8 * k`; `s0:x86state`]
      READ_MEMORY_BYTES64_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--5) THEN
    SUBGOAL_THEN
     `word_sub (word (t DIV 8 - k)) (word 1):int64 = word(t DIV 8 - (k + 1))`
    SUBST_ALL_TAC THENL
     [SUBGOAL_THEN `t DIV 8 - k = (t DIV 8 - (k + 1)) + 1` SUBST1_TAC THENL
       [UNDISCH_TAC `k < t DIV 8` THEN ARITH_TAC;
        REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
      ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[READ_MEMORY_WBYTES_LANES] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      ASM_SIMP_TAC[LANE_XOR_STEP] THEN COND_CASES_TAC THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE
          `8 * 72 * q + 64 * k = 8 * (72 * q + 8 * k)`];
        ASM_SIMP_TAC[]];
      REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
      SUBGOAL_THEN `t DIV 8 - (k + 1) < 2 EXP 64`
       (fun th -> SIMP_TAC[MOD_LT; th]) THENL
       [UNDISCH_TAC `t DIV 8 < 9` THEN ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `k < t DIV 8` THEN ARITH_TAC];

    (*** The backward branch ***)

    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLKEM_HASH_G_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The exit to the single bytes ***)

    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLKEM_HASH_G_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let MLKEM_HASH_G_BYTES = prove
 (MLKEM_HASH_G_BYTES_STMT,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o
    check (fun th -> concl th = `LENGTH(m:byte list) = 72 * q + t`)) THEN
  SUBGOAL_THEN `t < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `t < 72` THEN ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `t:num` THEN
  SUBGOAL_THEN `t MOD 8 < 8` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `t MOD 8` THEN
  MP_TAC(SPEC `t:num` WORD_AND_7_ZX32) THEN
  ANTS_TAC THENL [UNDISCH_TAC `t < 72` THEN ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `num_of_bytelist m DIV 2 EXP (8 * 72 * q) < 2 EXP (8 * t)`
  ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; GSYM MULT_ASSOC] THEN
    ASM_REWRITE_TAC[GSYM EXP_EXP] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN
    REWRITE_TAC[NUM_OF_BYTELIST_BOUND];
    ALL_TAC] THEN
  ASM_CASES_TAC `t MOD 8 = 0` THENL
   [SUBGOAL_THEN `8 * t DIV 8 = t` ASSUME_TAC THENL
     [MP_TAC(SPECL [`t:num`; `8`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE `64 * t DIV 8 = 8 * (8 * t DIV 8)`] THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  ENSURES_WHILE_PUP_TAC `t MOD 8` `pc + mlkem_hash_g_lastbyte`
   (pc_plus "mlkem_hash_g_lastbyte" 15)
   `\k s. (read RSP s = stackpointer /\
           read RDI s = word_add stackpointer (word(8 * t DIV 8 + k)) /\
           read RCX s = word(t MOD 8 - k) /\
           read RBP s = word_add inp (word(72 * q + 8 * t DIV 8 + k)) /\
           read R12 s = word t /\
           read R13 s = c /\
           read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
           read (memory :> bytes(c,192)) s =
           num_of_wordlist round_constants /\
           read (memory :> wbytes stackpointer) s =
           word_xor (A:1600 word)
            (word((num_of_bytelist m DIV 2 EXP (8 * 72 * q)) MOD
                  2 EXP (8 * (8 * t DIV 8 + k))))) /\
          (read ZF s <=> k = t MOD 8)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(*** The entry, past the test for no single bytes ***)

    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; SUB_0;
                    ARITH_RULE `8 * 8 * t DIV 8 = 64 * t DIV 8`];

    (*** The loop body, for byte 8 * t DIV 8 + k ***)

    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `8 * t DIV 8 + k < 200 /\
      72 * q + 8 * t DIV 8 + k < LENGTH(m:byte list)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`k < t MOD 8`; `t < 72`;
                             `72 * q + t = LENGTH(m:byte list)`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] o
      REWRITE_RULE[READ_MEMORY_WBYTES_BYTES] o
      check (can (term_match []
        `read (memory :> wbytes a) s = (x:1600 word)`) o concl)) THEN
    DISCH_THEN(fun th ->
      ASSUME_TAC(MP (SPEC `8 * t DIV 8 + k` th)
                    (ASSUME `8 * t DIV 8 + k < 200`)) THEN
      ASSUME_TAC(RESTRICT_RULE `8 * t DIV 8 + k` th)) THEN
    MP_TAC(SPECL [`inp:int64`; `LENGTH(m:byte list)`; `num_of_bytelist m`;
                  `72 * q + 8 * t DIV 8 + k`; `s0:x86state`]
      READ_MEMORY_BYTES8_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--5) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BYTE_ZX_X86]) THEN
    SUBGOAL_THEN
     `word_sub (word (t MOD 8 - k)) (word 1):int64 = word(t MOD 8 - (k + 1))`
    SUBST_ALL_TAC THENL
     [SUBGOAL_THEN `t MOD 8 - k = (t MOD 8 - (k + 1)) + 1` SUBST1_TAC THENL
       [UNDISCH_TAC `k < t MOD 8` THEN ARITH_TAC;
        REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
      ALL_TAC] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[READ_MEMORY_WBYTES_BYTES] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      REWRITE_TAC[ARITH_RULE
       `8 * t DIV 8 + k + 1 = (8 * t DIV 8 + k) + 1`] THEN
      ASM_SIMP_TAC[BYTE_XOR_STEP] THEN COND_CASES_TAC THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 8 = 256`;
                    ARITH_RULE `8 * 72 * q + 8 * (8 * t DIV 8 + k) =
                                8 * (72 * q + 8 * t DIV 8 + k)`];
        ASM_SIMP_TAC[]];
      REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
      SUBGOAL_THEN `t MOD 8 - (k + 1) < 2 EXP 64`
       (fun th -> SIMP_TAC[MOD_LT; th]) THENL
       [UNDISCH_TAC `t MOD 8 < 8` THEN ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `k < t MOD 8` THEN ARITH_TAC];

    (*** The backward branch ***)

    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLKEM_HASH_G_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The exit to the padding ***)

    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLKEM_HASH_G_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `8 * t DIV 8 + t MOD 8 = t` SUBST1_TAC THENL
     [MP_TAC(SPECL [`t:num`; `8`] DIVISION) THEN ARITH_TAC;
      ASM_SIMP_TAC[MOD_LT]]]);;

let MLKEM_HASH_G_PAD = prove
 (MLKEM_HASH_G_PAD_STMT,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The domain byte at byte t ***)

  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] o
    REWRITE_RULE[READ_MEMORY_WBYTES_BYTES] o
    check (can (term_match [] `read (memory :> wbytes a) s = (x:1600 word)`) o
           concl)) THEN
  DISCH_THEN(fun th ->
    ASSUME_TAC(MP (SPEC `t:num` th)
                  (MP (ARITH_RULE `t < 72 ==> t < 200`)
                      (ASSUME `t < 72`))) THEN
    ASSUME_TAC(RESTRICT_RULE `t:num` th)) THEN
  X86_STEPS_TAC MLKEM_HASH_G_EXEC [1] THEN
  SUBGOAL_THEN
   `!j. j < 200
        ==> read (memory :> bytes8 (word_add stackpointer (word j))) s1 =
            word_subword (word_xor (A:1600 word) (word(2 EXP (8 * t) * 6)))
                         (8 * j,8)`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[BYTE_XOR_SHIFT; ARITH_RULE `6 < 256`;
                 ARITH_RULE `t < 72 ==> t < 200`] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
DISCH_THEN(fun th ->
    ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV
      (MP (SPEC `71` th) (ARITH_RULE `71 < 200`))) THEN
    ASSUME_TAC(RESTRICT_RULE `71` th)) THEN
  X86_STEPS_TAC MLKEM_HASH_G_EXEC [2] THEN
X86_STEPS_TAC MLKEM_HASH_G_EXEC (3--5) THEN
  SUBGOAL_THEN
   `read (memory :> wbytes stackpointer) s5 =
    word_xor (word_xor (A:1600 word) (word(2 EXP (8 * t) * 6)))
             (word(2 EXP (8 * 71) * 128))`
  ASSUME_TAC THENL
   [REWRITE_TAC[READ_MEMORY_WBYTES_BYTES] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[BYTE_XOR_SHIFT; ARITH_RULE `128 < 256 /\ 71 < 200`] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `wordlist_from_memory(c,24) s5 = round_constants`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WORDLIST_FROM_MEMORY_ROUND_CONSTANTS]; ALL_TAC] THEN
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,MLKEM_HASH_G_EXEC,0,
    mlkem_native2_image_mc,SHA3_KECCAK_F1600_ALT2_IMAGE_CORRECT_F1600)
   [`read RDI s`; `read RSI s`;
    `word_xor (word_xor (A:1600 word) (word(2 EXP (8 * t) * 6)))
              (word(2 EXP (8 * 71) * 128))`;
    `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`] 6 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
   `word_add (word_sub x (word 8)) (word 8):int64 = x`]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let MLKEM_HASH_G_TAIL = prove
 (MLKEM_HASH_G_TAIL_STMT,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC[KECCAK_LAST_BLOCK_XOR; ARITH_RULE `0 < 72 /\ 6 < 128`] THEN
  REWRITE_TAC[ARITH_RULE `72 - 1 = 71`] THEN
  ABBREV_TAC `q = LENGTH(m:byte list) DIV 72` THEN
  ABBREV_TAC `t = LENGTH(m:byte list) MOD 72` THEN
  ABBREV_TAC `A = keccak_absorb 72 (keccak_padded 72 6 m) q` THEN
  SUBGOAL_THEN `LENGTH(m:byte list) = 72 * q + t /\ t < 72`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
    MP_TAC(SPECL [`LENGTH(m:byte list)`; `72`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(m:byte list) - 72 * q = t` SUBST1_TAC THENL
   [UNDISCH_TAC `LENGTH(m:byte list) = 72 * q + t` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  ENSURES_SEQUENCE_TAC `pc + mlkem_hash_g_lastbytes`
   `\s. read RSP s = stackpointer /\
        read RDI s = word_add stackpointer (word(8 * t DIV 8)) /\
        read RBP s = word_add inp (word(72 * q + 8 * t DIV 8)) /\
        read R12 s = word t /\
        read R13 s = c /\
        read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
        read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
        read (memory :> wbytes stackpointer) s =
        word_xor (A:1600 word)
         (word((num_of_bytelist m DIV 2 EXP (8 * 72 * q)) MOD
               2 EXP (64 * t DIV 8)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
                   MLKEM_HASH_G_WORDS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + mlkem_hash_g_pad`
   `\s. read RSP s = stackpointer /\
        read RDI s = word_add stackpointer (word t) /\
        read R13 s = c /\
        read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
        read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
        read (memory :> wbytes stackpointer) s =
        word_xor (A:1600 word)
         (word(num_of_bytelist m DIV 2 EXP (8 * 72 * q)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
                   MLKEM_HASH_G_BYTES) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
                   MLKEM_HASH_G_PAD) THEN
    ASM_REWRITE_TAC[]]);;

let MLKEM_HASH_G_ABSORB = prove
 (MLKEM_HASH_G_ABSORB_STMT,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ; LE_EXISTS] THEN
  REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` MP_TAC) THEN
  SPEC_TAC(`i:num`,`i:num`) THEN SPEC_TAC(`d:num`,`d:num`) THEN
  INDUCT_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o REWRITE_RULE[ADD_CLAUSES]) THEN
    MATCH_MP_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
                   MLKEM_HASH_G_TAIL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + mlkem_hash_g_block`
   `\s. read RSP s = stackpointer /\
        read RBP s = word_add inp (word(72 * (i + 1))) /\
        read R12 s = word(LENGTH m - 72 * (i + 1)) /\
        read R13 s = c /\
        read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
        read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
        read (memory :> wbytes stackpointer) s =
        keccak_absorb 72 (keccak_padded 72 6 m) (i + 1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
                   MLKEM_HASH_G_BLOCK) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`LENGTH(m:byte list)`; `72`] DIVISION) THEN
    UNDISCH_TAC `LENGTH(m:byte list) DIV 72 = i + SUC d` THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `i + 1`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `LENGTH(m:byte list) DIV 72 = i + SUC d` THEN ARITH_TAC;
      SIMP_TAC[]]]);;

let MLKEM_HASH_G_ABSORB_0 = prove
 (MLKEM_HASH_G_ABSORB_0_STMT,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`m:byte list`; `inp:int64`; `c:int64`; `pc:num`;
                `stackpointer:int64`; `0`] MLKEM_HASH_G_ABSORB) THEN
  ASM_REWRITE_TAC[LE_0; MULT_CLAUSES; SUB_0; WORD_ADD_0;
                  CONJUNCT1 keccak_absorb] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    (ONCE_REWRITE_RULE[CONJ_SYM] ENSURES_POSTCONDITION_THM))) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_HASH_G_ASM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_HASH_G_ASM_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`out:int64`; `inp:int64`; `m:byte list`; `c:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 256 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `LENGTH(m:byte list) < 2 EXP 64` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `256 + l <= 2 EXP 64 ==> l < 2 EXP 64`) THEN
    MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(stackpointer:int64)`; `val(inp:int64)`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORDLIST_FROM_MEMORY_ROUND_CONSTANTS]) THEN
  X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--18) THEN
  SUBGOAL_THEN
   `read (memory :> wbytes (word_add stackpointer (word 8))) s18 =
    (word 0:1600 word)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC READ_MEMORY_WBYTES_ZERO THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[WORD_ADD_0];
    ALL_TAC] THEN
  X86_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,MLKEM_HASH_G_EXEC,0,
    mlkem_native2_image_mc,MLKEM_HASH_G_ABSORB_0_AT)
   [`m:byte list`; `inp:int64`; `c:int64`; `pc:num`;
    `stackpointer:int64`] 19 THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match []
    `read (memory :> wbytes a) s19 = keccak_f1600 x`) o concl)) THEN
  ABBREV_TAC
   `S = keccak_f1600
         (word_xor
           (keccak_absorb 72 (keccak_padded 72 6 m) (LENGTH m DIV 72))
           (word((keccak_padded 72 6 m DIV
                  2 EXP (8 * 72 * LENGTH m DIV 72)) MOD 2 EXP (8 * 72))))`
  THEN
  REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN DISCH_TAC THEN
  MAP_EVERY (fun k ->
    MP_TAC(SPECL [`word_add stackpointer (word 8):int64`; `200`;
                  `val(S:1600 word)`; k; `s19:x86state`]
      READ_MEMORY_BYTES256_OF_NUM))
   [`0`; `32`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[WORD_ADD_0; DIV_1] THEN REPEAT DISCH_TAC THEN
  X86_STEPS_TAC MLKEM_HASH_G_EXEC (20--38) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`out:int64`; `2`; `val(S:1600 word)`; `s38:x86state`]
    READ_MEMORY_BYTES_OF_BYTES256) THEN
  CONV_TAC(LAND_CONV(LAND_CONV EXPAND_CASES_CONV)) THEN
  CONV_TAC(LAND_CONV(LAND_CONV NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[ARITH_RULE `32 * 2 = 64 /\ 256 * 2 = 512`] THEN
  ASM_REWRITE_TAC[WORD_ADD_0; DIV_1] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[sha3_512] THEN
  MP_TAC(SPECL [`1024`; `6`; `m:byte list`; `72`; `keccak_padded 72 6 m`;
                `64`] KECCAK_SPONGE_BYTES) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[keccak_padded] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 64 = 512`]);;

let MLKEM_NATIVE_HASH_G_ASM_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_HASH_G_ASM_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC SHA3_KECCAK_F1600_ALT2_IMAGE_SAFE
    "H_KECCAK" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(inp:int64) (len:num) (c:int64) (out:int64) (pc:num)
     (stackpointer:int64) (returnaddress:int64).
      APPEND (f_ev_fin inp len c out pc stackpointer returnaddress)
       (APPEND
         (if (len MOD 72) MOD 8 = 0
          then f_ev_bskip inp len c out pc stackpointer returnaddress
          else APPEND (f_ev_bexit inp len c out pc stackpointer returnaddress)
                (APPEND
                  (ENUMERATEL ((len MOD 72) MOD 8)
                    (\k. f_ev_byte inp len c out pc stackpointer
                                   returnaddress k))
                  (f_ev_bentry inp len c out pc stackpointer returnaddress)))
         (APPEND
           (if (len MOD 72) DIV 8 = 0
            then f_ev_wskip inp len c out pc stackpointer returnaddress
            else APPEND
                  (f_ev_wexit inp len c out pc stackpointer returnaddress)
                  (APPEND
                    (ENUMERATEL ((len MOD 72) DIV 8)
                      (\k. f_ev_word inp len c out pc stackpointer
                                     returnaddress k))
                    (f_ev_wentry inp len c out pc stackpointer
                                 returnaddress)))
           (if len DIV 72 = 0
            then f_ev_lskip inp len c out pc stackpointer returnaddress
            else APPEND
                  (f_ev_lexit inp len c out pc stackpointer returnaddress)
                  (APPEND
                    (ENUMERATEL (len DIV 72)
                      (\i. f_ev_block inp len c out pc stackpointer
                                      returnaddress i))
                    (f_ev_prol inp len c out pc stackpointer
                               returnaddress)))))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `len < 2 EXP 64` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `256 + l <= 2 EXP 64 ==> l < 2 EXP 64`) THEN
    MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(stackpointer:int64)`; `val(inp:int64)`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `72 * len DIV 72 + len MOD 72 = len /\ len MOD 72 < 72`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`len:num`; `72`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word(len MOD 72):int64) = len MOD 72` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `len MOD 72 < 72` THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN

  (*** Split at the padding, the single bytes and the last block ***)

  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_hash_g_pad`
   (mlkem_hash_g_inv
    `read RSP s = word_add stackpointer (word 8) /\
     read RDI s = word_add stackpointer (word (8 + len MOD 72)) /\
     read RBX s = out /\ read R13 s = c`) THEN
  CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_hash_g_lastbytes`
     (mlkem_hash_g_inv
      `read RSP s = word_add stackpointer (word 8) /\
       read RDI s =
       word_add stackpointer (word (8 + 8 * (len MOD 72) DIV 8)) /\
       read RBP s =
       word_add inp (word (72 * len DIV 72 + 8 * (len MOD 72) DIV 8)) /\
       read R12 s = word (len MOD 72) /\
       read RBX s = out /\ read R13 s = c`) THEN
    CONJ_TAC THENL
     [ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_hash_g_last`
       (mlkem_hash_g_inv
        `read RSP s = word_add stackpointer (word 8) /\
         read RBP s = word_add inp (word (72 * len DIV 72)) /\
         read R12 s = word (len MOD 72) /\
         read RBX s = out /\ read R13 s = c`) THEN
      CONJ_TAC THENL
       [(*** The prologue and the whole blocks ***)

        ASM_CASES_TAC `len DIV 72 = 0` THEN ASM_REWRITE_TAC[] THENL
         [SUBGOAL_THEN `len < 72` ASSUME_TAC THENL
           [MP_TAC(SPECL [`len:num`; `72`] DIVISION) THEN
            ASM_REWRITE_TAC[] THEN ARITH_TAC;
            ALL_TAC] THEN
          VAL_INT64_TAC `len:num` THEN
          ASM_SIMP_TAC[MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
          REWRITE_TAC(!simulation_precanon_thms) THEN
          ENSURES_INIT_TAC "s0" THEN
          X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--20) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          DISCHARGE_SAFETY_PROPERTY_TAC;
          ALL_TAC] THEN
        ENSURES_EVENTS_WHILE_UP2_TAC `len DIV 72` `pc + mlkem_hash_g_block`
         `pc + mlkem_hash_g_block`
         (mlkem_hash_g_loop_inv
          `read RSP s = word_add stackpointer (word 8) /\
           read RBP s = word_add inp (word (72 * i)) /\
           read R12 s = word (len - 72 * i) /\
           read RBX s = out /\ read R13 s = c`) THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[];

          REWRITE_TAC(!simulation_precanon_thms) THEN
          ENSURES_INIT_TAC "s0" THEN
          X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--18) THEN
          ENSURES_FINAL_STATE_TAC THEN
          ASM_REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
          DISCHARGE_SAFETY_PROPERTY_TAC;

          X_GEN_TAC `i:num` THEN STRIP_TAC THEN
          SUBGOAL_THEN `72 * (i + 1) <= len` ASSUME_TAC THENL
           [MP_TAC(SPECL [`len:num`; `72`] DIVISION) THEN
            UNDISCH_TAC `i < len DIV 72` THEN ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN `~(val(word(len - 72 * i):int64) < 72)`
          ASSUME_TAC THENL
           [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
            W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o lhand o rand o snd)
            THEN ANTS_TAC THENL
             [UNDISCH_TAC `len < 2 EXP 64` THEN ARITH_TAC;
              DISCH_THEN SUBST1_TAC] THEN
            UNDISCH_TAC `72 * (i + 1) <= len` THEN ARITH_TAC;
            ALL_TAC] THEN
          REWRITE_TAC(!simulation_precanon_thms) THEN
          ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
          X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--13) THEN
          MLKEM_HASH_G_SAFE_CALL_TAC [`i:num`] 14 THEN
          X86_STEPS_TAC MLKEM_HASH_G_EXEC (15--17) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[COND_ID] THEN
          REPEAT CONJ_TAC THENL
           [REWRITE_TAC[ARITH_RULE `72 * (i + 1) = 72 * i + 72`; WORD_ADD;
                        WORD_ADD_ASSOC];
            SUBGOAL_THEN `len - 72 * i = (len - 72 * (i + 1)) + 72`
            SUBST1_TAC THENL
             [UNDISCH_TAC `72 * (i + 1) <= len` THEN ARITH_TAC;
              REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
            DISCHARGE_SAFETY_PROPERTY_TAC];

          SUBGOAL_THEN `len - 72 * len DIV 72 = len MOD 72` SUBST1_TAC THENL
           [UNDISCH_TAC `72 * len DIV 72 + len MOD 72 = len` THEN ARITH_TAC;
            ALL_TAC] THEN
          REWRITE_TAC(!simulation_precanon_thms) THEN
          ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
          X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--2) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          DISCHARGE_SAFETY_PROPERTY_TAC];

        (*** The whole words of the last block ***)

        SUBGOAL_THEN
         `word_ushr (word (len MOD 72):int64) 3 = word((len MOD 72) DIV 8)`
        ASSUME_TAC THENL
         [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR] THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
          CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
          UNDISCH_TAC `len MOD 72 < 72` THEN ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN
         `val(word((len MOD 72) DIV 8):int64) = (len MOD 72) DIV 8`
        ASSUME_TAC THENL
         [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
          UNDISCH_TAC `len MOD 72 < 72` THEN ARITH_TAC;
          ALL_TAC] THEN
        ASM_CASES_TAC `(len MOD 72) DIV 8 = 0` THEN ASM_REWRITE_TAC[] THENL
         [REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
          REWRITE_TAC(!simulation_precanon_thms) THEN
          ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
          X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--4) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          DISCHARGE_SAFETY_PROPERTY_TAC;
          ALL_TAC] THEN
        ENSURES_EVENTS_WHILE_UP2_TAC `(len MOD 72) DIV 8`
         `pc + mlkem_hash_g_lastwords` `pc + mlkem_hash_g_lastbytes`
         (mlkem_hash_g_loop_inv
          `read RSP s = word_add stackpointer (word 8) /\
           read RDI s = word_add stackpointer (word (8 + 8 * i)) /\
           read RCX s = word ((len MOD 72) DIV 8 - i) /\
           read RBP s = word_add inp (word (72 * len DIV 72 + 8 * i)) /\
           read R12 s = word (len MOD 72) /\
           read RBX s = out /\ read R13 s = c`) THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[];

          REWRITE_TAC(!simulation_precanon_thms) THEN
          ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
          X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--4) THEN
          ENSURES_FINAL_STATE_TAC THEN
          ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0; WORD_ADD_0] THEN
          DISCHARGE_SAFETY_PROPERTY_TAC;

          X_GEN_TAC `k:num` THEN STRIP_TAC THEN
          SUBGOAL_THEN `(72 * len DIV 72 + 8 * k) + 8 <= len`
          ASSUME_TAC THENL
           [MAP_EVERY UNDISCH_TAC
             [`k < (len MOD 72) DIV 8`;
              `72 * len DIV 72 + len MOD 72 = len`] THEN
            ARITH_TAC;
            ALL_TAC] THEN
          REWRITE_TAC(!simulation_precanon_thms) THEN
          ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
          X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--6) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          MLKEM_HASH_G_COUNTER_TAC `(len MOD 72) DIV 8` `k:num` THEN
          REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
           [COND_CASES_TAC THEN REWRITE_TAC[];
            REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
            AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
            REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
            AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
            DISCHARGE_SAFETY_PROPERTY_TAC];

          REWRITE_TAC(!simulation_precanon_thms) THEN
          ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          DISCHARGE_SAFETY_PROPERTY_TAC]];

      (*** The single bytes of the last block ***)

      MP_TAC(SPEC `len MOD 72` WORD_AND_7_ZX32) THEN
      ANTS_TAC THENL [ARITH_TAC; STRIP_TAC] THEN
      SUBGOAL_THEN
       `val(word((len MOD 72) MOD 8):int64) = (len MOD 72) MOD 8`
      ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `8 * (len MOD 72) DIV 8 + (len MOD 72) MOD 8 = len MOD 72`
      ASSUME_TAC THENL
       [MP_TAC(SPECL [`len MOD 72`; `8`] DIVISION) THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_CASES_TAC `(len MOD 72) MOD 8 = 0` THEN ASM_REWRITE_TAC[] THENL
       [SUBGOAL_THEN `8 * (len MOD 72) DIV 8 = len MOD 72` ASSUME_TAC THENL
         [UNDISCH_TAC
           `8 * (len MOD 72) DIV 8 + (len MOD 72) MOD 8 = len MOD 72` THEN
          ASM_REWRITE_TAC[ADD_CLAUSES];
          ALL_TAC] THEN
        REWRITE_TAC(!simulation_precanon_thms) THEN
        ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
        X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--3) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;
        ALL_TAC] THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `(len MOD 72) MOD 8`
       `pc + mlkem_hash_g_lastbyte` `pc + mlkem_hash_g_pad`
       (mlkem_hash_g_loop_inv
        `read RSP s = word_add stackpointer (word 8) /\
         read RDI s =
         word_add stackpointer (word (8 + 8 * (len MOD 72) DIV 8 + i)) /\
         read RCX s = word ((len MOD 72) MOD 8 - i) /\
         read RBP s =
         word_add inp
          (word (72 * len DIV 72 + 8 * (len MOD 72) DIV 8 + i)) /\
         read R12 s = word (len MOD 72) /\
         read RBX s = out /\ read R13 s = c`) THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];

        REWRITE_TAC(!simulation_precanon_thms) THEN
        ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
        X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--3) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;

        (*** For the offset nw of the single bytes, an abbreviation, as   ***)
        (*** the arithmetic of the simulation fails with its DIV and MOD  ***)

        X_GEN_TAC `k:num` THEN STRIP_TAC THEN
        ABBREV_TAC `nw = (len MOD 72) DIV 8` THEN
        SUBGOAL_THEN
         `(72 * len DIV 72 + 8 * nw + k) + 1 <= len /\ 8 * nw + k < 72`
        STRIP_ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC
           [`k < (len MOD 72) MOD 8`; `72 * len DIV 72 + len MOD 72 = len`;
            `8 * nw + (len MOD 72) MOD 8 = len MOD 72`;
            `len MOD 72 < 72`] THEN
          ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC(!simulation_precanon_thms) THEN
        ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
        X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--6) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        MLKEM_HASH_G_COUNTER_TAC `(len MOD 72) MOD 8` `k:num` THEN
        REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [COND_CASES_TAC THEN REWRITE_TAC[];
          REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
          REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
          MLKEM_HASH_G_DISCHARGE_TAC (EXPAND_TAC "nw") false];

        REWRITE_TAC(!simulation_precanon_thms) THEN
        ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC]];

    (*** The padding, the last permutation, the digest and the return ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_HASH_G_EXEC (1--5) THEN
    MLKEM_HASH_G_SAFE_CALL_TAC [] 6 THEN
    X86_STEPS_TAC MLKEM_HASH_G_EXEC (7--25) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MLKEM_HASH_G_DISCHARGE_TAC ALL_TAC true]);;
