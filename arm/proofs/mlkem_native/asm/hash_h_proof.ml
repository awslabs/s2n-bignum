(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The hash H of ML-KEM, SHA3-256 of FIPS 202, with the x1 Keccak            *)
(* permutation sha3_keccak_f1600, in the mlkem_native2 image.                *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/asm/hash_h_spec.ml";;
needs "arm/proofs/utils/mlkem_native2_sponge.ml";;

(**** The function's code is arm/mlkem_native/asm/mlkem_hash_h.S. Its frame of
 **** 256 bytes has the saved registers at sp and the 200-byte state at
 **** sp + 48, and sha3_keccak_f1600 uses 128 bytes below it.
 ****)

let MLKEM_HASH_H_EXEC = MLKEM_NATIVE2_IMAGE_EXEC ["mlkem_hash_h"];;

let pc_plus name off =
  parse_term (Printf.sprintf "pc + %d" (layout name + off));;

(* ------------------------------------------------------------------------- *)
(* One whole block of 136 bytes of the message m at inp, as for              *)
(* keccak_absorb on the padded message, from the test at the start of the    *)
(* loop back to it. Here stackpointer is the stack pointer of the function   *)
(* after its frame is made. The round constants are bytes in memory, which   *)
(* the simulation keeps, unlike wordlist_from_memory.                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_HASH_H_BLOCK = prove
 (`!m inp c i pc stackpointer.
    LENGTH m < 2 EXP 64 /\ 136 * (i + 1) <= LENGTH m /\
    aligned 16 stackpointer /\
    ALL (nonoverlapping (word_add stackpointer (word 48),200))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192)] /\
    ALL (nonoverlapping (word_sub stackpointer (word 128),128))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192);
         (word_add stackpointer (word 48),200)]
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read PC s = word(pc + mlkem_hash_h_block) /\
          read SP s = stackpointer /\
          read X20 s = word_add inp (word(136 * i)) /\
          read X21 s = word(LENGTH m - 136 * i) /\
          read X22 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes(word_add stackpointer (word 48))) s =
          keccak_absorb 136 (keccak_padded 136 6 m) i)
     (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read PC s = word(pc + mlkem_hash_h_block) /\
          read SP s = stackpointer /\
          read X20 s = word_add inp (word(136 * (i + 1))) /\
          read X21 s = word(LENGTH m - 136 * (i + 1)) /\
          read X22 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes(word_add stackpointer (word 48))) s =
          keccak_absorb 136 (keccak_padded 136 6 m) (i + 1))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X20; X21; X30] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 48),200);
                 memory :> bytes(word_sub stackpointer (word 128),128)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `A = keccak_absorb 136 (keccak_padded 136 6 m) i` THEN
  ABBREV_TAC
   `B = (num_of_bytelist m DIV 2 EXP (8 * 136 * i)) MOD 2 EXP (8 * 136)` THEN
  SUBGOAL_THEN `~(val(word(LENGTH(m:byte list) - 136 * i):int64) < 136)`
  ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o lhand o rand o snd) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN

  (*** The lanes of the state after the block is XORed in ***)

  SUBGOAL_THEN
   `!j. j < 25
        ==> word_subword (word_xor (A:1600 word) (word B)) (64 * j,64):int64 =
            if j < 17
            then word_xor (word_subword A (64 * j,64))
                  (word((num_of_bytelist m DIV
                         2 EXP (8 * (136 * i + 8 * j))) MOD 2 EXP 64))
            else word_subword A (64 * j,64)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`A:1600 word`; `B:num`; `17`; `j:num`] KECCAK_XOR_LANE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "B" THEN
      REWRITE_TAC[ARITH_RULE `64 * 17 = 8 * 136`; MOD_LT_EQ; EXP_EQ_0;
                  ARITH_EQ];
      DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN EXPAND_TAC "B" THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC KECCAK_BLOCK_LANE THEN
    UNDISCH_TAC `j < 17` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The lanes of the state and the words of the block in memory ***)

  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[READ_MEMORY_WBYTES_LANES] o
    check (can (term_match [] `read (memory :> wbytes a) s = (x:1600 word)`) o
           concl)) THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
                     ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. j < 17
        ==> read (memory :> bytes64(word_add inp (word(136 * i + 8 * j)))) s0 =
            word((num_of_bytelist m DIV 2 EXP (8 * (136 * i + 8 * j))) MOD
                 2 EXP 64)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC READ_MEMORY_BYTES64_OF_NUM THEN
    EXISTS_TAC `LENGTH(m:byte list)` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`j < 17`; `136 * (i + 1) <= LENGTH(m:byte list)`] THEN
    ARITH_TAC;
    CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV)) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC] THEN
  W(fun (asl,w) ->
    let ths = filter (fun th ->
      can (term_match [`inp:int64`]
            `read (memory :> bytes64 (word_add inp (word(n + k)))) s =
             (y:int64)`) (concl th)) (map snd asl) in
    MAP_EVERY (ASSUME_TAC o REWRITE_RULE[WORD_ADD_SPLIT_OFFSET]) ths) THEN

  (*** The XOR of the block into the state, and the permutation ***)

  ARM_STEPS_TAC MLKEM_HASH_H_EXEC (1--49) THEN
  SUBGOAL_THEN
   `read (memory :> wbytes (word_add stackpointer (word 48))) s49 =
    word_xor (A:1600 word) (word B)`
  ASSUME_TAC THENL
   [REWRITE_TAC[READ_MEMORY_WBYTES_LANES] THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && can (find_term ((=) `B:num`)) (concl th)
      then SIMP_TAC[th] else NO_TAC) THEN
    CONV_TAC(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV THENC
             ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `18446744073709551616 = 2 EXP 64`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wordlist_from_memory(c,24) s49 = round_constants`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WORDLIST_FROM_MEMORY_ROUND_CONSTANTS]; ALL_TAC] THEN
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,MLKEM_HASH_H_EXEC,layout "sha3_keccak_f1600",
    sha3_keccak_f1600_mc,SHA3_KECCAK_F1600_SUBROUTINE_CORRECT_F1600)
   [`read X0 s`; `read X1 s`; `word_xor (A:1600 word) (word B)`;
    `pc + sha3_keccak_f1600`; `read SP s`; `read X30 s`] 50 THEN
  ARM_STEPS_TAC MLKEM_HASH_H_EXEC (51--52) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `136 * (i + 1) = 136 * i + 136`; WORD_ADD;
                WORD_ADD_ASSOC];
    SUBGOAL_THEN
     `LENGTH(m:byte list) - 136 * i = (LENGTH m - 136 * (i + 1)) + 136`
    SUBST1_TAC THENL
     [UNDISCH_TAC `136 * (i + 1) <= LENGTH(m:byte list)` THEN ARITH_TAC;
      REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
    REWRITE_TAC[GSYM ADD1; keccak_absorb] THEN ASM_REWRITE_TAC[ADD1] THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[keccak_padded] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC KECCAK_BLOCK_FULL THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The last t < 136 bytes of the message, after q whole blocks, from the     *)
(* exit of the loop above to the padding: first the t DIV 8 whole words,     *)
(* each XORed into a lane of the state A, then the t MOD 8 single bytes.     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_HASH_H_WORDS = prove
 (`!m inp c pc stackpointer q t (A:1600 word).
    LENGTH(m:byte list) = 136 * q + t /\ t < 136 /\ LENGTH m < 2 EXP 64 /\
    aligned 16 stackpointer /\
    ALL (nonoverlapping (word_add stackpointer (word 48),200))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192)]
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read PC s = word(pc + mlkem_hash_h_block) /\
          read SP s = stackpointer /\
          read X20 s = word_add inp (word(136 * q)) /\
          read X21 s = word t /\
          read X22 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes(word_add stackpointer (word 48))) s = A)
     (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read PC s = word(pc + mlkem_hash_h_lastbytes) /\
          read SP s = stackpointer /\
          read X0 s = word_add stackpointer (word(48 + 8 * t DIV 8)) /\
          read X20 s = word_add inp (word(136 * q + 8 * t DIV 8)) /\
          read X21 s = word t /\
          read X22 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes(word_add stackpointer (word 48))) s =
          word_xor A (word((num_of_bytelist m DIV 2 EXP (8 * 136 * q)) MOD
                           2 EXP (64 * t DIV 8))))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X20; X21; X30] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 48),200);
                 memory :> bytes(word_sub stackpointer (word 128),128)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o
    check (fun th -> concl th = `LENGTH(m:byte list) = 136 * q + t`)) THEN
  SUBGOAL_THEN `t < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `t < 136` THEN ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `t:num` THEN
  SUBGOAL_THEN `word_ushr (word t:int64) 3 = word(t DIV 8)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `t < 136` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `t DIV 8 < 17` ASSUME_TAC THENL
   [UNDISCH_TAC `t < 136` THEN ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `t DIV 8` THEN
  ASM_CASES_TAC `t DIV 8 = 0` THENL
   [ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLKEM_HASH_H_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; EXP; MOD_1; WORD_XOR_0;
                    WORD_ADD_0];
    ALL_TAC] THEN
  ENSURES_WHILE_PUP_TAC `t DIV 8` `pc + mlkem_hash_h_lastwords`
   (pc_plus "mlkem_hash_h_lastwords" 20)
   `\k s. (read SP s = stackpointer /\
           read X0 s = word_add stackpointer (word(48 + 8 * k)) /\
           read X1 s = word(t DIV 8 - k) /\
           read X20 s = word_add inp (word(136 * q + 8 * k)) /\
           read X21 s = word t /\
           read X22 s = c /\
           read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
           read (memory :> bytes(c,192)) s =
           num_of_wordlist round_constants /\
           read (memory :> wbytes(word_add stackpointer (word 48))) s =
           word_xor (A:1600 word)
            (word((num_of_bytelist m DIV 2 EXP (8 * 136 * q)) MOD
                  2 EXP (64 * k)))) /\
          (read ZF s <=> k = t DIV 8)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(*** The entry, past the test for no whole words ***)

    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLKEM_HASH_H_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; EXP; MOD_1; WORD_XOR_0;
                    WORD_ADD_0; SUB_0];

    (*** The loop body, for word and lane k ***)

    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `k < 25 /\ (136 * q + 8 * k) + 8 <= LENGTH(m:byte list)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`k < t DIV 8`; `t < 136`;
                             `136 * q + t = LENGTH(m:byte list)`] THEN
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
                  `136 * q + 8 * k`; `s0:armstate`]
      READ_MEMORY_BYTES64_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC MLKEM_HASH_H_EXEC (1--5) THEN
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
          `8 * 136 * q + 64 * k = 8 * (136 * q + 8 * k)`];
        ASM_SIMP_TAC[]];
      REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
      SUBGOAL_THEN `t DIV 8 - (k + 1) < 2 EXP 64`
       (fun th -> SIMP_TAC[MOD_LT; th]) THENL
       [UNDISCH_TAC `t DIV 8 < 17` THEN ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `k < t DIV 8` THEN ARITH_TAC];

    (*** The backward branch ***)

    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLKEM_HASH_H_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The exit to the single bytes ***)

    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLKEM_HASH_H_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let MLKEM_HASH_H_BYTES = prove
 (`!m inp c pc stackpointer q t (A:1600 word).
    LENGTH(m:byte list) = 136 * q + t /\ t < 136 /\ LENGTH m < 2 EXP 64 /\
    aligned 16 stackpointer /\
    ALL (nonoverlapping (word_add stackpointer (word 48),200))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192)]
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read PC s = word(pc + mlkem_hash_h_lastbytes) /\
          read SP s = stackpointer /\
          read X0 s = word_add stackpointer (word(48 + 8 * t DIV 8)) /\
          read X20 s = word_add inp (word(136 * q + 8 * t DIV 8)) /\
          read X21 s = word t /\
          read X22 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes(word_add stackpointer (word 48))) s =
          word_xor A (word((num_of_bytelist m DIV 2 EXP (8 * 136 * q)) MOD
                           2 EXP (64 * t DIV 8))))
     (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read PC s = word(pc + mlkem_hash_h_pad) /\
          read SP s = stackpointer /\
          read X0 s = word_add stackpointer (word(48 + t)) /\
          read X22 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes(word_add stackpointer (word 48))) s =
          word_xor A (word(num_of_bytelist m DIV 2 EXP (8 * 136 * q))))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X20; X21; X30] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 48),200);
                 memory :> bytes(word_sub stackpointer (word 128),128)])`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o
    check (fun th -> concl th = `LENGTH(m:byte list) = 136 * q + t`)) THEN
  SUBGOAL_THEN `t < 2 EXP 64` ASSUME_TAC THENL
   [UNDISCH_TAC `t < 136` THEN ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `t:num` THEN
  SUBGOAL_THEN `word_and (word t:int64) (word 7) = word(t MOD 8)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`word t:int64`; `3`] (CONJUNCT1 WORD_AND_MASK_WORD)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t MOD 8 < 8` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `t MOD 8` THEN
  SUBGOAL_THEN
   `num_of_bytelist m DIV 2 EXP (8 * 136 * q) < 2 EXP (8 * t)`
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
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLKEM_HASH_H_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE `64 * t DIV 8 = 8 * (8 * t DIV 8)`] THEN
    ASM_SIMP_TAC[MOD_LT];
    ALL_TAC] THEN
  ENSURES_WHILE_PUP_TAC `t MOD 8` `pc + mlkem_hash_h_lastbyte`
   (pc_plus "mlkem_hash_h_lastbyte" 20)
   `\k s. (read SP s = stackpointer /\
           read X0 s = word_add stackpointer (word(48 + 8 * t DIV 8 + k)) /\
           read X1 s = word(t MOD 8 - k) /\
           read X20 s = word_add inp (word(136 * q + 8 * t DIV 8 + k)) /\
           read X21 s = word t /\
           read X22 s = c /\
           read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
           read (memory :> bytes(c,192)) s =
           num_of_wordlist round_constants /\
           read (memory :> wbytes(word_add stackpointer (word 48))) s =
           word_xor (A:1600 word)
            (word((num_of_bytelist m DIV 2 EXP (8 * 136 * q)) MOD
                  2 EXP (8 * (8 * t DIV 8 + k))))) /\
          (read ZF s <=> k = t MOD 8)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(*** The entry, past the test for no single bytes ***)

    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLKEM_HASH_H_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; SUB_0;
                    ARITH_RULE `8 * 8 * t DIV 8 = 64 * t DIV 8`];

    (*** The loop body, for byte 8 * t DIV 8 + k ***)

    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `8 * t DIV 8 + k < 200 /\
      136 * q + 8 * t DIV 8 + k < LENGTH(m:byte list)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`k < t MOD 8`; `t < 136`;
                             `136 * q + t = LENGTH(m:byte list)`] THEN
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
                  `136 * q + 8 * t DIV 8 + k`; `s0:armstate`]
      READ_MEMORY_BYTES8_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ARM_STEPS_TAC MLKEM_HASH_H_EXEC (1--5) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[BYTE_XOR_ZX]) THEN
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
                    ARITH_RULE `8 * 136 * q + 8 * (8 * t DIV 8 + k) =
                                8 * (136 * q + 8 * t DIV 8 + k)`];
        ASM_SIMP_TAC[]];
      REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
      SUBGOAL_THEN `t MOD 8 - (k + 1) < 2 EXP 64`
       (fun th -> SIMP_TAC[MOD_LT; th]) THENL
       [UNDISCH_TAC `t MOD 8 < 8` THEN ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `k < t MOD 8` THEN ARITH_TAC];

    (*** The backward branch ***)

    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLKEM_HASH_H_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The exit to the padding ***)

    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC MLKEM_HASH_H_EXEC [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `8 * t DIV 8 + t MOD 8 = t` SUBST1_TAC THENL
     [MP_TAC(SPECL [`t:num`; `8`] DIVISION) THEN ARITH_TAC;
      ASM_SIMP_TAC[MOD_LT]]]);;

(* ------------------------------------------------------------------------- *)
(* The padding of the last block, the domain byte 0x06 at byte t and 0x80 at *)
(* byte 135 (the same byte if t = 135), and the permutation.                 *)
(* ------------------------------------------------------------------------- *)

let MLKEM_HASH_H_PAD = prove
 (`!inp len c pc stackpointer t (A:1600 word) M.
    t < 136 /\
    aligned 16 stackpointer /\
    ALL (nonoverlapping (word_add stackpointer (word 48),200))
        [(word pc,mlkem_native2_image_size); (inp,len); (c,192)] /\
    ALL (nonoverlapping (word_sub stackpointer (word 128),128))
        [(word pc,mlkem_native2_image_size); (inp,len); (c,192);
         (word_add stackpointer (word 48),200)]
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read PC s = word(pc + mlkem_hash_h_pad) /\
          read SP s = stackpointer /\
          read X0 s = word_add stackpointer (word(48 + t)) /\
          read X22 s = c /\
          read (memory :> bytes(inp,len)) s = M /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes(word_add stackpointer (word 48))) s = A)
     (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read PC s = word(pc + mlkem_hash_h_digest) /\
          read SP s = stackpointer /\
          read X22 s = c /\
          read (memory :> bytes(inp,len)) s = M /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes(word_add stackpointer (word 48))) s =
          keccak_f1600(word_xor (word_xor A (word(2 EXP (8 * t) * 6)))
                                (word(2 EXP (8 * 135) * 128))))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X20; X21; X30] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 48),200);
                 memory :> bytes(word_sub stackpointer (word 128),128)])`,
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
                  (MP (ARITH_RULE `t < 136 ==> t < 200`)
                      (ASSUME `t < 136`))) THEN
    ASSUME_TAC(RESTRICT_RULE `t:num` th)) THEN
  ARM_STEPS_TAC MLKEM_HASH_H_EXEC (1--3) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BYTE_XOR_CONST_ZX]) THEN
  SUBGOAL_THEN
   `!j. j < 200
        ==> read (memory :> bytes8
                   (word_add stackpointer (word (48 + j)))) s3 =
            word_subword (word_xor (A:1600 word) (word(2 EXP (8 * t) * 6)))
                         (8 * j,8)`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[BYTE_XOR_SHIFT; ARITH_RULE `6 < 256`;
                 ARITH_RULE `t < 136 ==> t < 200`] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN

  (*** The final bit at byte 135 ***)

  DISCH_THEN(fun th ->
    ASSUME_TAC(CONV_RULE NUM_REDUCE_CONV
      (MP (SPEC `135` th) (ARITH_RULE `135 < 200`))) THEN
    ASSUME_TAC(RESTRICT_RULE `135` th)) THEN
  ARM_STEPS_TAC MLKEM_HASH_H_EXEC (4--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[BYTE_XOR_CONST_ZX]) THEN
  SUBGOAL_THEN
   `read (memory :> wbytes (word_add stackpointer (word 48))) s9 =
    word_xor (word_xor (A:1600 word) (word(2 EXP (8 * t) * 6)))
             (word(2 EXP (8 * 135) * 128))`
  ASSUME_TAC THENL
   [REWRITE_TAC[READ_MEMORY_WBYTES_BYTES] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    ASM_SIMP_TAC[BYTE_XOR_SHIFT; ARITH_RULE `128 < 256 /\ 135 < 200`] THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN

  (*** The permutation ***)

  SUBGOAL_THEN `wordlist_from_memory(c,24) s9 = round_constants`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[WORDLIST_FROM_MEMORY_ROUND_CONSTANTS]; ALL_TAC] THEN
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,MLKEM_HASH_H_EXEC,layout "sha3_keccak_f1600",
    sha3_keccak_f1600_mc,SHA3_KECCAK_F1600_SUBROUTINE_CORRECT_F1600)
   [`read X0 s`; `read X1 s`;
    `word_xor (word_xor (A:1600 word) (word(2 EXP (8 * t) * 6)))
              (word(2 EXP (8 * 135) * 128))`;
    `pc + sha3_keccak_f1600`; `read SP s`; `read X30 s`] 10 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The last block as a whole, from the exit of the loop over whole blocks to *)
(* the state for the digest, which is that of KECCAK_SPONGE_BYTES.           *)
(* ------------------------------------------------------------------------- *)

let MLKEM_HASH_H_TAIL = prove
 (`!m inp c pc stackpointer.
    LENGTH m < 2 EXP 64 /\ aligned 16 stackpointer /\
    ALL (nonoverlapping (word_add stackpointer (word 48),200))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192)] /\
    ALL (nonoverlapping (word_sub stackpointer (word 128),128))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192);
         (word_add stackpointer (word 48),200)]
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read PC s = word(pc + mlkem_hash_h_block) /\
          read SP s = stackpointer /\
          read X20 s = word_add inp (word(136 * LENGTH m DIV 136)) /\
          read X21 s = word(LENGTH m - 136 * LENGTH m DIV 136) /\
          read X22 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes(word_add stackpointer (word 48))) s =
          keccak_absorb 136 (keccak_padded 136 6 m) (LENGTH m DIV 136))
     (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read PC s = word(pc + mlkem_hash_h_digest) /\
          read SP s = stackpointer /\
          read X22 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes(word_add stackpointer (word 48))) s =
          keccak_f1600
           (word_xor
             (keccak_absorb 136 (keccak_padded 136 6 m) (LENGTH m DIV 136))
             (word((keccak_padded 136 6 m DIV
                    2 EXP (8 * 136 * LENGTH m DIV 136)) MOD 2 EXP (8 * 136)))))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X20; X21; X30] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 48),200);
                 memory :> bytes(word_sub stackpointer (word 128),128)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC[KECCAK_LAST_BLOCK_XOR; ARITH_RULE `0 < 136 /\ 6 < 128`] THEN
  REWRITE_TAC[ARITH_RULE `136 - 1 = 135`] THEN
  ABBREV_TAC `q = LENGTH(m:byte list) DIV 136` THEN
  ABBREV_TAC `t = LENGTH(m:byte list) MOD 136` THEN
  ABBREV_TAC `A = keccak_absorb 136 (keccak_padded 136 6 m) q` THEN
  SUBGOAL_THEN `LENGTH(m:byte list) = 136 * q + t /\ t < 136`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
    MP_TAC(SPECL [`LENGTH(m:byte list)`; `136`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(m:byte list) - 136 * q = t` SUBST1_TAC THENL
   [UNDISCH_TAC `LENGTH(m:byte list) = 136 * q + t` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  ENSURES_SEQUENCE_TAC `pc + mlkem_hash_h_lastbytes`
   `\s. read SP s = stackpointer /\
        read X0 s = word_add stackpointer (word(48 + 8 * t DIV 8)) /\
        read X20 s = word_add inp (word(136 * q + 8 * t DIV 8)) /\
        read X21 s = word t /\
        read X22 s = c /\
        read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
        read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
        read (memory :> wbytes(word_add stackpointer (word 48))) s =
        word_xor (A:1600 word)
         (word((num_of_bytelist m DIV 2 EXP (8 * 136 * q)) MOD
               2 EXP (64 * t DIV 8)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
                   MLKEM_HASH_H_WORDS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + mlkem_hash_h_pad`
   `\s. read SP s = stackpointer /\
        read X0 s = word_add stackpointer (word(48 + t)) /\
        read X22 s = c /\
        read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
        read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
        read (memory :> wbytes(word_add stackpointer (word 48))) s =
        word_xor (A:1600 word)
         (word(num_of_bytelist m DIV 2 EXP (8 * 136 * q)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
                   MLKEM_HASH_H_BYTES) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
                   MLKEM_HASH_H_PAD) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The whole absorption, from block i by induction on the blocks left, and   *)
(* from the zero state, without the code in the postcondition so that the    *)
(* proof below can use it as a step.                                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_HASH_H_ABSORB = prove
 (`!m inp c pc stackpointer i.
    LENGTH m < 2 EXP 64 /\ aligned 16 stackpointer /\
    i <= LENGTH m DIV 136 /\
    ALL (nonoverlapping (word_add stackpointer (word 48),200))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192)] /\
    ALL (nonoverlapping (word_sub stackpointer (word 128),128))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192);
         (word_add stackpointer (word 48),200)]
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read PC s = word(pc + mlkem_hash_h_block) /\
          read SP s = stackpointer /\
          read X20 s = word_add inp (word(136 * i)) /\
          read X21 s = word(LENGTH m - 136 * i) /\
          read X22 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes(word_add stackpointer (word 48))) s =
          keccak_absorb 136 (keccak_padded 136 6 m) i)
     (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read PC s = word(pc + mlkem_hash_h_digest) /\
          read SP s = stackpointer /\
          read X22 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes(word_add stackpointer (word 48))) s =
          keccak_f1600
           (word_xor
             (keccak_absorb 136 (keccak_padded 136 6 m) (LENGTH m DIV 136))
             (word((keccak_padded 136 6 m DIV
                    2 EXP (8 * 136 * LENGTH m DIV 136)) MOD 2 EXP (8 * 136)))))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X20; X21; X30] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 48),200);
                 memory :> bytes(word_sub stackpointer (word 128),128)])`,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ; LE_EXISTS] THEN
  REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` MP_TAC) THEN
  SPEC_TAC(`i:num`,`i:num`) THEN SPEC_TAC(`d:num`,`d:num`) THEN
  INDUCT_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o REWRITE_RULE[ADD_CLAUSES]) THEN
    MATCH_MP_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
                   MLKEM_HASH_H_TAIL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_SEQUENCE_TAC `pc + mlkem_hash_h_block`
   `\s. read SP s = stackpointer /\
        read X20 s = word_add inp (word(136 * (i + 1))) /\
        read X21 s = word(LENGTH m - 136 * (i + 1)) /\
        read X22 s = c /\
        read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
        read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
        read (memory :> wbytes(word_add stackpointer (word 48))) s =
        keccak_absorb 136 (keccak_padded 136 6 m) (i + 1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
                   MLKEM_HASH_H_BLOCK) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`LENGTH(m:byte list)`; `136`] DIVISION) THEN
    UNDISCH_TAC `LENGTH(m:byte list) DIV 136 = i + SUC d` THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `i + 1`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `LENGTH(m:byte list) DIV 136 = i + SUC d` THEN ARITH_TAC;
      SIMP_TAC[]]]);;

let MLKEM_HASH_H_ABSORB_0 = prove
 (`!m inp c pc stackpointer.
    LENGTH m < 2 EXP 64 /\ aligned 16 stackpointer /\
    ALL (nonoverlapping (word_add stackpointer (word 48),200))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192)] /\
    ALL (nonoverlapping (word_sub stackpointer (word 128),128))
        [(word pc,mlkem_native2_image_size); (inp,LENGTH m); (c,192);
         (word_add stackpointer (word 48),200)]
    ==> ensures arm
     (\s. aligned_bytes_loaded s (word pc) mlkem_native2_image_mc /\
          read PC s = word(pc + mlkem_hash_h_block) /\
          read SP s = stackpointer /\
          read X20 s = inp /\
          read X21 s = word(LENGTH m) /\
          read X22 s = c /\
          read (memory :> bytes(inp,LENGTH m)) s = num_of_bytelist m /\
          read (memory :> bytes(c,192)) s = num_of_wordlist round_constants /\
          read (memory :> wbytes(word_add stackpointer (word 48))) s =
          (word 0:1600 word))
     (\s. read PC s = word(pc + mlkem_hash_h_digest) /\
          read SP s = stackpointer /\
          read (memory :> wbytes(word_add stackpointer (word 48))) s =
          keccak_f1600
           (word_xor
             (keccak_absorb 136 (keccak_padded 136 6 m) (LENGTH m DIV 136))
             (word((keccak_padded 136 6 m DIV
                    2 EXP (8 * 136 * LENGTH m DIV 136)) MOD 2 EXP (8 * 136)))))
     (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X20; X21; X30] ,,
      MAYCHANGE [memory :> bytes(word_add stackpointer (word 48),200);
                 memory :> bytes(word_sub stackpointer (word 128),128)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`m:byte list`; `inp:int64`; `c:int64`; `pc:num`;
                `stackpointer:int64`; `0`] MLKEM_HASH_H_ABSORB) THEN
  ASM_REWRITE_TAC[LE_0; MULT_CLAUSES; SUB_0; WORD_ADD_0;
                  CONJUNCT1 keccak_absorb] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    (ONCE_REWRITE_RULE[CONJ_SYM] ENSURES_POSTCONDITION_THM))) THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness of the function: the 32 bytes of the result at out are        *)
(* sha3_256 of the message m at inp, given the round constants at c (in the  *)
(* constants block, which may be in the image). The stack is the 256 bytes   *)
(* of the frame and the 128 below them used by sha3_keccak_f1600.            *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_HASH_H_ASM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_HASH_H_ASM_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`out:int64`; `inp:int64`; `m:byte list`; `c:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 384 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `LENGTH(m:byte list) < 2 EXP 64` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `384 + l <= 2 EXP 64 ==> l < 2 EXP 64`) THEN
    MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(stackpointer:int64)`; `val(inp:int64)`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29` THEN
  ENSURES_INIT_TAC "s0" THEN
  RULE_ASSUM_TAC(REWRITE_RULE[WORDLIST_FROM_MEMORY_ROUND_CONSTANTS]) THEN

  (*** The frame, the saved registers and the zero state ***)

  ARM_STEPS_TAC MLKEM_HASH_H_EXEC (1--18) THEN
  SUBGOAL_THEN
   `read (memory :> wbytes (word_add stackpointer (word 176))) s18 =
    (word 0:1600 word)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC READ_MEMORY_WBYTES_ZERO THEN
    CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
    ASM_REWRITE_TAC[WORD_ADD_0];
    ALL_TAC] THEN

  (*** The absorption of the message and the last permutation ***)

  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native2_image_mc,MLKEM_HASH_H_EXEC,0,
    mlkem_native2_image_mc,MLKEM_HASH_H_ABSORB_0)
   [`m:byte list`; `inp:int64`; `c:int64`; `pc:num`; `read SP s`] 19 THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match []
    `read (memory :> wbytes a) s19 = keccak_f1600 x`) o concl)) THEN
  ABBREV_TAC
   `S = keccak_f1600
         (word_xor
           (keccak_absorb 136 (keccak_padded 136 6 m) (LENGTH m DIV 136))
           (word((keccak_padded 136 6 m DIV
                  2 EXP (8 * 136 * LENGTH m DIV 136)) MOD 2 EXP (8 * 136))))`
  THEN
  REWRITE_TAC[READ_MEMORY_WBYTES_1600] THEN DISCH_TAC THEN

  (*** The digest, the zeroing of the state and the return ***)

  MP_TAC(SPECL [`word_add stackpointer (word 176):int64`; `200`;
                `val(S:1600 word)`; `0`; `s19:armstate`]
    READ_MEMORY_BYTES128_OF_NUM) THEN
  MP_TAC(SPECL [`word_add stackpointer (word 176):int64`; `200`;
                `val(S:1600 word)`; `16`; `s19:armstate`]
    READ_MEMORY_BYTES128_OF_NUM) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  REWRITE_TAC[WORD_ADD_0; DIV_1] THEN REPEAT DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_HASH_H_EXEC (20--35) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** The 32 bytes of the state as in sha3_256 ***)

  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ADD_0]) THEN
  MP_TAC(SPECL [`out:int64`; `2`; `val(S:1600 word)`; `s35:armstate`]
    READ_MEMORY_BYTES_OF_BYTES128) THEN
  CONV_TAC(LAND_CONV(LAND_CONV EXPAND_CASES_CONV)) THEN
  CONV_TAC(LAND_CONV(LAND_CONV NUM_REDUCE_CONV)) THEN
  REWRITE_TAC[ARITH_RULE `16 * 2 = 32 /\ 128 * 2 = 256`] THEN
  ASM_REWRITE_TAC[WORD_ADD_0; DIV_1] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[sha3_256] THEN
  MP_TAC(SPECL [`512`; `6`; `m:byte list`; `136`; `keccak_padded 136 6 m`;
                `32`] KECCAK_SPONGE_BYTES) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[keccak_padded] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 32 = 256`]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. The events depend only on the      *)
(* length of the message: those of the prologue and of each whole block,     *)
(* the last block's whole words and single bytes, and the padding, the last  *)
(* permutation and the epilogue, with those of the permutations from the     *)
(* framed theorem for sha3_keccak_f1600.                                     *)
(* ------------------------------------------------------------------------- *)

(*** The registers saved in the frame, part of every invariant ***)

let MLKEM_HASH_H_SAVED =
  `read (memory :> bytes64 (word_add stackpointer (word 128))) s = x19_init /\
   read (memory :> bytes64 (word_add stackpointer (word 136))) s = x20_init /\
   read (memory :> bytes64 (word_add stackpointer (word 144))) s = x21_init /\
   read (memory :> bytes64 (word_add stackpointer (word 152))) s = x22_init /\
   read (memory :> bytes64 (word_add stackpointer (word 160))) s = x29_init /\
   read (memory :> bytes64 (word_add stackpointer (word 168))) s =
   returnaddress`;;

let mlkem_hash_h_inv tm =
  mk_abs(`s:armstate`,mk_conj(tm,MLKEM_HASH_H_SAVED));;

let mlkem_hash_h_loop_inv tm =
  mk_abs(`i:num`,mk_abs(`s:armstate`,mk_conj(tm,MLKEM_HASH_H_SAVED)));;

(*** The call of sha3_keccak_f1600, given its safety theorem as H_KECCAK ***)

let MLKEM_HASH_H_SAFE_CALL_TAC extra n =
  W(fun (asl,w) ->
    let fevs = filter (fun v -> String.length (name_of v) > 4 &&
                                String.sub (name_of v) 0 4 = "f_ev")
                      (frees w) in
    let vars =
      [`inp:int64`; `len:num`; `c:int64`; `out:int64`; `pc:num`;
       `stackpointer:int64`; `returnaddress:int64`] @ extra @ fevs in
    REMOVE_THEN "H_KECCAK" (fun safety_th ->
      ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
        (mlkem_native2_image_mc,MLKEM_HASH_H_EXEC,layout "sha3_keccak_f1600",
         sha3_keccak_f1600_mc,safety_th)
        [`e:(uarch_event)list`; `read X0 s`; `read X1 s`;
         `pc + sha3_keccak_f1600`; `read SP s`; `read X30 s`] n THENL
       [EXISTS_E2_TAC (ref vars); LABEL_TAC "H_KECCAK" safety_th]));;

(*** DISCHARGE_SAFETY_PROPERTY_TAC, but with a tactic to expand local     ***)
(*** abbreviations for the unification of the events, and the old events  ***)
(*** in the same association as the new for the memory accesses           ***)

let MLKEM_HASH_H_DISCHARGE_TAC unabbrev normalize =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [unabbrev THEN FULL_UNIFY_F_EVENTS_TAC;
    (if normalize then
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC; APPEND_NIL]) THEN
      REWRITE_TAC[GSYM APPEND_ASSOC; APPEND_NIL]
     else ALL_TAC) THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC];;

(*** The decrement of a loop counter, and the test after it ***)

let MLKEM_HASH_H_COUNTER_TAC =
  let pth = prove
   (`!n k. k < n /\ n < 2 EXP 64
           ==> word_sub (word(n - k)) (word 1):int64 = word(n - (k + 1)) /\
               (~(val(word(n - (k + 1)):int64) = 0) <=> k + 1 < n)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `n - k = (n - (k + 1)) + 1` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
      SUBGOAL_THEN `val(word(n - (k + 1)):int64) = n - (k + 1)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        ASM_ARITH_TAC;
        ASM_ARITH_TAC]]) in
  fun n k ->
    MP_TAC(SPECL [n; k] pth) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ARITH_TAC]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC);;

let MLKEM_NATIVE_HASH_H_ASM_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_HASH_H_ASM_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC SHA3_KECCAK_F1600_SUBROUTINE_SAFE_FRAMED
    "H_KECCAK" THEN
  CONCRETIZE_F_EVENTS_TAC
   `\(inp:int64) (len:num) (c:int64) (out:int64) (pc:num)
     (stackpointer:int64) (returnaddress:int64).
      APPEND (f_ev_fin inp len c out pc stackpointer returnaddress)
       (APPEND
         (if (len MOD 136) MOD 8 = 0
          then f_ev_bskip inp len c out pc stackpointer returnaddress
          else APPEND (f_ev_bexit inp len c out pc stackpointer returnaddress)
                (APPEND
                  (ENUMERATEL ((len MOD 136) MOD 8)
                    (\k. f_ev_byte inp len c out pc stackpointer
                                   returnaddress k))
                  (f_ev_bentry inp len c out pc stackpointer returnaddress)))
         (APPEND
           (if (len MOD 136) DIV 8 = 0
            then f_ev_wskip inp len c out pc stackpointer returnaddress
            else APPEND
                  (f_ev_wexit inp len c out pc stackpointer returnaddress)
                  (APPEND
                    (ENUMERATEL ((len MOD 136) DIV 8)
                      (\k. f_ev_word inp len c out pc stackpointer
                                     returnaddress k))
                    (f_ev_wentry inp len c out pc stackpointer
                                 returnaddress)))
           (if len DIV 136 = 0
            then f_ev_lskip inp len c out pc stackpointer returnaddress
            else APPEND
                  (f_ev_lexit inp len c out pc stackpointer returnaddress)
                  (APPEND
                    (ENUMERATEL (len DIV 136)
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
   [MATCH_MP_TAC(ARITH_RULE `384 + l <= 2 EXP 64 ==> l < 2 EXP 64`) THEN
    MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(stackpointer:int64)`; `val(inp:int64)`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `136 * len DIV 136 + len MOD 136 = len /\ len MOD 136 < 136`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`len:num`; `136`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word(len MOD 136):int64) = len MOD 136` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `len MOD 136 < 136` THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29` THEN

  (*** Split at the padding, the single bytes and the last block ***)

  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_hash_h_pad`
   (mlkem_hash_h_inv
    `read SP s = word_add stackpointer (word 128) /\
     read X0 s = word_add stackpointer (word (176 + len MOD 136)) /\
     read X19 s = out /\ read X22 s = c`) THEN
  CONJ_TAC THENL
   [ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_hash_h_lastbytes`
     (mlkem_hash_h_inv
      `read SP s = word_add stackpointer (word 128) /\
       read X0 s =
       word_add stackpointer (word (176 + 8 * (len MOD 136) DIV 8)) /\
       read X20 s =
       word_add inp (word (136 * len DIV 136 + 8 * (len MOD 136) DIV 8)) /\
       read X21 s = word (len MOD 136) /\
       read X19 s = out /\ read X22 s = c`) THEN
    CONJ_TAC THENL
     [ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_hash_h_last`
       (mlkem_hash_h_inv
        `read SP s = word_add stackpointer (word 128) /\
         read X20 s = word_add inp (word (136 * len DIV 136)) /\
         read X21 s = word (len MOD 136) /\
         read X19 s = out /\ read X22 s = c`) THEN
      CONJ_TAC THENL
       [(*** The prologue and the whole blocks ***)

        ASM_CASES_TAC `len DIV 136 = 0` THEN ASM_REWRITE_TAC[] THENL
         [SUBGOAL_THEN `len < 136` ASSUME_TAC THENL
           [MP_TAC(SPECL [`len:num`; `136`] DIVISION) THEN
            ASM_REWRITE_TAC[] THEN ARITH_TAC;
            ALL_TAC] THEN
          VAL_INT64_TAC `len:num` THEN
          ASM_SIMP_TAC[MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
          REWRITE_TAC(!simulation_precanon_thms) THEN
          ENSURES_INIT_TAC "s0" THEN
          ARM_STEPS_TAC MLKEM_HASH_H_EXEC (1--20) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          DISCHARGE_SAFETY_PROPERTY_TAC;
          ALL_TAC] THEN
        ENSURES_EVENTS_WHILE_UP2_TAC `len DIV 136` `pc + mlkem_hash_h_block`
         `pc + mlkem_hash_h_block`
         (mlkem_hash_h_loop_inv
          `read SP s = word_add stackpointer (word 128) /\
           read X20 s = word_add inp (word (136 * i)) /\
           read X21 s = word (len - 136 * i) /\
           read X19 s = out /\ read X22 s = c`) THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[];

          REWRITE_TAC(!simulation_precanon_thms) THEN
          ENSURES_INIT_TAC "s0" THEN
          ARM_STEPS_TAC MLKEM_HASH_H_EXEC (1--18) THEN
          ENSURES_FINAL_STATE_TAC THEN
          ASM_REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
          DISCHARGE_SAFETY_PROPERTY_TAC;

          X_GEN_TAC `i:num` THEN STRIP_TAC THEN
          SUBGOAL_THEN `136 * (i + 1) <= len` ASSUME_TAC THENL
           [MP_TAC(SPECL [`len:num`; `136`] DIVISION) THEN
            UNDISCH_TAC `i < len DIV 136` THEN ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN `~(val(word(len - 136 * i):int64) < 136)`
          ASSUME_TAC THENL
           [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
            W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o lhand o rand o snd)
            THEN ANTS_TAC THENL
             [UNDISCH_TAC `len < 2 EXP 64` THEN ARITH_TAC;
              DISCH_THEN SUBST1_TAC] THEN
            UNDISCH_TAC `136 * (i + 1) <= len` THEN ARITH_TAC;
            ALL_TAC] THEN
          REWRITE_TAC(!simulation_precanon_thms) THEN
          ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
          ARM_STEPS_TAC MLKEM_HASH_H_EXEC (1--49) THEN
          MLKEM_HASH_H_SAFE_CALL_TAC [`i:num`] 50 THEN
          ARM_STEPS_TAC MLKEM_HASH_H_EXEC (51--52) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[COND_ID] THEN
          REPEAT CONJ_TAC THENL
           [REWRITE_TAC[ARITH_RULE `136 * (i + 1) = 136 * i + 136`; WORD_ADD;
                        WORD_ADD_ASSOC];
            SUBGOAL_THEN `len - 136 * i = (len - 136 * (i + 1)) + 136`
            SUBST1_TAC THENL
             [UNDISCH_TAC `136 * (i + 1) <= len` THEN ARITH_TAC;
              REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE];
            DISCHARGE_SAFETY_PROPERTY_TAC];

          SUBGOAL_THEN `len - 136 * len DIV 136 = len MOD 136` SUBST1_TAC THENL
           [UNDISCH_TAC `136 * len DIV 136 + len MOD 136 = len` THEN ARITH_TAC;
            ALL_TAC] THEN
          REWRITE_TAC(!simulation_precanon_thms) THEN
          ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
          ARM_STEPS_TAC MLKEM_HASH_H_EXEC (1--2) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          DISCHARGE_SAFETY_PROPERTY_TAC];

        (*** The whole words of the last block ***)

        SUBGOAL_THEN
         `word_ushr (word (len MOD 136):int64) 3 = word((len MOD 136) DIV 8)`
        ASSUME_TAC THENL
         [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR] THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
          CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
          UNDISCH_TAC `len MOD 136 < 136` THEN ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN
         `val(word((len MOD 136) DIV 8):int64) = (len MOD 136) DIV 8`
        ASSUME_TAC THENL
         [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
          UNDISCH_TAC `len MOD 136 < 136` THEN ARITH_TAC;
          ALL_TAC] THEN
        ASM_CASES_TAC `(len MOD 136) DIV 8 = 0` THEN ASM_REWRITE_TAC[] THENL
         [REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
          REWRITE_TAC(!simulation_precanon_thms) THEN
          ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
          ARM_STEPS_TAC MLKEM_HASH_H_EXEC (1--3) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          DISCHARGE_SAFETY_PROPERTY_TAC;
          ALL_TAC] THEN
        ENSURES_EVENTS_WHILE_UP2_TAC `(len MOD 136) DIV 8`
         `pc + mlkem_hash_h_lastwords` `pc + mlkem_hash_h_lastbytes`
         (mlkem_hash_h_loop_inv
          `read SP s = word_add stackpointer (word 128) /\
           read X0 s = word_add stackpointer (word (176 + 8 * i)) /\
           read X1 s = word ((len MOD 136) DIV 8 - i) /\
           read X20 s = word_add inp (word (136 * len DIV 136 + 8 * i)) /\
           read X21 s = word (len MOD 136) /\
           read X19 s = out /\ read X22 s = c`) THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[];

          REWRITE_TAC(!simulation_precanon_thms) THEN
          ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
          ARM_STEPS_TAC MLKEM_HASH_H_EXEC (1--3) THEN
          ENSURES_FINAL_STATE_TAC THEN
          ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_0; WORD_ADD_0] THEN
          DISCHARGE_SAFETY_PROPERTY_TAC;

          X_GEN_TAC `k:num` THEN STRIP_TAC THEN
          SUBGOAL_THEN `(136 * len DIV 136 + 8 * k) + 8 <= len`
          ASSUME_TAC THENL
           [MAP_EVERY UNDISCH_TAC
             [`k < (len MOD 136) DIV 8`;
              `136 * len DIV 136 + len MOD 136 = len`] THEN
            ARITH_TAC;
            ALL_TAC] THEN
          REWRITE_TAC(!simulation_precanon_thms) THEN
          ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
          ARM_STEPS_TAC MLKEM_HASH_H_EXEC (1--6) THEN
          ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
          MLKEM_HASH_H_COUNTER_TAC `(len MOD 136) DIV 8` `k:num` THEN
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

      SUBGOAL_THEN `word_and (word (len MOD 136):int64) (word 7) =
                    word((len MOD 136) MOD 8)`
      ASSUME_TAC THENL
       [MP_TAC(ISPECL [`word (len MOD 136):int64`; `3`]
          (CONJUNCT1 WORD_AND_MASK_WORD)) THEN
        CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `val(word((len MOD 136) MOD 8):int64) = (len MOD 136) MOD 8`
      ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `8 * (len MOD 136) DIV 8 + (len MOD 136) MOD 8 = len MOD 136`
      ASSUME_TAC THENL
       [MP_TAC(SPECL [`len MOD 136`; `8`] DIVISION) THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_CASES_TAC `(len MOD 136) MOD 8 = 0` THEN ASM_REWRITE_TAC[] THENL
       [SUBGOAL_THEN `8 * (len MOD 136) DIV 8 = len MOD 136` ASSUME_TAC THENL
         [UNDISCH_TAC
           `8 * (len MOD 136) DIV 8 + (len MOD 136) MOD 8 = len MOD 136` THEN
          ASM_REWRITE_TAC[ADD_CLAUSES];
          ALL_TAC] THEN
        REWRITE_TAC(!simulation_precanon_thms) THEN
        ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
        ARM_STEPS_TAC MLKEM_HASH_H_EXEC (1--2) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;
        ALL_TAC] THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `(len MOD 136) MOD 8`
       `pc + mlkem_hash_h_lastbyte` `pc + mlkem_hash_h_pad`
       (mlkem_hash_h_loop_inv
        `read SP s = word_add stackpointer (word 128) /\
         read X0 s =
         word_add stackpointer (word (176 + 8 * (len MOD 136) DIV 8 + i)) /\
         read X1 s = word ((len MOD 136) MOD 8 - i) /\
         read X20 s =
         word_add inp
          (word (136 * len DIV 136 + 8 * (len MOD 136) DIV 8 + i)) /\
         read X21 s = word (len MOD 136) /\
         read X19 s = out /\ read X22 s = c`) THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];

        REWRITE_TAC(!simulation_precanon_thms) THEN
        ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
        ARM_STEPS_TAC MLKEM_HASH_H_EXEC (1--2) THEN
        ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;

        (*** For the offset nw of the single bytes, an abbreviation, as   ***)
        (*** the arithmetic of the simulation fails with its DIV and MOD  ***)

        X_GEN_TAC `k:num` THEN STRIP_TAC THEN
        ABBREV_TAC `nw = (len MOD 136) DIV 8` THEN
        SUBGOAL_THEN
         `(136 * len DIV 136 + 8 * nw + k) + 1 <= len /\ 8 * nw + k < 136`
        STRIP_ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC
           [`k < (len MOD 136) MOD 8`; `136 * len DIV 136 + len MOD 136 = len`;
            `8 * nw + (len MOD 136) MOD 8 = len MOD 136`;
            `len MOD 136 < 136`] THEN
          ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC(!simulation_precanon_thms) THEN
        ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
        ARM_STEPS_TAC MLKEM_HASH_H_EXEC (1--6) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        MLKEM_HASH_H_COUNTER_TAC `(len MOD 136) MOD 8` `k:num` THEN
        REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [COND_CASES_TAC THEN REWRITE_TAC[];
          REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
          REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
          AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
          MLKEM_HASH_H_DISCHARGE_TAC (EXPAND_TAC "nw") false];

        REWRITE_TAC(!simulation_precanon_thms) THEN
        ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC]];

    (*** The padding, the last permutation, the digest and the return ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_HASH_H_EXEC (1--9) THEN
    MLKEM_HASH_H_SAFE_CALL_TAC [] 10 THEN
    ARM_STEPS_TAC MLKEM_HASH_H_EXEC (11--26) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    MLKEM_HASH_H_DISCHARGE_TAC ALL_TAC true]);;
