(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_O2/keccak_absorb_once_spec.ml";;


let READ_MEMORY_BYTES_SUB = prove
 (READ_MEMORY_BYTES_SUB_STMT,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let WORD_ZX_BYTE_SMALL = prove
 (WORD_ZX_BYTE_SMALL_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32;
              DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `p < 256 ==> p < 4294967296 /\ p < 18446744073709551616`]);;

let WORD_ZX_SUB1_SMALL = prove
 (WORD_ZX_SUB1_SMALL_STMT,
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_SUB_CASES;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `r < 4294967296 ==> r < 18446744073709551616`;
   ARITH_RULE `0 < r ==> 1 <= r`;
   ARITH_RULE `r < 4294967296 ==> r - 1 < 4294967296`;
   ARITH_RULE `r < 4294967296 ==> r - 1 < 18446744073709551616`]);;

let BIT7_SMALL = prove
 (BIT7_SMALL_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[BIT_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[DIV_LT; ARITH_ODD]);;

let ABSORB_BLOCK_BOUND = prove
 (ABSORB_BLOCK_BOUND_STMT,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> GEN_REWRITE_TAC RAND_CONV [th])
    ASSUME_TAC) THEN
  MATCH_MP_TAC(ARITH_RULE `a <= b ==> a <= b + c`) THEN
  REWRITE_TAC[ARITH_RULE `r * i + r = (i + 1) * r`; LE_MULT_RCANCEL] THEN
  ASM_ARITH_TAC);;

let ABSORB_MOD_EQ = prove
 (ABSORB_MOD_EQ_STMT,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`mlen:num`; `r:num`] (CONJUNCT2 DIVISION_SIMP)) THEN
  ARITH_TAC);;

let ABSORB_LOOP_TEST = prove
 (ABSORB_LOOP_TEST_STMT,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `i + 1 < q <=> i + 2 <= q`; LE_RDIV_EQ;
               ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  ASM_ARITH_TAC);;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`st:int64`; `r:num`; `m:int64`; `mlen:num`; `p:num`; `M:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 256 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `200 + mlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(m:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `P = M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad r p mlen)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN

  (*** The state after the whole blocks, before the last block ***)

  ENSURES_SEQUENCE_TAC `pc + mlk_keccak_absorb_once_loop1_exit`
   `\s. read X19 s = st /\ read X20 s = word(mlen MOD r) /\
        read X21 s = word_add m (word(r * mlen DIV r)) /\
        read X23 s = word r /\
        read SP s = word_add stackpointer (word 192) /\
        read (memory :> bytes64 (word_add stackpointer (word 192))) s =
        x19_init /\
        read (memory :> bytes64 (word_add stackpointer (word 200))) s =
        x20_init /\
        read (memory :> bytes64 (word_add stackpointer (word 208))) s =
        x21_init /\
        read (memory :> bytes64 (word_add stackpointer (word 216))) s =
        x22_init /\
        read (memory :> bytes64 (word_add stackpointer (word 224))) s =
        x23_init /\
        read (memory :> bytes64 (word_add stackpointer (word 232))) s =
        returnaddress /\
        read (memory :> bytes8 (word_add stackpointer (word 255))) s =
        word p /\
        read (memory :> bytes(m,mlen)) s = M /\
        read (memory :> bytes(st,200)) s =
        val(keccak_absorb r P (mlen DIV r))` THEN
  CONJ_TAC THENL
   [(*** A message shorter than a block, with no loop ***)

    ASM_CASES_TAC `mlen < r` THENL
     [ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--18) THEN
      ARGS_32_TAC [`r:num`] THEN ABSORB_BYTE_TAC THEN ABSORB_VAL_TAC THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (19--19) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
      REWRITE_TAC[keccak_absorb; VAL_WORD_0] THEN KECCAK_ZERO_STATE_TAC;
      ALL_TAC] THEN

    (*** Otherwise the loop over the whole blocks ***)

    ENSURES_WHILE_UP_TAC `mlen DIV r` `pc + mlk_keccak_absorb_once_loop1`
     `pc + mlk_keccak_absorb_once_loop1_test`
     `\k s. read X19 s = st /\ read X20 s = word(mlen - r * k) /\
            read X21 s = word_add m (word(r * k)) /\
            read X22 s = word r /\ read X23 s = word r /\
            read SP s = word_add stackpointer (word 192) /\
            read (memory :> bytes64 (word_add stackpointer (word 192))) s =
            x19_init /\
            read (memory :> bytes64 (word_add stackpointer (word 200))) s =
            x20_init /\
            read (memory :> bytes64 (word_add stackpointer (word 208))) s =
            x21_init /\
            read (memory :> bytes64 (word_add stackpointer (word 216))) s =
            x22_init /\
            read (memory :> bytes64 (word_add stackpointer (word 224))) s =
            x23_init /\
            read (memory :> bytes64 (word_add stackpointer (word 232))) s =
            returnaddress /\
            read (memory :> bytes8 (word_add stackpointer (word 255))) s =
            word p /\
            read (memory :> bytes(m,mlen)) s = M /\
            read (memory :> bytes(st,200)) s = val(keccak_absorb r P k)` THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[DIV_EQ_0; ARITH_RULE `0 < r ==> ~(r = 0)`];

      (*** Initialization of the loop, with the state zeroed ***)

      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--18) THEN
      ARGS_32_TAC [`r:num`] THEN ABSORB_BYTE_TAC THEN ABSORB_VAL_TAC THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (19--20) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
      REWRITE_TAC[keccak_absorb; VAL_WORD_0] THEN KECCAK_ZERO_STATE_TAC;

      (*** The loop body: XOR in a block and permute ***)

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
      MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_BLOCK_BOUND) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `0 + r <= 200` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; `r * i`; `r:num`;
                    `s0:armstate`] READ_MEMORY_BYTES_SUB) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--5) THEN
      ARGS_32_TAC [`r:num`] THEN
      KECCAK_STATE_AT_TAC `st:int64` THEN
      LOCAL_XOR_BYTES_TAC
       [`read X0 s`; `read X1 s`; `0`; `r:num`; `keccak_absorb r P i`;
        `(M DIV 2 EXP (8 * r * i)) MOD 2 EXP (8 * r)`; `pc:num`;
        `read X30 s`] 6 THEN
      RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (7--9) THEN
      KECCAK_STATE_AT_TAC `st:int64` THEN
      KECCAK_STATE_THEN `st:int64` (fun v ->
        LOCAL_PERMUTE_TAC
         [`read X0 s`; v; `pc:num`; `read SP s`; `read X30 s`] 10) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (11--11) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
        ANTS_TAC THENL [UNDISCH_TAC `r * i + r <= mlen` THEN ARITH_TAC;
                        DISCH_THEN SUBST1_TAC] THEN
        AP_TERM_TAC THEN ARITH_TAC;
        REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`];
        AP_TERM_TAC THEN REWRITE_TAC[GSYM ADD1; keccak_absorb] THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[MULT_CLAUSES; EXP] THEN EXPAND_TAC "P" THEN
        CONV_TAC SYM_CONV THEN AP_TERM_TAC THEN
        MATCH_MP_TAC KECCAK_BLOCK_FULL THEN
        UNDISCH_TAC `r * i + r <= mlen` THEN ARITH_TAC];

      (*** The loop-back branch ***)

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_BLOCK_BOUND) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--1) THEN
      SUBGOAL_THEN `val(word(mlen - r * i):int64) = mlen - r * i /\
                    val(word r:int64) = r`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
        REWRITE_TAC[DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      DECIDE_FLAGS_TAC THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (2--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

      (*** The loop exit ***)

      ENSURES_INIT_TAC "s0" THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--1) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ABSORB_MOD_EQ]) THEN
      SUBGOAL_THEN `val(word(mlen MOD r):int64) = mlen MOD r /\
                    val(word r:int64) = r /\ mlen MOD r < r`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
       [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC VAL_WORD_EQ) THEN
        REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
        ASM_SIMP_TAC[MOD_LT_EQ; ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
        MP_TAC(SPECL [`mlen:num`; `r:num`] MOD_LT_EQ) THEN
        ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      DECIDE_FLAGS_TAC THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (2--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    ALL_TAC] THEN

  (*** The last block: the rest of the message, if any, and the padding ***)

  ABBREV_TAC `q = mlen DIV r` THEN ABBREV_TAC `t = mlen MOD r` THEN
  SUBGOAL_THEN `mlen = r * q + t /\ t < r` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q"; "t"] THEN
    MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  SUBGOAL_THEN `M < 2 EXP (8 * mlen)` ASSUME_TAC THENL
   [UNDISCH_TAC `read (memory :> bytes (m,mlen)) s0 = M` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(P DIV 2 EXP (8 * r * q)) MOD 2 EXP (8 * r) =
    M DIV 2 EXP (8 * r * q) +
    2 EXP (8 * t) * num_of_bytelist(keccak_pad r p mlen)`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "q"; "t"] THEN
    MATCH_MP_TAC KECCAK_BLOCK_LAST THEN ASM_SIMP_TAC[KECCAK_PAD_BOUND];
    ALL_TAC] THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--2) THEN
  ARGS_32_TAC [`t:num`] THEN
  MP_TAC(SPEC `r:num` WORD_ZX_SUB1_SMALL) THEN
  ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
                  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  SUBGOAL_THEN `val(word t:int64) = t` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `t = 0` THENL
   [(*** A whole number of blocks: p at byte 0 and 128 at byte r - 1 ***)

    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (3--9) THEN
    ABSORB_BYTE_FACT_TAC "s9" `p:num` THEN
    ABSORB_XOR_CALL_TAC `0` `1` `p:num` 10 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (11--17) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSORB_BYTE_FACT_TAC "s17" `128` THEN
    SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ABSORB_XOR_CALL_TAC `r - 1` `1` `128` 18 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (19--22) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[KECCAK_PAD_NUM] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    ASM_SIMP_TAC[MOD_MULT; ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
    SUBGOAL_THEN `M DIV 2 EXP (8 * r * q) = 0` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_LT THEN
      UNDISCH_TAC `M < 2 EXP (8 * mlen)` THEN ASM_REWRITE_TAC[ADD_CLAUSES];
      ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES; SUB_0] THEN
    COND_CASES_TAC THENL
     [UNDISCH_TAC `0 = r - 1` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(INST_TYPE [`:1600`,`:N`]
       (SPECL [`p:num`; `1`; `7`] WORD_XOR_DISJOINT_ADD)) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN
      TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
        REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN

  (*** Otherwise, first the t bytes of the message after the blocks ***)

  SUBGOAL_THEN
   `0 + t <= 200 /\ M DIV 2 EXP (8 * r * q) < 2 EXP (8 * t)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
    UNDISCH_TAC `M < 2 EXP (8 * mlen)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; `r * q`; `t:num`;
                `s2:armstate`] READ_MEMORY_BYTES_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (3--8) THEN
  ARGS_32_TAC [`t:num`] THEN
  ABSORB_XOR_CALL_TAC `0` `t:num` `M DIV 2 EXP (8 * r * q)` 9 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (10--10) THEN
  ARGS_32_TAC [`r - 1`] THEN PTR_DECIDE_FLAGS_TAC THEN
  ABSORB_CASE_FLAG_TAC `t = r - 1` THENL
   [(*** The padding is just the single byte p + 128 at byte r - 1 ***)

    FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `t = r - 1`)) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (11--18) THEN
    ABSORB_ORR_BYTE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (19--19) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSORB_BYTE_FACT_TAC "s19" `p + 128` THEN
    SUBGOAL_THEN `r - 1 + 1 <= 200` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ABSORB_XOR_CALL_TAC `r - 1` `1` `p + 128` 20 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (21--24) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(r * q + r - 1) MOD r = r - 1` ASSUME_TAC THENL
     [SUBGOAL_THEN `r * q + r - 1 = q * r + (r - 1)` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT; ARITH_RULE `0 < r ==> r - 1 < r`];
      ALL_TAC] THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[KECCAK_PAD_NUM] THEN REWRITE_TAC[MULT_CLAUSES; EXP] THEN
    MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[];

    (*** Otherwise p at byte t and 128 at byte r - 1 ***)

    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (11--17) THEN
    ARGS_32_TAC [`t:num`] THEN
    ABSORB_BYTE_FACT_TAC "s17" `p:num` THEN
    SUBGOAL_THEN `t + 1 <= 200 /\ r - 1 + 1 <= 200` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ABSORB_XOR_CALL_TAC `t:num` `1` `p:num` 18 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (19--25) THEN
    ARGS_32_TAC [`r - 1`] THEN
    ABSORB_BYTE_FACT_TAC "s25" `128` THEN
    ABSORB_XOR_CALL_TAC `r - 1` `1` `128` 26 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (27--30) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ABSORB_TAIL_ARITH_TAC THEN
    SUBGOAL_THEN
     `2 EXP (8 * (r - 1)) = 2 EXP (8 * t) * 2 EXP (8 * (r - t - 1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    W(fun (_,w) -> MP_TAC(ISPECL
      [`2 EXP (8 * t) * p`; `128`; `8 * t + 8 * (r - t - 1)`]
      (INST_TYPE [`:1600`,`:N`] WORD_XOR_DISJOINT_ADD))) THEN
    REWRITE_TAC[EXP_ADD] THEN ANTS_TAC THENL
     [REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ] THEN
      TRANS_TAC LTE_TRANS `2 EXP 8` THEN CONJ_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
        REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
      REWRITE_TAC[GSYM MULT_ASSOC] THEN DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
    MATCH_MP_TAC WORD_XOR_DISJOINT_ADD THEN ASM_REWRITE_TAC[]]);;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_XOR" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(m:int64) (st:int64) (r:num) (mlen:num) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
       (if mlen MOD r = 0
        then f_ev_t0 m st r mlen pc stackpointer returnaddress
        else if mlen MOD r = r - 1
        then f_ev_t1 m st r mlen pc stackpointer returnaddress
        else f_ev_t2 m st r mlen pc stackpointer returnaddress)
       (if mlen < r
        then f_ev_short m st r mlen pc stackpointer returnaddress
        else APPEND (f_ev_epil m st r mlen pc stackpointer returnaddress)
              (APPEND
                (ENUMERATEL (mlen DIV r)
                  (\i. f_ev_loop m st r mlen pc stackpointer returnaddress i))
                (f_ev_prol m st r mlen pc stackpointer returnaddress)))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `200 + mlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(m:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlk_keccak_absorb_once_loop1_exit`
   `\s. read X19 s = st /\ read X20 s = word(mlen MOD r) /\
        read X21 s = word_add m (word(r * mlen DIV r)) /\
        read X23 s = word r /\
        read SP s = word_add stackpointer (word 192) /\
        read (memory :> bytes64 (word_add stackpointer (word 192))) s =
        x19_init /\
        read (memory :> bytes64 (word_add stackpointer (word 200))) s =
        x20_init /\
        read (memory :> bytes64 (word_add stackpointer (word 208))) s =
        x21_init /\
        read (memory :> bytes64 (word_add stackpointer (word 216))) s =
        x22_init /\
        read (memory :> bytes64 (word_add stackpointer (word 224))) s =
        x23_init /\
        read (memory :> bytes64 (word_add stackpointer (word 232))) s =
        returnaddress` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THENL
     [(*** A message shorter than a block, with no loop ***)

      REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--18) THEN
      ARGS_32_TAC [`r:num`] THEN ABSORB_VAL_TAC THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (19--19) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      ALL_TAC] THEN

    (*** Otherwise the loop over the whole blocks ***)

    ENSURES_EVENTS_WHILE_UP2_TAC `mlen DIV r`
     `pc + mlk_keccak_absorb_once_loop1`
     `pc + mlk_keccak_absorb_once_loop1_exit`
     `\k s. read X19 s = st /\ read X20 s = word(mlen - r * k) /\
            read X21 s = word_add m (word(r * k)) /\
            read X22 s = word r /\ read X23 s = word r /\
            read SP s = word_add stackpointer (word 192) /\
            read (memory :> bytes64 (word_add stackpointer (word 192))) s =
            x19_init /\
            read (memory :> bytes64 (word_add stackpointer (word 200))) s =
            x20_init /\
            read (memory :> bytes64 (word_add stackpointer (word 208))) s =
            x21_init /\
            read (memory :> bytes64 (word_add stackpointer (word 216))) s =
            x22_init /\
            read (memory :> bytes64 (word_add stackpointer (word 224))) s =
            x23_init /\
            read (memory :> bytes64 (word_add stackpointer (word 232))) s =
            returnaddress` THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[DIV_EQ_0; ARITH_RULE `0 < r ==> ~(r = 0)`];

      REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--18) THEN
      ARGS_32_TAC [`r:num`] THEN ABSORB_VAL_TAC THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (19--20) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
      MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_BLOCK_BOUND) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `0 + r <= 200` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (1--5) THEN
      ARGS_32_TAC [`r:num`] THEN
      ABSORB_SAFE_CALL_TAC "H_XOR"
        [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `0`; `r:num`;
         `pc:num`; `read X30 s`]
        (ABSORB_SAFE_VARS @ [`i:num`]) 6 THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (7--9) THEN
      ABSORB_SAFE_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
         `read X30 s`]
        (ABSORB_SAFE_VARS @ [`i:num`]) 10 THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (11--12) THEN
      SUBGOAL_THEN `word_sub (word (mlen - r * i)) (word r):int64 =
                    word(mlen - r * (i + 1))` SUBST_ALL_TAC THENL
       [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
        ANTS_TAC THENL [UNDISCH_TAC `r * i + r <= mlen` THEN ARITH_TAC;
                        DISCH_THEN SUBST1_TAC] THEN
        AP_TERM_TAC THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `val(word(mlen - r * (i + 1)):int64) = mlen - r * (i + 1) /\
        val(word r:int64) = r`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
        REWRITE_TAC[DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_EXEC (13--13) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_LOOP_TEST) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`];
        ALL_TAC] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;

      REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ABSORB_MOD_EQ] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The last block ***)

    ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THEN
    ABSORB_SAFE_TAIL_TAC]);;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  ABSORB_CS_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC
   `pc + mlk_keccak_absorb_once_loop1_exit` ABSORB_CS_MID THEN CONJ_TAC THENL
   [ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THENL
     [ABSORB_CS_SHORT_TAC; ABSORB_CS_LOOP_TAC];
    ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THEN
    ABSORB_CS_TAIL_TAC]);;
