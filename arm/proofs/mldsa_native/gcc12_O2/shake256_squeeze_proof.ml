(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squeezing bytes from a SHAKE256 context: the proof (see                   *)
(* shake256_squeeze_spec.ml).                                                *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/shake256_squeeze_spec.ml";;
needs "arm/proofs/utils/mldsa_native_squeeze.ml";;

(* ------------------------------------------------------------------------- *)
(* The 32-bit arithmetic on the position and the rate.                       *)
(* ------------------------------------------------------------------------- *)

let SQUEEZE_ZF_POS_LT = prove
 (`!p. p < 136
       ==> (val(word_sub (word_zx (word p:int64):int32) (word 136)) = 0
            <=> F)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `p < 136 ==> p < 4294967296 /\ p < 18446744073709551616`] THEN
  ASM_ARITH_TAC);;

let SQUEEZE_ZX4_SMALL = prove
 (`!p. p < 2 EXP 32
       ==> word_zx(word_zx(word_zx(word_zx(word p:int64):int32):int64):int32)
           :int64 = word p`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `p < 4294967296 ==> p < 18446744073709551616`]);;

let SQUEEZE_ZX_SUB_RATE = prove
 (`!p. p <= 136
       ==> word_zx(word_sub (word 136) (word_zx (word p:int64):int32)):int64 =
           word(136 - p)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_SUB_CASES;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `p <= 136 ==> p < 4294967296 /\ p < 18446744073709551616 /\
                136 - p < 4294967296 /\ 136 - p < 18446744073709551616`]);;

let SQUEEZE_ZX_SMALL = prove
 (`!x. x <= 136 ==> word_zx(word x:int64):int32 = word x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `x <= 136 ==> x < 4294967296 /\ x < 18446744073709551616`]);;

let SQUEEZE_VAL_WORD_RATE = prove
 (`!x. x <= 200 ==> val(word x:int64) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;

let SQUEEZE_VAL_OUTLEN = prove
 (`204 + outlen <= 18446744073709551616 ==> val(word outlen:int64) = outlen`,
  DISCH_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the calls.                                                    *)
(* ------------------------------------------------------------------------- *)

let LOCAL_EXTRACT_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mldsa_native_libmldsa_gcc12_O2_mc,
    MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_EXEC,
    0x0,mldsa_native_libmldsa_gcc12_O2_mc,
    MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT);;

let LOCAL_PERMUTE_TAC =
  ARM_SUBROUTINE_SIM_TAC
   (mldsa_native_libmldsa_gcc12_O2_mc,
    MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_EXEC,
    0x0,mldsa_native_libmldsa_gcc12_O2_mc,
    MLDSA_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. With b0 = pos DIV 136 the index of the block of the    *)
(* position (0, or 1 for pos = 136), the m = (pos + outlen - 1) DIV 136 + 1  *)
(* - b0 iterations of the loop at loop1 copy the bytes of blocks b0 to b0 +  *)
(* m - 1; the first starts at pos and does not permute, the others permute   *)
(* first. After k of them, t is the offset into the stream up to which the   *)
(* output has been written and K the number of permutations of S.            *)
(* ------------------------------------------------------------------------- *)

let SQUEEZE_INV =
 `\k s. read X23 s = ctx /\ read X25 s = out /\ read X24 s = word 136 /\
        read X21 s =
        word((if k = 0 then pos else if k < m then 136 * (b0 + k)
              else pos + outlen) - 136 * (if k = 0 then 0 else b0 + k - 1)) /\
        read X19 s =
        word(outlen - ((if k = 0 then pos else if k < m then 136 * (b0 + k)
                        else pos + outlen) - pos)) /\
        read X22 s =
        word((if k = 0 then pos else if k < m then 136 * (b0 + k)
              else pos + outlen) - pos) /\
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
        x24_init /\
        read (memory :> bytes64 (word_add stackpointer (word 240))) s =
        x25_init /\
        read (memory :> bytes64 (word_add stackpointer (word 248))) s =
        returnaddress /\
        read (memory :> bytes32(word_add ctx (word 200))) s = word pos /\
        read (memory :> bytes(ctx,200)) s =
        val(keccak_squeeze (if k = 0 then 0 else b0 + k - 1) S) /\
        read (memory :> bytes(out,
                (if k = 0 then pos else if k < m then 136 * (b0 + k)
                 else pos + outlen) - pos)) s =
        num_of_bytelist
         (list_of_seq (mld_keccak_squeeze_byte 136 S pos)
           ((if k = 0 then pos else if k < m then 136 * (b0 + k)
             else pos + outlen) - pos))`;;

(*** Joining the bytes of an iteration after the bytes before it ***)

let SQUEEZE_APPEND_TAC eqn =
  FIRST_X_ASSUM(fun th -> if concl th = eqn then SUBST1_TAC(SYM th)
                          else NO_TAC) THEN
  REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SQUEEZE_CHUNK THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `0 < 136 /\ 136 <= 200`];;

(*** The bytes of the first iteration, from S itself; bnd bounds them ***)

let SQUEEZE_FIRST_TAC n bnd =
  MP_TAC(SPECL [`136`; `S:1600 word`; `pos:num`; n] SQUEEZE_CHUNK_0) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC bnd THEN ARITH_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  ASM_REWRITE_TAC[];;

let MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`out:int64`; `outlen:num`; `ctx:int64`; `S:1600 word`; `pos:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 256 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `204 + outlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(ctx:int64)`; `val(out:int64)`] THEN
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
  ENSURES_PRESERVED_TAC "x24_init" `X24` THEN
  ENSURES_PRESERVED_TAC "x25_init" `X25` THEN

  (*** No output: nothing changes ***)

  ASM_CASES_TAC `outlen = 0` THENL
   [ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o
      check (fun th -> concl th = `outlen = 0`)) THEN
    ARM_STEPS_TAC EXEC (1--13) THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[mld_keccak_squeeze_state; list_of_seq; num_of_bytelist;
                    READ_MEMORY_BYTES_TRIVIAL; WORD_ZX_ZX_32_64_32];
    ALL_TAC] THEN

  (*** The number of iterations ***)

  ABBREV_TAC `b0 = pos DIV 136` THEN
  ABBREV_TAC `m = (pos + outlen - 1) DIV 136 + 1 - b0` THEN
  SUBGOAL_THEN `(b0 = 0 /\ pos < 136 \/ b0 = 1 /\ pos = 136) /\ 1 <= m /\
                136 * b0 <= pos /\
                (pos + outlen - 1) DIV 136 = b0 + m - 1`
  (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THENL
   [ASM_CASES_TAC `pos = 136` THENL
     [FIRST_X_ASSUM(fun th -> if concl th = `pos = 136`
                              then SUBST_ALL_TAC th else NO_TAC) THEN
      RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
      FIRST_X_ASSUM(fun th -> if concl th = `1 = b0`
                              then SUBST_ALL_TAC(SYM th) else NO_TAC) THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `1 <= (136 + outlen - 1) DIV 136` MP_TAC THENL
       [SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN
        UNDISCH_TAC `~(outlen = 0)` THEN ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `(136 + outlen - 1) DIV 136 + 1 - 1 = m` THEN ARITH_TAC;
      SUBGOAL_THEN `b0 = 0` SUBST_ALL_TAC THENL
       [EXPAND_TAC "b0" THEN SIMP_TAC[DIV_EQ_0; ARITH_EQ] THEN
        UNDISCH_TAC `pos <= 136` THEN UNDISCH_TAC `~(pos = 136)` THEN
        ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[MULT_CLAUSES; LE_0] THEN
      UNDISCH_TAC `(pos + outlen - 1) DIV 136 + 1 - 0 = m` THEN
      UNDISCH_TAC `pos <= 136` THEN UNDISCH_TAC `~(pos = 136)` THEN ARITH_TAC];
    ALL_TAC] THEN

  ENSURES_WHILE_UP2_TAC `m:num` `pc + mldsa_shake256_squeeze_loop1`
   `pc + mldsa_shake256_squeeze_loop1_exit` SQUEEZE_INV THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `1 <= m` THEN ARITH_TAC;

    (*** The prologue: nothing written yet ***)

    ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC EXEC (1--7) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[UNDISCH SQUEEZE_VAL_OUTLEN;
                                ASSUME `~(outlen = 0)`]) THEN
    ARM_STEPS_TAC EXEC (8--13) THEN ARGS_64_TAC [`pos:num`] THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[SUB_0; SUB_REFL; keccak_squeeze; list_of_seq;
                    num_of_bytelist; READ_MEMORY_BYTES_TRIVIAL] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0];

    (*** The loop body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `t = if i = 0 then pos else 136 * (b0 + i)` THEN
    ABBREV_TAC `K = if i = 0 then 0 else b0 + i - 1` THEN
    SUBGOAL_THEN
     `pos <= t /\ t - pos < outlen /\ t <= 136 * (b0 + i) + 136 /\
      136 * (b0 + i) <= t /\
      ((i = 0 /\ b0 = 0 /\ t = pos /\ K = 0 /\ pos < 136) \/
       (t = 136 * (b0 + i) /\ K + 1 = b0 + i)) /\
      (i + 1 < m ==> 136 * (b0 + i) + 136 < pos + outlen) /\
      (~(i + 1 < m) ==> pos + outlen <= 136 * (b0 + i) + 136)`
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THENL
     [MP_TAC(SPECL [`pos + outlen - 1`; `136`] DIVISION) THEN
      ASM_REWRITE_TAC[ARITH_EQ] THEN
      MAP_EVERY UNDISCH_TAC
       [`(if i = 0 then pos else 136 * (b0 + i)) = t`;
        `(if i = 0 then 0 else b0 + i - 1) = K`;
        `b0 = 0 /\ pos < 136 \/ b0 = 1 /\ pos = 136`; `i < m`;
        `~(outlen = 0)`; `pos <= 136`; `136 * b0 <= pos`] THEN
      SPEC_TAC(`(pos + outlen - 1) MOD 136`,`u:num`) THEN
      ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THENL
       [GEN_TAC THEN UNDISCH_TAC `1 <= m` THEN ARITH_TAC;
        UNDISCH_TAC `~(i = 0)` THEN UNDISCH_TAC `1 <= m` THEN ARITH_TAC];
      ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
      is_disj(concl th) && free_in `K:num` (concl th))) THENL
     [

      (*** The first iteration, from pos < 136, without a permutation ***)

      FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th ->
        concl th = `i = 0 /\ b0 = 0 /\ t = pos /\ K = 0 /\ pos < 136`)) THEN
      REWRITE_TAC[ASSUME `t = pos`; ASSUME `K = 0`; ASSUME `i = 0`;
                  ASSUME `b0 = 0`; MULT_CLAUSES; SUB_0; SUB_REFL;
                  ADD_CLAUSES] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC EXEC (1--1) THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [MP (SPEC `pos:num` SQUEEZE_ZF_POS_LT) (ASSUME `pos < 136`)]) THEN
      ARM_STEPS_TAC EXEC (2--10) THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [MP (SPEC `pos:num` SQUEEZE_ZX4_SMALL)
           (MP (ARITH_RULE `pos < 136 ==> pos < 2 EXP 32`)
               (ASSUME `pos < 136`));
        MP (SPEC `pos:num` SQUEEZE_ZX_SUB_RATE) (ASSUME `pos <= 136`);
        SUB_0; ASSUME `t = pos`; SUB_REFL]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [VAL_WORD_SUB_EQ_0; UNDISCH SQUEEZE_VAL_OUTLEN;
        MP (SPEC `136 - pos` SQUEEZE_VAL_WORD_RATE)
           (ARITH_RULE `136 - pos <= 200`)]) THEN
      ASM_CASES_TAC `outlen < 136 - pos` THENL
       [

        (*** All the output from the rest of the block ***)

        SUBGOAL_THEN `~(0 + 1 < m)` ASSUME_TAC THENL
         [DISCH_TAC THEN
          UNDISCH_TAC `i + 1 < m ==> 136 * (b0 + i) + 136 < pos + outlen` THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `outlen < 136 - pos` THEN UNDISCH_TAC `pos < 136` THEN
          ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN
         `(outlen <= 136 - pos <=> T) /\ (136 - pos = outlen <=> F)`
         (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
         [UNDISCH_TAC `outlen < 136 - pos` THEN ARITH_TAC; ALL_TAC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[keccak_squeeze]) THEN
        ARM_STEPS_TAC EXEC (11--15) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[SUB_0]) THEN
        ARGS_32_TAC [`outlen:num`] THEN
        SUBGOAL_THEN `pos + outlen <= 200` ASSUME_TAC THENL
         [UNDISCH_TAC `outlen < 136 - pos` THEN ARITH_TAC; ALL_TAC] THEN
        KECCAK_STATE_AT_TAC `ctx:int64` THEN
        LOCAL_EXTRACT_TAC [`read X0 s`; `read X1 s`; `pos:num`; `outlen:num`;
                           `S:1600 word`; `pc:num`; `read X30 s`] 16 THEN
        ARM_STEPS_TAC EXEC (17--19) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[SUB_0; WORD_SUB_REFL; VAL_WORD_0]) THEN
        ENSURES_FINAL_STATE_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
        ASM_REWRITE_TAC[ARITH_EQ; keccak_squeeze; MULT_CLAUSES; SUB_0;
                        ADD_SUB2;
                        SUB_REFL] THEN
        CONJ_TAC THENL
         [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
                      DIMINDEX_32; DIMINDEX_64] THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          SUBGOAL_THEN
           `pos < 4294967296 /\ outlen < 4294967296 /\
            pos + outlen < 4294967296`
          STRIP_ASSUME_TAC THENL
           [UNDISCH_TAC `pos + outlen <= 200` THEN ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[MOD_LT;
            ARITH_RULE `x < 4294967296 ==> x < 18446744073709551616`];
          SQUEEZE_FIRST_TAC `outlen:num` `outlen < 136 - pos`];

        ASM_CASES_TAC `outlen = 136 - pos` THENL
         [

          (*** All the output from the rest of the block, exactly ***)

          SUBGOAL_THEN `~(0 + 1 < m)` ASSUME_TAC THENL
           [DISCH_TAC THEN
            UNDISCH_TAC
             `i + 1 < m ==> 136 * (b0 + i) + 136 < pos + outlen` THEN
            ASM_REWRITE_TAC[] THEN
            UNDISCH_TAC `outlen = 136 - pos` THEN UNDISCH_TAC `pos < 136` THEN
            ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN
           `(outlen <= 136 - pos <=> T) /\ (136 - pos = outlen <=> T)`
           (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
           [UNDISCH_TAC `outlen = 136 - pos` THEN ARITH_TAC; ALL_TAC] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[keccak_squeeze]) THEN
          SUBGOAL_THEN `pos + (136 - pos) <= 200 /\ 136 - pos <= outlen`
          STRIP_ASSUME_TAC THENL
           [UNDISCH_TAC `pos < 136` THEN UNDISCH_TAC `outlen = 136 - pos` THEN
            ARITH_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC EXEC (11--12) THEN KECCAK_STATE_AT_TAC `ctx:int64` THEN
          LOCAL_EXTRACT_TAC [`read X0 s`; `read X1 s`; `pos:num`; `136 - pos`;
                             `S:1600 word`; `pc:num`; `read X30 s`] 13 THEN
          RULE_ASSUM_TAC(REWRITE_RULE[SUB_REFL; SUB_0]) THEN
          ARM_STEPS_TAC EXEC (14--15) THEN
          SUBGOAL_THEN
           `val(word_sub (word outlen) (word (136 - pos)):int64) = 0 <=> T`
           (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
           [REWRITE_TAC[VAL_WORD_SUB_EQ_0; UNDISCH SQUEEZE_VAL_OUTLEN;
                        MP (SPEC `136 - pos` SQUEEZE_VAL_WORD_RATE)
                           (ARITH_RULE `136 - pos <= 200`)] THEN
            UNDISCH_TAC `outlen = 136 - pos` THEN ARITH_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC EXEC (16--16) THEN ENSURES_FINAL_STATE_TAC THEN
          RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
          ASM_REWRITE_TAC[ARITH_EQ; ADD_CLAUSES; MULT_CLAUSES; SUB_0;
                          keccak_squeeze; SUB_REFL] THEN
          SUBGOAL_THEN `pos + 136 - pos = 136` SUBST1_TAC THENL
           [UNDISCH_TAC `pos < 136` THEN ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0; SUB_REFL] THEN
          SQUEEZE_FIRST_TAC `136 - pos` `pos < 136`;

          (*** The rest of the block, then more ***)

          SUBGOAL_THEN `0 + 1 < m` ASSUME_TAC THENL
           [ASM_CASES_TAC `0 + 1 < m` THEN ASM_REWRITE_TAC[] THEN
            UNDISCH_TAC
             `~(i + 1 < m) ==> pos + outlen <= 136 * (b0 + i) + 136` THEN
            ASM_REWRITE_TAC[] THEN
            UNDISCH_TAC `~(outlen < 136 - pos)` THEN
            UNDISCH_TAC `~(outlen = 136 - pos)` THEN
            UNDISCH_TAC `pos < 136` THEN ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN
           `(outlen <= 136 - pos <=> F) /\ (136 - pos = outlen <=> F)`
           (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
           [UNDISCH_TAC `~(outlen < 136 - pos)` THEN
            UNDISCH_TAC `~(outlen = 136 - pos)` THEN ARITH_TAC;
            ALL_TAC] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[keccak_squeeze]) THEN
          SUBGOAL_THEN `pos + (136 - pos) <= 200 /\ 136 - pos <= outlen`
          STRIP_ASSUME_TAC THENL
           [UNDISCH_TAC `pos < 136` THEN
            UNDISCH_TAC `~(outlen < 136 - pos)` THEN
            ARITH_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC EXEC (11--12) THEN KECCAK_STATE_AT_TAC `ctx:int64` THEN
          LOCAL_EXTRACT_TAC [`read X0 s`; `read X1 s`; `pos:num`; `136 - pos`;
                             `S:1600 word`; `pc:num`; `read X30 s`] 13 THEN
          RULE_ASSUM_TAC(REWRITE_RULE[SUB_REFL; SUB_0]) THEN
          ARM_STEPS_TAC EXEC (14--15) THEN
          SUBGOAL_THEN
           `val(word_sub (word outlen) (word (136 - pos)):int64) = 0 <=> F`
           (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th)
          THENL
           [REWRITE_TAC[VAL_WORD_SUB_EQ_0; UNDISCH SQUEEZE_VAL_OUTLEN;
                        MP (SPEC `136 - pos` SQUEEZE_VAL_WORD_RATE)
                           (ARITH_RULE `136 - pos <= 200`)] THEN
            UNDISCH_TAC `~(outlen = 136 - pos)` THEN ARITH_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC EXEC (16--16) THEN ENSURES_FINAL_STATE_TAC THEN
          RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
          ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_CLAUSES; MULT_CLAUSES; SUB_0;
                          keccak_squeeze; SUB_REFL] THEN
          CONJ_TAC THENL
           [REWRITE_TAC[WORD_SUB] THEN ASM_REWRITE_TAC[];
            SQUEEZE_FIRST_TAC `136 - pos` `pos < 136`]]];

      (*** A later iteration: permute, then copy from the start ***)

      FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (fun th ->
        is_conj(concl th) && free_in `K:num` (concl th) &&
        free_in `t:num` (concl th) && not(is_disj(concl th)))) THEN
      SUBGOAL_THEN `t - 136 * K = 136` (fun th -> REWRITE_TAC[th] THEN
                                                 ASSUME_TAC th) THENL
       [UNDISCH_TAC `t = 136 * (b0 + i)` THEN UNDISCH_TAC `K + 1 = b0 + i` THEN
        ARITH_TAC;
        ALL_TAC] THEN
      ENSURES_INIT_TAC "s0" THEN ARM_STEPS_TAC EXEC (1--4) THEN
      KECCAK_STATE_AT_TAC `ctx:int64` THEN
      LOCAL_PERMUTE_TAC [`read X0 s`; `keccak_squeeze K (S:1600 word)`;
                         `pc:num`; `read SP s`; `read X30 s`] 5 THEN
      SUBGOAL_THEN
       `keccak_f1600 (keccak_squeeze K (S:1600 word)) =
        keccak_squeeze (b0 + i) S`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [REWRITE_TAC[GSYM(ASSUME `K + 1 = b0 + i`); GSYM ADD1; keccak_squeeze];
        ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
      ARM_STEPS_TAC EXEC (6--14) THEN
      FIRST_X_ASSUM(fun th -> if concl th = `t = 136 * (b0 + i)`
                              then SUBST_ALL_TAC th else NO_TAC) THEN
      ABBREV_TAC `togo = outlen - (136 * (b0 + i) - pos)` THEN
      SUBGOAL_THEN `togo <= outlen /\ 0 < togo` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "togo" THEN UNDISCH_TAC `136 * (b0 + i) - pos < outlen` THEN
        ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `val(word togo:int64) = togo`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; VAL_WORD_SUB_EQ_0])) THENL
       [MATCH_MP_TAC SQUEEZE_VAL_WORD_LE THEN EXISTS_TAC `outlen:num` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV(fun t ->
        if t = `val(word 136:int64)` then WORD_REDUCE_CONV t
        else failwith ""))) THEN
      ASM_CASES_TAC `togo < 136` THENL
       [

        (*** The last bytes, fewer than a block ***)

        SUBGOAL_THEN `~(i + 1 < m)` ASSUME_TAC THENL
         [DISCH_TAC THEN
          UNDISCH_TAC `i + 1 < m ==> 136 * (b0 + i) + 136 < pos + outlen` THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `togo < 136` THEN EXPAND_TAC "togo" THEN
          UNDISCH_TAC `pos <= 136 * (b0 + i)` THEN
          UNDISCH_TAC `136 * (b0 + i) - pos < outlen` THEN ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `(togo <= 136 <=> T) /\ (136 = togo <=> F)`
         (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
         [UNDISCH_TAC `togo < 136` THEN ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `(136 * (b0 + i) - pos) + togo = outlen` ASSUME_TAC THENL
         [EXPAND_TAC "togo" THEN
          UNDISCH_TAC `136 * (b0 + i) - pos < outlen` THEN ARITH_TAC;
          ALL_TAC] THEN
        ARM_STEPS_TAC EXEC (15--19) THEN ARGS_32_TAC [`togo:num`] THEN
        SUBGOAL_THEN `0 + togo <= 200` ASSUME_TAC THENL
         [UNDISCH_TAC `togo < 136` THEN ARITH_TAC; ALL_TAC] THEN
        KECCAK_STATE_AT_TAC `ctx:int64` THEN
        LOCAL_EXTRACT_TAC [`read X0 s`; `read X1 s`; `0`; `togo:num`;
                           `keccak_squeeze (b0 + i) (S:1600 word)`; `pc:num`;
                           `read X30 s`] 20 THEN
        ARM_STEPS_TAC EXEC (21--23) THEN ENSURES_FINAL_STATE_TAC THEN
        ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB; WORD_SUB_REFL;
                        VAL_WORD_0] THEN
        REWRITE_TAC[ADD_SUB2] THEN REPEAT CONJ_TAC THENL
         [AP_TERM_TAC THEN EXPAND_TAC "togo" THEN
          UNDISCH_TAC `pos <= 136 * (b0 + i)` THEN
          UNDISCH_TAC `136 * (b0 + i) - pos < outlen` THEN ARITH_TAC;
          REWRITE_TAC[SUB_REFL];
          REWRITE_TAC[GSYM WORD_ADD] THEN ASM_REWRITE_TAC[];
          SQUEEZE_APPEND_TAC `(136 * (b0 + i) - pos) + togo = outlen` THEN
          UNDISCH_TAC `pos <= 136 * (b0 + i)` THEN
          UNDISCH_TAC `togo < 136` THEN
          ARITH_TAC];

        ASM_CASES_TAC `togo = 136` THENL
         [

          (*** The last bytes, a whole block ***)

          SUBGOAL_THEN `~(i + 1 < m)` ASSUME_TAC THENL
           [DISCH_TAC THEN
            UNDISCH_TAC
             `i + 1 < m ==> 136 * (b0 + i) + 136 < pos + outlen` THEN
            ASM_REWRITE_TAC[] THEN
            UNDISCH_TAC `togo = 136` THEN EXPAND_TAC "togo" THEN
            UNDISCH_TAC `pos <= 136 * (b0 + i)` THEN
            UNDISCH_TAC `136 * (b0 + i) - pos < outlen` THEN ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN `(togo <= 136 <=> T) /\ (136 = togo <=> T)`
           (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
           [UNDISCH_TAC `togo = 136` THEN ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `(136 * (b0 + i) - pos) + 136 = outlen` ASSUME_TAC THENL
           [UNDISCH_TAC `togo = 136` THEN EXPAND_TAC "togo" THEN
            UNDISCH_TAC `136 * (b0 + i) - pos < outlen` THEN ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN `(136 * (b0 + i) - pos) + 136 <= outlen`
          ASSUME_TAC THENL
           [UNDISCH_TAC `(136 * (b0 + i) - pos) + 136 = outlen` THEN ARITH_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC EXEC (15--16) THEN KECCAK_STATE_AT_TAC `ctx:int64` THEN
          LOCAL_EXTRACT_TAC [`read X0 s`; `read X1 s`; `0`; `136`;
                             `keccak_squeeze (b0 + i) (S:1600 word)`; `pc:num`;
                             `read X30 s`] 17 THEN
          ARM_STEPS_TAC EXEC (18--19) THEN
          RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `togo = 136`; WORD_SUB_REFL;
                                      VAL_WORD_0]) THEN
          ARM_STEPS_TAC EXEC (20--20) THEN ENSURES_FINAL_STATE_TAC THEN
          ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB; ADD_SUB2;
                          WORD_SUB_REFL] THEN
          REPEAT CONJ_TAC THENL
           [AP_TERM_TAC THEN
            UNDISCH_TAC `(136 * (b0 + i) - pos) + 136 = outlen` THEN
            UNDISCH_TAC `pos <= 136 * (b0 + i)` THEN ARITH_TAC;
            REWRITE_TAC[SUB_REFL];
            REWRITE_TAC[GSYM WORD_ADD] THEN ASM_REWRITE_TAC[];
            SQUEEZE_APPEND_TAC `(136 * (b0 + i) - pos) + 136 = outlen` THEN
            UNDISCH_TAC `pos <= 136 * (b0 + i)` THEN ARITH_TAC];

          (*** A whole block, then more ***)

          SUBGOAL_THEN `i + 1 < m` ASSUME_TAC THENL
           [ASM_CASES_TAC `i + 1 < m` THEN ASM_REWRITE_TAC[] THEN
            UNDISCH_TAC
             `~(i + 1 < m) ==> pos + outlen <= 136 * (b0 + i) + 136` THEN
            ASM_REWRITE_TAC[] THEN
            UNDISCH_TAC `~(togo < 136)` THEN UNDISCH_TAC `~(togo = 136)` THEN
            EXPAND_TAC "togo" THEN UNDISCH_TAC `pos <= 136 * (b0 + i)` THEN
            ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN `(togo <= 136 <=> F) /\ (136 = togo <=> F)`
           (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
           [UNDISCH_TAC `~(togo < 136)` THEN UNDISCH_TAC `~(togo = 136)` THEN
            ARITH_TAC;
            ALL_TAC] THEN
          SUBGOAL_THEN `(136 * (b0 + i) - pos) + 136 <= outlen`
          ASSUME_TAC THENL
           [UNDISCH_TAC `outlen - (136 * (b0 + i) - pos) = togo` THEN
            UNDISCH_TAC `~(togo < 136)` THEN ARITH_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC EXEC (15--16) THEN KECCAK_STATE_AT_TAC `ctx:int64` THEN
          LOCAL_EXTRACT_TAC [`read X0 s`; `read X1 s`; `0`; `136`;
                             `keccak_squeeze (b0 + i) (S:1600 word)`; `pc:num`;
                             `read X30 s`] 17 THEN
          ARM_STEPS_TAC EXEC (18--19) THEN
          SUBGOAL_THEN `val(word_sub (word togo) (word 136):int64) = 0 <=> F`
           (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
           [REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
            SUBGOAL_THEN `val(word togo:int64) = togo` SUBST1_TAC THENL
             [MATCH_MP_TAC SQUEEZE_VAL_WORD_LE THEN
              EXISTS_TAC `outlen:num` THEN
              ASM_REWRITE_TAC[];
              ALL_TAC] THEN
            CONV_TAC WORD_REDUCE_CONV THEN UNDISCH_TAC `~(togo = 136)` THEN
            ARITH_TAC;
            ALL_TAC] THEN
          ARM_STEPS_TAC EXEC (20--20) THEN ENSURES_FINAL_STATE_TAC THEN
          ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
          REPEAT CONJ_TAC THENL
           [AP_TERM_TAC THEN ARITH_TAC;
            SUBGOAL_THEN `outlen - (136 * (b0 + i + 1) - pos) = togo - 136`
            SUBST1_TAC THENL
             [EXPAND_TAC "togo" THEN UNDISCH_TAC `pos <= 136 * (b0 + i)` THEN
              ARITH_TAC;
              ALL_TAC] THEN
            REWRITE_TAC[WORD_SUB] THEN
            SUBGOAL_THEN `136 <= togo` (fun th -> REWRITE_TAC[th]) THEN
            UNDISCH_TAC `~(togo < 136)` THEN ARITH_TAC;
            REWRITE_TAC[GSYM WORD_ADD] THEN AP_TERM_TAC THEN
            UNDISCH_TAC `pos <= 136 * (b0 + i)` THEN ARITH_TAC;
            SUBGOAL_THEN
             `(136 * (b0 + i) - pos) + 136 = 136 * (b0 + i + 1) - pos`
            ASSUME_TAC THENL
             [UNDISCH_TAC `pos <= 136 * (b0 + i)` THEN ARITH_TAC;
              ALL_TAC] THEN
            SQUEEZE_APPEND_TAC
             `(136 * (b0 + i) - pos) + 136 = 136 * (b0 + i + 1) - pos` THEN
            UNDISCH_TAC `pos <= 136 * (b0 + i)` THEN ARITH_TAC]]]];

    (*** The epilogue: store the position ***)

    ENSURES_INIT_TAC "s0" THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LT_REFL;
      MP (ARITH_RULE `1 <= m ==> ~(m = 0)`) (ASSUME `1 <= m`)]) THEN
    ARM_STEPS_TAC EXEC (1--7) THEN ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[ADD_SUB2; mld_keccak_squeeze_state] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_SUB2]) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQUEEZE_ZX_SMALL THEN
    MP_TAC(SPECL [`pos + outlen - 1`; `136`] DIVISION) THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `(x:num) * 136 = 136 * x`] THEN
    SPEC_TAC(`(pos + outlen - 1) MOD 136`,`u:num`) THEN
    SPEC_TAC(`b0 + m - 1`,`q:num`) THEN REPEAT GEN_TAC THEN
    UNDISCH_TAC `~(outlen = 0)` THEN ARITH_TAC]);;
