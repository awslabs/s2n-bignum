(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proof for mldsa_shake128x4_squeezeblocks (see                         *)
(* shake128x4_squeezeblocks_spec.ml): that of the same code in the gcc12_O2  *)
(* image of mlkem-native (proofs/mlkem_native/gcc12_O2), with the names      *)
(* changed.                                                                  *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/shake128x4_squeezeblocks_spec.ml";;



(* ------------------------------------------------------------------------- *)
(* Tactics for the four states, the number of blocks and the loop counter.   *)
(* ------------------------------------------------------------------------- *)

let SQX4_STATES_TAC =
  MAP_EVERY KECCAK_STATE_AT_TAC
   [`st:int64`; `word_add (st:int64) (word 200)`;
    `word_add (st:int64) (word 400)`; `word_add (st:int64) (word 600)`];;

let SQX4_BOUND_TAC =
  SUBGOAL_THEN `800 + 168 * nblocks <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(out0:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word nblocks:int64) = nblocks` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC];;

let SQX4_PRESERVED_TAC =
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23` THEN
  ENSURES_PRESERVED_TAC "x24_init" `X24`;;

let SQX4_NONZERO_TAC =
  let t1 = `val(word nblocks:int64) = nblocks` and t2 = `~(nblocks = 0)` in
  RULE_ASSUM_TAC(fun th ->
    if concl th = t1 || concl th = t2 then th
    else REWRITE_RULE[ASSUME t1; ASSUME t2] th);;

let SQX4_COUNTER_TAC =
  SUBGOAL_THEN `word_sub (word (nblocks - i)) (word 1):int64 =
                word(nblocks - (i + 1))` SUBST_ALL_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
    ANTS_TAC THENL [UNDISCH_TAC `i < nblocks` THEN ARITH_TAC;
                    DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word(nblocks - (i + 1)):int64) = nblocks - (i + 1)`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(nblocks - (i + 1) = 0) <=> i + 1 < nblocks`
  SUBST_ALL_TAC THENL [ARITH_TAC; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mldsa_shake128_squeezeblocks, for each of the   *)
(* four states S, block i of its output, as a number, is the first 168       *)
(* bytes of keccak_squeeze (i + 1) S, and the state becomes                  *)
(* keccak_squeeze nblocks S.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`; `nblocks:num`;
    `st:int64`; `S0:1600 word`; `S1:1600 word`; `S2:1600 word`;
    `S3:1600 word`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 272 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The case nblocks = 0, where nothing is done ***)

  ASM_CASES_TAC `nblocks = 0` THENL
   [ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze];
    ALL_TAC] THEN
  SQX4_BOUND_TAC THEN SQX4_PRESERVED_TAC THEN

  (*** The loop, with i blocks done ***)

  ENSURES_WHILE_UP2_TAC `nblocks:num`
   `pc + mldsa_shake128x4_squeezeblocks_loop1`
   `pc + mldsa_shake128x4_squeezeblocks_loop1_exit`
   `\i s. read X19 s = word_add out3 (word(168 * i)) /\
          read X20 s = word_add out2 (word(168 * i)) /\
          read X21 s = word_add out1 (word(168 * i)) /\
          read X22 s = word_add out0 (word(168 * i)) /\
          read X23 s = word(nblocks - i) /\
          read X24 s = st /\
          read SP s = word_add stackpointer (word 208) /\
          read (memory :> bytes64 (word_add stackpointer (word 208))) s =
          x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 216))) s =
          x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 224))) s =
          x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 232))) s =
          x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 240))) s =
          x23_init /\
          read (memory :> bytes64 (word_add stackpointer (word 248))) s =
          x24_init /\
          read (memory :> bytes64 (word_add stackpointer (word 256))) s =
          returnaddress /\
          read (memory :> bytes(out0,168 * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * 168 * j) *
                val(keccak_squeeze (j + 1) S0) MOD 2 EXP (8 * 168)) /\
          read (memory :> bytes(out1,168 * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * 168 * j) *
                val(keccak_squeeze (j + 1) S1) MOD 2 EXP (8 * 168)) /\
          read (memory :> bytes(out2,168 * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * 168 * j) *
                val(keccak_squeeze (j + 1) S2) MOD 2 EXP (8 * 168)) /\
          read (memory :> bytes(out3,168 * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * 168 * j) *
                val(keccak_squeeze (j + 1) S3) MOD 2 EXP (8 * 168)) /\
          read (memory :> bytes(st,200)) s =
          val(keccak_squeeze i (S0:1600 word)) /\
          read (memory :> bytes(word_add st (word 200),200)) s =
          val(keccak_squeeze i (S1:1600 word)) /\
          read (memory :> bytes(word_add st (word 400),200)) s =
          val(keccak_squeeze i (S2:1600 word)) /\
          read (memory :> bytes(word_add st (word 600),200)) s =
          val(keccak_squeeze i (S3:1600 word))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--1) THEN
    SQX4_NONZERO_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (2--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze];

    (*** The loop body: permute, extract a block of each, the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `168 * i + 168 <= 168 * nblocks` ASSUME_TAC THENL
     [UNDISCH_TAC `i < nblocks` THEN ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--2) THEN
    SQX4_STATES_TAC THEN
    ARM_SUBROUTINE_SIM_TAC
     (mldsa_native_libmldsa_gcc12_O2_mc,
      MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC,
      0x0,mldsa_native_libmldsa_gcc12_O2_mc,
    MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600)
     [`read X0 s`; `keccak_squeeze i (S0:1600 word)`;
      `keccak_squeeze i (S1:1600 word)`; `keccak_squeeze i (S2:1600 word)`;
      `keccak_squeeze i (S3:1600 word)`; `pc:num`; `read SP s`;
      `read X30 s`] 3 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (4--11) THEN
    SQX4_STATES_TAC THEN
    ARM_SUBROUTINE_SIM_TAC
     (mldsa_native_libmldsa_gcc12_O2_mc,
      MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC,
      0x0,mldsa_native_libmldsa_gcc12_O2_mc,
    MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT)
     [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`; `0`;
      `168`; `keccak_f1600(keccak_squeeze i (S0:1600 word))`;
      `keccak_f1600(keccak_squeeze i (S1:1600 word))`;
      `keccak_f1600(keccak_squeeze i (S2:1600 word))`;
      `keccak_f1600(keccak_squeeze i (S3:1600 word))`; `pc:num`;
      `read SP s`; `read X30 s`] 12 THEN
    ARM_STEPS_TAC MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (13--18) THEN
    SQX4_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        REWRITE_TAC[ARITH_RULE `168 * (i + 1) = 168 * i + 168`] THEN
        NO_TAC) THEN
    TRY(REWRITE_TAC[GSYM ADD1; keccak_squeeze] THEN NO_TAC) THEN
    REWRITE_TAC[ARITH_RULE `168 * (i + 1) = 168 * i + 168`] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM ADD1; NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1];

    (*** The return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;
