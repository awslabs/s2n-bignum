(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proof for mldsa_keccakf1600_extract_bytes (see keccakf1600_extract_bytes_spec.ml). *)
(* The proof is that of the same code in the gcc12_O2 image of               *)
(* mlkem-native (proofs/mlkem_native/gcc12_O2), with the names changed.      *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/keccakf1600_extract_bytes_spec.ml";;



(*** The zero-extended arguments off and len, and the test of len ***)

let EXTRACT_BYTES_ARGS_TAC =
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  FIRST_ASSUM(fun th ->
    if concl th <> `~(len = 0)` then NO_TAC else
    RULE_ASSUM_TAC(fun th' ->
      if concl th' = concl th then th' else REWRITE_RULE[th] th'));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As in common/fips202.ml, the state is a 1600-bit word  *)
(* S, and the bytes extracted are bytes off to off + len - 1 of it, which    *)
(* as a number are (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len).          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d:int64`; `off:num`; `len:num`; `S:1600 word`;
    `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; READ_MEMORY_WBYTES_VAL] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The case len = 0, where nothing is done ***)

  ASM_CASES_TAC `len = 0` THENL
   [ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1];
    ALL_TAC] THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `len:num` `pc + mldsa_keccakf1600_extract_bytes_loop1`
   `pc + mldsa_keccakf1600_extract_bytes_loop1_test`
   `\i s. read X0 s = word i /\ read X1 s = d /\ read X3 s = word len /\
          read X4 s = word_add a (word off) /\
          read X30 s = returnaddress /\
          read (memory :> bytes(a,200)) s = val(S:1600 word) /\
          read (memory :> bytes(d,i)) s =
          (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * i)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--2) THEN
    EXTRACT_BYTES_ARGS_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (3--6) THEN
    ARGS_32_TAC [`off:num`; `len:num`] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1];

    (*** The loop body, copying one byte ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`; `off + i`;
                  `s0:armstate`] READ_MEMORY_BYTES8_OF_NUM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_ADD; READ_MEMORY_BYTES_SNOC] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_16;
                DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8 /\ 4294967296 = 2 EXP 32 /\
                            18446744073709551616 = 2 EXP 64`;
                MOD_MOD_EXP_MIN] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MIN_CONV) THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; GSYM DIV_DIV] THEN
    SPEC_TAC(`val(S:1600 word) DIV 2 EXP (8 * off)`,`x:num`) THEN
    REWRITE_TAC[MULT_CLAUSES; MOD_MULT_MOD] THEN ARITH_TAC;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (2--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;
