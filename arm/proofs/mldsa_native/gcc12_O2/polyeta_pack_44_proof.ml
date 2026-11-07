(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 3 bits per coefficient, of 2 - a: the proof. *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/polyeta_pack_44_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. Each of the 32 iterations of the loop handles 8        *)
(* coefficients and 3 bytes.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYETA_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = MLDSA_NATIVE_POLYETA_PACK_44_GCC12_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `x:num->int32`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP_TAC `32` `pc + mldsa44_polyeta_pack_loop1`
   `pc + mldsa44_polyeta_pack_loop1_test`
   `\i s. read X0 s = word_add r (word(3 * i)) /\
          read X1 s = word_add a (word(32 * i)) /\
          read X10 s = word_add a (word 1024) /\
          read X5 s = word 2 /\
          read X30 s = returnaddress /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   x j) /\
          (!j. j < 3 * i
               ==> read(memory :> bytes8(word_add r (word j))) s =
                   mld_polyeta_pack_2 x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    CHUNK_INPUT_TAC `x:num->int32` 8 THEN
    ARM_STEPS_TAC EXEC (1--33) THEN
    CHUNK_FINAL_TAC mld_polyeta_pack_2 `x:num->int32`;

    (*** The loop-back branch and the exit ***)

    LOOP_BACK_TAC EXEC;
    LOOP_EXIT_TAC EXEC 3]);;
