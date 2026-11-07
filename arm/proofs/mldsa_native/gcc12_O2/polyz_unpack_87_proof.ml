(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 20 bits per coefficient, of 2^19 - a: the  *)
(* proof.                                                                    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/polyz_unpack_87_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. Each of the 128 iterations of the loop handles 5 bytes *)
(* and 2 coefficients.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_UNPACK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYZ_UNPACK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = MLDSA_NATIVE_POLYZ_UNPACK_87_GCC12_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `b:num->byte`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP_TAC `128` `pc + mldsa87_polyz_unpack_loop1`
   `pc + mldsa87_polyz_unpack_loop1_test`
   `\i s. read X0 s = word_add r (word(8 * i)) /\
          read X1 s = word_add a (word(5 * i)) /\
          read X6 s = word_add a (word 640) /\
          read X5 s = word 524288 /\
          read X30 s = returnaddress /\
          (!j. j < 640
               ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\
          (!j. j < 2 * i
               ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                   mld_polyz_unpack_19 b j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    CHUNK_INPUT_TAC `b:num->byte` 5 THEN
    ARM_STEPS_TAC EXEC (1--23) THEN
    CHUNK_FINAL_TAC mld_polyz_unpack_19 `b:num->byte`;

    (*** The loop-back branch and the exit ***)

    LOOP_BACK_TAC EXEC;
    LOOP_EXIT_TAC EXEC 3]);;
