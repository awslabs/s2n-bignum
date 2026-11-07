(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 3 bits per coefficient, of 2 - a: the      *)
(* proof.                                                                    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/polyeta_unpack_87_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. Each of the 32 iterations of the loop handles 3 bytes  *)
(* and 8 coefficients.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYETA_UNPACK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = MLDSA_NATIVE_POLYETA_UNPACK_87_GCC12_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `b:num->byte`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP_TAC `32` `pc + mldsa87_polyeta_unpack_loop1`
   `pc + mldsa87_polyeta_unpack_loop1_test`
   `\i s. read X0 s = word_add r (word(32 * i)) /\
          read X1 s = word_add a (word(3 * i)) /\
          read X5 s = word_add a (word 96) /\
          read Q2 s = word 158456325065422163343096938498 /\
          read X30 s = returnaddress /\
          (!j. j < 96
               ==> read(memory :> bytes8(word_add a (word j))) s = b j) /\
          (!j. j < 8 * i
               ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                   mld_polyeta_unpack_2 b j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    CHUNK_INPUT_TAC `b:num->byte` 3 THEN
    ARM_STEPS_TAC EXEC (1--44) THEN WIDE_STORE_SPLIT_TAC `r:int64` 32 THEN
    CHUNK_FINAL_TAC mld_polyeta_unpack_2 `b:num->byte`;

    (*** The loop-back branch and the exit ***)

    LOOP_BACK_TAC EXEC;
    LOOP_EXIT_TAC EXEC 3]);;
