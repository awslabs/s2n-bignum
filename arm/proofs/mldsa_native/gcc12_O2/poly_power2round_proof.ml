(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Splitting at 2^13: the proof (see poly_power2round_spec.ml).              *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/poly_power2round_spec.ml";;

(*** The values computed in each lane: with y = a + 2^12 - 1, the high ***)
(*** part y >> 13 and the low part a - (y & ~(2^13 - 1))                ***)

let POWER2ROUND_LANES = prove
 (`!x:int32.
     word_ishr (word_add x (word 4095)) 13 = mld_power2round_hi x /\
     word_sub x (word_and (word 4294959104) (word_add x (word 4095))) =
     mld_power2round_lo x`,
  REWRITE_TAC[mld_power2round_lo; mld_power2round_hi] THEN GEN_TAC THEN
  AP_TERM_TAC THEN SPEC_TAC(`word_add (x:int32) (word 4095)`,`y:int32`) THEN
  BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. Each of the 64 iterations of the loop splits 4         *)
(* coefficients, loaded and stored as 128-bit words.                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`a1:int64`; `a0:int64`; `a:int64`; `x:num->int32`; `pc:num`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; PAIRWISE; ALL;
              mld_poly_power2round_hi; mld_poly_power2round_lo] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `64` `pc + mldsa_poly_power2round_loop1`
   `pc + mldsa_poly_power2round_loop1_test`
   `\i s. read X0 s = a1 /\ read X1 s = a0 /\ read X2 s = a /\
          read X3 s = word(16 * i) /\ read X30 s = returnaddress /\
          read Q3 s = word 0xffffe000ffffe000ffffe000ffffe000 /\
          read Q4 s = word 0x00000fff00000fff00000fff00000fff /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   x j) /\
          (!j. j < 4 * i
               ==> read(memory :> bytes32(word_add a1 (word(4 * j)))) s =
                   mld_power2round_hi (x j)) /\
          (!j. j < 4 * i
               ==> read(memory :> bytes32(word_add a0 (word(4 * j)))) s =
                   mld_power2round_lo (x j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    CONV_TAC WORD_REDUCE_CONV;

    (*** The loop body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    VEC4_LOOP_BODY_TAC EXEC 8 THEN
    VEC4_LOOP_FINAL_TAC [POWER2ROUND_LANES];

    (*** The loop-back branch and the exit ***)

    LOOP_BACK_TAC EXEC;
    LOOP_EXIT_TAC EXEC 3]);;
