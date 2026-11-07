(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Correction of the high parts of the coefficients of a polynomial by       *)
(* hints: the proof (see poly_use_hint_87_spec.ml).                          *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/poly_use_hint_87_spec.ml";;
needs "arm/proofs/utils/mldsa_native_rounding.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The loop handles one coefficient per iteration, with   *)
(* the offset 4 * i in X6. The high and low parts are folded into            *)
(* mld_decompose_hi_32 and mld_decompose_lo_32 as soon as the code has them  *)
(* in X2 and X3; the branch on the hint (CBZ) splits the iteration into two  *)
(* cases, and in each the stored value is equal to the spec by bit-blasting. *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let EXEC = MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_O2_EXEC in
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `h:int64`; `x:num->int32`; `y:num->int32`; `pc:num`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; PAIRWISE; ALL; mld_poly_use_hint_32] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `256` `pc + mldsa87_poly_use_hint_loop1`
   `pc + mldsa87_poly_use_hint_loop1_test`
   `\i s. read X0 s = a /\ read X1 s = h /\ read X6 s = word(4 * i) /\
          read X10 s = word 4190208 /\ read X9 s = word 4286586879 /\
          read X30 s = returnaddress /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   x j) /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add h (word(4 * j)))) s =
                   y j) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   mld_use_hint_32 (x j) (y j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV;

    (*** The loop body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `mld_use_hint_32` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o C MP (ASSUME `i < 256`) o SPEC `i:num` o
      check (fun th -> is_forall(concl th) &&
        free_in `y:num->int32` (concl th) &&
        not(free_in `mld_use_hint_32` (concl th)))) THEN
    DISCH_TAC THEN
    ARM_STEPS_TAC EXEC (1--6) THEN
    REG_LANE_TAC `X2` `(x:num->int32) i` `mld_decompose_hi_32`
      [DECOMPOSE_HI_32_ALT] THEN
    ARM_STEPS_TAC EXEC (7--18) THEN
    REG_LANE_TAC `X3` `(x:num->int32) i` `mld_decompose_lo_32`
      [DECOMPOSE_LO_32_ALT; mld_ct_sel] THEN
    ARM_STEPS_TAC EXEC (19--22) THEN
    BRANCH_CASES_TAC THENL
     [ARM_STEPS_TAC EXEC (23--24); ARM_STEPS_TAC EXEC (23--25)] THEN
    SCALAR_LANE2_TAC `word_add (a:int64) (word(4 * i))` `(x:num->int32) i`
      `(y:num->int32) i` `mld_use_hint_32` [mld_use_hint_32] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
    CONV_TAC WORD_RULE;

    (*** The loop-back branch and the exit ***)

    LOOP_BACK_TAC EXEC;
    LOOP_EXIT_TAC EXEC 3]);;
