(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decomposition of the coefficients of a polynomial into high and low       *)
(* parts: the proof (see poly_decompose_65_spec.ml).                         *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/poly_decompose_65_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_rounding.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The loop handles one        *)
(* coefficient per iteration, with the offset 4 * i in X5; the stored high   *)
(* and low parts are equal to the spec by bit-blasting, with the coefficient *)
(* as a variable (and the high part as a variable for the low part, see      *)
(* SCALAR_LANE_TAC). The loop test is the end of the body, as                *)
(* ENSURES_EVENTS_WHILE_UP2_TAC requires, and the events of an iteration     *)
(* depend on its index only.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_DECOMPOSE_65_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_DECOMPOSE_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLY_DECOMPOSE_65_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(a1:int64) (a0:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a1 a0 pc returnaddress)
        (APPEND
          (ENUMERATEL 256 (\i. f_ev_loop a1 a0 pc returnaddress i))
          (f_ev_prol a1 a0 pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a1:int64`; `a0:int64`; `x:num->int32`; `pc:num`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; PAIRWISE; ALL;
              mld_poly_decompose_hi_32; mld_poly_decompose_lo_32; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

    ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + mldsa65_poly_decompose_loop1`
   `pc + mldsa65_poly_decompose_loop1_exit`
   `\i s. read X0 s = a1 /\ read X1 s = a0 /\ read X5 s = word(4 * i) /\
          read X7 s = word 4190208 /\ read X6 s = word 4286586879 /\
          read X30 s = returnaddress /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add a0 (word(4 * j)))) s =
                   x j) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a1 (word(4 * j)))) s =
                   mld_decompose_hi_32 (x j)) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a0 (word(4 * j)))) s =
                   mld_decompose_lo_32 (x j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    FULL_INIT_TAC THEN
    ARM_STEPS_TAC EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `mld_decompose_hi_32` (concl th)) &&
        not(free_in `mld_decompose_lo_32` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ARM_STEPS_TAC EXEC (1--20) THEN
    SCALAR_LANE_TAC `word_add (a1:int64) (word(4 * i))` `(x:num->int32) i`
      `mld_decompose_hi_32` [DECOMPOSE_HI_32_ALT] THEN
    SCALAR_LANE_TAC `word_add (a0:int64) (word(4 * i))` `(x:num->int32) i`
      `mld_decompose_lo_32` [DECOMPOSE_LO_32_ALT; mld_ct_sel] THEN
    FULL_FINAL_TAC [ONE_OUTPUT_SPLIT];

    (*** The return ***)

    FULL_EXIT_TAC EXEC 1]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_DECOMPOSE_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_DECOMPOSE_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_DECOMPOSE_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_DECOMPOSE_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_DECOMPOSE_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_DECOMPOSE_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
