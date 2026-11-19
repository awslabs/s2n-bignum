(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition of polynomials: the proof (see poly_add_spec.ml).                *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/poly_add_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

(* The sum of two 32-bit words, as the code computes it: the registers W3    *)
(* and W4 are the low halves of X3 and X4.                                   *)

let ADD32_ZX = prove
 (`!x y:int32.
     word_zx(word_zx(word_add (word_zx(word_zx x:int64):int32)
                              (word_zx(word_zx y:int64):int32)):int64):int32 =
     word_add x y`,
  BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. Each of the 256 iterations  *)
(* of the loop adds one coefficient;                                         *)
(* the loop test is the end of the body, as ENSURES_EVENTS_WHILE_UP2_TAC     *)
(* requires, and the events of an iteration depend on its index only.        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(r:int64) (b:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil r b pc returnaddress)
        (APPEND
          (ENUMERATEL 256 (\i. f_ev_loop r b pc returnaddress i))
          (f_ev_prol r b pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `r:int64`; `b:int64`; `x:num->int32`;
    `y:num->int32`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; mld_poly_add;
              fst MLDSA_NATIVE_POLY_ADD_GCC12_OS_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + mldsa_poly_add_loop1`
   `pc + mldsa_poly_add_loop1_exit`
   `\i s. read X0 s = r /\ read X1 s = b /\ read X2 s = word(4 * i) /\
          read X30 s = returnaddress /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s =
                   y j) /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                   x j) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                   word_add (x j) (y j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_ADD_GCC12_OS_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0] THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `y:num->int32` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `read(memory :> bytes32(word_add b (word(4 * i)))) s0 = y i`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o
        check (fun th -> is_forall(concl th) &&
                         free_in `y:num->int32` (concl th) &&
                         free_in `b:int64` (concl th) &&
                         not(free_in `x:num->int32` (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_ADD_GCC12_OS_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
    LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ADD32_ZX];
      DISCHARGE_SAFETY_PROPERTY_TAC];

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_ADD_GCC12_OS_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC MLDSA_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC MLDSA_NATIVE_POLY_ADD_GCC12_OS_IMAGE_SUBROUTINE_FULL);;
