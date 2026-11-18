(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Splitting at 2^13: the proof (see poly_power2round_spec.ml).              *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/poly_power2round_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

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
(* Correctness, constant time and memory safety. Each of the 64 iterations   *)
(* of the loop splits 4 coefficients, loaded and stored as 128-bit words;    *)
(* the loop test is the end of the body, as ENSURES_EVENTS_WHILE_UP2_TAC     *)
(* requires, and the events of an iteration depend on its index only.        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(a1:int64) (a0:int64) (a:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a1 a0 a pc returnaddress)
        (APPEND
          (ENUMERATEL 64 (\i. f_ev_loop a1 a0 a pc returnaddress i))
          (f_ev_prol a1 a0 a pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a1:int64`; `a0:int64`; `a:int64`;
    `x:num->int32`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; PAIRWISE; ALL;
              mld_poly_power2round_hi; mld_poly_power2round_lo;
              fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64` `pc + mldsa_poly_power2round_loop1`
   `pc + mldsa_poly_power2round_loop1_exit`
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

    FULL_INIT_TAC THEN
    ARM_STEPS_TAC EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    CONV_TAC WORD_REDUCE_CONV THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    VEC4_LOOP_BODY_TAC EXEC 8 THEN ARM_STEPS_TAC EXEC (9--10) THEN
    VEC4_FULL_FINAL_TAC [POWER2ROUND_LANES] ALL_TAC;

    (*** The return ***)

    FULL_EXIT_TAC EXEC 1]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

(* ------------------------------------------------------------------------- *)
(* The same in place: the invariant states the input coefficients from 4 * i *)
(* on and the results before 4 * i at a0.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_FULL_INPLACE =
  prove
 (MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_FULL_INPLACE_STMT,
  let EXEC = MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(a1:int64) (a0:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a1 a0 pc returnaddress)
        (APPEND
          (ENUMERATEL 64 (\i. f_ev_loop a1 a0 pc returnaddress i))
          (f_ev_prol a1 a0 pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a1:int64`; `a0:int64`;
    `x:num->int32`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; PAIRWISE; ALL;
              mld_poly_power2round_hi; mld_poly_power2round_lo;
              fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64` `pc + mldsa_poly_power2round_loop1`
   `pc + mldsa_poly_power2round_loop1_exit`
   `\i s. read X0 s = a1 /\ read X1 s = a0 /\ read X2 s = a0 /\
          read X3 s = word(16 * i) /\ read X30 s = returnaddress /\
          read Q3 s = word 0xffffe000ffffe000ffffe000ffffe000 /\
          read Q4 s = word 0x00000fff00000fff00000fff00000fff /\
          (!j. 4 * i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add a0 (word(4 * j)))) s =
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

    FULL_INIT_TAC THEN
    ARM_STEPS_TAC EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    CONV_TAC WORD_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    VEC4_LOOP_BODY_TAC EXEC 8 THEN ARM_STEPS_TAC EXEC (9--10) THEN
    VEC4_FULL_FINAL_TAC [POWER2ROUND_LANES] ALL_TAC;

    (*** The return ***)

    FULL_EXIT_TAC EXEC 1]);;
