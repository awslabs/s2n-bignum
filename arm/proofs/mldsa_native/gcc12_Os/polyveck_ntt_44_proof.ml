(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number-theoretic transform of a vector of 4 polynomials: the      *)
(* proof (see polyveck_ntt_44_spec.ml).                                      *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/polyveck_ntt_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together. The code is a      *)
(* tail call of mldsa44_polyvecl_ntt, whose theorem is used.                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECL_NTT_44_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_POLY" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES;
              fst MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_OS_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  ARM_STEPS_TAC MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_OS_EXEC (1--1) THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc
   MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_OS_EXEC "H_POLY"
   [`read X0 s`; `x:num->int32`; `pc:num`; `read SP s`; `read X30 s`]
   [`pc:num`; `v:int64`; `stackpointer:int64`;
    `returnaddress:int64`] 2 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_OS_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECK_NTT_44_GCC12_OS_IMAGE_SUBROUTINE_FULL);;
