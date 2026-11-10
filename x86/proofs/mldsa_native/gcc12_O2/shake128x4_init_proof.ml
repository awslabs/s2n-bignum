(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proof for mldsa_shake128x4_init (see shake128x4_init_spec.ml): that   *)
(* of the same code in the x86 gcc12_O2 image of mlkem-native, with the      *)
(* names changed.                                                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/shake128x4_init_spec.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety: the code is the return.     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  META_EXISTS_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLDSA_NATIVE_SHAKE128X4_INIT_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN FULL_INIT_TAC THEN
  X86_STEPS_TAC MLDSA_NATIVE_SHAKE128X4_INIT_GCC12_O2_EXEC (1--1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
