(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proof for mldsa_shake128x4_init (see shake128x4_init_spec.ml): that   *)
(* of the same code in the gcc12_O2 image of mlkem-native                    *)
(* (proofs/mlkem_native/gcc12_O2), with the names changed.                   *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/shake128x4_init_spec.ml";;



(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SHAKE128X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLDSA_NATIVE_SHAKE128X4_INIT_GCC12_O2_EXEC (1--1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;
