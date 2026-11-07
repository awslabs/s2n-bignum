(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proof for mldsa_shake256x4_init (see shake256x4_init_spec.ml): that   *)
(* of mldsa_shake128x4_init (see shake128x4_init_proof.ml), itself that of   *)
(* the same code in mlkem-native, with the rate 136 of SHAKE256 for the rate *)
(* 168 of SHAKE128: the code differs only in that constant.                  *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/shake256x4_init_spec.ml";;



(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SHAKE256X4_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REWRITE_TAC[C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLDSA_NATIVE_SHAKE256X4_INIT_GCC12_O2_EXEC (1--1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;
