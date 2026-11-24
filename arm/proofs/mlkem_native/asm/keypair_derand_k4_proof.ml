(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* Proofs of the contracts of the function mlkem1024_keypair_derand in     *)
(* the image (see keypair_derand_k4_spec.ml).                              *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/asm/keypair_derand_k4_spec.ml";;
needs "arm/proofs/utils/mlkem_native2_api.ml";;
needs "arm/proofs/utils/mlkem_native2_kem.ml";;
needs "arm/proofs/utils/mlkem_native2_kem_safe.ml";;

let MLKEM1024_KEYPAIR_DERAND_EXEC =
  MLKEM_NATIVE2_IMAGE_EXEC ["mlkem1024_keypair_derand"];;

let MLKEM_NATIVE_KEYPAIR_DERAND_K4_ASM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_KEYPAIR_DERAND_K4_ASM_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLKEM_NATIVE2_KEYPAIR_DERAND_CORRECT_TAC 4 MLKEM1024_KEYPAIR_DERAND_EXEC
   MLKEM_NATIVE_GEN_MATRIX_K4_NOISE_ASM_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_KEYPAIR_DERAND_K4_ASM_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_KEYPAIR_DERAND_K4_ASM_IMAGE_SUBROUTINE_SAFE_STMT,
  MLKEM_NATIVE2_KEYPAIR_DERAND_SAFE_TAC 4 MLKEM1024_KEYPAIR_DERAND_EXEC
   MLKEM_NATIVE_GEN_MATRIX_K4_NOISE_ASM_IMAGE_SUBROUTINE_SAFE);;
