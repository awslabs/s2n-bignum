(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* Proofs of the contracts of the function mlkem768_enc_derand in the      *)
(* image (see enc_derand_k3_spec.ml).                                      *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/asm/enc_derand_k3_spec.ml";;
needs "arm/proofs/utils/mlkem_native2_api.ml";;
needs "arm/proofs/utils/mlkem_native2_kem.ml";;
needs "arm/proofs/utils/mlkem_native2_kem_safe.ml";;

let MLKEM768_ENC_DERAND_EXEC =
  MLKEM_NATIVE2_IMAGE_EXEC ["mlkem768_enc_derand"];;

let MLKEM_NATIVE_ENC_DERAND_K3_ASM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_ENC_DERAND_K3_ASM_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLKEM_NATIVE2_ENC_DERAND_CORRECT_TAC 3 MLKEM768_ENC_DERAND_EXEC
   MLKEM_NATIVE_GEN_MATRIX_K3_HASH_ASM_IMAGE_SUBROUTINE_CORRECT
   MLKEM_NATIVE_PKE_ENCRYPT_K3_ASM_IMAGE_SUBROUTINE_CORRECT);;

let MLKEM_NATIVE_ENC_DERAND_K3_ASM_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_ENC_DERAND_K3_ASM_IMAGE_SUBROUTINE_SAFE_STMT,
  MLKEM_NATIVE2_ENC_DERAND_SAFE_TAC 3 MLKEM768_ENC_DERAND_EXEC
   MLKEM_NATIVE_GEN_MATRIX_K3_HASH_ASM_IMAGE_SUBROUTINE_SAFE
   MLKEM_NATIVE_PKE_ENCRYPT_K3_ASM_IMAGE_SUBROUTINE_SAFE);;
