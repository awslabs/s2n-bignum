(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* Proofs of the contracts of the function mlkem768_pke_encrypt in the     *)
(* image (see pke_encrypt_k3_spec.ml).                                     *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/asm/pke_encrypt_k3_spec.ml";;
needs "arm/proofs/utils/mlkem_native2_api.ml";;
needs "arm/proofs/utils/mlkem_native2_kem.ml";;
needs "arm/proofs/utils/mlkem_native2_kem_safe.ml";;

let MLKEM768_PKE_ENCRYPT_EXEC =
  MLKEM_NATIVE2_IMAGE_EXEC ["mlkem768_pke_encrypt"];;

let MLKEM_NATIVE_PKE_ENCRYPT_K3_ASM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_PKE_ENCRYPT_K3_ASM_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLKEM_NATIVE2_PKE_ENCRYPT_CORRECT_TAC 3 MLKEM768_PKE_ENCRYPT_EXEC);;

let MLKEM_NATIVE_PKE_ENCRYPT_K3_ASM_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_PKE_ENCRYPT_K3_ASM_IMAGE_SUBROUTINE_SAFE_STMT,
  MLKEM_NATIVE2_PKE_ENCRYPT_SAFE_TAC 3 MLKEM768_PKE_ENCRYPT_EXEC);;
