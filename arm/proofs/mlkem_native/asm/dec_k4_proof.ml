(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* Proofs of the contracts of the function mlkem1024_dec in the image      *)
(* (see dec_k4_spec.ml).                                                   *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/asm/dec_k4_spec.ml";;
needs "arm/proofs/utils/mlkem_native2_api.ml";;
needs "arm/proofs/utils/mlkem_native2_kem.ml";;
needs "arm/proofs/utils/mlkem_native2_kem_safe.ml";;

let MLKEM1024_DEC_EXEC = MLKEM_NATIVE2_IMAGE_EXEC ["mlkem1024_dec"];;

let MLKEM_NATIVE_DEC_K4_ASM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_DEC_K4_ASM_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLKEM_NATIVE2_DEC_CORRECT_TAC 4 MLKEM1024_DEC_EXEC
   MLKEM_NATIVE_GEN_MATRIX_K4_HASHES_NOISE_ASM_IMAGE_SUBROUTINE_CORRECT
   (MLKEM_NATIVE_PKE_DECRYPT_K4_ASM_IMAGE_SUBROUTINE_CORRECT,
    MLKEM_NATIVE_PKE_ENCRYPT_K4_ASM_IMAGE_SUBROUTINE_CORRECT));;

let MLKEM_NATIVE_DEC_K4_ASM_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_DEC_K4_ASM_IMAGE_SUBROUTINE_SAFE_STMT,
  MLKEM_NATIVE2_DEC_SAFE_TAC 4 MLKEM1024_DEC_EXEC
   MLKEM_NATIVE_GEN_MATRIX_K4_HASHES_NOISE_ASM_IMAGE_SUBROUTINE_SAFE
   (MLKEM_NATIVE_PKE_DECRYPT_K4_ASM_IMAGE_SUBROUTINE_SAFE,
    MLKEM_NATIVE_PKE_ENCRYPT_K4_ASM_IMAGE_SUBROUTINE_SAFE));;
