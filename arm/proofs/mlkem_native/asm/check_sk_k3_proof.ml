(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* Proofs of the contracts of the function mlkem768_check_sk in the image  *)
(* (see check_sk_k3_spec.ml).                                              *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/asm/check_sk_k3_spec.ml";;
needs "arm/proofs/utils/mlkem_native2_api.ml";;

let MLKEM768_CHECK_SK_EXEC = MLKEM_NATIVE2_IMAGE_EXEC ["mlkem768_check_sk"];;

let MLKEM_NATIVE_CHECK_SK_K3_ASM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_CHECK_SK_K3_ASM_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLKEM_NATIVE2_CHECK_SK_CORRECT_TAC MLKEM768_CHECK_SK_EXEC 2336);;

let MLKEM_NATIVE_CHECK_SK_K3_ASM_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_CHECK_SK_K3_ASM_IMAGE_SUBROUTINE_SAFE_STMT,
  MLKEM_NATIVE2_CHECK_SK_SAFE_TAC MLKEM768_CHECK_SK_EXEC 1184);;
