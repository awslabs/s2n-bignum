(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/asm/gen_matrix_k3_spec.ml";;
needs "arm/proofs/mlkem_native/asm/gen_matrix_common_spec.ml";;

(* The proofs run at the same time with the parallel backend of
   common/par.ml, and one after the other without it *)

let proof_futures =
 [prove_async
 (MLKEM_NATIVE_GEN_MATRIX_K3_NOISE_ASM_IMAGE_SUBROUTINE_CORRECT_STMT,
  GM_INSTANCE_TAC 3312);
  prove_async
 (MLKEM_NATIVE_GEN_MATRIX_K3_HASH_ASM_IMAGE_SUBROUTINE_CORRECT_STMT,
  GM_INSTANCE_TAC 3312);
  prove_async
 (MLKEM_NATIVE_GEN_MATRIX_K3_HASHES_NOISE_ASM_IMAGE_SUBROUTINE_CORRECT_STMT,
  GM_INSTANCE_TAC 5040)];;

let [MLKEM_NATIVE_GEN_MATRIX_K3_NOISE_ASM_IMAGE_SUBROUTINE_CORRECT;
     MLKEM_NATIVE_GEN_MATRIX_K3_HASH_ASM_IMAGE_SUBROUTINE_CORRECT;
     MLKEM_NATIVE_GEN_MATRIX_K3_HASHES_NOISE_ASM_IMAGE_SUBROUTINE_CORRECT] =
  map par_await proof_futures;;
