(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* Proofs of the contracts of mlkem_decompress_d4 (see                     *)
(* decompress_d4_spec.ml). The standalone proof of                         *)
(* arm/proofs/mlkem_decompress_d4.ml runs here, in the job of this file,   *)
(* so that it runs once: it proves the correctness theorem and the safety  *)
(* theorem of the library, and the safety with the frame of the            *)
(* correctness theorem is made from them.                                  *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/asm/decompress_d4_spec.ml";;
needs "arm/proofs/utils/mlkem_native2_framed.ml";;

loadt "arm/proofs/mlkem_decompress_d4.ml";;

let MLKEM_DECOMPRESS_D4_NOIBT_SUBROUTINE_SAFE_FRAMED =
  framed_kernel_safe "mlkem_decompress_d4"
    MLKEM_DECOMPRESS_D4_NOIBT_SUBROUTINE_CORRECT
    MLKEM_DECOMPRESS_D4_EXEC;;

let MLKEM_DECOMPRESS_D4_SUBROUTINE_SAFE_FRAMED = prove
 (MLKEM_DECOMPRESS_D4_SUBROUTINE_SAFE_FRAMED_STMT,
  MATCH_ACCEPT_TAC
   (ARM_ADD_IBT_RULE mlkem_decompress_d4_mc mlkem_decompress_d4_tmc
      MLKEM_DECOMPRESS_D4_NOIBT_SUBROUTINE_SAFE_FRAMED));;
