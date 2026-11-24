(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* Proofs of the contracts of mlkem_compress_d11 (see                      *)
(* compress_d11_spec.ml). The standalone proof of                          *)
(* arm/proofs/mlkem_compress_d11.ml runs here, in the job of this file,    *)
(* so that it runs once: it proves the correctness theorem and the safety  *)
(* theorem of the library, and the safety with the frame of the            *)
(* correctness theorem is made from them.                                  *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/asm/compress_d11_spec.ml";;
needs "arm/proofs/utils/mlkem_native2_framed.ml";;

loadt "arm/proofs/mlkem_compress_d11.ml";;

let MLKEM_COMPRESS_D11_NOIBT_SUBROUTINE_SAFE_FRAMED =
  framed_kernel_safe "mlkem_compress_d11"
    MLKEM_COMPRESS_D11_NOIBT_SUBROUTINE_CORRECT
    MLKEM_COMPRESS_D11_EXEC;;

let MLKEM_COMPRESS_D11_SUBROUTINE_SAFE_FRAMED = prove
 (MLKEM_COMPRESS_D11_SUBROUTINE_SAFE_FRAMED_STMT,
  MATCH_ACCEPT_TAC
   (ARM_ADD_IBT_RULE mlkem_compress_d11_mc mlkem_compress_d11_tmc
      MLKEM_COMPRESS_D11_NOIBT_SUBROUTINE_SAFE_FRAMED));;
