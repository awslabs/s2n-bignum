(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* Proofs of the contracts of mlkem_compress_d10 (see                      *)
(* compress_d10_spec.ml). The standalone proof of                          *)
(* arm/proofs/mlkem_compress_d10.ml runs here, in the job of this file,    *)
(* so that it runs once: it proves the correctness theorem and the safety  *)
(* theorem of the library, and the safety with the frame of the            *)
(* correctness theorem is made from them.                                  *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/asm/compress_d10_spec.ml";;
needs "arm/proofs/utils/mlkem_native2_framed.ml";;

loadt "arm/proofs/mlkem_compress_d10.ml";;

let MLKEM_COMPRESS_D10_CORE_SAFE_FRAMED,
    MLKEM_COMPRESS_D10_NOIBT_SUBROUTINE_SAFE_FRAMED,
    MLKEM_COMPRESS_D10_IBT_SUBROUTINE_SAFE_FRAMED =
  FRAMED_STACK_KERNEL MLKEM_COMPRESS_D10_CORRECT
    MLKEM_COMPRESS_D10_NOIBT_SUBROUTINE_SAFE
    MLKEM_COMPRESS_D10_NOIBT_SUBROUTINE_CORRECT
    MLKEM_COMPRESS_D10_EXEC (4,4)
    mlkem_compress_d10_mc mlkem_compress_d10_tmc;;

let MLKEM_COMPRESS_D10_SUBROUTINE_SAFE_FRAMED = prove
 (MLKEM_COMPRESS_D10_SUBROUTINE_SAFE_FRAMED_STMT,
  MATCH_ACCEPT_TAC MLKEM_COMPRESS_D10_IBT_SUBROUTINE_SAFE_FRAMED);;
