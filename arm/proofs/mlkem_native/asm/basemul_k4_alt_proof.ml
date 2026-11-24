(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* Proofs of the contracts of mlkem_basemul_k4_alt (see                    *)
(* basemul_k4_alt_spec.ml). The standalone proof of                        *)
(* arm/proofs/mlkem_basemul_k4_alt.ml runs here, in the job of this file,  *)
(* so that it runs once: it proves the correctness theorem and the safety  *)
(* theorem of the library, and the safety with the frame of the            *)
(* correctness theorem is made from them.                                  *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/asm/basemul_k4_alt_spec.ml";;
needs "arm/proofs/utils/mlkem_native2_framed.ml";;

loadt "arm/proofs/mlkem_basemul_k4_alt.ml";;

let MLKEM_BASEMUL_K4_ALT_CORE_SAFE_FRAMED,
    MLKEM_BASEMUL_K4_ALT_NOIBT_SUBROUTINE_SAFE_FRAMED,
    MLKEM_BASEMUL_K4_ALT_IBT_SUBROUTINE_SAFE_FRAMED =
  FRAMED_STACK_KERNEL MLKEM_BASEMUL_K4_ALT_CORRECT
    MLKEM_BASEMUL_K4_ALT_NOIBT_SUBROUTINE_SAFE
    MLKEM_BASEMUL_K4_ALT_NOIBT_SUBROUTINE_CORRECT
    MLKEM_BASEMUL_K4_ALT_EXEC (5,5)
    mlkem_basemul_k4_alt_mc mlkem_basemul_k4_alt_tmc;;

let MLKEM_BASEMUL_K4_ALT_SUBROUTINE_SAFE_FRAMED = prove
 (MLKEM_BASEMUL_K4_ALT_SUBROUTINE_SAFE_FRAMED_STMT,
  MATCH_ACCEPT_TAC MLKEM_BASEMUL_K4_ALT_IBT_SUBROUTINE_SAFE_FRAMED);;
