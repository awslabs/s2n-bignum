(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* Proofs of the contracts of mlkem_tomont (see tomont_spec.ml). The       *)
(* standalone proof of arm/proofs/mlkem_tomont.ml runs here, in the job    *)
(* of this file, so that it runs once: it proves the correctness theorem   *)
(* and the safety theorem of the library, and the safety with the frame    *)
(* of the correctness theorem is made from them.                           *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/asm/tomont_spec.ml";;
needs "arm/proofs/utils/mlkem_native2_framed.ml";;

loadt "arm/proofs/mlkem_tomont.ml";;

let MLKEM_TOMONT_SUBROUTINE_SAFE_FRAMED = prove
 (MLKEM_TOMONT_SUBROUTINE_SAFE_FRAMED_STMT,
  MATCH_ACCEPT_TAC
   (framed_kernel_safe "mlkem_tomont"
      MLKEM_TOMONT_SUBROUTINE_CORRECT
      MLKEM_TOMONT_EXEC));;
