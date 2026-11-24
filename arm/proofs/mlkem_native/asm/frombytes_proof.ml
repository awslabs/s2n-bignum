(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ======================================================================= *)
(* Proofs of the contracts of mlkem_frombytes (see frombytes_spec.ml).     *)
(* The standalone proof of arm/proofs/mlkem_frombytes.ml runs here, in     *)
(* the job of this file, so that it runs once: it proves the correctness   *)
(* theorem and the safety theorem of the library, and the safety with the  *)
(* frame of the correctness theorem is made from them.                     *)
(* ======================================================================= *)

needs "arm/proofs/mlkem_native/asm/frombytes_spec.ml";;
needs "arm/proofs/utils/mlkem_native2_framed.ml";;

loadt "arm/proofs/mlkem_frombytes.ml";;

let MLKEM_FROMBYTES_NOIBT_SUBROUTINE_SAFE_FRAMED =
  framed_kernel_safe "mlkem_frombytes"
    MLKEM_FROMBYTES_NOIBT_SUBROUTINE_CORRECT
    MLKEM_FROMBYTES_EXEC;;

let MLKEM_FROMBYTES_SUBROUTINE_SAFE_FRAMED = prove
 (MLKEM_FROMBYTES_SUBROUTINE_SAFE_FRAMED_STMT,
  MATCH_ACCEPT_TAC
   (ARM_ADD_IBT_RULE mlkem_frombytes_mc mlkem_frombytes_tmc
      MLKEM_FROMBYTES_NOIBT_SUBROUTINE_SAFE_FRAMED));;
