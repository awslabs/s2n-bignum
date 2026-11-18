(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ENSURES_WEAKEN_PREPOST: an ensures statement stays true if its            *)
(* precondition is strengthened and its postcondition is weakened. The       *)
(* combined contract for memset, memset_full_contract in                     *)
(* arm/proofs/utils/mlkem_native_libc_full.ml, uses it.                      *)
(* ========================================================================= *)

needs "common/fips203/properties/mlkem_native_libc.ml";;

let ENSURES_WEAKEN_PREPOST = MESON[ENSURES_PREPOSTCONDITION_THM]
 `ensures step P Q C
  ==> (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x)
      ==> ensures step P' Q' C`;;
