(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Shared support for the RV32 ML-DSA shift/add NTT implementations.         *)
(* ========================================================================= *)

(* Rewrite the common Barrett multiplication into the equivalent RV32 form
   that multiplies by q using shifts and additions. *)

let RV32_MLDSA_BARRETT_SLOW_PAIR =
  REWRITE_RULE[LET_DEF; LET_END_DEF] MLDSA_BARRETT_MUL_SLOW;;

(* Replay the 40 state updates in one slow butterfly body before simplifying
   component reads. *)

let RV32_NTT_REWRITE_SLOW_BODY_UPDATES_TAC =
  MAP_EVERY
   (fun n ->
      USE_THEN ("body" ^ string_of_int n)
       (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
      CONV_TAC(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THEN
      ASM_REWRITE_TAC[])
   (rev(1--40));;
