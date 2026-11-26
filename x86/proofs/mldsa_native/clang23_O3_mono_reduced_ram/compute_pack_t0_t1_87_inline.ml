(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas for the loops that clang 23 -O3 has inlined into               *)
(* mld_compute_pack_t0_t187, instantiated for its labels (see inline_cp.ml   *)
(* and inline_sign.ml for the generators and the form of the lemmas). The    *)
(* frame is at fixed offsets from the value rsp0 of RSP after the prologue:  *)
(*                                                                           *)
(*   t (inverse NTT, sum, a0)   rsp0 + 32     s2 (unpacked), a1  rsp0 + 1056 *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_cp.ml";;

let CPT87_ADD_LOOP =
  PROVE_ADDLOOP "mld_compute_pack_t0_t187" "loop2" "loop2_exit" 32 1056;;

let CPT87_RED_LOOP =
  PROVE_REDLOOP "mld_compute_pack_t0_t187" "loop3" "loop3_exit" 16;;

let CPT87_CADDQ_LOOP =
  PROVE_CADDQ "mld_compute_pack_t0_t187" "loop4" "loop4_exit" 32 11;;

let CPT87_P2R_LOOP =
  PROVE_P2RLOOP "mld_compute_pack_t0_t187" "loop5" "loop5_exit" 32 1056;;

let CPT87_T1_LOOP =
  PROVE_T1PACK "mld_compute_pack_t0_t187" "loop6" "loop6_exit" 1056;;
