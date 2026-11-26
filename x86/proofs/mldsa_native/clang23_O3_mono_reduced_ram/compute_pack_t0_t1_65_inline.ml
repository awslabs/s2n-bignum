(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas for the loops that clang 23 -O3 has inlined into               *)
(* mld_compute_pack_t0_t165, instantiated for its labels (see inline_cp.ml   *)
(* and inline_sign.ml for the generators and the form of the lemmas). The    *)
(* frame is at fixed offsets from the value rsp0 of RSP after the prologue:  *)
(*                                                                           *)
(*   t (inverse NTT, sum, a0)   rsp0 + 32     s2 (unpacked), a1  rsp0 + 1056 *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_rl.ml";;

let CPT65_ETA_LOOP =
  PROVE_ETA4LOOP "mld_compute_pack_t0_t165" "loop2" "loop2_exit" 1056;;

let CPT65_ADD_LOOP =
  PROVE_ADDLOOP "mld_compute_pack_t0_t165" "loop3" "loop3_exit" 32 1056;;

let CPT65_RED_LOOP =
  PROVE_REDLOOP "mld_compute_pack_t0_t165" "loop4" "loop4_exit" 16;;

let CPT65_CADDQ_LOOP =
  PROVE_CADDQ "mld_compute_pack_t0_t165" "loop5" "loop5_exit" 32 11;;

let CPT65_P2R_LOOP =
  PROVE_P2RLOOP "mld_compute_pack_t0_t165" "loop6" "loop6_exit" 32 1056;;

let CPT65_T1_LOOP =
  PROVE_T1PACK "mld_compute_pack_t0_t165" "loop7" "loop7_exit" 1056;;
