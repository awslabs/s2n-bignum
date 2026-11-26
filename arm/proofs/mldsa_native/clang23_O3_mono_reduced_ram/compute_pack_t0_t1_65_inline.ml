(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas for the code that clang 23 -O3 has inlined into the row loop   *)
(* of mld_compute_pack_t0_t165, instantiated for its labels (see             *)
(* inline_cpt.ml for the generators): the unpacking of s2 (eta = 4) with the *)
(* sum t + s2, the reduction (with DUP of -q in the loop), the addition of   *)
(* q, power2round and the packing of t1.                                     *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_cpt.ml";;

let CPT65_FN = "mld_compute_pack_t0_t165";;

let CPT65_RED =
  CPT_LOOP_LEMMA (fun ex l e -> CPT_REDDUP_LOOP CPT_MC ex l e) CPT65_FN "loop2";;

let CPT65_CADDQ =
  CPT_LOOP_LEMMA (fun ex l e ->
    INLINE_CADDQ_LOOP CPT_MC ex l e ["X9";"X25";"X8";"X10";"X11";"X21"])
   CPT65_FN "loop3";;

let CPT65_P2R =
  CPT_LOOP_LEMMA (fun ex l e ->
    CPT_P2R_LOOP CPT_MC ex l e ["X9";"X25";"X8";"X10";"X24";"Q6";"Q7"])
   CPT65_FN "loop4";;

let CPT65_T1 =
  CPT_LOOP_LEMMA (fun ex l e ->
    CPT_T1_LOOP CPT_MC ex l e ["X24";"X8";"X9";"X10";"X11"]) CPT65_FN "loop5";;

let CPT65_ADD = CPT65_ADD_PROVE CPT65_FN;;
