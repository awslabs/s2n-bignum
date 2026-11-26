(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas for the code that clang 23 -O3 has inlined into the row loop   *)
(* of mld_compute_pack_t0_t144, instantiated for its labels (see             *)
(* inline_cpt.ml for the generators): the sum t + s2, the reduction, the     *)
(* addition of q, power2round and the packing of t1.                         *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_cpt.ml";;

let CPT44_FN = "mld_compute_pack_t0_t144";;

let CPT44_ADD = CPT_ADD_LEMMA CPT44_FN;;
let CPT44_RED = CPT_RED_LEMMA CPT44_FN;;
let CPT44_CADDQ = CPT_CADDQ_LEMMA CPT44_FN;;
let CPT44_P2R = CPT_P2R_LEMMA CPT44_FN;;
let CPT44_T1 = CPT_T1_LEMMA CPT44_FN;;
