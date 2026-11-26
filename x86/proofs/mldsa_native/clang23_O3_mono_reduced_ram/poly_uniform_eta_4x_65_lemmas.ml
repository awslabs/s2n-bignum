(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas for the regions that clang 23 inlines into                     *)
(* mldsa65_poly_uniform_eta_4x, from the generators of inline_eta4x.ml:      *)
(* the eight scans of mld_rej_eta_c (the first four of the first pass, the   *)
(* last four of the outer loop), the absorb of the four extended seeds (ABS) *)
(* and the four guarded scans of the outer loop (GUARD).                     *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_eta_4x_65_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_eta4x.ml";;

let ETA65_SCANS = PROVE_ETA4_SCANS "mldsa65_poly_uniform_eta_4x";;

let ETA65_ABS = PROVE_ETA4_ABS "mldsa65_poly_uniform_eta_4x";;

let ETA65_GUARDS = PROVE_ETA4_GUARDS "mldsa65_poly_uniform_eta_4x" ETA65_SCANS;;
