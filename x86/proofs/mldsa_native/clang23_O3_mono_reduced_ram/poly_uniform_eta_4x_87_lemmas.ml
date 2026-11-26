(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lemmas for the regions that clang 23 inlines into                     *)
(* mldsa87_poly_uniform_eta_4x, from the generators of inline_eta4x.ml:      *)
(* the eight scans of mld_rej_eta_c (the first four of the first pass, the   *)
(* last four of the outer loop), the absorb of the four extended seeds (ABS) *)
(* and the four guarded scans of the outer loop (GUARD).                     *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_eta_4x_87_spec.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_eta4x.ml";;

let ETA87_SCANS = PROVE_ETA2_SCANS "mldsa87_poly_uniform_eta_4x";;

let ETA87_ABS = PROVE_ETA2_ABS "mldsa87_poly_uniform_eta_4x";;

let ETA87_GUARDS = PROVE_ETA2_GUARDS "mldsa87_poly_uniform_eta_4x" ETA87_SCANS;;
