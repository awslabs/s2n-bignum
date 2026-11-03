(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Checks of the AES-GCM specification files under common/ that no proof    *)
(* depends on, run once by "make proofs" (see arm/Makefile) rather than at   *)
(* every load of the specification by the AES-GCM proofs.                   *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(* The GHASH and POLYVAL polynomials are irreducible over GF(2).             *)

needs "common/gf128_irreducible.ml";;

List.iter (fun th -> Printf.printf "%s\n" (string_of_thm th))
  [RING_IRREDUCIBLE_GHASH_POLYNOMIAL; RING_IRREDUCIBLE_POLYVAL_POLYNOMIAL];;
