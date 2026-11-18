(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Specification of Keccac (https://keccak.team/keccak_specs_summary.html).  *)
(* ========================================================================= *)

(* The specification of Keccak does not depend on the instruction set. It is *)
(* all in common/fips202/properties/keccak_spec.ml and keccak_bitblast.ml,   *)
(* which the AArch64 proofs load through this file.                          *)

needs "Library/words.ml";;
needs "common/fips202/properties/keccak_spec.ml";;
needs "common/fips202/properties/keccak_bitblast.ml";;
