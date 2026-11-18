(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Keccak-f[1600] and the sponge for the AArch64 proofs: this file loads the *)
(* lemmas about a state in memory (keccak_f1600.ml) and the lemmas about the *)
(* padding and the blocks of the padded message, as numbers, for             *)
(* keccak_absorb, and about the output of keccak_sponge, which do not depend *)
(* on the instruction set (common/fips202/properties/keccak_fips202.ml).     *)
(* ========================================================================= *)

needs "arm/proofs/utils/keccak_f1600.ml";;
needs "common/mlkem_mldsa.ml";;
needs "common/fips202/properties/keccak_fips202.ml";;
