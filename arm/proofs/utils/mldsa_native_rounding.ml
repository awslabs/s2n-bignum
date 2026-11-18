(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The decomposition of common/mldsa_native_rounding.ml in the form that the *)
(* gcc 12 -O2 code computes it, for SCALAR_LANE_TAC: the products by         *)
(* constants as the code does them, a multiplication or shifts and adds.     *)
(* ========================================================================= *)

(* The part that depends on AArch64; the rest is in                          *)
(* common/fips204/properties/mldsa_native_rounding.ml.                       *)

needs "arm/proofs/utils/mldsa_native_scalar.ml";;
needs "common/mldsa_native_rounding.ml";;
needs "common/fips204/properties/mldsa_native_rounding.ml";;
