(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The decomposition of common/mldsa_native_rounding.ml in the form that the *)
(* gcc 12 -O2 code computes it, for SCALAR_LANE_TAC: the products by         *)
(* constants as the code does them, a multiplication or shifts and adds, as  *)
(* in arm/proofs/utils/mldsa_native_rounding.ml (the x86 code computes them  *)
(* in the same way), and the test of the low part in mld_use_hint.           *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_scalar.ml";;
needs "common/mldsa_native_rounding.ml";;
needs "common/fips204/properties/mldsa_native_rounding.ml";;

(* ------------------------------------------------------------------------- *)
(* The test of the low part in mld_use_hint as the x86 code makes it: JG     *)
(* after the XOR that computes the low part w (which clears OF), taken when  *)
(* ~(ival w < &0) /\ ~(val w = 0), as a comparison.                          *)
(* ------------------------------------------------------------------------- *)

let USE_HINT_GT_COND = prove
 (`!w:int32. ~(ival w < &0) /\ ~(val w = 0) <=> &0 < ival w`,
  REWRITE_TAC[VAL_EQ_0; GSYM IVAL_EQ_0] THEN INT_ARITH_TAC);;