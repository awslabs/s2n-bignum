(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Bridge from gcm.ml NIST-level definitions to nist_dot / nist_ghash.       *)
(*                                                                           *)
(* gf128_mul (from gcm.ml) and nist_dot (from ghash_nist_defs.ml) are the    *)
(* same function: both compute                                               *)
(*   bit_reflect(ghash_reduce(pmul(bit_reflect a, bit_reflect b)))           *)
(* just via syntactically different aliases (bitrev128 vs bit_reflect128).   *)
(*                                                                           *)
(* ghash (from gcm.ml) and nist_ghash are then identical by induction.       *)
(* This completes the chain from the NIST SP 800-38D spec (gcm.ml) down to   *)
(* ghash_polyval_acc (via NIST_GHASH_IS_POLYVAL in ghash_nist_bridge.ml).    *)
(* ========================================================================= *)

needs "common/gcm.ml";;
needs "common/ghash_nist_defs.ml";;

let BITREV128_IS_BIT_REFLECT128 = prove
 (`!x:int128. bitrev128 x = bit_reflect128 x`,
  REWRITE_TAC[bitrev128; bit_reflect128]);;

let GF128_MUL_IS_NIST_DOT = prove
 (`!X Y:int128. gf128_mul X Y = nist_dot X Y`,
  REWRITE_TAC[gf128_mul; nist_dot; BITREV128_IS_BIT_REFLECT128]);;

let GHASH_IS_NIST_GHASH = prove
 (`!H xs acc. ghash H acc xs = nist_ghash H acc xs`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  ASM_REWRITE_TAC[ghash; nist_ghash; GF128_MUL_IS_NIST_DOT]);;
