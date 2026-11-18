(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the FULL proofs of mldsa44_polyvecl_pointwise_acc_montgomery    *)
(* and its versions for ML-DSA-65 and ML-DSA-87: the pointwise products of   *)
(* two vectors of L = 4, 5 or 7 polynomials, accumulated and reduced         *)
(* (mld_polyvec_pointwise_acc_montgomery L of                                *)
(* common/mldsa_native_polyvec.ml). The compiler has vectorized the three in *)
(* the same way: iteration i of the outer loop handles coefficients 4 * i,   *)
(* ..., 4 * i + 3 of each polynomial, with an inner loop over the L          *)
(* polynomials that loads them from both vectors as 128-bit words and        *)
(* accumulates the 64-bit products with SMLAL and SMLAL2, then the           *)
(* Montgomery reduction of the four sums with vectors of q^-1 mod 2^32 and   *)
(* -q, and one 128-bit store. The proofs simulate the inner loop unrolled.   *)
(* ========================================================================= *)

needs "common/fips204/properties/mldsa_native_full.ml";;
needs "common/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* The sum mld_polyvec_dot n x y i for a numeral n, unfolded into the n      *)
(* products in the order of the C loop.                                      *)
(* ------------------------------------------------------------------------- *)

let PWACC_DOT_CONV =
  let th0 = CONJUNCT1 mld_polyvec_dot and th1 = CONJUNCT2 mld_polyvec_dot in
  let rec conv tm =
    match tm with
      Comb(Comb(Comb(Comb(Const("mld_polyvec_dot",_),n),_),_),_) ->
        if n = `0` then REWR_CONV th0 tm else
        (RATOR_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV num_CONV))) THENC
         REWR_CONV th1 THENC LAND_CONV conv) tm
    | _ -> failwith "PWACC_DOT_CONV" in
  conv;;
