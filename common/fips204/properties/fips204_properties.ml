(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* All the properties of the handwritten FIPS 204 specification              *)
(* (common/fips204/fips204.ml), in dependency order: the rings Z_q and       *)
(* R_q, the NTT, encodings, the NTT-domain algorithms, rounding, the         *)
(* alternative signing check of the Round 3 specification, the bound on the  *)
(* attempts of signing, and the termination of the samplers.                 *)
(* ========================================================================= *)

needs "common/fips204/properties/rq_ring.ml";;
needs "common/fips204/properties/ntt.ml";;
needs "common/fips204/properties/encoding.ml";;
needs "common/fips204/properties/ntt_domain.ml";;
needs "common/fips204/properties/rounding.ml";;
needs "common/fips204/properties/sign_alt.ml";;
needs "common/fips204/properties/sign_bound.ml";;
needs "common/fips204/properties/terminates.ml";;
