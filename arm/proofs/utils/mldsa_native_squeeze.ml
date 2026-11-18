(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the proofs of mldsa-native's squeezing of bytes from a SHAKE   *)
(* context (shake128_squeeze and shake256_squeeze): the bytes that one call  *)
(* of mldsa_keccakf1600_extract_bytes copies are a run of the bytes          *)
(* mld_keccak_squeeze_byte of common/mldsa_native_fips202.ml.                *)
(* ========================================================================= *)

(* The part that depends on AArch64; the rest is in                          *)
(* common/fips204/properties/mldsa_native_squeeze.ml.                        *)

needs "arm/proofs/utils/mldsa_native_absorb.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "common/fips204/properties/mldsa_native_squeeze.ml";;
