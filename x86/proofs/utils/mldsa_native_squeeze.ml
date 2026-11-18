(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the proofs of mldsa-native's squeezing of bytes from a SHAKE   *)
(* context (shake128_squeeze and shake256_squeeze): the bytes that one call  *)
(* of mldsa_keccakf1600_extract_bytes copies are a run of the bytes          *)
(* mld_keccak_squeeze_byte of common/mldsa_native_fips202.ml. These are the  *)
(* lemmas of arm/proofs/utils/mldsa_native_squeeze.ml, which do not depend   *)
(* on the machine.                                                           *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_absorb.ml";;
needs "x86/proofs/utils/keccak_fips202.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "common/fips204/properties/mldsa_native_squeeze.ml";;