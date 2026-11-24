(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The API functions of mldsa-native in the gcc 12 -O2 reduced-RAM image,    *)
(* with their SAFE theorems free of the hypotheses that the rejection        *)
(* samplers terminate. The CORRECT, SAFE and FULL theorems of these          *)
(* functions assume that the samplers of the matrix, of the secret vectors   *)
(* and of the challenge find enough candidates (mld_matrix_terminates,       *)
(* mld_keypair_terminates_*, mld_sign_terminates_* and                       *)
(* mld_poly_challenge_terminates), which holds for all their inputs          *)
(* (common/fips204/properties/mldsa_native_fips204_terminates.ml). The       *)
(* FIPS204 theorems of fips204.ml, fips204_sign.ml and fips204_verify.ml     *)
(* discharge these hypotheses for correctness. Here, for each API function   *)
(* and parameter set, ..._IMAGE_SUBROUTINE_SAFE_FIPS204 is its SAFE theorem  *)
(* with them discharged by MLD_FIPS204_DISCHARGE, as ..._SAFE_FIPS203 is for *)
(* mlkem-native; it assumes only the contracts that the SAFE theorem         *)
(* assumes.                                                                  *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/keypair_internal_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/keypair_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/pk_from_sk_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/signature_internal_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/signature_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/signature_extmu_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/signature_pre_hash_internal_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/signature_pre_hash_shake256_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/verify_internal_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/verify_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/verify_extmu_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/verify_pre_hash_internal_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/verify_pre_hash_shake256_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/keypair_internal_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/keypair_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/pk_from_sk_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/signature_internal_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/signature_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/signature_extmu_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/signature_pre_hash_internal_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/signature_pre_hash_shake256_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/verify_internal_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/verify_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/verify_extmu_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/verify_pre_hash_internal_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/verify_pre_hash_shake256_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/keypair_internal_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/keypair_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/pk_from_sk_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/signature_internal_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/signature_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/signature_extmu_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/signature_pre_hash_internal_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/signature_pre_hash_shake256_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/verify_internal_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/verify_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/verify_extmu_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/verify_pre_hash_internal_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/verify_pre_hash_shake256_87_spec.ml";;
needs "common/fips204/properties/mldsa_native_fips204_terminates.ml";;

(* ------------------------------------------------------------------------- *)
(* ML-DSA-44.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_KEYPAIR_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_PK_FROM_SK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_PK_FROM_SK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_SIGNATURE_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_SIGNATURE_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_SIGNATURE_EXTMU_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_SIGNATURE_EXTMU_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_VERIFY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_VERIFY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_VERIFY_EXTMU_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

(* ------------------------------------------------------------------------- *)
(* ML-DSA-65.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_KEYPAIR_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_KEYPAIR_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_SIGNATURE_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_SIGNATURE_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_SIGNATURE_EXTMU_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_VERIFY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_VERIFY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_VERIFY_EXTMU_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_VERIFY_EXTMU_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

(* ------------------------------------------------------------------------- *)
(* ML-DSA-87.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_KEYPAIR_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_KEYPAIR_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_SIGNATURE_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_SIGNATURE_EXTMU_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_SIGNATURE_PRE_HASH_SHAKE256_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_VERIFY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_VERIFY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_VERIFY_EXTMU_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_VERIFY_EXTMU_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_VERIFY_PRE_HASH_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;

let MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_FIPS204 =
  MLD_FIPS204_DISCHARGE
   MLDSA_NATIVE_VERIFY_PRE_HASH_SHAKE256_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE;;
