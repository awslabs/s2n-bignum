(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The key generation, encapsulation and decapsulation functions of the      *)
(* ML-KEM API in x86_64 AVX-512 assembly (x86/mlkem_native/asm_avx512) under *)
(* the names that the builds of mlkem-native's compiled C give their final   *)
(* theorems. There, ..._IMAGE_SUBROUTINE_FIPS203 and                         *)
(* ..._IMAGE_SUBROUTINE_SAFE_FIPS203 are the CORRECT and SAFE theorems with  *)
(* the hypothesis that SampleNTT terminates discharged (see their            *)
(* fips203.ml). Those of the assembly have no such hypothesis, which their   *)
(* proofs discharge (MLKEM_SAMPLENTT_TERMINATES_TAC), so here they are the   *)
(* CORRECT and SAFE theorems themselves; with them every build has its final *)
(* theorems under the same names. (The assembly has no randomized keypair    *)
(* and enc, and the theorems of check_pk and check_sk have no FIPS203 names  *)
(* in any build.)                                                            *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/keypair_derand_k2_spec.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/enc_derand_k2_spec.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/dec_k2_spec.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/keypair_derand_k3_spec.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/enc_derand_k3_spec.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/dec_k3_spec.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/keypair_derand_k4_spec.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/enc_derand_k4_spec.ml";;
needs "x86/proofs/mlkem_native/asm_avx512/dec_k4_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* ML-KEM-512.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KEYPAIR_DERAND_K2_ASM_AVX512_IMAGE_SUBROUTINE_FIPS203 =
  MLKEM_NATIVE_KEYPAIR_DERAND_K2_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT;;

let MLKEM_NATIVE_KEYPAIR_DERAND_K2_ASM_AVX512_IMAGE_SUBROUTINE_SAFE_FIPS203 =
  MLKEM_NATIVE_KEYPAIR_DERAND_K2_ASM_AVX512_IMAGE_SUBROUTINE_SAFE;;

let MLKEM_NATIVE_ENC_DERAND_K2_ASM_AVX512_IMAGE_SUBROUTINE_FIPS203 =
  MLKEM_NATIVE_ENC_DERAND_K2_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT;;

let MLKEM_NATIVE_ENC_DERAND_K2_ASM_AVX512_IMAGE_SUBROUTINE_SAFE_FIPS203 =
  MLKEM_NATIVE_ENC_DERAND_K2_ASM_AVX512_IMAGE_SUBROUTINE_SAFE;;

let MLKEM_NATIVE_DEC_K2_ASM_AVX512_IMAGE_SUBROUTINE_FIPS203 =
  MLKEM_NATIVE_DEC_K2_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT;;

let MLKEM_NATIVE_DEC_K2_ASM_AVX512_IMAGE_SUBROUTINE_SAFE_FIPS203 =
  MLKEM_NATIVE_DEC_K2_ASM_AVX512_IMAGE_SUBROUTINE_SAFE;;

(* ------------------------------------------------------------------------- *)
(* ML-KEM-768.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KEYPAIR_DERAND_K3_ASM_AVX512_IMAGE_SUBROUTINE_FIPS203 =
  MLKEM_NATIVE_KEYPAIR_DERAND_K3_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT;;

let MLKEM_NATIVE_KEYPAIR_DERAND_K3_ASM_AVX512_IMAGE_SUBROUTINE_SAFE_FIPS203 =
  MLKEM_NATIVE_KEYPAIR_DERAND_K3_ASM_AVX512_IMAGE_SUBROUTINE_SAFE;;

let MLKEM_NATIVE_ENC_DERAND_K3_ASM_AVX512_IMAGE_SUBROUTINE_FIPS203 =
  MLKEM_NATIVE_ENC_DERAND_K3_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT;;

let MLKEM_NATIVE_ENC_DERAND_K3_ASM_AVX512_IMAGE_SUBROUTINE_SAFE_FIPS203 =
  MLKEM_NATIVE_ENC_DERAND_K3_ASM_AVX512_IMAGE_SUBROUTINE_SAFE;;

let MLKEM_NATIVE_DEC_K3_ASM_AVX512_IMAGE_SUBROUTINE_FIPS203 =
  MLKEM_NATIVE_DEC_K3_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT;;

let MLKEM_NATIVE_DEC_K3_ASM_AVX512_IMAGE_SUBROUTINE_SAFE_FIPS203 =
  MLKEM_NATIVE_DEC_K3_ASM_AVX512_IMAGE_SUBROUTINE_SAFE;;

(* ------------------------------------------------------------------------- *)
(* ML-KEM-1024.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_KEYPAIR_DERAND_K4_ASM_AVX512_IMAGE_SUBROUTINE_FIPS203 =
  MLKEM_NATIVE_KEYPAIR_DERAND_K4_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT;;

let MLKEM_NATIVE_KEYPAIR_DERAND_K4_ASM_AVX512_IMAGE_SUBROUTINE_SAFE_FIPS203 =
  MLKEM_NATIVE_KEYPAIR_DERAND_K4_ASM_AVX512_IMAGE_SUBROUTINE_SAFE;;

let MLKEM_NATIVE_ENC_DERAND_K4_ASM_AVX512_IMAGE_SUBROUTINE_FIPS203 =
  MLKEM_NATIVE_ENC_DERAND_K4_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT;;

let MLKEM_NATIVE_ENC_DERAND_K4_ASM_AVX512_IMAGE_SUBROUTINE_SAFE_FIPS203 =
  MLKEM_NATIVE_ENC_DERAND_K4_ASM_AVX512_IMAGE_SUBROUTINE_SAFE;;

let MLKEM_NATIVE_DEC_K4_ASM_AVX512_IMAGE_SUBROUTINE_FIPS203 =
  MLKEM_NATIVE_DEC_K4_ASM_AVX512_IMAGE_SUBROUTINE_CORRECT;;

let MLKEM_NATIVE_DEC_K4_ASM_AVX512_IMAGE_SUBROUTINE_SAFE_FIPS203 =
  MLKEM_NATIVE_DEC_K4_ASM_AVX512_IMAGE_SUBROUTINE_SAFE;;
