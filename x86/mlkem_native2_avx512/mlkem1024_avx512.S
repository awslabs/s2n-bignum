// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// ML-KEM-1024 (FIPS 203 with k = 4): the functions of mlkem-native's API,
// AVX-512 version
//
//   mlkem1024_keypair_derand_avx512, mlkem1024_enc_derand_avx512,
//   mlkem1024_dec_avx512, mlkem1024_check_pk_avx512,
//   mlkem1024_check_sk_avx512
//
// and the internal mlkem1024_pke_encrypt_avx512 and
// mlkem1024_pke_decrypt_avx512: the template of ../mlkem_native2
// (mlkem_kem_template.S) assembled with MLKEM_NATIVE2_AVX512 defined, the
// same functions with the same contracts as those without the suffix, but
// calling the AVX-512 versions of the middle layer, for processors with
// AVX-512F and AVX-512VL.
// ----------------------------------------------------------------------------

#define MLKEM_NATIVE2_AVX512 1
#include "_internal_s2n_bignum_x86.h"
#include "../mlkem_native2/mlkem_native2_consts.h"
#include "../mlkem_native2/mlkem_native2_names.h"

#define MLKEM_K 4
#define MLKEM_L 1024
#include "../mlkem_native2/mlkem_kem_template.S"
