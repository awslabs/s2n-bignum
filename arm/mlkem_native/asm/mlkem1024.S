// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// ML-KEM-1024 (FIPS 203 with k = 4): the functions of mlkem-native's API
//
//   mlkem1024_keypair_derand, mlkem1024_enc_derand, mlkem1024_dec,
//   mlkem1024_check_pk, mlkem1024_check_sk
//
// and the internal mlkem1024_pke_encrypt and mlkem1024_pke_decrypt; see
// mlkem_kem_template.S.
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"
#include "mlkem_native2_consts.h"

#define MLKEM_K 4
#define MLKEM_L 1024
#include "mlkem_kem_template.S"
