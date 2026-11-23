// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// ML-KEM-768 (FIPS 203 with k = 3): the functions of mlkem-native's API
//
//   mlkem768_keypair_derand, mlkem768_enc_derand, mlkem768_dec,
//   mlkem768_check_pk, mlkem768_check_sk
//
// and the internal mlkem768_pke_encrypt and mlkem768_pke_decrypt; see
// mlkem_kem_template.S.
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"
#include "mlkem_native2_consts.h"

#define MLKEM_K 3
#define MLKEM_L 768
#include "mlkem_kem_template.S"
