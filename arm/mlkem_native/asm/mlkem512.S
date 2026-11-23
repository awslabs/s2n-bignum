// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// ML-KEM-512 (FIPS 203 with k = 2): the functions of mlkem-native's API
//
//   mlkem512_keypair_derand, mlkem512_enc_derand, mlkem512_dec,
//   mlkem512_check_pk, mlkem512_check_sk
//
// and the internal mlkem512_pke_encrypt and mlkem512_pke_decrypt; see
// mlkem_kem_template.S.
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"
#include "mlkem_native2_consts.h"

#define MLKEM_K 2
#define MLKEM_L 512
#include "mlkem_kem_template.S"
