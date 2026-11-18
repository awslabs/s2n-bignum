// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// The hash H of ML-KEM, SHA3-256:
// AVX-512 version
//
// mlkem_hash_h_avx512 is the function mlkem_hash_h of
// ../mlkem_native2, from the same source assembled with
// MLKEM_NATIVE2_AVX512 defined: it has the same contract, but calls the
// AVX-512 Keccak-f1600 permutations sha3_keccak_f1600_avx512 and
// sha3_keccak4_f1600_avx512 and the AVX-512 versions of the other
// functions of mlkem_native2 that it calls, for processors with AVX-512F
// and AVX-512VL.
// ----------------------------------------------------------------------------

#define MLKEM_NATIVE2_AVX512 1
#include "_internal_s2n_bignum_x86.h"
#include "../mlkem_native2/mlkem_native2_consts.h"
#include "../mlkem_native2/mlkem_native2_names.h"
#include "../mlkem_native2/mlkem_hash_h.S"
