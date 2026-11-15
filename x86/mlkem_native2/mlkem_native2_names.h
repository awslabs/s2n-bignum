/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *
 * The names that differ between the AVX2 version of mlkem_native2 (here)
 * and its AVX-512 version (../mlkem_native2_avx512, which assembles the
 * same files with MLKEM_NATIVE2_AVX512 defined): N2(f) is the global
 * symbol f of the API or the middle layer, with the suffix _avx512 in
 * the AVX-512 version, and N2_KECCAK_X1 and N2_KECCAK_X4 are the
 * Keccak-f1600 permutations that the middle layer calls.
 */
#ifndef MLKEM_NATIVE2_NAMES_H
#define MLKEM_NATIVE2_NAMES_H

#define N2_CAT2(a, b) a##b
#define N2_CAT(a, b) N2_CAT2(a, b)

#if defined(MLKEM_NATIVE2_AVX512)
#define N2(f) N2_CAT(f, _avx512)
#define N2_KECCAK_X1 sha3_keccak_f1600_avx512
#define N2_KECCAK_X4 sha3_keccak4_f1600_avx512
#else
#define N2(f) f
#define N2_KECCAK_X1 sha3_keccak_f1600_alt2
#define N2_KECCAK_X4 sha3_keccak4_f1600_alt
#endif

#endif
