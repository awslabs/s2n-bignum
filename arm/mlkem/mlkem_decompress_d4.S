// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Unpack 4-bit ML-KEM compressed coefficients and decompress them
// Input a[128] (bytes); output r[256] (signed 16-bit words)
//
// The input is read as 256 4-bit fields u[i], two to a byte with the
// even-numbered one in the low nibble (ByteDecode_4), and each is mapped
// to round(u[i] * 3329 / 2^4), rounding halves up (Decompress_4 of FIPS
// 203, section 4.2.1), which is in the range 0 <= r[i] < 3329. This is
// mlkem-native's mlk_poly_decompress_d4.
//
// extern void mlkem_decompress_d4(int16_t r[S2N_BIGNUM_STATIC 256],
//                                 const uint8_t a[S2N_BIGNUM_STATIC 128]);
//
// Standard ARM ABI: X0 = r, X1 = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_decompress_d4)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_decompress_d4)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_decompress_d4)
        .text
        .balign 4

// The low and high nibbles are separated and interleaved (zip) into the
// order of the coefficients, and interleaving those bytes with zeros
// gives 16-bit lanes u[i] * 2^8. The rounding doubling multiply high by
// 8 * 3329 (sqrdmulh) is then floor((2 * u * 2^8 * 8 * 3329 + 2^15) / 2^16),
// that is floor((u * 3329 + 2^3) / 2^4), the rounded result.
//
// Each iteration takes 32 bytes to 64 coefficients.
//
// Registers: v0, v1 input, v2-v5 nibbles, v16-v23 coefficients,
// v29 = 0x0f (bytes), v30 = 0, v31 = 8 * 3329 (16-bit lanes).

S2N_BN_SYMBOL(mlkem_decompress_d4):
        CFI_START
        AARCH64_VALID_CALL_TARGET

        movz    w2, #26632
        dup     v31.8h, w2
        movi    v30.2d, #0
        movi    v29.16b, #0x0f
        mov     x4, #4

Lmlkem_decompress_d4_loop:
        ldp     q0, q1, [x1], #32

        and     v2.16b, v0.16b, v29.16b
        and     v3.16b, v1.16b, v29.16b
        ushr    v0.16b, v0.16b, #4
        ushr    v1.16b, v1.16b, #4
        zip1    v4.16b, v2.16b, v0.16b
        zip2    v5.16b, v2.16b, v0.16b
        zip1    v2.16b, v3.16b, v1.16b
        zip2    v3.16b, v3.16b, v1.16b

        zip1    v16.16b, v30.16b, v4.16b
        zip2    v17.16b, v30.16b, v4.16b
        zip1    v18.16b, v30.16b, v5.16b
        zip2    v19.16b, v30.16b, v5.16b
        zip1    v20.16b, v30.16b, v2.16b
        zip2    v21.16b, v30.16b, v2.16b
        zip1    v22.16b, v30.16b, v3.16b
        zip2    v23.16b, v30.16b, v3.16b

        sqrdmulh v16.8h, v16.8h, v31.8h
        sqrdmulh v17.8h, v17.8h, v31.8h
        sqrdmulh v18.8h, v18.8h, v31.8h
        sqrdmulh v19.8h, v19.8h, v31.8h
        sqrdmulh v20.8h, v20.8h, v31.8h
        sqrdmulh v21.8h, v21.8h, v31.8h
        sqrdmulh v22.8h, v22.8h, v31.8h
        sqrdmulh v23.8h, v23.8h, v31.8h

        stp     q16, q17, [x0], #32
        stp     q18, q19, [x0], #32
        stp     q20, q21, [x0], #32
        stp     q22, q23, [x0], #32

        subs    x4, x4, #1
        bne     Lmlkem_decompress_d4_loop

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_decompress_d4)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
