// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Compress ML-KEM polynomial coefficients to 4 bits and pack them
// Input a[256] (signed 16-bit words); output r[128] (bytes)
//
// The input coefficients are assumed to be in the range 0 <= a[i] < 3329.
// Each is mapped to round(a[i] * 2^4 / 3329) mod 2^4 (Compress_4 of FIPS
// 203, section 4.2.1), and the 256 results are packed two to a byte, the
// even-numbered coefficient in the low nibble (ByteEncode_4), as in
// mlkem-native's mlk_poly_compress_d4.
//
// extern void mlkem_compress_d4(uint8_t r[S2N_BIGNUM_STATIC 128],
//                               const int16_t a[S2N_BIGNUM_STATIC 256]);
//
// Standard ARM ABI: X0 = r, X1 = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_compress_d4)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_compress_d4)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_compress_d4)
        .text
        .balign 4

// The rounding: f = floor(a * 20159 / 2^15), the high half of the doubled
// product (sqdmulh), is floor(2^7 * y + e) where y = a * 2^4 / 3329 and
// 0 <= e < 0.01, and the rounding right shift of f by 7 (urshr) is then
// round(y) exactly. For f + 2^6 >= 2^7 * (k + 1) just when
// 2^7 * y + e >= 2^7 * (k + 1/2), the bound being an integer, and that is
// just when y >= k + 1/2 because y is at least 1 / (2 * 3329) from k + 1/2
// and e / 2^7 is smaller. The result is at most 2^4 (for a >= 3226), the
// value 2^4 to be taken as 0.
//
// The packing: the low bytes of the 16-bit results are gathered (uzp1),
// separated into even- and odd-numbered coefficients (uzp1, uzp2), and
// combined with a shift-and-insert (sli) of the odd ones by 4, which also
// discards bit 4 of both and so takes 2^4 to 0.
//
// Each iteration takes 64 coefficients to 32 bytes.
//
// Registers: v0-v7 coefficients, v16-v19 bytes, v20-v23 nibbles,
// v31 = 20159 (16-bit lanes).

S2N_BN_SYMBOL(mlkem_compress_d4):
        CFI_START
        AARCH64_VALID_CALL_TARGET

        movz    w2, #20159
        dup     v31.8h, w2
        mov     x4, #4

Lmlkem_compress_d4_loop:
        ldp     q0, q1, [x1], #32
        ldp     q2, q3, [x1], #32
        ldp     q4, q5, [x1], #32
        ldp     q6, q7, [x1], #32

        sqdmulh v0.8h, v0.8h, v31.8h
        sqdmulh v1.8h, v1.8h, v31.8h
        sqdmulh v2.8h, v2.8h, v31.8h
        sqdmulh v3.8h, v3.8h, v31.8h
        sqdmulh v4.8h, v4.8h, v31.8h
        sqdmulh v5.8h, v5.8h, v31.8h
        sqdmulh v6.8h, v6.8h, v31.8h
        sqdmulh v7.8h, v7.8h, v31.8h
        urshr   v0.8h, v0.8h, #7
        urshr   v1.8h, v1.8h, #7
        urshr   v2.8h, v2.8h, #7
        urshr   v3.8h, v3.8h, #7
        urshr   v4.8h, v4.8h, #7
        urshr   v5.8h, v5.8h, #7
        urshr   v6.8h, v6.8h, #7
        urshr   v7.8h, v7.8h, #7

        uzp1    v16.16b, v0.16b, v1.16b
        uzp1    v17.16b, v2.16b, v3.16b
        uzp1    v18.16b, v4.16b, v5.16b
        uzp1    v19.16b, v6.16b, v7.16b
        uzp1    v20.16b, v16.16b, v17.16b
        uzp2    v21.16b, v16.16b, v17.16b
        uzp1    v22.16b, v18.16b, v19.16b
        uzp2    v23.16b, v18.16b, v19.16b
        sli     v20.16b, v21.16b, #4
        sli     v22.16b, v23.16b, #4
        stp     q20, q22, [x0], #32

        subs    x4, x4, #1
        bne     Lmlkem_compress_d4_loop

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_compress_d4)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
