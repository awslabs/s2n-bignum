// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Compress ML-KEM polynomial coefficients to 5 bits and pack them
// Input a[256] (signed 16-bit words); output r[160] (bytes)
//
// The input coefficients are assumed to be in the range 0 <= a[i] < 3329.
// Each is mapped to round(a[i] * 2^5 / 3329) mod 2^5 (Compress_5 of FIPS
// 203, section 4.2.1), and the 256 results are packed as 5-bit
// little-endian fields, 8 to each group of 5 bytes (ByteEncode_5), as in
// mlkem-native's mlk_poly_compress_d5.
//
// extern void mlkem_compress_d5(uint8_t r[S2N_BIGNUM_STATIC 160],
//                               const int16_t a[S2N_BIGNUM_STATIC 256]);
//
// Standard ARM ABI: X0 = r, X1 = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_compress_d5)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_compress_d5)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_compress_d5)
        .text
        .balign 4

// The rounding: f = floor(a * 20159 / 2^15), the high half of the doubled
// product (sqdmulh), is floor(2^6 * y + e) where y = a * 2^5 / 3329 and
// 0 <= e < 0.01, and the rounding right shift of f by 6 (urshr) is then
// round(y) exactly, as for mlkem_compress_d4: the rounding bound
// 2^6 * (k + 1/2) is an integer, and y is at least 1 / (2 * 3329) from
// k + 1/2 while e / 2^6 is smaller. A mask takes it mod 2^5.
//
// The packing: the 8 coefficients t_0..t_7 of a group occupy bits 5 * j
// onwards of its 5 bytes. With s_j = t_j * 2^((5 * j) mod 8) in 16-bit
// lanes (a multiply by a vector of powers of 2), each output byte is the
// OR of at most three bytes of the s_j, so three table lookups (tbl) in
// two such vectors and two ORs give the 10 bytes of two groups.
//
// Each iteration takes 64 coefficients to 40 bytes.
//
// Registers: v0-v7 coefficients, v16-v23 lookups, v24-v27 output,
// v28-v30 the table indices, v31 the powers of 2, v26 = 20159 and
// v27 = 31 (16-bit lanes) until the output needs them.

S2N_BN_SYMBOL(mlkem_compress_d5):
        CFI_START
        AARCH64_VALID_CALL_TARGET

        movz    x2, #0x300
        movk    x2, #0x907, lsl #16
        movk    x2, #0x100d, lsl #32
        movk    x2, #0x1713, lsl #48
        movz    x3, #0x1d19
        movk    x3, #0xffff, lsl #16
        movk    x3, #0xffff, lsl #32
        movk    x3, #0xffff, lsl #48
        fmov    d28, x2
        mov     v28.d[1], x3
        movz    x2, #0x402
        movk    x2, #0xa08, lsl #16
        movk    x2, #0x120e, lsl #32
        movk    x2, #0x1814, lsl #48
        movz    x3, #0x1e1a
        movk    x3, #0xffff, lsl #16
        movk    x3, #0xffff, lsl #32
        movk    x3, #0xffff, lsl #48
        fmov    d29, x2
        mov     v29.d[1], x3
        movz    x2, #0x6ff
        movk    x2, #0xcff, lsl #16
        movk    x2, #0xffff, lsl #32
        movk    x2, #0xff16, lsl #48
        movz    x3, #0xff1c
        movk    x3, #0xffff, lsl #16
        movk    x3, #0xffff, lsl #32
        movk    x3, #0xffff, lsl #48
        fmov    d30, x2
        mov     v30.d[1], x3
        movz    x2, #0x1
        movk    x2, #0x20, lsl #16
        movk    x2, #0x4, lsl #32
        movk    x2, #0x80, lsl #48
        movz    x3, #0x10
        movk    x3, #0x2, lsl #16
        movk    x3, #0x40, lsl #32
        movk    x3, #0x8, lsl #48
        fmov    d31, x2
        mov     v31.d[1], x3
        movz    w2, #20159
        mov     x4, #4

Lmlkem_compress_d5_loop:
        dup     v26.8h, w2
        movi    v27.8h, #31
        ldp     q0, q1, [x1], #32
        ldp     q2, q3, [x1], #32
        ldp     q4, q5, [x1], #32
        ldp     q6, q7, [x1], #32
        sqdmulh v0.8h, v0.8h, v26.8h
        sqdmulh v1.8h, v1.8h, v26.8h
        sqdmulh v2.8h, v2.8h, v26.8h
        sqdmulh v3.8h, v3.8h, v26.8h
        sqdmulh v4.8h, v4.8h, v26.8h
        sqdmulh v5.8h, v5.8h, v26.8h
        sqdmulh v6.8h, v6.8h, v26.8h
        sqdmulh v7.8h, v7.8h, v26.8h
        urshr   v0.8h, v0.8h, #6
        urshr   v1.8h, v1.8h, #6
        urshr   v2.8h, v2.8h, #6
        urshr   v3.8h, v3.8h, #6
        urshr   v4.8h, v4.8h, #6
        urshr   v5.8h, v5.8h, #6
        urshr   v6.8h, v6.8h, #6
        urshr   v7.8h, v7.8h, #6
        and     v0.16b, v0.16b, v27.16b
        and     v1.16b, v1.16b, v27.16b
        and     v2.16b, v2.16b, v27.16b
        and     v3.16b, v3.16b, v27.16b
        and     v4.16b, v4.16b, v27.16b
        and     v5.16b, v5.16b, v27.16b
        and     v6.16b, v6.16b, v27.16b
        and     v7.16b, v7.16b, v27.16b
        mul     v0.8h, v0.8h, v31.8h
        mul     v1.8h, v1.8h, v31.8h
        mul     v2.8h, v2.8h, v31.8h
        mul     v3.8h, v3.8h, v31.8h
        mul     v4.8h, v4.8h, v31.8h
        mul     v5.8h, v5.8h, v31.8h
        mul     v6.8h, v6.8h, v31.8h
        mul     v7.8h, v7.8h, v31.8h
        tbl     v24.16b, {v0.16b, v1.16b}, v28.16b
        tbl     v16.16b, {v0.16b, v1.16b}, v29.16b
        tbl     v20.16b, {v0.16b, v1.16b}, v30.16b
        tbl     v25.16b, {v2.16b, v3.16b}, v28.16b
        tbl     v17.16b, {v2.16b, v3.16b}, v29.16b
        tbl     v21.16b, {v2.16b, v3.16b}, v30.16b
        tbl     v26.16b, {v4.16b, v5.16b}, v28.16b
        tbl     v18.16b, {v4.16b, v5.16b}, v29.16b
        tbl     v22.16b, {v4.16b, v5.16b}, v30.16b
        tbl     v27.16b, {v6.16b, v7.16b}, v28.16b
        tbl     v19.16b, {v6.16b, v7.16b}, v29.16b
        tbl     v23.16b, {v6.16b, v7.16b}, v30.16b
        orr     v24.16b, v24.16b, v16.16b
        orr     v25.16b, v25.16b, v17.16b
        orr     v26.16b, v26.16b, v18.16b
        orr     v27.16b, v27.16b, v19.16b
        orr     v24.16b, v24.16b, v20.16b
        orr     v25.16b, v25.16b, v21.16b
        orr     v26.16b, v26.16b, v22.16b
        orr     v27.16b, v27.16b, v23.16b
        str     d24, [x0], #8
        st1     {v24.h}[4], [x0], #2
        str     d25, [x0], #8
        st1     {v25.h}[4], [x0], #2
        str     d26, [x0], #8
        st1     {v26.h}[4], [x0], #2
        str     d27, [x0], #8
        st1     {v27.h}[4], [x0], #2

        subs    x4, x4, #1
        bne     Lmlkem_compress_d5_loop

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_compress_d5)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
