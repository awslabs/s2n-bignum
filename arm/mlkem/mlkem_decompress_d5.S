// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Unpack 5-bit ML-KEM compressed coefficients and decompress them
// Input a[160] (bytes); output r[256] (signed 16-bit words)
//
// The input is read as 256 5-bit little-endian fields u[i], 8 to each
// group of 5 bytes (ByteDecode_5), and each is mapped to
// round(u[i] * 3329 / 2^5), rounding halves up (Decompress_5 of FIPS 203,
// section 4.2.1), which is in the range 0 <= r[i] < 3329. This is
// mlkem-native's mlk_poly_decompress_d5.
//
// extern void mlkem_decompress_d5(int16_t r[S2N_BIGNUM_STATIC 256],
//                                 const uint8_t a[S2N_BIGNUM_STATIC 160]);
//
// Standard ARM ABI: X0 = r, X1 = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_decompress_d5)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_decompress_d5)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_decompress_d5)
        .text
        .balign 4

// A table lookup (tbl) gathers, for each of 8 coefficients from 5 bytes,
// the 2 bytes containing its field into a 16-bit lane, where the field is
// at bit (5 * j) mod 8 for j = 0..7; a shift of each lane (ushl) to put
// it at bit 10 and a mask leave u[i] * 2^10. The rounding doubling
// multiply high by 3329 (sqrdmulh) is floor((2 * u * 2^10 * 3329 + 2^15)
// / 2^16), that is floor((u * 3329 + 2^4) / 2^5), the rounded result.
//
// Each iteration takes 40 bytes to 64 coefficients. With the bytes in
// v0, v1, v2 at offsets 0, 16, 32, byte shifts (ext) give the bytes from
// offsets 15 and 30, so the 5-byte groups are at offsets 0, 5 or 10 of
// one of three registers, and three index vectors serve for all.
//
// Registers: v0-v2 input, v3, v4 shifted input, v16-v23 coefficients,
// v26 = 0, v27 = 0x7c00, v28-v30 the table indices, v31 the shifts,
// v25 = 3329 (16-bit lanes).

S2N_BN_SYMBOL(mlkem_decompress_d5):
        CFI_START
        AARCH64_VALID_CALL_TARGET

        movz    w2, #0xd01
        dup     v25.8h, w2
        movi    v26.2d, #0
        movi    v27.8h, #0x7c, lsl #8
        movz    x2, #0x100
        movk    x2, #0x100, lsl #16
        movk    x2, #0x201, lsl #32
        movk    x2, #0x201, lsl #48
        movz    x3, #0x302
        movk    x3, #0x403, lsl #16
        movk    x3, #0x403, lsl #32
        movk    x3, #0x504, lsl #48
        fmov    d28, x2
        mov     v28.d[1], x3
        movz    x2, #0x605
        movk    x2, #0x605, lsl #16
        movk    x2, #0x706, lsl #32
        movk    x2, #0x706, lsl #48
        movz    x3, #0x807
        movk    x3, #0x908, lsl #16
        movk    x3, #0x908, lsl #32
        movk    x3, #0xa09, lsl #48
        fmov    d29, x2
        mov     v29.d[1], x3
        movz    x2, #0xb0a
        movk    x2, #0xb0a, lsl #16
        movk    x2, #0xc0b, lsl #32
        movk    x2, #0xc0b, lsl #48
        movz    x3, #0xd0c
        movk    x3, #0xe0d, lsl #16
        movk    x3, #0xe0d, lsl #32
        movk    x3, #0xf0e, lsl #48
        fmov    d30, x2
        mov     v30.d[1], x3
        movz    x2, #0xa
        movk    x2, #0x5, lsl #16
        movk    x2, #0x8, lsl #32
        movk    x2, #0x3, lsl #48
        movz    x3, #0x6
        movk    x3, #0x9, lsl #16
        movk    x3, #0x4, lsl #32
        movk    x3, #0x7, lsl #48
        fmov    d31, x2
        mov     v31.d[1], x3
        mov     x4, #4

Lmlkem_decompress_d5_loop:
        ldp     q0, q1, [x1], #32
        ldr     d2, [x1], #8

        ext     v3.16b, v0.16b, v1.16b, #15
        ext     v4.16b, v1.16b, v2.16b, #14
        tbl     v16.16b, {v0.16b}, v28.16b
        tbl     v17.16b, {v0.16b}, v29.16b
        tbl     v18.16b, {v0.16b}, v30.16b
        tbl     v19.16b, {v3.16b}, v28.16b
        tbl     v20.16b, {v3.16b}, v29.16b
        tbl     v21.16b, {v3.16b}, v30.16b
        tbl     v22.16b, {v4.16b}, v28.16b
        tbl     v23.16b, {v4.16b}, v29.16b
        ushl    v16.8h, v16.8h, v31.8h
        ushl    v17.8h, v17.8h, v31.8h
        ushl    v18.8h, v18.8h, v31.8h
        ushl    v19.8h, v19.8h, v31.8h
        ushl    v20.8h, v20.8h, v31.8h
        ushl    v21.8h, v21.8h, v31.8h
        ushl    v22.8h, v22.8h, v31.8h
        ushl    v23.8h, v23.8h, v31.8h
        and     v16.16b, v16.16b, v27.16b
        and     v17.16b, v17.16b, v27.16b
        and     v18.16b, v18.16b, v27.16b
        and     v19.16b, v19.16b, v27.16b
        and     v20.16b, v20.16b, v27.16b
        and     v21.16b, v21.16b, v27.16b
        and     v22.16b, v22.16b, v27.16b
        and     v23.16b, v23.16b, v27.16b
        sqrdmulh v16.8h, v16.8h, v25.8h
        sqrdmulh v17.8h, v17.8h, v25.8h
        sqrdmulh v18.8h, v18.8h, v25.8h
        sqrdmulh v19.8h, v19.8h, v25.8h
        sqrdmulh v20.8h, v20.8h, v25.8h
        sqrdmulh v21.8h, v21.8h, v25.8h
        sqrdmulh v22.8h, v22.8h, v25.8h
        sqrdmulh v23.8h, v23.8h, v25.8h
        stp     q16, q17, [x0], #32
        stp     q18, q19, [x0], #32
        stp     q20, q21, [x0], #32
        stp     q22, q23, [x0], #32

        subs    x4, x4, #1
        bne     Lmlkem_decompress_d5_loop

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_decompress_d5)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
