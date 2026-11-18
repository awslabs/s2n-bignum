// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Unpack 11-bit ML-KEM compressed coefficients and decompress them
// Input a[352] (bytes); output r[256] (signed 16-bit words)
//
// The input is read as 256 11-bit little-endian fields u[i], 8 to each
// group of 11 bytes (ByteDecode_11), and each is mapped to
// round(u[i] * 3329 / 2^11), rounding halves up (Decompress_11 of FIPS 203,
// section 4.2.1), which is in the range 0 <= r[i] < 3329. This is
// mlkem-native's mlk_poly_decompress_d11.
//
// extern void mlkem_decompress_d11(int16_t r[S2N_BIGNUM_STATIC 256],
//                                  const uint8_t a[S2N_BIGNUM_STATIC 352]);
//
// Standard ARM ABI: X0 = r, X1 = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_decompress_d11)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_decompress_d11)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_decompress_d11)
        .text
        .balign 4

// A field can span three bytes, so two table lookups (tbl) gather, for
// each of 8 coefficients from 11 bytes, the 4 bytes from the one holding
// its first bit into a 32-bit lane, where the field is at bit
// (11 * j) mod 8 for j = 0..7. A shift of each lane (ushl) to put it at
// bit 4, narrowing to 16 bits (uzp1) and a mask leave u[i] * 2^4. The
// rounding doubling multiply high by 3329 (sqrdmulh) is
// floor((2 * u * 2^4 * 3329 + 2^15) / 2^16), that is
// floor((u * 3329 + 2^10) / 2^11), the rounded result.
//
// Each iteration takes 44 bytes to 32 coefficients; byte shifts (ext) of
// the loaded vectors give the 11-byte windows at offsets 11, 22 and 33.
//
// Registers: v0-v2 input, v3-v6 windows, v16-v23 32-bit lanes and then
// coefficients, v26 = 0, v27 = 0x7ff0, v28, v29 the table indices,
// v30, v31 the shifts (32-bit lanes), v25 = 3329 (16-bit lanes).

S2N_BN_SYMBOL(mlkem_decompress_d11):
        CFI_START
        AARCH64_VALID_CALL_TARGET

        movz    w2, #0xd01
        dup     v25.8h, w2
        movi    v26.2d, #0
        mvni    v27.8h, #0x80, lsl #8
        bic     v27.8h, #0x0f
        movz    x2, #0x100
        movk    x2, #0x302, lsl #16
        movk    x2, #0x201, lsl #32
        movk    x2, #0x403, lsl #48
        movz    x3, #0x302
        movk    x3, #0x504, lsl #16
        movk    x3, #0x504, lsl #32
        movk    x3, #0x706, lsl #48
        fmov    d28, x2
        mov     v28.d[1], x3
        movz    x2, #0x605
        movk    x2, #0x807, lsl #16
        movk    x2, #0x706, lsl #32
        movk    x2, #0x908, lsl #48
        movz    x3, #0x908
        movk    x3, #0xb0a, lsl #16
        movk    x3, #0xa09, lsl #32
        movk    x3, #0xc0b, lsl #48
        fmov    d29, x2
        mov     v29.d[1], x3
        movz    x2, #0x4
        movk    x2, #0x1, lsl #32
        movz    x3, #0xfffe
        movk    x3, #0xffff, lsl #16
        movk    x3, #0x3, lsl #32
        fmov    d30, x2
        mov     v30.d[1], x3
        movz    x2, #0x0
        movk    x2, #0xfffd, lsl #32
        movk    x2, #0xffff, lsl #48
        movz    x3, #0x2
        movk    x3, #0xffff, lsl #32
        movk    x3, #0xffff, lsl #48
        fmov    d31, x2
        mov     v31.d[1], x3
        mov     x4, #8

Lmlkem_decompress_d11_loop:
        ldp     q0, q1, [x1], #32
        ldr     d2, [x1], #8
        ld1     {v2.s}[2], [x1], #4

        ext     v4.16b, v0.16b, v1.16b, #11
        ext     v5.16b, v1.16b, v2.16b, #6
        ext     v6.16b, v2.16b, v26.16b, #1
        tbl     v16.16b, {v0.16b}, v28.16b
        tbl     v17.16b, {v0.16b}, v29.16b
        tbl     v18.16b, {v4.16b}, v28.16b
        tbl     v19.16b, {v4.16b}, v29.16b
        tbl     v20.16b, {v5.16b}, v28.16b
        tbl     v21.16b, {v5.16b}, v29.16b
        tbl     v22.16b, {v6.16b}, v28.16b
        tbl     v23.16b, {v6.16b}, v29.16b
        ushl    v16.4s, v16.4s, v30.4s
        ushl    v17.4s, v17.4s, v31.4s
        ushl    v18.4s, v18.4s, v30.4s
        ushl    v19.4s, v19.4s, v31.4s
        ushl    v20.4s, v20.4s, v30.4s
        ushl    v21.4s, v21.4s, v31.4s
        ushl    v22.4s, v22.4s, v30.4s
        ushl    v23.4s, v23.4s, v31.4s
        uzp1    v16.8h, v16.8h, v17.8h
        uzp1    v17.8h, v18.8h, v19.8h
        uzp1    v18.8h, v20.8h, v21.8h
        uzp1    v19.8h, v22.8h, v23.8h
        and     v16.16b, v16.16b, v27.16b
        and     v17.16b, v17.16b, v27.16b
        and     v18.16b, v18.16b, v27.16b
        and     v19.16b, v19.16b, v27.16b
        sqrdmulh v16.8h, v16.8h, v25.8h
        sqrdmulh v17.8h, v17.8h, v25.8h
        sqrdmulh v18.8h, v18.8h, v25.8h
        sqrdmulh v19.8h, v19.8h, v25.8h
        stp     q16, q17, [x0], #32
        stp     q18, q19, [x0], #32

        subs    x4, x4, #1
        bne     Lmlkem_decompress_d11_loop

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_decompress_d11)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
