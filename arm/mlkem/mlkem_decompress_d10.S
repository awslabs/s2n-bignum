// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Unpack 10-bit ML-KEM compressed coefficients and decompress them
// Input a[320] (bytes); output r[256] (signed 16-bit words)
//
// The input is read as 256 10-bit little-endian fields u[i], 4 to each
// group of 5 bytes (ByteDecode_10), and each is mapped to
// round(u[i] * 3329 / 2^10), rounding halves up (Decompress_10 of FIPS 203,
// section 4.2.1), which is in the range 0 <= r[i] < 3329. This is
// mlkem-native's mlk_poly_decompress_d10.
//
// extern void mlkem_decompress_d10(int16_t r[S2N_BIGNUM_STATIC 256],
//                                  const uint8_t a[S2N_BIGNUM_STATIC 320]);
//
// Standard ARM ABI: X0 = r, X1 = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_decompress_d10)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_decompress_d10)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_decompress_d10)
        .text
        .balign 4

// A table lookup (tbl) gathers, for each of 8 coefficients from 10 bytes,
// the 2 bytes containing its field into a 16-bit lane, where the field
// is at bit 0, 2, 4 or 6; a shift of each lane by 5, 3, 1 or -1 (ushl)
// and a mask then leave u[i] * 2^5. The rounding doubling multiply high
// by 3329 (sqrdmulh) is floor((2 * u * 2^5 * 3329 + 2^15) / 2^16), that
// is floor((u * 3329 + 2^9) / 2^10), the rounded result.
//
// Each iteration takes 40 bytes to 32 coefficients; byte shifts (ext) of
// the three loaded vectors give the 10-byte windows at offsets 10, 20, 30.
//
// Registers: v0-v2 input, v3-v6 windows and then coefficients,
// v28 = 0x7fe0, v29 the shifts, v30 the table indices,
// v31 = 3329 (16-bit lanes).

S2N_BN_SYMBOL(mlkem_decompress_d10):
        CFI_START
        AARCH64_VALID_CALL_TARGET

        movz    w2, #3329
        dup     v31.8h, w2
        movi    v28.8h, #0x7f, lsl #8
        orr     v28.8h, #0xe0
        movz    x2, #0x100
        movk    x2, #0x201, lsl #16
        movk    x2, #0x302, lsl #32
        movk    x2, #0x403, lsl #48
        movz    x3, #0x605
        movk    x3, #0x706, lsl #16
        movk    x3, #0x807, lsl #32
        movk    x3, #0x908, lsl #48
        fmov    d30, x2
        mov     v30.d[1], x3
        movz    x2, #0x5
        movk    x2, #0x3, lsl #16
        movk    x2, #0x1, lsl #32
        movk    x2, #0xffff, lsl #48
        dup     v29.2d, x2
        mov     x4, #8

Lmlkem_decompress_d10_loop:
        ldp     q0, q1, [x1], #32
        ldr     d2, [x1], #8

        ext     v4.16b, v0.16b, v1.16b, #10
        ext     v5.16b, v1.16b, v2.16b, #4
        ext     v6.16b, v1.16b, v2.16b, #14
        tbl     v3.16b, {v0.16b}, v30.16b
        tbl     v4.16b, {v4.16b}, v30.16b
        tbl     v5.16b, {v5.16b}, v30.16b
        tbl     v6.16b, {v6.16b}, v30.16b
        ushl    v3.8h, v3.8h, v29.8h
        ushl    v4.8h, v4.8h, v29.8h
        ushl    v5.8h, v5.8h, v29.8h
        ushl    v6.8h, v6.8h, v29.8h
        and     v3.16b, v3.16b, v28.16b
        and     v4.16b, v4.16b, v28.16b
        and     v5.16b, v5.16b, v28.16b
        and     v6.16b, v6.16b, v28.16b
        sqrdmulh v3.8h, v3.8h, v31.8h
        sqrdmulh v4.8h, v4.8h, v31.8h
        sqrdmulh v5.8h, v5.8h, v31.8h
        sqrdmulh v6.8h, v6.8h, v31.8h
        stp     q3, q4, [x0], #32
        stp     q5, q6, [x0], #32

        subs    x4, x4, #1
        bne     Lmlkem_decompress_d10_loop

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_decompress_d10)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
