// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Unpack 12-bit ML-KEM polynomial coefficients
// Input a[384] (bytes); output r[256] (signed 16-bit words)
//
// The input is read as 256 12-bit little-endian fields, two to each group
// of 3 bytes (ByteDecode_12 of FIPS 203 without the reduction mod 3329),
// so each output is in the range 0 <= r[i] < 2^12. This is
// mlkem-native's mlk_poly_frombytes.
//
// extern void mlkem_frombytes(int16_t r[S2N_BIGNUM_STATIC 256],
//                             const uint8_t a[S2N_BIGNUM_STATIC 384]);
//
// Standard ARM ABI: X0 = r, X1 = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_frombytes)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_frombytes)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_frombytes)
        .text
        .balign 4

// A table lookup (tbl) gathers, for each of 8 coefficients from 12 bytes,
// the 2 bytes containing its field into a 16-bit lane, where the field is
// in the low 12 bits for an even-numbered coefficient and the high 12
// bits for an odd-numbered one; a shift of each lane by 0 or -4 (ushl)
// and a mask then leave the coefficient.
//
// Each iteration takes 48 bytes to 32 coefficients; byte shifts (ext) of
// the three loaded vectors give the 12-byte windows at offsets 12, 24, 36.
//
// Registers: v0-v2 input, v3-v6 windows and then coefficients,
// v29 = 0x0fff, v30 the shifts 0, -4 (16-bit lanes), v31 the indices.

S2N_BN_SYMBOL(mlkem_frombytes):
        CFI_START
        AARCH64_VALID_CALL_TARGET

        movz    x2, #0x100
        movk    x2, #0x201, lsl #16
        movk    x2, #0x403, lsl #32
        movk    x2, #0x504, lsl #48
        movz    x3, #0x706
        movk    x3, #0x807, lsl #16
        movk    x3, #0xa09, lsl #32
        movk    x3, #0xb0a, lsl #48
        fmov    d31, x2
        mov     v31.d[1], x3
        movz    x2, #0x0
        movk    x2, #0xfffc, lsl #16
        movk    x2, #0xfffc, lsl #48
        dup     v30.2d, x2
        mvni    v29.8h, #0xf0, lsl #8
        mov     x4, #8

Lmlkem_frombytes_loop:
        ldp     q0, q1, [x1], #32
        ldr     q2, [x1], #16

        ext     v4.16b, v0.16b, v1.16b, #12
        ext     v5.16b, v1.16b, v2.16b, #8
        ext     v6.16b, v2.16b, v2.16b, #4
        tbl     v3.16b, {v0.16b}, v31.16b
        tbl     v4.16b, {v4.16b}, v31.16b
        tbl     v5.16b, {v5.16b}, v31.16b
        tbl     v6.16b, {v6.16b}, v31.16b
        ushl    v3.8h, v3.8h, v30.8h
        ushl    v4.8h, v4.8h, v30.8h
        ushl    v5.8h, v5.8h, v30.8h
        ushl    v6.8h, v6.8h, v30.8h
        and     v3.16b, v3.16b, v29.16b
        and     v4.16b, v4.16b, v29.16b
        and     v5.16b, v5.16b, v29.16b
        and     v6.16b, v6.16b, v29.16b
        stp     q3, q4, [x0], #32
        stp     q5, q6, [x0], #32

        subs    x4, x4, #1
        bne     Lmlkem_frombytes_loop

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_frombytes)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
