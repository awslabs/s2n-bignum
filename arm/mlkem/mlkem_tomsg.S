// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert an ML-KEM polynomial to a 32-byte message
// Input a[256] (signed 16-bit words); output msg[32] (bytes)
//
// The input coefficients are assumed to be in the range 0 <= a[i] < 3329.
// Bit j of msg[i] is round(2 * a[8 * i + j] / 3329) mod 2, i.e. 1 exactly
// when 833 <= a[8 * i + j] <= 2496: ByteEncode_1 of Compress_1 (FIPS 203,
// section 4.2.1), as in mlkem-native's mlk_poly_tomsg.
//
// extern void mlkem_tomsg(uint8_t msg[S2N_BIGNUM_STATIC 32],
//                         const int16_t a[S2N_BIGNUM_STATIC 256]);
//
// Standard ARM ABI: X0 = msg, X1 = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_tomsg)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_tomsg)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_tomsg)
        .text
        .balign 4

// The test 833 <= a <= 2496 is the unsigned comparison a - 833 < 1664
// (sub and cmhi), giving all ones or zero in each 16-bit lane; a mask
// with 2^j in lane j selects the bits, and three levels of pairwise
// additions (addp) of eight such vectors give the eight message bytes
// in 16-bit lanes, narrowed (xtn) for the store. Each iteration takes 64
// coefficients to 8 bytes.
//
// Registers: v0-v7 coefficients, then bits and partial sums,
// v29 = 833, v30 the bits 1, 2, 4, ..., 128, v31 = 1664 (16-bit lanes).

S2N_BN_SYMBOL(mlkem_tomsg):
        CFI_START
        AARCH64_VALID_CALL_TARGET

        movi    v29.8h, #0x03, lsl #8
        orr     v29.8h, #0x41
        movi    v31.8h, #0x06, lsl #8
        orr     v31.8h, #0x80
        movz    x2, #0x0001
        movk    x2, #0x0002, lsl #16
        movk    x2, #0x0004, lsl #32
        movk    x2, #0x0008, lsl #48
        movz    x3, #0x0010
        movk    x3, #0x0020, lsl #16
        movk    x3, #0x0040, lsl #32
        movk    x3, #0x0080, lsl #48
        fmov    d30, x2
        mov     v30.d[1], x3
        mov     x4, #4

Lmlkem_tomsg_loop:
        ldp     q0, q1, [x1], #32
        ldp     q2, q3, [x1], #32
        ldp     q4, q5, [x1], #32
        ldp     q6, q7, [x1], #32
        sub     v0.8h, v0.8h, v29.8h
        sub     v1.8h, v1.8h, v29.8h
        sub     v2.8h, v2.8h, v29.8h
        sub     v3.8h, v3.8h, v29.8h
        sub     v4.8h, v4.8h, v29.8h
        sub     v5.8h, v5.8h, v29.8h
        sub     v6.8h, v6.8h, v29.8h
        sub     v7.8h, v7.8h, v29.8h
        cmhi    v0.8h, v31.8h, v0.8h
        cmhi    v1.8h, v31.8h, v1.8h
        cmhi    v2.8h, v31.8h, v2.8h
        cmhi    v3.8h, v31.8h, v3.8h
        cmhi    v4.8h, v31.8h, v4.8h
        cmhi    v5.8h, v31.8h, v5.8h
        cmhi    v6.8h, v31.8h, v6.8h
        cmhi    v7.8h, v31.8h, v7.8h
        and     v0.16b, v0.16b, v30.16b
        and     v1.16b, v1.16b, v30.16b
        and     v2.16b, v2.16b, v30.16b
        and     v3.16b, v3.16b, v30.16b
        and     v4.16b, v4.16b, v30.16b
        and     v5.16b, v5.16b, v30.16b
        and     v6.16b, v6.16b, v30.16b
        and     v7.16b, v7.16b, v30.16b
        addp    v0.8h, v0.8h, v1.8h
        addp    v2.8h, v2.8h, v3.8h
        addp    v4.8h, v4.8h, v5.8h
        addp    v6.8h, v6.8h, v7.8h
        addp    v0.8h, v0.8h, v2.8h
        addp    v4.8h, v4.8h, v6.8h
        addp    v0.8h, v0.8h, v4.8h
        xtn     v0.8b, v0.8h
        str     d0, [x0], #8

        subs    x4, x4, #1
        bne     Lmlkem_tomsg_loop

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_tomsg)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
