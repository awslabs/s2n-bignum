// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert a 32-byte message to an ML-KEM polynomial
// Input msg[32] (bytes); output r[256] (signed 16-bit words)
//
// Coefficient 8 * i + j is 1665 = (3329 + 1) / 2 if bit j of msg[i] is
// set and 0 otherwise, i.e. Decompress_1 of FIPS 203 (section 4.2.1)
// applied to ByteDecode_1(msg), as in mlkem-native's mlk_poly_frommsg.
//
// extern void mlkem_frommsg(int16_t r[S2N_BIGNUM_STATIC 256],
//                           const uint8_t msg[S2N_BIGNUM_STATIC 32]);
//
// Standard ARM ABI: X0 = r, X1 = msg
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_frommsg)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_frommsg)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_frommsg)
        .text
        .balign 4

// Each message byte is broadcast to all 16 bytes of a vector (dup), so
// each 16-bit lane j holds it twice; testing lane j against 2^j (cmtst)
// gives all ones exactly when bit j is set, and a mask turns that into
// 1665. Each iteration takes 8 message bytes to 64 coefficients.
//
// Registers: v0 message bytes, v16-v23 coefficients, v30 the bits
// 1, 2, 4, ..., 128 (16-bit lanes), v31 = 1665 (16-bit lanes).

S2N_BN_SYMBOL(mlkem_frommsg):
        CFI_START
        AARCH64_VALID_CALL_TARGET

        movz    w2, #1665
        dup     v31.8h, w2
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

Lmlkem_frommsg_loop:
        ldr     d0, [x1], #8

        dup     v16.16b, v0.b[0]
        dup     v17.16b, v0.b[1]
        dup     v18.16b, v0.b[2]
        dup     v19.16b, v0.b[3]
        dup     v20.16b, v0.b[4]
        dup     v21.16b, v0.b[5]
        dup     v22.16b, v0.b[6]
        dup     v23.16b, v0.b[7]
        cmtst   v16.8h, v16.8h, v30.8h
        cmtst   v17.8h, v17.8h, v30.8h
        cmtst   v18.8h, v18.8h, v30.8h
        cmtst   v19.8h, v19.8h, v30.8h
        cmtst   v20.8h, v20.8h, v30.8h
        cmtst   v21.8h, v21.8h, v30.8h
        cmtst   v22.8h, v22.8h, v30.8h
        cmtst   v23.8h, v23.8h, v30.8h
        and     v16.16b, v16.16b, v31.16b
        and     v17.16b, v17.16b, v31.16b
        and     v18.16b, v18.16b, v31.16b
        and     v19.16b, v19.16b, v31.16b
        and     v20.16b, v20.16b, v31.16b
        and     v21.16b, v21.16b, v31.16b
        and     v22.16b, v22.16b, v31.16b
        and     v23.16b, v23.16b, v31.16b
        stp     q16, q17, [x0], #32
        stp     q18, q19, [x0], #32
        stp     q20, q21, [x0], #32
        stp     q22, q23, [x0], #32

        subs    x4, x4, #1
        bne     Lmlkem_frommsg_loop

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_frommsg)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
