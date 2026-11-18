// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Sample from the centered binomial distribution with eta = 2 for ML-KEM
// Input buf[128] (bytes); output r[256] (signed 16-bit words)
//
// Each input byte b = buf[i], with bits b_0 (least significant) to b_7,
// gives two coefficients, each in the range -2..2:
//
//   r[2*i]   = (b_0 + b_1) - (b_2 + b_3)
//   r[2*i+1] = (b_4 + b_5) - (b_6 + b_7)
//
// This is SamplePolyCBD_2 of FIPS 203 (Algorithm 8) on the 128 bytes, as in
// mlkem-native's mlk_poly_cbd2.
//
// extern void mlkem_cbd2(int16_t r[S2N_BIGNUM_STATIC 256],
//                        const uint8_t buf[S2N_BIGNUM_STATIC 128]);
//
// Standard ARM ABI: X0 = r, X1 = buf
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_cbd2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_cbd2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_cbd2)
        .text
        .balign 4

// Each nibble of the input, with bits b_0..b_3 (low to high), gives the
// coefficient (b_0 + b_1) - (b_2 + b_3), a function of the nibble alone,
// so a table lookup (tbl) of the nibbles gives the coefficients as bytes,
// biased by 3 to be nonnegative: the table is
//
//   T[n] = (n_0 + n_1) - (n_2 + n_3) + 3
//        = 3,4,4,5, 2,3,3,4, 2,3,3,4, 1,2,2,3   for n = 0..15.
//
// The low and high nibbles of each byte are separated and interleaved
// (zip) into the order of the coefficients before the lookup, and a
// widening subtraction of the bias gives the 16-bit coefficients.
//
// Each iteration takes 64 bytes to 128 coefficients.
//
// Registers: v0-v3 input and then high nibbles, v4-v7 low nibbles,
// v16-v23 interleaved nibbles and then biased coefficients, v24-v27 and
// v0-v7 coefficients, v29 = 0x0f, v30 = T, v31 = 3 (all bytes).

S2N_BN_SYMBOL(mlkem_cbd2):
        CFI_START
        AARCH64_VALID_CALL_TARGET

        movi    v29.16b, #0x0f
        movi    v31.16b, #3
        movz    x2, #0x0403
        movk    x2, #0x0504, lsl #16
        movk    x2, #0x0302, lsl #32
        movk    x2, #0x0403, lsl #48
        movz    x3, #0x0302
        movk    x3, #0x0403, lsl #16
        movk    x3, #0x0201, lsl #32
        movk    x3, #0x0302, lsl #48
        fmov    d30, x2
        mov     v30.d[1], x3
        mov     x2, #2

Lmlkem_cbd2_loop:
        ldp     q0, q1, [x1], #32
        ldp     q2, q3, [x1], #32

        and     v4.16b, v0.16b, v29.16b
        and     v5.16b, v1.16b, v29.16b
        and     v6.16b, v2.16b, v29.16b
        and     v7.16b, v3.16b, v29.16b
        ushr    v0.16b, v0.16b, #4
        ushr    v1.16b, v1.16b, #4
        ushr    v2.16b, v2.16b, #4
        ushr    v3.16b, v3.16b, #4

        zip1    v16.16b, v4.16b, v0.16b
        zip2    v17.16b, v4.16b, v0.16b
        zip1    v18.16b, v5.16b, v1.16b
        zip2    v19.16b, v5.16b, v1.16b
        zip1    v20.16b, v6.16b, v2.16b
        zip2    v21.16b, v6.16b, v2.16b
        zip1    v22.16b, v7.16b, v3.16b
        zip2    v23.16b, v7.16b, v3.16b

        tbl     v16.16b, {v30.16b}, v16.16b
        tbl     v17.16b, {v30.16b}, v17.16b
        tbl     v18.16b, {v30.16b}, v18.16b
        tbl     v19.16b, {v30.16b}, v19.16b
        tbl     v20.16b, {v30.16b}, v20.16b
        tbl     v21.16b, {v30.16b}, v21.16b
        tbl     v22.16b, {v30.16b}, v22.16b
        tbl     v23.16b, {v30.16b}, v23.16b

        usubl   v24.8h, v16.8b, v31.8b
        usubl2  v25.8h, v16.16b, v31.16b
        usubl   v26.8h, v17.8b, v31.8b
        usubl2  v27.8h, v17.16b, v31.16b
        stp     q24, q25, [x0], #32
        stp     q26, q27, [x0], #32
        usubl   v0.8h, v18.8b, v31.8b
        usubl2  v1.8h, v18.16b, v31.16b
        usubl   v2.8h, v19.8b, v31.8b
        usubl2  v3.8h, v19.16b, v31.16b
        stp     q0, q1, [x0], #32
        stp     q2, q3, [x0], #32
        usubl   v4.8h, v20.8b, v31.8b
        usubl2  v5.8h, v20.16b, v31.16b
        usubl   v6.8h, v21.8b, v31.8b
        usubl2  v7.8h, v21.16b, v31.16b
        stp     q4, q5, [x0], #32
        stp     q6, q7, [x0], #32
        usubl   v24.8h, v22.8b, v31.8b
        usubl2  v25.8h, v22.16b, v31.16b
        usubl   v26.8h, v23.8b, v31.8b
        usubl2  v27.8h, v23.16b, v31.16b
        stp     q24, q25, [x0], #32
        stp     q26, q27, [x0], #32

        subs    x2, x2, #1
        bne     Lmlkem_cbd2_loop

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_cbd2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
