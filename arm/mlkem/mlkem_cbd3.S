// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Sample from the centered binomial distribution with eta = 3 for ML-KEM
// Input buf[192] (bytes); output r[256] (signed 16-bit words)
//
// Each group of 3 input bytes, the 24-bit little-endian number t, gives
// four coefficients, each in the range -3..3: with t_k the bits of t,
//
//   r[4*i+j] = (t_6j + t_6j+1 + t_6j+2) - (t_6j+3 + t_6j+4 + t_6j+5)
//
// for group i = 0..63 and j = 0..3. This is SamplePolyCBD_3 of FIPS 203
// (Algorithm 8) on the 192 bytes, as in mlkem-native's mlk_poly_cbd3.
//
// extern void mlkem_cbd3(int16_t r[S2N_BIGNUM_STATIC 256],
//                        const uint8_t buf[S2N_BIGNUM_STATIC 192]);
//
// Standard ARM ABI: X0 = r, X1 = buf
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_cbd3)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_cbd3)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_cbd3)
        .text
        .balign 4

// Each coefficient is a function of its 6-bit field n alone, so a lookup
// in a 64-byte table (tbl with four registers) gives the coefficients as
// bytes, biased by 3 to be nonnegative:
//
//   T[n] = popcount(n AND 7) - popcount(n >> 3) + 3.
//
// The table is built in registers: with A the 8 bytes popcount(x) + 3
// for x = 0..7, its four 16-byte parts are A,A plus 0,...,0,-1,...,-1,
// then that less 1 (twice) and less 2.
//
// A de-interleaving load (ld3) gives the bytes b0, b1, b2 of 16 groups,
// from which the four fields are b0 AND 63, (b0 >> 6) + 4 * b1 AND 63,
// (b1 >> 4) + 16 * b2 AND 63 and b2 >> 2 (with shift-and-insert, sli).
// After the lookups, two levels of interleaving (zip of bytes and then of
// 16-bit pairs) put the coefficients in order, and a widening subtraction
// of the bias gives them as 16-bit words.
//
// Each iteration takes 48 bytes to 64 coefficients.
//
// Registers: v0-v2 input bytes, v3-v6 fields and then coefficient bytes,
// v7, v16-v19 interleaved bytes, v20-v27 coefficients, v28 = 63,
// v29 = 3 (bytes), v30 = 1 (bytes), v31 = 0; v24-v27 are first the table.

S2N_BN_SYMBOL(mlkem_cbd3):
        CFI_START
        AARCH64_VALID_CALL_TARGET

        movz    x2, #0x0403
        movk    x2, #0x0504, lsl #16
        movk    x2, #0x0504, lsl #32
        movk    x2, #0x0605, lsl #48
        dup     v24.2d, x2
        movi    v31.2d, #0
        movi    v30.16b, #1
        movi    v29.16b, #3
        movi    v28.16b, #63
        movi    v7.2d, #0xffffffffffffffff
        ext     v7.16b, v31.16b, v7.16b, #8
        add     v24.16b, v24.16b, v7.16b
        sub     v25.16b, v24.16b, v30.16b
        mov     v26.16b, v25.16b
        sub     v27.16b, v25.16b, v30.16b
        mov     x4, #4

Lmlkem_cbd3_loop:
        ld3     {v0.16b, v1.16b, v2.16b}, [x1], #48

        and     v3.16b, v0.16b, v28.16b
        ushr    v4.16b, v0.16b, #6
        ushr    v5.16b, v1.16b, #4
        ushr    v6.16b, v2.16b, #2
        sli     v4.16b, v1.16b, #2
        sli     v5.16b, v2.16b, #4
        and     v4.16b, v4.16b, v28.16b
        and     v5.16b, v5.16b, v28.16b

        tbl     v3.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v3.16b
        tbl     v4.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v4.16b
        tbl     v5.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v5.16b
        tbl     v6.16b, {v24.16b, v25.16b, v26.16b, v27.16b}, v6.16b

        zip1    v0.16b, v3.16b, v4.16b
        zip1    v1.16b, v5.16b, v6.16b
        zip2    v2.16b, v3.16b, v4.16b
        zip2    v7.16b, v5.16b, v6.16b
        zip1    v16.8h, v0.8h, v1.8h
        zip2    v17.8h, v0.8h, v1.8h
        zip1    v18.8h, v2.8h, v7.8h
        zip2    v19.8h, v2.8h, v7.8h

        usubl   v0.8h, v16.8b, v29.8b
        usubl2  v1.8h, v16.16b, v29.16b
        usubl   v2.8h, v17.8b, v29.8b
        usubl2  v3.8h, v17.16b, v29.16b
        usubl   v4.8h, v18.8b, v29.8b
        usubl2  v5.8h, v18.16b, v29.16b
        usubl   v6.8h, v19.8b, v29.8b
        usubl2  v7.8h, v19.16b, v29.16b
        stp     q0, q1, [x0], #32
        stp     q2, q3, [x0], #32
        stp     q4, q5, [x0], #32
        stp     q6, q7, [x0], #32

        subs    x4, x4, #1
        bne     Lmlkem_cbd3_loop

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_cbd3)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
