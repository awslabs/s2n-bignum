// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Add ML-KEM polynomials and reduce the coefficients
// Inputs r[256], a[256] (signed 16-bit words);
// output r[256] (signed 16-bit words)
//
// Sets r[i] := (r[i] + a[i]) mod 3329 in the range 0 <= r[i] < 3329, for
// inputs with |r[i] + a[i]| < 2^15. This is mlkem-native's mlk_poly_add
// followed by mlk_poly_reduce.
//
// extern void mlkem_add_reduce(int16_t r[S2N_BIGNUM_STATIC 256],
//                              const int16_t a[S2N_BIGNUM_STATIC 256]);
//
// Standard ARM ABI: X0 = r, X1 = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_add_reduce)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_add_reduce)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_add_reduce)
        .text
        .balign 4

// The reduction is that of mlkem_reduce: with t the sum, the quotient
// estimate is round(floor(t * 20159 / 2^15) / 2^11) (sqdmulh and srshr,
// 20159 being round(2^26 / 3329)), t less that multiple of 3329 is in the
// range -3329 < t < 3329, and 3329 is added if it is negative (the sign
// mask from sshr). Each iteration takes 32 coefficients.
//
// Registers: v0-v3 r, v4-v7 a, v16-v19 quotients and masks,
// v30 = 3329, v31 = 20159 (16-bit lanes).

S2N_BN_SYMBOL(mlkem_add_reduce):
        CFI_START
        AARCH64_VALID_CALL_TARGET

        mov     w2, #3329
        dup     v30.8h, w2
        mov     w2, #20159
        dup     v31.8h, w2
        mov     x4, #8

Lmlkem_add_reduce_loop:
        ldp     q0, q1, [x0]
        ldp     q2, q3, [x0, #32]
        ldp     q4, q5, [x1], #32
        ldp     q6, q7, [x1], #32
        add     v0.8h, v0.8h, v4.8h
        add     v1.8h, v1.8h, v5.8h
        add     v2.8h, v2.8h, v6.8h
        add     v3.8h, v3.8h, v7.8h
        sqdmulh v16.8h, v0.8h, v31.8h
        sqdmulh v17.8h, v1.8h, v31.8h
        sqdmulh v18.8h, v2.8h, v31.8h
        sqdmulh v19.8h, v3.8h, v31.8h
        srshr   v16.8h, v16.8h, #11
        srshr   v17.8h, v17.8h, #11
        srshr   v18.8h, v18.8h, #11
        srshr   v19.8h, v19.8h, #11
        mls     v0.8h, v16.8h, v30.8h
        mls     v1.8h, v17.8h, v30.8h
        mls     v2.8h, v18.8h, v30.8h
        mls     v3.8h, v19.8h, v30.8h
        sshr    v16.8h, v0.8h, #15
        sshr    v17.8h, v1.8h, #15
        sshr    v18.8h, v2.8h, #15
        sshr    v19.8h, v3.8h, #15
        and     v16.16b, v16.16b, v30.16b
        and     v17.16b, v17.16b, v30.16b
        and     v18.16b, v18.16b, v30.16b
        and     v19.16b, v19.16b, v30.16b
        add     v0.8h, v0.8h, v16.8h
        add     v1.8h, v1.8h, v17.8h
        add     v2.8h, v2.8h, v18.8h
        add     v3.8h, v3.8h, v19.8h
        stp     q0, q1, [x0], #32
        stp     q2, q3, [x0], #32

        subs    x4, x4, #1
        bne     Lmlkem_add_reduce_loop

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_add_reduce)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
