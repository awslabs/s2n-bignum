// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Canonical reduction of polynomial coefficients for ML-KEM
// Input a[256] (signed 16-bit words); output a[256] (signed 16-bit words)
//
// This reduces each element of the 256-element array of 16-bit signed
// integers modulo 3329 with the result being 0 <= r < 3329, in-place.
// It is the same operation as mlkem_reduce, but this is the code for
// mlkem_poly_reduce from mlkem-native's portable C implementation as
// compiled by clang 17.0.6 with -O2 (see README.md for details).
//
// extern void mlkem_native_poly_reduce_clang17_O2(int16_t a[static 256]);
//
// Standard ARM ABI: X0 = a
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_poly_reduce_clang17_O2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_native_poly_reduce_clang17_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_poly_reduce_clang17_O2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_poly_reduce_clang17_O2):
        CFI_START

        mov     x8, xzr
        mov     w9, #0x4ebf
        mov     w10, #0x2000000
        mov     w11, #0xfffff2ff
Lmlkem_native_poly_reduce_clang17_O2_loop:
        ldrsh   w12, [x0, x8]
        madd    w13, w12, w9, w10
        asr     w13, w13, #26
        madd    w12, w13, w11, w12
        sxth    w13, w12
        add     w14, w12, #0xd01
        neg     w13, w13, lsr #16
        lsr     w13, w13, #16
        bic     w12, w12, w13
        and     w13, w14, w13
        orr     w12, w13, w12
        strh    w12, [x0, x8]
        add     x8, x8, #0x2
        cmp     x8, #0x200
        b.ne    Lmlkem_native_poly_reduce_clang17_O2_loop
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_native_poly_reduce_clang17_O2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
