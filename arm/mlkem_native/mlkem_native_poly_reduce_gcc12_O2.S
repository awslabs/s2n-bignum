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
// compiled by gcc 12.3.0 with -O2 (see README.md for details).
//
// extern void mlkem_native_poly_reduce_gcc12_O2(int16_t a[static 256]);
//
// Standard ARM ABI: X0 = a
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_poly_reduce_gcc12_O2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_native_poly_reduce_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_poly_reduce_gcc12_O2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_poly_reduce_gcc12_O2):
        CFI_START

        add     x5, x0, #0x200
        mov     w7, #0x4ebf
        mov     w6, #0x2000000
        mov     w4, #0xfffff2ff
Lmlkem_native_poly_reduce_gcc12_O2_loop:
        ldrsh   w2, [x0]
        madd    w1, w2, w7, w6
        asr     w1, w1, #26
        madd    w1, w1, w4, w2
        sxth    w1, w1
        mov     w2, w1
        neg     w2, w2, lsr #16
        add     w3, w1, #0xd01
        eor     w3, w1, w3
        and     w2, w3, w2, asr #16
        eor     w1, w1, w2
        strh    w1, [x0], #2
        cmp     x5, x0
        b.ne    Lmlkem_native_poly_reduce_gcc12_O2_loop
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_native_poly_reduce_gcc12_O2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
