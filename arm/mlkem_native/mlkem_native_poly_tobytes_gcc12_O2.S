// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Pack ML-KEM polynomial coefficients as 12-bit numbers
// Input a[256] (signed 16-bit words); output r[384] (bytes)
//
// This accepts an array of 256 16-bit numbers assumed to be in the range
// 0 <= a[i] < 2^12 (typically they will be < 3329, the ML-KEM prime).
// It packs them into the output array as 12-bit unsigned numbers. This
// is the same operation as mlkem_tobytes, but this is the code for
// mlkem_poly_tobytes from mlkem-native's portable C implementation as
// compiled by gcc 12.3.0 with -O2 (see README.md for details).
//
// extern void mlkem_native_poly_tobytes_gcc12_O2
//   (uint8_t r[static 384],const int16_t a[static 256]);
//
// Standard ARM ABI: X0 = r, X1 = a
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_poly_tobytes_gcc12_O2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_native_poly_tobytes_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_poly_tobytes_gcc12_O2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_poly_tobytes_gcc12_O2):
        CFI_START

        add     x4, x0, #0x180
        nop
Lmlkem_native_poly_tobytes_gcc12_O2_loop:
        ldrsh   w2, [x1]
        add     x0, x0, #0x3
        ldrh    w3, [x1, #2]
        add     x1, x1, #0x4
        sturb   w2, [x0, #-3]
        ubfx    x2, x2, #8, #8
        orr     w2, w2, w3, lsl #4
        lsr     w3, w3, #4
        sturb   w2, [x0, #-2]
        sturb   w3, [x0, #-1]
        cmp     x4, x0
        b.ne    Lmlkem_native_poly_tobytes_gcc12_O2_loop
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_native_poly_tobytes_gcc12_O2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
