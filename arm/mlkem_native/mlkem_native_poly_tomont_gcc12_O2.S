// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Conversion of ML-KEM polynomial coefficients to Montgomery form
// Input a[256] (signed 16-bit words); output a[256] (signed 16-bit words)
//
// This converts each element of the 256-element array of 16-bit signed
// integers modulo 3329 into Montgomery form, giving a signed result
// satisfying (output[i] == 2^16 * input[i]) (mod 3329), without full
// modular reduction but with |output[i]| < 3329 guaranteed. This is the
// same operation as mlkem_tomont, but this is the code for mlkem_poly_tomont
// from mlkem-native's portable C implementation as compiled by gcc 12.3.0
// with -O2 (see README.md for details), which the compiler has vectorized.
// It uses its own vectors of constants, which are the anonymous constants
// at addresses 0x6220 and 0x6230 in the binary.
//
// extern void mlkem_native_poly_tomont_gcc12_O2(int16_t a[static 256]);
//
// Standard ARM ABI: X0 = a
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_poly_tomont_gcc12_O2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_native_poly_tomont_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_poly_tomont_gcc12_O2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_poly_tomont_gcc12_O2):
        CFI_START

#if defined(__ELF__)
        adrp    x2, mlkem_native_poly_tomont_gcc12_O2_constants+16
        adrp    x1, mlkem_native_poly_tomont_gcc12_O2_constants
#else
        adrp    x2, mlkem_native_poly_tomont_gcc12_O2_constants@PAGE+16
        adrp    x1, mlkem_native_poly_tomont_gcc12_O2_constants@PAGE
#endif
        mvni    v3.8h, #0xd, lsl #8
#if defined(__ELF__)
        ldr     q5, [x2, :lo12:mlkem_native_poly_tomont_gcc12_O2_constants+16]
        ldr     q4, [x1, :lo12:mlkem_native_poly_tomont_gcc12_O2_constants]
#else
        ldr     q5, [x2, mlkem_native_poly_tomont_gcc12_O2_constants@PAGEOFF+16]
        ldr     q4, [x1, mlkem_native_poly_tomont_gcc12_O2_constants@PAGEOFF]
#endif
        add     x1, x0, #0x200
Lmlkem_native_poly_tomont_gcc12_O2_loop:
        ldr     q0, [x0]
        smull   v1.4s, v0.4h, v4.4h
        smull2  v0.4s, v0.8h, v4.8h
        uzp1    v2.8h, v1.8h, v0.8h
        mul     v2.8h, v2.8h, v5.8h
        smlal   v1.4s, v2.4h, v3.4h
        smlal2  v0.4s, v2.8h, v3.8h
        uzp2    v1.8h, v1.8h, v0.8h
        str     q1, [x0], #16
        cmp     x1, x0
        b.ne    Lmlkem_native_poly_tomont_gcc12_O2_loop
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_native_poly_tomont_gcc12_O2)

// The vectors of constants: 2^32 mod 3329 = 1353 and the inverse of 3329
// modulo 2^16, as the signed value -3327, in each 16-bit lane

#if defined(__ELF__)
        .section .rodata
#elif defined(__APPLE__)
        .const_data
#endif
        .balign 16
#if defined(__ELF__)
        .type   mlkem_native_poly_tomont_gcc12_O2_constants, %object
        .size   mlkem_native_poly_tomont_gcc12_O2_constants, 32
#endif
mlkem_native_poly_tomont_gcc12_O2_constants:
        .short  1353, 1353, 1353, 1353, 1353, 1353, 1353, 1353
        .short  -3327, -3327, -3327, -3327, -3327, -3327, -3327, -3327

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
