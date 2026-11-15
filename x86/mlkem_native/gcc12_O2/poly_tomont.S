// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Conversion of ML-KEM polynomial coefficients to Montgomery form
// Input a[256] (signed 16-bit words); output a[256] (signed 16-bit words)
//
// This converts each element of the 256-element array of 16-bit signed
// integers modulo 3329 into Montgomery form, giving a signed result satisfying
// (output[i] == 2^16 * input[i]) (mod 3329), without full modular reduction
// but with |output[i]| < 3329 guaranteed. This is the same operation as
// mlkem_tomont, but this is the code for mlkem_poly_tomont from mlkem-native's
// portable C implementation as compiled by gcc 12.3.0 with -O2 for x86-64 (see
// README.md for details), which the compiler has vectorized. It uses its own
// vectors of constants, which are the anonymous constants at addresses 0x8070,
// 0x8080 and 0x8090 in the binary.
//
// extern void mlkem_native_poly_tomont_gcc12_O2(int16_t a[static 256]);
//
// Standard x86-64 ABI: RDI = a
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

.intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_poly_tomont_gcc12_O2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_native_poly_tomont_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_poly_tomont_gcc12_O2)
        .text
        .balign 4

#define CONSTANTS mlkem_native_poly_tomont_gcc12_O2_constants

S2N_BN_SYMBOL(mlkem_native_poly_tomont_gcc12_O2):
        CFI_START

        movdqa  xmm5, XMMWORD PTR [rip+CONSTANTS]
        movdqa  xmm6, XMMWORD PTR [rip+CONSTANTS+0x10]
        lea     rax, [rdi+0x200]
        movdqa  xmm4, XMMWORD PTR [rip+CONSTANTS+0x20]
        // nop
        .byte   0x90
Lmlkem_native_poly_tomont_gcc12_O2_20:
        movdqa  xmm3, XMMWORD PTR [rdi]
        movdqa  xmm0, xmm5
        pmulhw  xmm0, XMMWORD PTR [rdi]
        add     rdi, 0x10
        pmullw  xmm3, xmm5
        movdqa  xmm7, xmm3
        punpckhwd xmm3, xmm0
        punpcklwd xmm7, xmm0
        movdqa  xmm0, xmm7
        movdqa  xmm1, xmm7
        punpcklwd xmm0, xmm3
        punpckhwd xmm1, xmm3
        movdqa  xmm2, xmm0
        punpcklwd xmm0, xmm1
        punpckhwd xmm2, xmm1
        punpcklwd xmm0, xmm2
        pmullw  xmm0, xmm6
        movdqa  xmm2, xmm0
        movdqa  xmm1, xmm0
        pmulhw  xmm1, xmm4
        pmullw  xmm2, xmm4
        movdqa  xmm0, xmm2
        punpckhwd xmm2, xmm1
        punpcklwd xmm0, xmm1
        movdqa  xmm1, xmm2
        paddd   xmm0, xmm7
        paddd   xmm1, xmm3
        psrad   xmm1, 0x10
        psrad   xmm0, 0x10
        movdqa  xmm2, xmm0
        punpcklwd xmm0, xmm1
        punpckhwd xmm2, xmm1
        movdqa  xmm1, xmm0
        punpckhwd xmm1, xmm2
        punpcklwd xmm0, xmm2
        punpcklwd xmm0, xmm1
        movaps  XMMWORD PTR [rdi-0x10], xmm0
        cmp     rax, rdi
        jne     Lmlkem_native_poly_tomont_gcc12_O2_20
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_native_poly_tomont_gcc12_O2)

// Vectors of constants for the multiplications

#if defined(__ELF__)
        .section .rodata
#elif defined(__APPLE__)
        .const_data
#endif
        .balign 16
#if defined(__ELF__)
        .type   CONSTANTS, %object
        .size   CONSTANTS, 48
#endif
CONSTANTS:
        .short  1353, 1353, 1353, 1353, 1353, 1353, 1353, 1353
        .short  -3327, -3327, -3327, -3327, -3327, -3327, -3327, -3327
        .short  -3329, -3329, -3329, -3329, -3329, -3329, -3329, -3329

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
