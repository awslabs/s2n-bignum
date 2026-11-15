// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Pack ML-KEM polynomial coefficients as 12-bit numbers
// Input a[256] (signed 16-bit words); output r[384] (bytes)
//
// This accepts an array of 256 16-bit numbers assumed to be in the range 0 <=
// a[i] < 2^12 (typically they will be < 3329, the ML-KEM prime). It packs them
// into the output array as 12-bit unsigned numbers. This is the same operation
// as mlkem_tobytes, but this is the code for mlkem_poly_tobytes from
// mlkem-native's portable C implementation as compiled by gcc 12.3.0 with -O2
// for x86-64 (see README.md for details).
//
// extern void mlkem_native_poly_tobytes_gcc12_O2
//   (uint8_t r[static 384],const int16_t a[static 256]);
//
// Standard x86-64 ABI: RDI = r, RSI = a
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

.intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_poly_tobytes_gcc12_O2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_native_poly_tobytes_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_poly_tobytes_gcc12_O2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_poly_tobytes_gcc12_O2):
        CFI_START

        lea     r8, [rdi+0x180]
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x84,0x00,0x00,0x00,0x00,0x00
Lmlkem_native_poly_tobytes_gcc12_O2_10:
        movzx   eax, WORD PTR [rsi+0x2]
        movzx   edx, WORD PTR [rsi]
        add     rdi, 0x3
        add     rsi, 0x4
        mov     ecx, eax
        mov     BYTE PTR [rdi-0x3], dl
        shr     dx, 0x8
        shl     ecx, 0x4
        shr     ax, 0x4
        or      edx, ecx
        mov     BYTE PTR [rdi-0x1], al
        mov     BYTE PTR [rdi-0x2], dl
        cmp     r8, rdi
        jne     Lmlkem_native_poly_tobytes_gcc12_O2_10
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_native_poly_tobytes_gcc12_O2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
