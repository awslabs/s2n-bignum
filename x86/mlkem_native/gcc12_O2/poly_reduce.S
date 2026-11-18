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
// compiled by gcc 12.3.0 with -O2 for x86-64 (see README.md for details).
//
// extern void mlkem_native_poly_reduce_gcc12_O2(int16_t a[static 256]);
//
// Standard x86-64 ABI: RDI = a
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

.intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_poly_reduce_gcc12_O2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_native_poly_reduce_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_poly_reduce_gcc12_O2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_poly_reduce_gcc12_O2):
        CFI_START

        mov     rcx, rdi
        lea     rsi, [rdi+0x200]
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
Lmlkem_native_poly_reduce_gcc12_O2_10:
        movsx   edx, WORD PTR [rcx]
        mov     eax, edx
        imul    edx, edx, 0x4ebf
        add     edx, 0x2000000
        sar     edx, 0x1a
        imul    dx, dx, 0xf2ff
        add     edx, eax
        movsx   eax, dx
        shr     eax, 0x10
        neg     eax
        lea     edi, [rdx+0xd01]
        sar     eax, 0x10
        add     rcx, 0x2
        xor     edi, edx
        and     eax, edi
        xor     eax, edx
        mov     WORD PTR [rcx-0x2], ax
        cmp     rcx, rsi
        jne     Lmlkem_native_poly_reduce_gcc12_O2_10
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_native_poly_reduce_gcc12_O2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
