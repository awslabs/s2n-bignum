// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Scalar product of 2-element polynomial vectors in NTT domain, with mulcache
// Inputs a[512], b[512], bt[256] (signed 16-bit words); output r[256]
//
// The inputs a and b are considered as 2-element vectors of linear polynomials
// in the NTT domain (in Montgomery form), and the bt argument an analogous
// 2-element vector of mulcaches for the bi. This is the same operation as
// mlkem_basemul_k2, but this is the code for
// mlkem512_polyvec_basemul_acc_montgomery_cached from mlkem-native's portable
// C implementation as compiled by gcc 12.3.0 with -O2 for x86-64 (see
// README.md for details).
//
// All input elements are assumed <= 2^12 and the bts are assumed to be as
// computed by mlkem_mulcache_compute.
//
// extern void mlkem_native_basemul_k2_gcc12_O2
//      (int16_t r[static 256],const int16_t a[static 512],
//       const int16_t b[static 512], const int16_t bt[static 256]);
//
// Standard x86-64 ABI: RDI = r, RSI = a, RDX = b, RCX = bt
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

.intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_basemul_k2_gcc12_O2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_native_basemul_k2_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_basemul_k2_gcc12_O2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_basemul_k2_gcc12_O2):
        CFI_START

        push    r13
        mov     r8, rdx
        mov     r9, rcx
        xor     eax, eax
        push    r12
        push    rbp
        push    rbx
        // xchg    ax, ax
        .byte   0x66,0x90
Lmlkem_native_basemul_k2_gcc12_O2_10:
        movsx   r11d, WORD PTR [r8+rax*4]
        movsx   r12d, WORD PTR [rsi+rax*4+0x2]
        movsx   r13d, WORD PTR [rsi+rax*4]
        movsx   ecx, WORD PTR [r9+rax*2]
        mov     edx, r11d
        imul    r11d, r12d
        movsx   r10d, WORD PTR [rsi+rax*4+0x202]
        movsx   ebp, WORD PTR [rsi+rax*4+0x200]
        movsx   ebx, WORD PTR [r8+rax*4+0x200]
        imul    edx, r13d
        imul    ecx, r12d
        add     ecx, edx
        movsx   edx, WORD PTR [r9+rax*2+0x100]
        imul    edx, r10d
        imul    r10d, ebx
        add     ecx, edx
        mov     edx, ebp
        imul    edx, ebx
        add     ecx, edx
        movsx   edx, WORD PTR [r8+rax*4+0x2]
        imul    edx, r13d
        add     edx, r11d
        movsx   r11d, WORD PTR [r8+rax*4+0x202]
        imul    r11d, ebp
        add     edx, r11d
        add     edx, r10d
        imul    r10w, cx, 0xf301
        movsx   r10d, r10w
        imul    r10d, r10d, 0xfffff2ff
        add     ecx, r10d
        sar     ecx, 0x10
        mov     WORD PTR [rdi+rax*4], cx
        imul    cx, dx, 0xf301
        movsx   ecx, cx
        imul    ecx, ecx, 0xfffff2ff
        add     edx, ecx
        sar     edx, 0x10
        mov     WORD PTR [rdi+rax*4+0x2], dx
        add     rax, 0x1
        cmp     rax, 0x80
        jne     Lmlkem_native_basemul_k2_gcc12_O2_10
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_native_basemul_k2_gcc12_O2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
