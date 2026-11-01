// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Scalar product of 3-element polynomial vectors in NTT domain, with mulcache
// Inputs a[768], b[768], bt[384] (signed 16-bit words); output r[256]
//
// The inputs a and b are considered as 3-element vectors of linear polynomials
// in the NTT domain (in Montgomery form), and the bt argument an analogous
// 3-element vector of mulcaches for the bi. This is the same operation as
// mlkem_basemul_k3, but this is the code for
// mlkem768_polyvec_basemul_acc_montgomery_cached from mlkem-native's portable
// C implementation as compiled by gcc 12.3.0 with -O2 for x86-64 (see
// README.md for details).
//
// All input elements are assumed <= 2^12 and the bts are assumed to be as
// computed by mlkem_mulcache_compute.
//
// extern void mlkem_native_basemul_k3_gcc12_O2
//      (int16_t r[static 256],const int16_t a[static 768],
//       const int16_t b[static 768], const int16_t bt[static 384]);
//
// Standard x86-64 ABI: RDI = r, RSI = a, RDX = b, RCX = bt
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

.intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_basemul_k3_gcc12_O2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_native_basemul_k3_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_basemul_k3_gcc12_O2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_basemul_k3_gcc12_O2):
        CFI_START

        push    r15
        lea     r8, [rdx+0x2]
        mov     rax, rcx
        mov     r9, rsi
        push    r14
        lea     rdx, [rdi+0x2]
        lea     r14, [rcx+0x100]
        push    r13
        push    r12
        push    rbp
        push    rbx
        // nop
        .byte   0x90
Lmlkem_native_basemul_k3_gcc12_O2_20:
        mov     r11, rax
        xor     ecx, ecx
        xor     edi, edi
        xor     esi, esi
        lea     r12, [r9+0x2]
        lea     rbp, [r8-0x2]
Lmlkem_native_basemul_k3_gcc12_O2_31:
        movsx   ebx, WORD PTR [r12+rcx*1]
        movsx   r10d, WORD PTR [r11]
        add     r11, 0x100
        movsx   r13d, WORD PTR [r9+rcx*1]
        movsx   r15d, WORD PTR [rbp+rcx*1+0x0]
        imul    r10d, ebx
        mov     DWORD PTR [rsp-0x4], ebx
        mov     ebx, r10d
        mov     r10d, r13d
        imul    r10d, r15d
        add     ebx, r10d
        movsx   r10d, WORD PTR [r8+rcx*1]
        add     rcx, 0x200
        add     esi, ebx
        mov     ebx, DWORD PTR [rsp-0x4]
        imul    r10d, r13d
        imul    ebx, r15d
        add     ebx, r10d
        add     edi, ebx
        cmp     rcx, 0x600
        jne     Lmlkem_native_basemul_k3_gcc12_O2_31
        add     rax, 0x2
        add     r9, 0x4
        add     r8, 0x4
        add     rdx, 0x4
        imul    cx, si, 0xf301
        movsx   ecx, cx
        imul    ecx, ecx, 0xfffff2ff
        add     ecx, esi
        sar     ecx, 0x10
        mov     WORD PTR [rdx-0x6], cx
        imul    cx, di, 0xf301
        movsx   ecx, cx
        imul    ecx, ecx, 0xfffff2ff
        add     ecx, edi
        sar     ecx, 0x10
        mov     WORD PTR [rdx-0x4], cx
        cmp     r14, rax
        jne     Lmlkem_native_basemul_k3_gcc12_O2_20
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_native_basemul_k3_gcc12_O2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
