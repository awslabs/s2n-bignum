// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Scalar product of 4-element polynomial vectors in NTT domain, with mulcache
// Inputs a[1024], b[1024], bt[512] (signed 16-bit words); output r[256]
//
// The inputs a and b are considered as 4-element vectors of linear polynomials
// in the NTT domain (in Montgomery form), and the bt argument an analogous
// 4-element vector of mulcaches for the bi. This is the same operation as
// mlkem_basemul_k4, but this is the code for
// mlkem1024_polyvec_basemul_acc_montgomery_cached from mlkem-native's portable
// C implementation as compiled by gcc 12.3.0 with -O2 for x86-64 (see
// README.md for details).
//
// All input elements are assumed <= 2^12 and the bts are assumed to be as
// computed by mlkem_mulcache_compute.
//
// extern void mlkem_native_basemul_k4_gcc12_O2
//      (int16_t r[static 256],const int16_t a[static 1024],
//       const int16_t b[static 1024], const int16_t bt[static 512]);
//
// Standard x86-64 ABI: RDI = r, RSI = a, RDX = b, RCX = bt
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_x86.h"

.intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_basemul_k4_gcc12_O2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_native_basemul_k4_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_basemul_k4_gcc12_O2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_basemul_k4_gcc12_O2):
        CFI_START

        push    r15
        mov     r9, rdi
        mov     rax, rcx
        lea     rdi, [rdx+0x2]
        push    r14
        mov     r8, rsi
        lea     rdx, [r9+0x2]
        lea     r14, [rcx+0x100]
        push    r13
        push    r12
        push    rbp
        push    rbx
        // nop     WORD PTR [rax+rax*1+0x0]
        .byte   0x66,0x0f,0x1f,0x44,0x00,0x00
Lmlkem_native_basemul_k4_gcc12_O2_28:
        mov     r10, rax
        xor     r9d, r9d
        xor     esi, esi
        xor     ecx, ecx
        lea     rbx, [r8+0x2]
        lea     r11, [rdi-0x2]
Lmlkem_native_basemul_k4_gcc12_O2_3a:
        movsx   r15d, WORD PTR [rbx+r9*1]
        movsx   ebp, WORD PTR [r10]
        add     r10, 0x100
        movsx   r13d, WORD PTR [r8+r9*1]
        mov     DWORD PTR [rsp-0x4], r15d
        mov     r12d, DWORD PTR [rsp-0x4]
        movsx   r15d, WORD PTR [r11+r9*1]
        imul    ebp, r12d
        mov     r12d, ebp
        mov     ebp, r13d
        imul    ebp, r15d
        add     r12d, ebp
        movsx   ebp, WORD PTR [rdi+r9*1]
        add     r9, 0x200
        add     ecx, r12d
        mov     r12d, DWORD PTR [rsp-0x4]
        imul    ebp, r13d
        imul    r12d, r15d
        add     ebp, r12d
        add     esi, ebp
        cmp     r9, 0x800
        jne     Lmlkem_native_basemul_k4_gcc12_O2_3a
        add     rax, 0x2
        add     r8, 0x4
        add     rdi, 0x4
        add     rdx, 0x4
        imul    r9w, cx, 0xf301
        movsx   r9d, r9w
        imul    r9d, r9d, 0xfffff2ff
        add     ecx, r9d
        sar     ecx, 0x10
        mov     WORD PTR [rdx-0x6], cx
        imul    cx, si, 0xf301
        movsx   ecx, cx
        imul    ecx, ecx, 0xfffff2ff
        add     ecx, esi
        sar     ecx, 0x10
        mov     WORD PTR [rdx-0x4], cx
        cmp     r14, rax
        jne     Lmlkem_native_basemul_k4_gcc12_O2_28
        pop     rbx
        pop     rbp
        pop     r12
        pop     r13
        pop     r14
        pop     r15
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_native_basemul_k4_gcc12_O2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
