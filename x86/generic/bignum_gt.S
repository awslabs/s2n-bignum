// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Compare bignums, x > y
// Inputs x[m], y[n]; output function return
//
//    extern uint64_t bignum_gt(uint64_t m, const uint64_t *x, uint64_t n,
//                              const uint64_t *y);
//
// Standard x86-64 ABI: RDI = m, RSI = x, RDX = n, RCX = y, returns RAX
// Microsoft x64 ABI:   RCX = m, RDX = x, R8 = n, R9 = y, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_gt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_gt)
        .text

#define m rdi
#define x rsi
#define n rdx
#define y rcx
#define i r8
#define a rax

#define ashort eax



S2N_BN_SYMBOL(bignum_gt):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
#endif

// Zero the main index counter for both branches

        xor     i, i

// Speculatively form n := n - m and do case split

        sub     n, m
        jc      bignum_gt_ylonger

// The case where y is longer or of the same size (n >= m)

        inc     n
        test    m, m
        jz      bignum_gt_xtest
bignum_gt_xmainloop:
        mov     a, [y+8*i]
        sbb     a, [x+8*i]
        inc     i
        dec     m
        jnz     bignum_gt_xmainloop
        jmp     bignum_gt_xtest
bignum_gt_xtoploop:
        mov     a, [y+8*i]
        sbb     a, 0
        inc     i
bignum_gt_xtest:
        dec     n
        jnz     bignum_gt_xtoploop
        sbb     a, a
        neg     a
#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

// The case where x is longer (m > n)

bignum_gt_ylonger:
        add     n, m
        sub     m, n
        test    n, n
        jz      bignum_gt_ytoploop
bignum_gt_ymainloop:
        mov     a, [y+8*i]
        sbb     a, [x+8*i]
        inc     i
        dec     n
        jnz     bignum_gt_ymainloop
bignum_gt_ytoploop:
        mov     ashort, 0
        sbb     a, [x+8*i]
        inc     i
        dec     m
        jnz     bignum_gt_ytoploop

        sbb     a, a
        neg     a
#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
