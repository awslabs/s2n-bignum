// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Test bignums for equality, x = y
// Inputs x[m], y[n]; output function return
//
//    extern uint64_t bignum_eq
//     (uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);
//
// Standard x86-64 ABI: RDI = m, RSI = x, RDX = n, RCX = y, returns RAX
// Microsoft x64 ABI:   RCX = m, RDX = x, R8 = n, R9 = y, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_eq)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_eq)
        .text

#define m rdi
#define x rsi
#define n rdx
#define y rcx
#define c rax
// We can re-use n for this, not needed when d appears
#define d rdx

S2N_BN_SYMBOL(bignum_eq):

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
#endif

// Initialize the accumulated OR of differences to zero

        xor     c, c

// If m >= n jump into the m > n loop at the final equality test
// This will drop through for m = n

        cmp     m, n
        jnc     mtest

// Toploop for the case n > m

nloop:
        dec     n
        or      c, [y+8*n]
        cmp     m, n
        jnz     nloop
        jmp     mmain

// Toploop for the case m > n (or n = m which enters at "mtest")

mloop:
        dec     m
        or      c, [x+8*m]
        cmp     m, n
mtest:
        jnz     mloop

// Combined main loop for the min(m,n) lower words

mmain:
        test    m, m
        jz      end

loop:
        mov     d, [x+8*m-8]
        xor     d, [y+8*m-8]
        or      c, d
        dec     m
        jnz     loop

// Set a standard C condition based on whether c is nonzero

end:
        neg     c
        sbb     c, c
        inc     c
#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
