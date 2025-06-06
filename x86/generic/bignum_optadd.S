// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Optionally add, z := x + y (if p nonzero) or z := x (if p zero)
// Inputs x[k], p, y[k]; outputs function return (carry-out) and z[k]
//
//    extern uint64_t bignum_optadd(uint64_t k, uint64_t *z, const uint64_t *x,
//                                  uint64_t p, const uint64_t *y);
//
// It is assumed that all numbers x, y and z have the same size k digits.
// Returns carry-out as per usual addition, always 0 if p was zero.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = x, RCX = p, R8 = y, returns RAX
// Microsoft x64 ABI:   RCX = k, RDX = z, R8 = x, R9 = p, [RSP+40] = y, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_optadd)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_optadd)
        .text

#define k rdi
#define z rsi
#define x rdx
#define p rcx
#define y r8

#define c rax
#define i r9
#define b r10
#define a r11


S2N_BN_SYMBOL(bignum_optadd):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
        mov     rcx, r9
        mov     r8, [rsp+56]
#endif

// Initialize top carry to zero in all cases (also return value)

        xor     c, c

// If k = 0 do nothing

        test    k, k
        jz      bignum_optadd_end

// Convert the nonzero/zero status of p into an all-1s or all-0s mask

        neg     p
        sbb     p, p

// Now go round the loop for i=0...k-1, saving the carry in c each iteration

        xor     i, i
bignum_optadd_loop:
        mov     a, [x+8*i]
        mov     b, [y+8*i]
        and     b, p
        neg     c
        adc     a, b
        sbb     c, c
        mov     [z+8*i], a
        inc     i
        cmp     i, k
        jc      bignum_optadd_loop

// Return top carry

        neg     rax

bignum_optadd_end:
#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
