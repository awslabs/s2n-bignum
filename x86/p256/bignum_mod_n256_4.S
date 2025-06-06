// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Reduce modulo group order, z := x mod n_256
// Input x[4]; output z[4]
//
//    extern void bignum_mod_n256_4(uint64_t z[static 4], const uint64_t x[static 4]);
//
// Reduction is modulo the group order of the NIST curve P-256.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mod_n256_4)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mod_n256_4)
        .text

#define z rdi
#define x rsi



#define d0 rdx
#define d1 rcx
#define d2 r8
#define d3 r9

#define n0 rax
#define n1 r10
#define n3 r11

#define n3short r11d

// Can re-use this as a temporary once we've loaded the input

#define c rsi

S2N_BN_SYMBOL(bignum_mod_n256_4):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// Load a set of registers [n3; 0; n1; n0] = 2^256 - n_256

        mov     n0, 0x0c46353d039cdaaf
        mov     n1, 0x4319055258e8617b
        mov     n3short, 0x00000000ffffffff

// Load the input and compute x + (2^256 - n_256)

        mov     d0, [x]
        add     d0, n0
        mov     d1, [x+8]
        adc     d1, n1
        mov     d2, [x+16]
        adc     d2, 0
        mov     d3, [x+24]
        adc     d3, n3

// Now CF is set iff 2^256 <= x + (2^256 - n_256), i.e. iff n_256 <= x.
// Create a mask for the condition x < n, and mask the three nontrivial digits
// ready to undo the previous addition with a compensating subtraction

        sbb     c, c
        not     c
        and     n0, c
        and     n1, c
        and     n3, c

// Now subtract mask * (2^256 - n_256) again and store

        sub     d0, n0
        mov     [z], d0
        sbb     d1, n1
        mov     [z+8], d1
        sbb     d2, 0
        mov     [z+16], d2
        sbb     d3, n3
        mov     [z + 24], d3

#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
