// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Count trailing zero bits
// Input x[k]; output function return
//
//    extern uint64_t bignum_ctz(uint64_t k, const uint64_t *x);
//
//
// In the case of a zero bignum as input the result is 64 * k
//
// In principle this has a precondition k < 2^58, but obviously that
// is always true in practice because of address space limitations
//
// Standard x86-64 ABI: RDI = k, RSI = x, returns RAX
// Microsoft x64 ABI:   RCX = k, RDX = x, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_ctz)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_ctz)
        .text

#define k rdi
#define x rsi
#define i rdx
#define w rcx
#define a rax

#define wshort ecx



S2N_BN_SYMBOL(bignum_ctz):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
#endif

// If the bignum is zero-length, just return 0

        xor     rax, rax
        test    k, k
        jz      bignum_ctz_end

// Use w = a[i-1] to store nonzero words in a top-down sweep
// Set the initial default to be as if we had a 1 word directly above

        mov     i, k
        inc     i
        mov     wshort, 1

bignum_ctz_loop:
        mov     a, [x+8*k-8]
        test    a, a
        cmovne  i, k
        cmovne  w, a
        dec     k
        jnz     bignum_ctz_loop

// Now w = a[i-1] is the lowest nonzero word, or in the zero case the
// default of the "extra" 1 = a[k]. We now want 64*(i-1) + ctz(w).
// Note that this code does not rely on the behavior of the BSF instruction
// for zero inputs, which is undefined according to the manual.

        dec     i
        shl     i, 6
        bsf     rax, w
        add     rax, i

bignum_ctz_end:
#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
