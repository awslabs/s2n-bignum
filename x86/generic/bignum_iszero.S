// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Test bignum for zero-ness, x = 0
// Input x[k]; output function return
//
//    extern uint64_t bignum_iszero (uint64_t k, uint64_t *x);
//
// Standard x86-64 ABI: RDI = k, RSI = x, returns RAX
// Microsoft x64 ABI:   RCX = k, RDX = x, returns RAX
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_iszero)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_iszero)
        .text

#define a rax
#define k rdi
#define x rsi

S2N_BN_SYMBOL(bignum_iszero):
        CFI_START
        _CET_ENDBR

#if WINDOWS_ABI
        CFI_PUSH(rdi)
        CFI_PUSH(rsi)
        mov     rdi, rcx
        mov     rsi, rdx
#endif
        xor     a, a
        test    k,k
        jz      bignum_iszero_end

bignum_iszero_loop:
        or      a, [x+8*k-8]
        dec     k
        jnz     bignum_iszero_loop

// Set a standard C condition based on whether a is nonzero

        neg     a
        sbb     a, a

bignum_iszero_end:
        inc     a
#if WINDOWS_ABI
        CFI_POP(rsi)
        CFI_POP(rdi)
#endif
        CFI_RET

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
