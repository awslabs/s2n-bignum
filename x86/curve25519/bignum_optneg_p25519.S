// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Optionally negate modulo p_25519, z := (-x) mod p_25519 (if p nonzero) or
// z := x (if p zero), assuming x reduced
// Inputs p, x[4]; output z[4]
//
//    extern void bignum_optneg_p25519(uint64_t z[static 4], uint64_t p,
//                                     const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = p, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = p, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_optneg_p25519)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_optneg_p25519)
        .text

#define z rdi
#define q rsi
#define x rdx

#define n0 rax
#define n1 rcx
#define n2 r8
#define n3 r9

S2N_BN_SYMBOL(bignum_optneg_p25519):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Adjust q by zeroing it if the input is zero (to avoid giving -0 = p_25519,
// which is not strictly reduced even though it's correct modulo p_25519).

        mov     n0, [x]
        or      n0, [x+8]
        mov     n1, [x+16]
        or      n1, [x+24]
        or      n0, n1
        neg     n0
        sbb     n0, n0
        and     q, n0

// Turn q into a bitmask, all 1s for q=false, all 0s for q=true

        neg     q
        sbb     q, q
        not     q

// Let [n3;n2;n1;n0] = if q then p_25519 else -1

        mov     n0, 0xffffffffffffffed
        or      n0, q
        mov     n1, 0xffffffffffffffff
        mov     n2, n1
        mov     n3, 0x7fffffffffffffff
        or      n3, q

// Subtract so [n3;n2;n1;n0] = if q then p_25519 - x else -1 - x

        sub     n0, [x]
        sbb     n1, [x+8]
        sbb     n2, [x+16]
        sbb     n3, [x+24]

// XOR the words with the bitmask, which in the case q = false has the
// effect of restoring ~(-1 - x) = -(-1 - x) - 1 = 1 + x - 1 = x
// and write back the digits to the output

        xor     n0, q
        mov     [z], n0
        xor     n1, q
        mov     [z+8], n1
        xor     n2, q
        mov     [z+16], n2
        xor     n3, q
        mov     [z+24], n3

#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
