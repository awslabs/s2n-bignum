// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert to Montgomery form z := (2^256 * x) mod p_256k1
// Input x[4]; output z[4]
//
//    extern void bignum_tomont_p256k1_alt(uint64_t z[static 4],
//                                         const uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_tomont_p256k1_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_tomont_p256k1_alt)
        .text

#define z %rdi
#define x %rsi

#define c %rcx
#define d %rdx
#define h %rdx

#define a %rax
#define ashort %eax
#define q %rax

#define d0 %r8
#define d1 %r9
#define d2 %r10
#define d3 %rsi

S2N_BN_SYMBOL(bignum_tomont_p256k1_alt):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif

// Since 2^256 == 4294968273 (mod p_256k1) we more or less just set
// m = 4294968273 then devolve to a variant of bignum_cmul_p256k1;
// the logic that q = h + 1 < 2^64 and hence doesn't wrap still holds
// since the multiplier 4294968273 is known to be much less than 2^64.
// We keep this constant in %rcx throughout as it's used repeatedly.

        movq    $4294968273, c

// Multiply, accumulating the result as 2^256 * h + [d3;d2;d1;d0]

        movq    (x), a
        mulq    c
        movq    a, d0
        movq    d, d1

        movq    8(x), a
        xorq    d2, d2
        mulq    c
        addq    a, d1
        adcq    d, d2

        movq    16(x), a
        mulq    c
        addq    a, d2
        adcq    $0, d

        movq    24(x), a
        movq    d, d3
        mulq    c
        addq    a, d3
        adcq    $0, h

// Now the quotient estimate is q = h + 1, and then we do the reduction,
// writing z = [d3;d2;d1;d0], as z' = (2^256 * h + z) - q * p_256k1 =
// (2^256 * h + z) - q * (2^256 - 4294968273) = -2^256 + (z + 4294968273 * q)

        leaq    1(h), q
        mulq    c

        addq    %rax, d0
        adcq    %rdx, d1
        adcq    $0, d2
        adcq    $0, d3

// Because of the implicit -2^256, CF means >= 0 so z' is the answer; ~CF
// means z' < 0 so we add p_256k1, which in 4 digits means subtracting c.

        movq    $0, a
        cmovcq  a, c

        subq    c, d0
        movq    d0, (z)
        sbbq    a, d1
        movq    d1, 8(z)
        sbbq    a, d2
        movq    d2, 16(z)
        sbbq    a, d3
        movq    d3, 24(z)

#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
