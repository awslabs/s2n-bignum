// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Reduce modulo field characteristic, z := x mod p_256
// Input x[k]; output z[4]
//
//    extern void bignum_mod_p256(uint64_t z[static 4], uint64_t k,
//                                const uint64_t *x);
//
// Standard x86-64 ABI: RDI = z, RSI = k, RDX = x
// Microsoft x64 ABI:   RCX = z, RDX = k, R8 = x
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_mod_p256)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_mod_p256)
        .text

#define z rdi
#define k rsi
#define x rcx

#define m0 r8
#define m1 r9
#define m2 r10
#define m3 r11
#define d r12

#define n0 rax
#define n1 rbx
#define n3 rdx
#define q rdx

#define n0short eax
#define n1short ebx


S2N_BN_SYMBOL(bignum_mod_p256):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Save extra registers

        push    rbx
        push    r12

// If the input is already <= 3 words long, go to a trivial "copy" path

        cmp     k, 4
        jc      bignum_mod_p256_shortinput

// Otherwise load the top 4 digits (top-down) and reduce k by 4

        sub     k, 4
        mov     m3, [rdx+8*k+24]
        mov     m2, [rdx+8*k+16]
        mov     m1, [rdx+8*k+8]
        mov     m0, [rdx+8*k]

// Move x into another register to leave rdx free for multiplies and use of n3

        mov     x, rdx

// Load non-trivial digits [n3; 0; n1; -1] = p_256 and do a conditional
// subtraction to reduce the four starting digits [m3;m2;m1;m0] modulo p_256

        sub     m0, -1
        mov     n1short, 0x00000000ffffffff
        sbb     m1, n1
        mov     n3, 0xffffffff00000001
        sbb     m2, 0
        sbb     m3, n3

        sbb     n0, n0

        and     n1, n0
        and     n3, n0
        add     m0, n0
        adc     m1, n1
        adc     m2, 0
        adc     m3, n3

// Now do (k-4) iterations of 5->4 word modular reduction

        test    k, k
        jz      bignum_mod_p256_writeback

bignum_mod_p256_loop:

// Writing the input as z = 2^256 * m3 + 2^192 * m2 + t = 2^192 * h + t, our
// intended quotient approximation is MIN ((h + h>>32 + 1)>>64) (2^64 - 1).

        mov     n0, m3
        shld    n0, m2, 32
        mov     q, m3
        shr     q, 32

        xor     n1, n1
        sub     n1, 1

        adc     n0, m2
        adc     q, m3
        sbb     n0, n0
        or      q, n0

// Load the next digit so current m to reduce = [m3;m2;m1;m0;d]

        mov     d, [x+8*k-8]

// Now compute the initial pre-reduced [m3;m2;m1;m0;d] = m - p_256 * q
// = z - (2^256 - 2^224 + 2^192 + 2^96 - 1) * q
// = z - 2^192 * 0xffffffff00000001 * q - 2^64 * 0x0000000100000000 * q + q

        add     d, q
        mov     n0, 0x0000000100000000
        mulx    n1, n0, n0
        sbb     n0, 0
        sbb     n1, 0
        sub     m0, n0
        sbb     m1, n1
        mov     n0, 0xffffffff00000001
        mulx    n1, n0, n0
        sbb     m2, n0
        sbb     m3, n1

// Now our top word m3 is either zero or all 1s, and we use this to discriminate
// whether a correction is needed because our result is negative, as a bitmask
// Do a masked addition of p_256

        mov     n0short, 0x00000000ffffffff
        and     n0, m3
        xor     n1, n1
        sub     n1, n0
        add     d, m3
        adc     m0, n0
        adc     m1, 0
        adc     m2, n1

// Shuffle registers up and loop

        mov     m3, m2
        mov     m2, m1
        mov     m1, m0
        mov     m0, d

        dec     k
        jnz     bignum_mod_p256_loop

// Write back

bignum_mod_p256_writeback:

        mov     [z], m0
        mov     [z+8], m1
        mov     [z+16], m2
        mov     [z+24], m3

// Restore registers and return

        pop     r12
        pop     rbx
#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

bignum_mod_p256_shortinput:

        xor     m0, m0
        xor     m1, m1
        xor     m2, m2
        xor     m3, m3

        test    k, k
        jz      bignum_mod_p256_writeback
        mov     m0, [rdx]
        dec     k
        jz      bignum_mod_p256_writeback
        mov     m1, [rdx + 8]
        dec     k
        jz      bignum_mod_p256_writeback
        mov     m2, [rdx + 16]
        jmp     bignum_mod_p256_writeback

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
