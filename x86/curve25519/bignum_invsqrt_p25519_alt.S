// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Inverse square root modulo p_25519 = 2^255 - 19
// Input x[4]; output function return (Legendre symbol) and z[4]
//
// extern int64_t bignum_invsqrt_p25519_alt(uint64_t z[static 4],
//                                          const uint64_t x[static 4]);
//
// Given a 4-digit input x, returns a modular inverse square root mod p_25519,
// i.e. a z such that x * z^2 == 1 (mod p_25519), whenever one exists. The
// inverse square root z is chosen so that its LSB is even (note that p_25519-z
// is another possibility). The function return is the Legendre/Jacobi symbol
// (x//p_25519), which indicates whether indeed x has a modular inverse square
// root and hence whether the result is meaningful:
//
//   0: x is divisible by p_25519 so trivially there is no inverse square root
//  +1: x is coprime to p_25519 and z is indeed an inverse square root
//  -1: x is coprime to p_25519 but there is no (inverse or direct) square root
//
// Standard x86-64 ABI: RDI = z, RSI = x
// Microsoft x64 ABI:   RCX = z, RDX = x
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_invsqrt_p25519_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_invsqrt_p25519_alt)
        .text

// Size in bytes of a 64-bit word

#define N 8

// Pointer-offset pairs for temporaries on stack

#define a rsp+0
#define b rsp+(4*N)
#define s rsp+(8*N)
#define t rsp+(12*N)
#define u rsp+(16*N)
#define res QWORD PTR [rsp+(20*N)]

// Total size to reserve on the stack

#define NSPACE (22*N)

// Corrupted versions when stack is down 8 more

#define u8 rsp+(17*N)

// Syntactic variants to make x86_att version simpler to generate

#define A 0
#define B (4*N)
#define S (8*N)
#define T (12*N)
#define U (16*N)
#define U8 (17*N)

S2N_BN_SYMBOL(bignum_invsqrt_p25519_alt):
        _CET_ENDBR

// In this case the Windows form literally makes a subroutine call.
// This avoids hassle arising from subroutine offsets

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        call    bignum_invsqrt_p25519_alt_standard
        pop     rsi
        pop     rdi
        ret

bignum_invsqrt_p25519_alt_standard:
#endif

// Save registers and make room for temporaries

        push    rbx
        push    rbp
        push    r12
        push    r13
        push    r14
        push    r15

        sub     rsp, NSPACE

// Save the return pointer for the end so we can overwrite rdi later

        mov     res, rdi

// Set up reduced version of the input argument a = x mod p_25519. Then
// get the candidate inverse square root s = a^{252-3}

        mov     rdx, [rsi]
        mov     rcx, [rsi+0x8]
        mov     r8, [rsi+0x10]
        mov     r9, [rsi+0x18]
        mov     eax, 0x1
        xor     r10d, r10d
        bts     r9, 0x3f
        adc     rax, r10
        imul    rax, rax, 0x13
        add     rdx, rax
        adc     rcx, r10
        adc     r8, r10
        adc     r9, r10
        mov     eax, 0x13
        cmovb   rax, r10
        sub     rdx, rax
        sbb     rcx, r10
        sbb     r8, r10
        sbb     r9, r10
        btr     r9, 0x3f
        mov     [rsp+A], rdx
        mov     [rsp+A+0x8], rcx
        mov     [rsp+A+0x10], r8
        mov     [rsp+A+0x18], r9

  // Power 2^2 - 1 = 3

        lea     rdi, [rsp+T]
        mov     rsi, 1
        lea     rdx, [rsp+A]
        call    bignum_invsqrt_p25519_alt_nsqr_p25519

        lea     rdi, [rsp+T]
        lea     rsi, [rsp+T]
        lea     rdx, [rsp+A]
        call    bignum_invsqrt_p25519_alt_mul_p25519

  // Power 2^4 - 1 = 15

        lea     rdi, [rsp+S]
        mov     rsi, 2
        lea     rdx, [rsp+T]
        call    bignum_invsqrt_p25519_alt_nsqr_p25519

        lea     rdi, [rsp+T]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+T]
        call    bignum_invsqrt_p25519_alt_mul_p25519

  // Power 2^5 - 1 = 31

        lea     rdi, [rsp+S]
        mov     rsi, 1
        lea     rdx, [rsp+T]
        call    bignum_invsqrt_p25519_alt_nsqr_p25519

        lea     rdi, [rsp+B]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+A]
        call    bignum_invsqrt_p25519_alt_mul_p25519

  // Power 2^10 - 1

        lea     rdi, [rsp+S]
        mov     rsi, 5
        lea     rdx, [rsp+B]
        call    bignum_invsqrt_p25519_alt_nsqr_p25519

        lea     rdi, [rsp+T]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+B]
        call    bignum_invsqrt_p25519_alt_mul_p25519

  // Power 2^20 - 1

        lea     rdi, [rsp+S]
        mov     rsi, 10
        lea     rdx, [rsp+T]
        call    bignum_invsqrt_p25519_alt_nsqr_p25519

        lea     rdi, [rsp+T]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+T]
        call    bignum_invsqrt_p25519_alt_mul_p25519

  // Power 2^25 - 1

        lea     rdi, [rsp+S]
        mov     rsi, 5
        lea     rdx, [rsp+T]
        call    bignum_invsqrt_p25519_alt_nsqr_p25519

        lea     rdi, [rsp+B]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+B]
        call    bignum_invsqrt_p25519_alt_mul_p25519

  // Power 2^50 - 1

        lea     rdi, [rsp+S]
        mov     rsi, 25
        lea     rdx, [rsp+B]
        call    bignum_invsqrt_p25519_alt_nsqr_p25519

        lea     rdi, [rsp+T]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+B]
        call    bignum_invsqrt_p25519_alt_mul_p25519

  // Power 2^100 - 1

        lea     rdi, [rsp+S]
        mov     rsi, 50
        lea     rdx, [rsp+T]
        call    bignum_invsqrt_p25519_alt_nsqr_p25519

        lea     rdi, [rsp+T]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+T]
        call    bignum_invsqrt_p25519_alt_mul_p25519

  // Power 2^125 - 1

        lea     rdi, [rsp+S]
        mov     rsi, 25
        lea     rdx, [rsp+T]
        call    bignum_invsqrt_p25519_alt_nsqr_p25519

        lea     rdi, [rsp+B]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+B]
        call    bignum_invsqrt_p25519_alt_mul_p25519

  // Power 2^250 - 1

        lea     rdi, [rsp+S]
        mov     rsi, 125
        lea     rdx, [rsp+B]
        call    bignum_invsqrt_p25519_alt_nsqr_p25519

        lea     rdi, [rsp+B]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+B]
        call    bignum_invsqrt_p25519_alt_mul_p25519

  // Power 2^252 - 3

        lea     rdi, [rsp+S]
        mov     rsi, 2
        lea     rdx, [rsp+B]
        call    bignum_invsqrt_p25519_alt_nsqr_p25519

        lea     rdi, [rsp+S]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+A]
        call    bignum_invsqrt_p25519_alt_mul_p25519

// s = a^{2^252-3} is now one candidate inverse square root.
// Generate the other one t = s * j_25519 where j_25519 = sqrt(-1)

        mov     rax, 0xc4ee1b274a0ea0b0
        mov     [rsp+T], rax
        mov     rax, 0x2f431806ad2fe478
        mov     [rsp+T+8], rax
        mov     rax, 0x2b4d00993dfbd7a7
        mov     [rsp+T+16], rax
        mov     rax, 0x2b8324804fc1df0b
        mov     [rsp+T+24], rax

        lea     rdi, [rsp+T]
        lea     rsi, [rsp+S]
        lea     rdx, [rsp+T]
        call    bignum_invsqrt_p25519_alt_mul_p25519

// Now multiplex between them according to whether a * s^2 = 1

        lea     rdi, [rsp+B]
        mov     rsi, 1
        lea     rdx, [rsp+S]
        call    bignum_invsqrt_p25519_alt_nsqr_p25519

        lea     rdi, [rsp+B]
        lea     rsi, [rsp+A]
        lea     rdx, [rsp+B]
        call    bignum_invsqrt_p25519_alt_mul_p25519

        mov     rax, [rsp+B]
        xor     rax, 1
        mov     rbx, [rsp+B+8]
        or      rax, rbx
        mov     rcx, [rsp+B+16]
        mov     rdx, [rsp+B+24]
        or      rcx, rdx
        or      rax, rcx

        mov     rax, [rsp+S]
        mov     rbx, [rsp+T]
        cmovnz  rax, rbx
        mov     rbx, [rsp+S+8]
        mov     rcx, [rsp+T+8]
        cmovnz  rbx, rcx
        mov     rcx, [rsp+S+16]
        mov     rdx, [rsp+T+16]
        cmovnz  rcx, rdx
        mov     rbp, [rsp+S+24]
        mov     rdx, [rsp+T+24]
        cmovnz  rbp, rdx

// For definiteness, choose "positive" (LSB=0) inverse square root

        xor     edx, edx
        lea     r8, [rdx-19]
        lea     r11, [rdx-1]
        mov     r9, r11
        mov     r10, r11
        btr     r11, 63

        sub     r8, rax
        sbb     r9, rbx
        sbb     r10, rcx
        sbb     r11, rbp

        mov     rdx, res
        test    rax, 1
        cmovnz  rax, r8
        mov     [rdx], rax
        cmovnz  rbx, r9
        mov     [rdx+8], rbx
        cmovnz  rcx, r10
        mov     [rdx+16], rcx
        cmovnz  rbp, r11
        mov     [rdx+24], rbp

// Determine if it is is indeed an inverse square root, also distinguishing
// the degenerate x * z^2 == 0 (mod p_25519) case, which is equivalent to
// x == 0 (mod p_25519). Hence return the Legendre-Jacobi symbol as required.

        lea     rdi, [rsp+B]
        mov     rsi, 1
        call    bignum_invsqrt_p25519_alt_nsqr_p25519

        lea     rdi, [rsp+B]
        lea     rsi, [rsp+A]
        lea     rdx, [rsp+B]
        call    bignum_invsqrt_p25519_alt_mul_p25519

        mov     rax, 1
        mov     rbp, [rsp+B]
        xor     rax, rbp
        mov     rbx, [rsp+B+8]
        or      rax, rbx
        or      rbp, rbx
        mov     rcx, [rsp+B+16]
        mov     rdx, [rsp+B+24]
        or      rcx, rdx
        or      rax, rcx
        or      rbp, rcx

        neg     rax
        sbb     rax, rax
        lea     rax, [rax+rax+1]

        test    rbp, rbp
        cmovz   rax, rbp

// Restore stack and registers

        add     rsp, NSPACE

        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbp
        pop     rbx
        ret

// *************************************************************
// Local z = x * y
// *************************************************************

bignum_invsqrt_p25519_alt_mul_p25519:
        mov     rcx, rdx
        mov     rax, [rsi]
        mul     QWORD PTR [rcx]
        mov     r8, rax
        mov     r9, rdx
        xor     r10, r10
        xor     r11, r11
        mov     rax, [rsi]
        mul     QWORD PTR [rcx+0x8]
        add     r9, rax
        adc     r10, rdx
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rcx]
        add     r9, rax
        adc     r10, rdx
        adc     r11, 0x0
        xor     r12, r12
        mov     rax, [rsi]
        mul     QWORD PTR [rcx+0x10]
        add     r10, rax
        adc     r11, rdx
        adc     r12, r12
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rcx+0x8]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rcx]
        add     r10, rax
        adc     r11, rdx
        adc     r12, 0x0
        xor     r13, r13
        mov     rax, [rsi]
        mul     QWORD PTR [rcx+0x18]
        add     r11, rax
        adc     r12, rdx
        adc     r13, r13
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rcx+0x10]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rcx+0x8]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rcx]
        add     r11, rax
        adc     r12, rdx
        adc     r13, 0x0
        xor     r14, r14
        mov     rax, [rsi+0x8]
        mul     QWORD PTR [rcx+0x18]
        add     r12, rax
        adc     r13, rdx
        adc     r14, r14
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rcx+0x10]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rcx+0x8]
        add     r12, rax
        adc     r13, rdx
        adc     r14, 0x0
        xor     r15, r15
        mov     rax, [rsi+0x10]
        mul     QWORD PTR [rcx+0x18]
        add     r13, rax
        adc     r14, rdx
        adc     r15, r15
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rcx+0x10]
        add     r13, rax
        adc     r14, rdx
        adc     r15, 0x0
        mov     rax, [rsi+0x18]
        mul     QWORD PTR [rcx+0x18]
        add     r14, rax
        adc     r15, rdx
        mov     esi, 0x26
        mov     rax, r12
        mul     rsi
        add     r8, rax
        adc     r9, rdx
        sbb     rcx, rcx
        mov     rax, r13
        mul     rsi
        sub     rdx, rcx
        add     r9, rax
        adc     r10, rdx
        sbb     rcx, rcx
        mov     rax, r14
        mul     rsi
        sub     rdx, rcx
        add     r10, rax
        adc     r11, rdx
        sbb     rcx, rcx
        mov     rax, r15
        mul     rsi
        sub     rdx, rcx
        xor     rcx, rcx
        add     r11, rax
        mov     r12, rdx
        adc     r12, rcx
        shld    r12, r11, 0x1
        lea     rax, [r12+0x1]
        mov     esi, 0x13
        bts     r11, 0x3f
        imul    rax, rsi
        add     r8, rax
        adc     r9, rcx
        adc     r10, rcx
        adc     r11, rcx
        sbb     rax, rax
        not     rax
        and     rax, rsi
        sub     r8, rax
        sbb     r9, rcx
        sbb     r10, rcx
        sbb     r11, rcx
        btr     r11, 0x3f
        mov     [rdi], r8
        mov     [rdi+0x8], r9
        mov     [rdi+0x10], r10
        mov     [rdi+0x18], r11
        ret

// *************************************************************
// Local z = 2^n * x
// *************************************************************

bignum_invsqrt_p25519_alt_nsqr_p25519:

// Copy input argument into u

        mov     rax, [rdx]
        mov     rbx, [rdx+8]
        mov     rcx, [rdx+16]
        mov     rdx, [rdx+24]
        mov     [rsp+U8], rax
        mov     [rsp+U8+8], rbx
        mov     [rsp+U8+16], rcx
        mov     [rsp+U8+24], rdx

// Main squaring loop, accumulating in u consistently  and
// only ensuring the intermediates are < 2 * p_25519 = 2^256 - 38

bignum_invsqrt_p25519_alt_loop:
        mov     rax, [rsp+U8]
        mul     rax
        mov     r8,rax
        mov     r9,rdx
        xor     r10,r10
        xor     r11,r11
        mov     rax, [rsp+U8]
        mul     QWORD PTR [rsp+U8+0x8]
        add     rax,rax
        adc     rdx,rdx
        adc     r11,0x0
        add     r9,rax
        adc     r10,rdx
        adc     r11,0x0
        xor     r12,r12
        mov     rax, [rsp+U8+0x8]
        mul     rax
        add     r10,rax
        adc     r11,rdx
        adc     r12,0x0
        mov     rax, [rsp+U8]
        mul     QWORD PTR [rsp+U8+0x10]
        add     rax,rax
        adc     rdx,rdx
        adc     r12,0x0
        add     r10,rax
        adc     r11,rdx
        adc     r12,0x0
        xor     r13,r13
        mov     rax, [rsp+U8]
        mul     QWORD PTR [rsp+U8+0x18]
        add     rax,rax
        adc     rdx,rdx
        adc     r13,0x0
        add     r11,rax
        adc     r12,rdx
        adc     r13,0x0
        mov     rax, [rsp+U8+0x8]
        mul     QWORD PTR [rsp+U8+0x10]
        add     rax,rax
        adc     rdx,rdx
        adc     r13,0x0
        add     r11,rax
        adc     r12,rdx
        adc     r13,0x0
        xor     r14,r14
        mov     rax, [rsp+U8+0x8]
        mul     QWORD PTR [rsp+U8+0x18]
        add     rax,rax
        adc     rdx,rdx
        adc     r14,0x0
        add     r12,rax
        adc     r13,rdx
        adc     r14,0x0
        mov     rax, [rsp+U8+0x10]
        mul     rax
        add     r12,rax
        adc     r13,rdx
        adc     r14,0x0
        xor     r15,r15
        mov     rax, [rsp+U8+0x10]
        mul     QWORD PTR [rsp+U8+0x18]
        add     rax,rax
        adc     rdx,rdx
        adc     r15,0x0
        add     r13,rax
        adc     r14,rdx
        adc     r15,0x0
        mov     rax, [rsp+U8+0x18]
        mul     rax
        add     r14,rax
        adc     r15,rdx
        mov     ebx,0x26
        mov     rax,r12
        mul     rbx
        add     r8,rax
        adc     r9,rdx
        sbb     rcx,rcx
        mov     rax,r13
        mul     rbx
        sub     rdx,rcx
        add     r9,rax
        adc     r10,rdx
        sbb     rcx,rcx
        mov     rax,r14
        mul     rbx
        sub     rdx,rcx
        add     r10,rax
        adc     r11,rdx
        sbb     rcx,rcx
        mov     rax,r15
        mul     rbx
        sub     rdx,rcx
        xor     rcx,rcx
        add     r11,rax
        mov     r12,rdx
        adc     r12,rcx
        shld    r12, r11, 0x1
        btr     r11, 0x3f
        mov     edx, 0x13
        imul    rdx, r12
        add     r8, rdx
        adc     r9, rcx
        adc     r10, rcx
        adc     r11, rcx
        mov     [rsp+U8], r8
        mov     [rsp+U8+0x8], r9
        mov     [rsp+U8+0x10], r10
        mov     [rsp+U8+0x18], r11

// Loop as applicable

        dec     rsi
        jnz     bignum_invsqrt_p25519_alt_loop

// We know the intermediate result x < 2^256 - 38, and now we do strict
// modular reduction mod 2^255 - 19. Note x < 2^255 - 19 <=> x + 19 < 2^255
// which is equivalent to a "ns" condition. We just use the results where
// they were in registers [r11;r10;r9;r8] instead of re-loading them.

        mov     eax, 19
        xor     ebx, ebx
        xor     ecx, ecx
        xor     edx, edx
        add     rax, r8
        adc     rbx, r9
        adc     rcx, r10
        adc     rdx, r11

        cmovns  rax, r8
        cmovns  rbx, r9
        cmovns  rcx, r10
        cmovns  rdx, r11
        btr     rdx, 63
        mov     [rdi], rax
        mov     [rdi+8], rbx
        mov     [rdi+16], rcx
        mov     [rdi+24], rdx
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
