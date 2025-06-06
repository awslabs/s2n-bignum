// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point doubling on NIST curve P-256 in Montgomery-Jacobian coordinates
//
//    extern void p256_montjdouble_alt(uint64_t p3[static 12],
//                                     const uint64_t p1[static 12]);
//
// Does p3 := 2 * p1 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_256.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
//
// Standard x86-64 ABI: RDI = p3, RSI = p1
// Microsoft x64 ABI:   RCX = p3, RDX = p1
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"


        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p256_montjdouble_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p256_montjdouble_alt)
        .text
        .balign 4

// Size of individual field elements

#define NUMSIZE 32

// Pointer-offset pairs for inputs and outputs
// These assume %rdi = p3, %rsi = p1, which is true when the
// arguments come in initially and is not disturbed throughout.

#define x_1 0(%rsi)
#define y_1 NUMSIZE(%rsi)
#define z_1 (2*NUMSIZE)(%rsi)

#define x_3 0(%rdi)
#define y_3 NUMSIZE(%rdi)
#define z_3 (2*NUMSIZE)(%rdi)

// Pointer-offset pairs for temporaries, with some aliasing
// NSPACE is the total stack needed for these temporaries

#define z2 (NUMSIZE*0)(%rsp)
#define y4 (NUMSIZE*0)(%rsp)

#define y2 (NUMSIZE*1)(%rsp)

#define t1 (NUMSIZE*2)(%rsp)

#define t2 (NUMSIZE*3)(%rsp)
#define x2p (NUMSIZE*3)(%rsp)
#define dx2 (NUMSIZE*3)(%rsp)

#define xy2 (NUMSIZE*4)(%rsp)

#define x4p (NUMSIZE*5)(%rsp)
#define d (NUMSIZE*5)(%rsp)

#define NSPACE (NUMSIZE*6)

// Corresponds exactly to bignum_montmul_p256_alt

#define montmul_p256(P0,P1,P2)                  \
        movq    P2, %rbx ;                      \
        movq    P1, %rax ;                      \
        mulq    %rbx;                            \
        movq    %rax, %r8 ;                        \
        movq    %rdx, %r9 ;                        \
        movq    0x8+P1, %rax ;                  \
        mulq    %rbx;                            \
        xorl    %r10d, %r10d ;                     \
        addq    %rax, %r9 ;                        \
        adcq    %rdx, %r10 ;                       \
        movq    0x10+P1, %rax ;                 \
        mulq    %rbx;                            \
        xorl    %r11d, %r11d ;                     \
        addq    %rax, %r10 ;                       \
        adcq    %rdx, %r11 ;                       \
        movq    0x18+P1, %rax ;                 \
        mulq    %rbx;                            \
        xorl    %r12d, %r12d ;                     \
        addq    %rax, %r11 ;                       \
        adcq    %rdx, %r12 ;                       \
        movq    0x8+P2, %rbx ;                  \
        xorl    %r13d, %r13d ;                     \
        movq    P1, %rax ;                      \
        mulq    %rbx;                            \
        addq    %rax, %r9 ;                        \
        adcq    %rdx, %r10 ;                       \
        sbbq    %r14, %r14 ;                       \
        movq    0x8+P1, %rax ;                  \
        mulq    %rbx;                            \
        subq    %r14, %rdx ;                       \
        addq    %rax, %r10 ;                       \
        adcq    %rdx, %r11 ;                       \
        sbbq    %r14, %r14 ;                       \
        movq    0x10+P1, %rax ;                 \
        mulq    %rbx;                            \
        subq    %r14, %rdx ;                       \
        addq    %rax, %r11 ;                       \
        adcq    %rdx, %r12 ;                       \
        sbbq    %r14, %r14 ;                       \
        movq    0x18+P1, %rax ;                 \
        mulq    %rbx;                            \
        subq    %r14, %rdx ;                       \
        addq    %rax, %r12 ;                       \
        adcq    %rdx, %r13 ;                       \
        xorl    %r14d, %r14d ;                     \
        movq    $0x100000000, %rbx ;               \
        movq    %r8, %rax ;                        \
        mulq    %rbx;                            \
        addq    %rax, %r9 ;                        \
        adcq    %rdx, %r10 ;                       \
        sbbq    %r15, %r15 ;                       \
        movq    %r9, %rax ;                        \
        mulq    %rbx;                            \
        subq    %r15, %rdx ;                       \
        addq    %rax, %r10 ;                       \
        adcq    %rdx, %r11 ;                       \
        sbbq    %r15, %r15 ;                       \
        notq    %rbx;                            \
        leaq    0x2(%rbx), %rbx ;                 \
        movq    %r8, %rax ;                        \
        mulq    %rbx;                            \
        subq    %r15, %rdx ;                       \
        addq    %rax, %r11 ;                       \
        adcq    %rdx, %r12 ;                       \
        sbbq    %r15, %r15 ;                       \
        movq    %r9, %rax ;                        \
        mulq    %rbx;                            \
        subq    %r15, %rdx ;                       \
        addq    %rax, %r12 ;                       \
        adcq    %rdx, %r13 ;                       \
        adcq    %r14, %r14 ;                       \
        movq    0x10+P2, %rbx ;                 \
        xorl    %r15d, %r15d ;                     \
        movq    P1, %rax ;                      \
        mulq    %rbx;                            \
        addq    %rax, %r10 ;                       \
        adcq    %rdx, %r11 ;                       \
        sbbq    %r8, %r8 ;                         \
        movq    0x8+P1, %rax ;                  \
        mulq    %rbx;                            \
        subq    %r8, %rdx ;                        \
        addq    %rax, %r11 ;                       \
        adcq    %rdx, %r12 ;                       \
        sbbq    %r8, %r8 ;                         \
        movq    0x10+P1, %rax ;                 \
        mulq    %rbx;                            \
        subq    %r8, %rdx ;                        \
        addq    %rax, %r12 ;                       \
        adcq    %rdx, %r13 ;                       \
        sbbq    %r8, %r8 ;                         \
        movq    0x18+P1, %rax ;                 \
        mulq    %rbx;                            \
        subq    %r8, %rdx ;                        \
        addq    %rax, %r13 ;                       \
        adcq    %rdx, %r14 ;                       \
        adcq    %r15, %r15 ;                       \
        movq    0x18+P2, %rbx ;                 \
        xorl    %r8d, %r8d ;                       \
        movq    P1, %rax ;                      \
        mulq    %rbx;                            \
        addq    %rax, %r11 ;                       \
        adcq    %rdx, %r12 ;                       \
        sbbq    %r9, %r9 ;                         \
        movq    0x8+P1, %rax ;                  \
        mulq    %rbx;                            \
        subq    %r9, %rdx ;                        \
        addq    %rax, %r12 ;                       \
        adcq    %rdx, %r13 ;                       \
        sbbq    %r9, %r9 ;                         \
        movq    0x10+P1, %rax ;                 \
        mulq    %rbx;                            \
        subq    %r9, %rdx ;                        \
        addq    %rax, %r13 ;                       \
        adcq    %rdx, %r14 ;                       \
        sbbq    %r9, %r9 ;                         \
        movq    0x18+P1, %rax ;                 \
        mulq    %rbx;                            \
        subq    %r9, %rdx ;                        \
        addq    %rax, %r14 ;                       \
        adcq    %rdx, %r15 ;                       \
        adcq    %r8, %r8 ;                         \
        xorl    %r9d, %r9d ;                       \
        movq    $0x100000000, %rbx ;               \
        movq    %r10, %rax ;                       \
        mulq    %rbx;                            \
        addq    %rax, %r11 ;                       \
        adcq    %rdx, %r12 ;                       \
        sbbq    %rcx, %rcx ;                       \
        movq    %r11, %rax ;                       \
        mulq    %rbx;                            \
        subq    %rcx, %rdx ;                       \
        addq    %rax, %r12 ;                       \
        adcq    %rdx, %r13 ;                       \
        sbbq    %rcx, %rcx ;                       \
        notq    %rbx;                            \
        leaq    0x2(%rbx), %rbx ;                 \
        movq    %r10, %rax ;                       \
        mulq    %rbx;                            \
        subq    %rcx, %rdx ;                       \
        addq    %rax, %r13 ;                       \
        adcq    %rdx, %r14 ;                       \
        sbbq    %rcx, %rcx ;                       \
        movq    %r11, %rax ;                       \
        mulq    %rbx;                            \
        subq    %rcx, %rdx ;                       \
        addq    %rax, %r14 ;                       \
        adcq    %rdx, %r15 ;                       \
        adcq    %r9, %r8 ;                         \
        movl    $0x1, %ecx ;                       \
        addq    %r12, %rcx ;                       \
        decq    %rbx;                            \
        adcq    %r13, %rbx ;                       \
        decq    %r9;                             \
        movq    %r9, %rax ;                        \
        adcq    %r14, %r9 ;                        \
        movl    $0xfffffffe, %r11d ;               \
        adcq    %r15, %r11 ;                       \
        adcq    %r8, %rax ;                        \
        cmovbq  %rcx, %r12 ;                       \
        cmovbq  %rbx, %r13 ;                       \
        cmovbq  %r9, %r14 ;                        \
        cmovbq  %r11, %r15 ;                       \
        movq    %r12, P0 ;                      \
        movq    %r13, 0x8+P0 ;                  \
        movq    %r14, 0x10+P0 ;                 \
        movq    %r15, 0x18+P0

// Corresponds exactly to bignum_montsqr_p256_alt

#define montsqr_p256(P0,P1)                     \
        movq    P1, %rax ;                      \
        movq    %rax, %rbx ;                       \
        mulq    %rax;                            \
        movq    %rax, %r8 ;                        \
        movq    %rdx, %r15 ;                       \
        movq    0x8+P1, %rax ;                  \
        mulq    %rbx;                            \
        movq    %rax, %r9 ;                        \
        movq    %rdx, %r10 ;                       \
        movq    0x18+P1, %rax ;                 \
        movq    %rax, %r13 ;                       \
        mulq    %rbx;                            \
        movq    %rax, %r11 ;                       \
        movq    %rdx, %r12 ;                       \
        movq    0x10+P1, %rax ;                 \
        movq    %rax, %rbx ;                       \
        mulq    %r13;                            \
        movq    %rax, %r13 ;                       \
        movq    %rdx, %r14 ;                       \
        movq    P1, %rax ;                      \
        mulq    %rbx;                            \
        addq    %rax, %r10 ;                       \
        adcq    %rdx, %r11 ;                       \
        sbbq    %rcx, %rcx ;                       \
        movq    0x8+P1, %rax ;                  \
        mulq    %rbx;                            \
        subq    %rcx, %rdx ;                       \
        addq    %rax, %r11 ;                       \
        adcq    %rdx, %r12 ;                       \
        sbbq    %rcx, %rcx ;                       \
        movq    0x18+P1, %rbx ;                 \
        movq    0x8+P1, %rax ;                  \
        mulq    %rbx;                            \
        subq    %rcx, %rdx ;                       \
        addq    %rax, %r12 ;                       \
        adcq    %rdx, %r13 ;                       \
        adcq    $0x0, %r14 ;                       \
        xorl    %ecx, %ecx ;                       \
        addq    %r9, %r9 ;                         \
        adcq    %r10, %r10 ;                       \
        adcq    %r11, %r11 ;                       \
        adcq    %r12, %r12 ;                       \
        adcq    %r13, %r13 ;                       \
        adcq    %r14, %r14 ;                       \
        adcq    %rcx, %rcx ;                       \
        movq    0x8+P1, %rax ;                  \
        mulq    %rax;                            \
        addq    %r15, %r9 ;                        \
        adcq    %rax, %r10 ;                       \
        adcq    %rdx, %r11 ;                       \
        sbbq    %r15, %r15 ;                       \
        movq    0x10+P1, %rax ;                 \
        mulq    %rax;                            \
        negq    %r15;                            \
        adcq    %rax, %r12 ;                       \
        adcq    %rdx, %r13 ;                       \
        sbbq    %r15, %r15 ;                       \
        movq    0x18+P1, %rax ;                 \
        mulq    %rax;                            \
        negq    %r15;                            \
        adcq    %rax, %r14 ;                       \
        adcq    %rcx, %rdx ;                       \
        movq    %rdx, %r15 ;                       \
        movq    $0x100000000, %rbx ;               \
        movq    %r8, %rax ;                        \
        mulq    %rbx;                            \
        addq    %rax, %r9 ;                        \
        adcq    %rdx, %r10 ;                       \
        sbbq    %rcx, %rcx ;                       \
        movq    %r9, %rax ;                        \
        mulq    %rbx;                            \
        subq    %rcx, %rdx ;                       \
        addq    %rax, %r10 ;                       \
        adcq    %rdx, %r11 ;                       \
        sbbq    %rcx, %rcx ;                       \
        notq    %rbx;                            \
        leaq    0x2(%rbx), %rbx ;                 \
        movq    %r8, %rax ;                        \
        mulq    %rbx;                            \
        subq    %rcx, %rdx ;                       \
        addq    %rax, %r11 ;                       \
        adcq    %rdx, %r12 ;                       \
        sbbq    %rcx, %rcx ;                       \
        xorl    %r8d, %r8d ;                       \
        movq    %r9, %rax ;                        \
        mulq    %rbx;                            \
        subq    %rcx, %rdx ;                       \
        addq    %rax, %r12 ;                       \
        adcq    %rdx, %r13 ;                       \
        adcq    %r8, %r14 ;                        \
        adcq    %r8, %r15 ;                        \
        adcq    %r8, %r8 ;                         \
        movq    $0x100000000, %rbx ;               \
        movq    %r10, %rax ;                       \
        mulq    %rbx;                            \
        addq    %rax, %r11 ;                       \
        adcq    %rdx, %r12 ;                       \
        sbbq    %rcx, %rcx ;                       \
        movq    %r11, %rax ;                       \
        mulq    %rbx;                            \
        subq    %rcx, %rdx ;                       \
        addq    %rax, %r12 ;                       \
        adcq    %rdx, %r13 ;                       \
        sbbq    %rcx, %rcx ;                       \
        notq    %rbx;                            \
        leaq    0x2(%rbx), %rbx ;                 \
        movq    %r10, %rax ;                       \
        mulq    %rbx;                            \
        subq    %rcx, %rdx ;                       \
        addq    %rax, %r13 ;                       \
        adcq    %rdx, %r14 ;                       \
        sbbq    %rcx, %rcx ;                       \
        xorl    %r9d, %r9d ;                       \
        movq    %r11, %rax ;                       \
        mulq    %rbx;                            \
        subq    %rcx, %rdx ;                       \
        addq    %rax, %r14 ;                       \
        adcq    %rdx, %r15 ;                       \
        adcq    %r9, %r8 ;                         \
        movl    $0x1, %ecx ;                       \
        addq    %r12, %rcx ;                       \
        leaq    -0x1(%rbx), %rbx ;                 \
        adcq    %r13, %rbx ;                       \
        leaq    -0x1(%r9), %r9 ;                   \
        movq    %r9, %rax ;                        \
        adcq    %r14, %r9 ;                        \
        movl    $0xfffffffe, %r11d ;               \
        adcq    %r15, %r11 ;                       \
        adcq    %r8, %rax ;                        \
        cmovbq  %rcx, %r12 ;                       \
        cmovbq  %rbx, %r13 ;                       \
        cmovbq  %r9, %r14 ;                        \
        cmovbq  %r11, %r15 ;                       \
        movq    %r12, P0 ;                      \
        movq    %r13, 0x8+P0 ;                  \
        movq    %r14, 0x10+P0 ;                 \
        movq    %r15, 0x18+P0

// Corresponds exactly to bignum_sub_p256

#define sub_p256(P0,P1,P2)                      \
        movq    P1, %rax ;                       \
        subq    P2, %rax ;                       \
        movq    0x8+P1, %rcx ;                   \
        sbbq    0x8+P2, %rcx ;                   \
        movq    0x10+P1, %r8 ;                   \
        sbbq    0x10+P2, %r8 ;                   \
        movq    0x18+P1, %r9 ;                   \
        sbbq    0x18+P2, %r9 ;                   \
        movl    $0xffffffff, %r10d ;                \
        sbbq    %r11, %r11 ;                        \
        xorq    %rdx, %rdx ;                        \
        andq    %r11, %r10 ;                        \
        subq    %r10, %rdx ;                        \
        addq    %r11, %rax ;                        \
        movq    %rax, P0 ;                       \
        adcq    %r10, %rcx ;                        \
        movq    %rcx, 0x8+P0 ;                   \
        adcq    $0x0, %r8 ;                         \
        movq    %r8, 0x10+P0 ;                   \
        adcq    %rdx, %r9 ;                         \
        movq    %r9, 0x18+P0

// Corresponds exactly to bignum_add_p256

#define add_p256(P0,P1,P2)                      \
        xorq    %r11, %r11 ;                        \
        movq    P1, %rax ;                       \
        addq    P2, %rax ;                       \
        movq    0x8+P1, %rcx ;                   \
        adcq    0x8+P2, %rcx ;                   \
        movq    0x10+P1, %r8 ;                   \
        adcq    0x10+P2, %r8 ;                   \
        movq    0x18+P1, %r9 ;                   \
        adcq    0x18+P2, %r9 ;                   \
        adcq    %r11, %r11 ;                        \
        subq    $0xffffffffffffffff, %rax ;         \
        movl    $0xffffffff, %r10d ;                \
        sbbq    %r10, %rcx ;                        \
        sbbq    $0x0, %r8 ;                         \
        movq    $0xffffffff00000001, %rdx ;         \
        sbbq    %rdx, %r9 ;                         \
        sbbq    $0x0, %r11 ;                        \
        andq    %r11, %r10 ;                        \
        andq    %r11, %rdx ;                        \
        addq    %r11, %rax ;                        \
        movq    %rax, P0 ;                       \
        adcq    %r10, %rcx ;                        \
        movq    %rcx, 0x8+P0 ;                   \
        adcq    $0x0, %r8 ;                         \
        movq    %r8, 0x10+P0 ;                   \
        adcq    %rdx, %r9 ;                         \
        movq    %r9, 0x18+P0

// A weak version of add that only guarantees sum in 4 digits

#define weakadd_p256(P0,P1,P2)                  \
        movq    P1, %rax ;                       \
        addq    P2, %rax ;                       \
        movq    0x8+P1, %rcx ;                   \
        adcq    0x8+P2, %rcx ;                   \
        movq    0x10+P1, %r8 ;                   \
        adcq    0x10+P2, %r8 ;                   \
        movq    0x18+P1, %r9 ;                   \
        adcq    0x18+P2, %r9 ;                   \
        movl    $0xffffffff, %r10d ;                \
        sbbq    %r11, %r11 ;                        \
        xorq    %rdx, %rdx ;                        \
        andq    %r11, %r10 ;                        \
        subq    %r10, %rdx ;                        \
        subq    %r11, %rax ;                        \
        movq    %rax, P0 ;                       \
        sbbq    %r10, %rcx ;                        \
        movq    %rcx, 0x8+P0 ;                   \
        sbbq    $0x0, %r8 ;                         \
        movq    %r8, 0x10+P0 ;                   \
        sbbq    %rdx, %r9 ;                         \
        movq    %r9, 0x18+P0

// P0 = C * P1 - D * P2  computed as d * (p_256 - P2) + c * P1
// Quotient estimation is done just as q = h + 1 as in bignum_triple_p256_alt.
// This also applies to the other functions following.

#define cmsub_p256(P0,C,P1,D,P2)                \
        /* First (%r12;%r11;%r10;%r9) = p_256 - P2 */ \
        movq    $0xffffffffffffffff, %r9 ;          \
        xorl    %r11d, %r11d ;                      \
        subq    P2, %r9 ;                        \
        movq    $0x00000000ffffffff, %r10 ;         \
        sbbq    0x8+P2, %r10 ;                   \
        sbbq    0x10+P2, %r11 ;                  \
        movq    $0xffffffff00000001, %r12 ;         \
        sbbq    0x18+P2, %r12 ;                  \
        /* (%r12;%r11;%r10;%r9;%r8) = D * (p_256 - P2) */  \
        movq    $D, %rcx ;                         \
        movq    %r9, %rax ;                        \
        mulq    %rcx;                            \
        movq    %rax, %r8 ;                        \
        movq    %rdx, %r9 ;                        \
        movq    %r10, %rax ;                       \
        xorl    %r10d, %r10d ;                     \
        mulq    %rcx;                            \
        addq    %rax, %r9 ;                        \
        adcq    %rdx, %r10 ;                       \
        movq    %r11, %rax ;                       \
        xorl    %r11d, %r11d ;                     \
        mulq    %rcx;                            \
        addq    %rax, %r10 ;                       \
        adcq    %rdx, %r11 ;                       \
        movq    %r12, %rax ;                       \
        xorl    %r12d, %r12d ;                     \
        mulq    %rcx;                            \
        addq    %rax, %r11 ;                       \
        adcq    %rdx, %r12 ;                       \
        /* (%rcx;%r11;%r10;%r9;%r8) = 2^256 + C * P1 + D * (p_256 - P2) */ \
        movl    $C, %ecx ;                         \
        movq    P1, %rax ;                      \
        mulq    %rcx;                            \
        addq    %rax, %r8 ;                        \
        adcq    %rdx, %r9 ;                        \
        sbbq    %rbx, %rbx ;                       \
        movq    0x8+P1, %rax ;                  \
        mulq    %rcx;                            \
        subq    %rbx, %rdx ;                       \
        addq    %rax, %r9 ;                        \
        adcq    %rdx, %r10 ;                       \
        sbbq    %rbx, %rbx ;                       \
        movq    0x10+P1, %rax ;                 \
        mulq    %rcx;                            \
        subq    %rbx, %rdx ;                       \
        addq    %rax, %r10 ;                       \
        adcq    %rdx, %r11 ;                       \
        sbbq    %rbx, %rbx ;                       \
        movq    0x18+P1, %rax ;                 \
        mulq    %rcx;                            \
        subq    %rbx, %rdx ;                       \
        addq    %rax, %r11 ;                       \
        adcq    %rdx, %r12 ;                       \
        leaq    1(%r12), %rcx ;                   \
        /* Now the tail for modular reduction from tripling */ \
        movq    $0xffffffff00000001, %rax ;        \
        mulq    %rcx;                            \
        movq    %rcx, %rbx ;                       \
        shlq    $0x20, %rbx ;                      \
        addq    %rcx, %r8 ;                        \
        sbbq    $0x0, %rbx ;                       \
        subq    %rbx, %r9 ;                        \
        sbbq    $0x0, %r10 ;                       \
        sbbq    %rax, %r11 ;                       \
        sbbq    %rdx, %rcx ;                       \
        decq    %rcx;                            \
        movl    $0xffffffff, %eax ;                \
        andq    %rcx, %rax ;                       \
        xorl    %edx, %edx ;                       \
        subq    %rax, %rdx ;                       \
        addq    %rcx, %r8 ;                        \
        movq    %r8, P0 ;                       \
        adcq    %rax, %r9 ;                        \
        movq    %r9, 0x8+P0 ;                   \
        adcq    $0x0, %r10 ;                       \
        movq    %r10, 0x10+P0 ;                 \
        adcq    %rdx, %r11 ;                       \
        movq    %r11, 0x18+P0

// P0 = 3 * P1 - 8 * P2, computed as (p_256 - P2) << 3 + 3 * P1

#define cmsub38_p256(P0,P1,P2)                  \
        /* First (%r11;%r10;%r9;%r8) = p_256 - P2 */ \
        movq    $0xffffffffffffffff, %r8 ;          \
        xorl    %r10d, %r10d ;                      \
        subq    P2, %r8 ;                        \
        movq    $0x00000000ffffffff, %r9 ;          \
        sbbq    0x8+P2, %r9 ;                    \
        sbbq    0x10+P2, %r10 ;                  \
        movq    $0xffffffff00000001, %r11 ;         \
        sbbq    0x18+P2, %r11 ;                  \
        /* (%r12;%r11;%r10;%r9;%r8) = (p_256 - P2) << 3 */  \
        movq    %r11, %r12 ;                       \
        shldq   $3, %r10, %r11 ;                    \
        shldq   $3, %r9, %r10 ;                     \
        shldq   $3, %r8, %r9 ;                      \
        shlq    $3, %r8 ;                          \
        shrq    $61, %r12 ;                        \
        /* (%rcx;%r11;%r10;%r9;%r8) = 2^256 + 3 * P1 + 8 * (p_256 - P2) */ \
        movl    $3, %ecx ;                         \
        movq    P1, %rax ;                      \
        mulq    %rcx;                            \
        addq    %rax, %r8 ;                        \
        adcq    %rdx, %r9 ;                        \
        sbbq    %rbx, %rbx ;                       \
        movq    0x8+P1, %rax ;                  \
        mulq    %rcx;                            \
        subq    %rbx, %rdx ;                       \
        addq    %rax, %r9 ;                        \
        adcq    %rdx, %r10 ;                       \
        sbbq    %rbx, %rbx ;                       \
        movq    0x10+P1, %rax ;                 \
        mulq    %rcx;                            \
        subq    %rbx, %rdx ;                       \
        addq    %rax, %r10 ;                       \
        adcq    %rdx, %r11 ;                       \
        sbbq    %rbx, %rbx ;                       \
        movq    0x18+P1, %rax ;                 \
        mulq    %rcx;                            \
        subq    %rbx, %rdx ;                       \
        addq    %rax, %r11 ;                       \
        adcq    %rdx, %r12 ;                       \
        leaq    1(%r12), %rcx ;                   \
        /* Now the tail for modular reduction from tripling */ \
        movq    $0xffffffff00000001, %rax ;        \
        mulq    %rcx;                            \
        movq    %rcx, %rbx ;                       \
        shlq    $0x20, %rbx ;                      \
        addq    %rcx, %r8 ;                        \
        sbbq    $0x0, %rbx ;                       \
        subq    %rbx, %r9 ;                        \
        sbbq    $0x0, %r10 ;                       \
        sbbq    %rax, %r11 ;                       \
        sbbq    %rdx, %rcx ;                       \
        decq    %rcx;                            \
        movl    $0xffffffff, %eax ;                \
        andq    %rcx, %rax ;                       \
        xorl    %edx, %edx ;                       \
        subq    %rax, %rdx ;                       \
        addq    %rcx, %r8 ;                        \
        movq    %r8, P0 ;                       \
        adcq    %rax, %r9 ;                        \
        movq    %r9, 0x8+P0 ;                   \
        adcq    $0x0, %r10 ;                       \
        movq    %r10, 0x10+P0 ;                 \
        adcq    %rdx, %r11 ;                       \
        movq    %r11, 0x18+P0

// P0 = 4 * P1 - P2, by direct subtraction of P2,
// since the quotient estimate still works safely
// for initial value > -p_256

#define cmsub41_p256(P0,P1,P2)                  \
        movq    0x18+P1, %r11 ;                  \
        movq    %r11, %rcx ;                       \
        movq    0x10+P1, %r10 ;                  \
        shldq   $2, %r10, %r11 ;                    \
        movq    0x8+P1, %r9 ;                    \
        shldq   $2, %r9, %r10 ;                     \
        movq    P1, %r8 ;                        \
        shldq   $2, %r8, %r9 ;                      \
        shlq    $2, %r8 ;                          \
        shrq    $62, %rcx ;                        \
        addq    $1, %rcx ;                         \
        subq    P2, %r8 ;                       \
        sbbq    0x8+P2, %r9 ;                   \
        sbbq    0x10+P2, %r10 ;                 \
        sbbq    0x18+P2, %r11 ;                 \
        sbbq    $0, %rcx ;                         \
        /* Now the tail for modular reduction from tripling */ \
        movq    $0xffffffff00000001, %rax ;        \
        mulq    %rcx;                            \
        movq    %rcx, %rbx ;                       \
        shlq    $0x20, %rbx ;                      \
        addq    %rcx, %r8 ;                        \
        sbbq    $0x0, %rbx ;                       \
        subq    %rbx, %r9 ;                        \
        sbbq    $0x0, %r10 ;                       \
        sbbq    %rax, %r11 ;                       \
        sbbq    %rdx, %rcx ;                       \
        decq    %rcx;                            \
        movl    $0xffffffff, %eax ;                \
        andq    %rcx, %rax ;                       \
        xorl    %edx, %edx ;                       \
        subq    %rax, %rdx ;                       \
        addq    %rcx, %r8 ;                        \
        movq    %r8, P0 ;                       \
        adcq    %rax, %r9 ;                        \
        movq    %r9, 0x8+P0 ;                   \
        adcq    $0x0, %r10 ;                       \
        movq    %r10, 0x10+P0 ;                 \
        adcq    %rdx, %r11 ;                       \
        movq    %r11, 0x18+P0

S2N_BN_SYMBOL(p256_montjdouble_alt):
        _CET_ENDBR

#if WINDOWS_ABI
        pushq   %rdi
        pushq   %rsi
        movq    %rcx, %rdi
        movq    %rdx, %rsi
#endif

// Save registers and make room on stack for temporary variables

        pushq  %rbx
        pushq  %r12
        pushq  %r13
        pushq  %r14
        pushq  %r15

        subq    $NSPACE, %rsp

// Main code, just a sequence of basic field operations

// z2 = z^2
// y2 = y^2

        montsqr_p256(z2,z_1)
        montsqr_p256(y2,y_1)

// x2p = x^2 - z^4 = (x + z^2) * (x - z^2)

        sub_p256(t2,x_1,z2)
        weakadd_p256(t1,x_1,z2)
        montmul_p256(x2p,t1,t2)

// t1 = y + z
// xy2 = x * y^2
// x4p = x2p^2

        add_p256(t1,y_1,z_1)
        montmul_p256(xy2,x_1,y2)
        montsqr_p256(x4p,x2p)

// t1 = (y + z)^2

        montsqr_p256(t1,t1)

// d = 12 * xy2 - 9 * x4p
// t1 = y^2 + 2 * y * z

        cmsub_p256(d,12,xy2,9,x4p)
        sub_p256(t1,t1,z2)

// y4 = y^4

        montsqr_p256(y4,y2)

// dx2 = d * x2p

        montmul_p256(dx2,d,x2p)

// z_3' = 2 * y * z

        sub_p256(z_3,t1,y2)

// x' = 4 * xy2 - d

        cmsub41_p256(x_3,xy2,d)

// y' = 3 * dx2 - 8 * y4

        cmsub38_p256(y_3,dx2,y4)

// Restore stack and registers

        addq    $NSPACE, %rsp
        popq    %r15
        popq    %r14
        popq    %r13
        popq    %r12
        popq    %rbx

#if WINDOWS_ABI
        popq   %rsi
        popq   %rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
