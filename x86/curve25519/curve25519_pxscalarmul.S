// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Projective scalar multiplication, x coordinate only, for curve25519
// Inputs scalar[4], point[4]; output res[8]
//
// extern void curve25519_pxscalarmul
//   (uint64_t res[static 8],const uint64_t scalar[static 4],
//    const uint64_t point[static 4]);
//
// Given the X coordinate of an input point = (X,Y) on curve25519, which
// could also be part of a projective representation (X,Y,1) of the same
// point, returns a projective representation (X,Z) = scalar * point, where
// scalar is a 256-bit number. The corresponding affine form is (X/Z,Y'),
// X/Z meaning division modulo 2^255-19, and Y' not being computed by
// this function (nor is any Y coordinate of the input point used).
//
// Standard x86-64 ABI: RDI = res, RSI = scalar, RDX = point
// Microsoft x64 ABI:   RCX = res, RDX = scalar, R8 = point
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(curve25519_pxscalarmul)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(curve25519_pxscalarmul)
        .text

// Size of individual field elements

#define NUMSIZE 32

// Stable homes for input arguments during main code sequence
// and additional registers for loop counter and swap flag

#define res QWORD PTR [rsp+10*NUMSIZE]
#define point QWORD PTR [rsp+10*NUMSIZE+8]
#define scalar QWORD PTR [rsp+10*NUMSIZE+16]
#define i QWORD PTR [rsp+10*NUMSIZE+24]
#define swap QWORD PTR [rsp+10*NUMSIZE+32]

// Pointers to input x coord (we don't use y or z) and output coords.
// These all assume the base address (point and res respectively) is
// currently in the rbp register.

#define x rbp+0
#define resx rbp+0
#define resz rbp+NUMSIZE

// Pointer-offset pairs for temporaries on stack with some aliasing.
// Both dmsn and dnsm need space for >= 5 digits, and we allocate 8

#define zm rsp+(0*NUMSIZE)
#define sm rsp+(0*NUMSIZE)
#define dpro rsp+(0*NUMSIZE)

#define sn rsp+(1*NUMSIZE)

#define dm rsp+(2*NUMSIZE)

#define zn rsp+(3*NUMSIZE)
#define dn rsp+(3*NUMSIZE)
#define e rsp+(3*NUMSIZE)

#define dmsn rsp+(4*NUMSIZE)
#define p rsp+(4*NUMSIZE)

#define xm rsp+(6*NUMSIZE)
#define dnsm rsp+(6*NUMSIZE)
#define spro rsp+(6*NUMSIZE)

#define xn rsp+(8*NUMSIZE)
#define s rsp+(8*NUMSIZE)

#define d rsp+(9*NUMSIZE)

// Total size to reserve on the stack
// This includes space for the 5 other variables above

#define NSPACE (10*NUMSIZE+40)

// Macros wrapping up the basic field operation calls
// bignum_mul_p25519 and bignum_sqr_p25519.
// These two are only trivially different from pure
// function calls to those subroutines.

#define mul_p25519(P0,P1,P2)                    \
        xor    edi, edi;                        \
        mov    rdx, [P2];                       \
        mulx   r9, r8, [P1];                    \
        mulx   r10, rax, [P1+0x8];              \
        add    r9, rax;                         \
        mulx   r11, rax, [P1+0x10];             \
        adc    r10, rax;                        \
        mulx   r12, rax, [P1+0x18];             \
        adc    r11, rax;                        \
        adc    r12, rdi;                        \
        xor    edi, edi;                        \
        mov    rdx, [P2+0x8];                   \
        mulx   rbx, rax, [P1];                  \
        adcx   r9, rax;                         \
        adox   r10, rbx;                        \
        mulx   rbx, rax, [P1+0x8];              \
        adcx   r10, rax;                        \
        adox   r11, rbx;                        \
        mulx   rbx, rax, [P1+0x10];             \
        adcx   r11, rax;                        \
        adox   r12, rbx;                        \
        mulx   r13, rax, [P1+0x18];             \
        adcx   r12, rax;                        \
        adox   r13, rdi;                        \
        adcx   r13, rdi;                        \
        xor    edi, edi;                        \
        mov    rdx, [P2+0x10];                  \
        mulx   rbx, rax, [P1];                  \
        adcx   r10, rax;                        \
        adox   r11, rbx;                        \
        mulx   rbx, rax, [P1+0x8];              \
        adcx   r11, rax;                        \
        adox   r12, rbx;                        \
        mulx   rbx, rax, [P1+0x10];             \
        adcx   r12, rax;                        \
        adox   r13, rbx;                        \
        mulx   r14, rax, [P1+0x18];             \
        adcx   r13, rax;                        \
        adox   r14, rdi;                        \
        adcx   r14, rdi;                        \
        xor    edi, edi;                        \
        mov    rdx, [P2+0x18];                  \
        mulx   rbx, rax, [P1];                  \
        adcx   r11, rax;                        \
        adox   r12, rbx;                        \
        mulx   rbx, rax, [P1+0x8];              \
        adcx   r12, rax;                        \
        adox   r13, rbx;                        \
        mulx   rbx, rax, [P1+0x10];             \
        adcx   r13, rax;                        \
        adox   r14, rbx;                        \
        mulx   r15, rax, [P1+0x18];             \
        adcx   r14, rax;                        \
        adox   r15, rdi;                        \
        adcx   r15, rdi;                        \
        mov    edx, 0x26;                       \
        xor    edi, edi;                        \
        mulx   rbx, rax, r12;                   \
        adcx   r8, rax;                         \
        adox   r9, rbx;                         \
        mulx   rbx, rax, r13;                   \
        adcx   r9, rax;                         \
        adox   r10, rbx;                        \
        mulx   rbx, rax, r14;                   \
        adcx   r10, rax;                        \
        adox   r11, rbx;                        \
        mulx   r12, rax, r15;                   \
        adcx   r11, rax;                        \
        adox   r12, rdi;                        \
        adcx   r12, rdi;                        \
        shld   r12, r11, 0x1;                   \
        mov    edx, 0x13;                       \
        inc    r12;                             \
        bts    r11, 63;                         \
        mulx   rbx, rax, r12;                   \
        add    r8, rax;                         \
        adc    r9, rbx;                         \
        adc    r10, rdi;                        \
        adc    r11, rdi;                        \
        sbb    rax, rax;                        \
        not    rax;                             \
        and    rax, rdx;                        \
        sub    r8, rax;                         \
        sbb    r9, rdi;                         \
        sbb    r10, rdi;                        \
        sbb    r11, rdi;                        \
        btr    r11, 63;                         \
        mov    [P0], r8;                        \
        mov    [P0+0x8], r9;                    \
        mov    [P0+0x10], r10;                  \
        mov    [P0+0x18], r11

#define sqr_p25519(P0,P1)                       \
        mov    rdx, [P1];                       \
        mulx   r15, r8, rdx;                    \
        mulx   r10, r9, [P1+0x8];               \
        mulx   r12, r11, [P1+0x18];             \
        mov    rdx, [P1+0x10];                  \
        mulx   r14, r13, [P1+0x18];             \
        xor    ebx, ebx;                        \
        mulx   rcx, rax, [P1];                  \
        adcx   r10, rax;                        \
        adox   r11, rcx;                        \
        mulx   rcx, rax, [P1+0x8];              \
        adcx   r11, rax;                        \
        adox   r12, rcx;                        \
        mov    rdx, [P1+0x18];                  \
        mulx   rcx, rax, [P1+0x8];              \
        adcx   r12, rax;                        \
        adox   r13, rcx;                        \
        adcx   r13, rbx;                        \
        adox   r14, rbx;                        \
        adc    r14, rbx;                        \
        xor    ebx, ebx;                        \
        adcx   r9, r9;                          \
        adox   r9, r15;                         \
        mov    rdx, [P1+0x8];                   \
        mulx   rdx, rax, rdx;                   \
        adcx   r10, r10;                        \
        adox   r10, rax;                        \
        adcx   r11, r11;                        \
        adox   r11, rdx;                        \
        mov    rdx, [P1+0x10];                  \
        mulx   rdx, rax, rdx;                   \
        adcx   r12, r12;                        \
        adox   r12, rax;                        \
        adcx   r13, r13;                        \
        adox   r13, rdx;                        \
        mov    rdx, [P1+0x18];                  \
        mulx   r15, rax, rdx;                   \
        adcx   r14, r14;                        \
        adox   r14, rax;                        \
        adcx   r15, rbx;                        \
        adox   r15, rbx;                        \
        mov    edx, 0x26;                       \
        xor    ebx, ebx;                        \
        mulx   rcx, rax, r12;                   \
        adcx   r8, rax;                         \
        adox   r9, rcx;                         \
        mulx   rcx, rax, r13;                   \
        adcx   r9, rax;                         \
        adox   r10, rcx;                        \
        mulx   rcx, rax, r14;                   \
        adcx   r10, rax;                        \
        adox   r11, rcx;                        \
        mulx   r12, rax, r15;                   \
        adcx   r11, rax;                        \
        adox   r12, rbx;                        \
        adcx   r12, rbx;                        \
        shld   r12, r11, 0x1;                   \
        mov    edx, 0x13;                       \
        lea    rax, [r12+0x1];                  \
        bts    r11, 0x3f;                       \
        imul   rax, rdx;                        \
        add    r8, rax;                         \
        adc    r9, rbx;                         \
        adc    r10, rbx;                        \
        adc    r11, rbx;                        \
        cmovb  rdx, rbx;                        \
        sub    r8, rdx;                         \
        sbb    r9, rbx;                         \
        sbb    r10, rbx;                        \
        sbb    r11, rbx;                        \
        btr    r11, 0x3f;                       \
        mov    [P0], r8;                        \
        mov    [P0+0x8], r9;                    \
        mov    [P0+0x10], r10;                  \
        mov    [P0+0x18], r11

// Multiplication just giving a 5-digit result (actually < 39 * p_25519)
// by not doing anything beyond the first stage of reduction

#define mul_5(P0,P1,P2)                         \
        xor    edi, edi;                        \
        mov    rdx, [P2];                       \
        mulx   r9, r8, [P1];                    \
        mulx   r10, rax, [P1+0x8];              \
        add    r9, rax;                         \
        mulx   r11, rax, [P1+0x10];             \
        adc    r10, rax;                        \
        mulx   r12, rax, [P1+0x18];             \
        adc    r11, rax;                        \
        adc    r12, rdi;                        \
        xor    edi, edi;                        \
        mov    rdx, [P2+0x8];                   \
        mulx   rbx, rax, [P1];                  \
        adcx   r9, rax;                         \
        adox   r10, rbx;                        \
        mulx   rbx, rax, [P1+0x8];              \
        adcx   r10, rax;                        \
        adox   r11, rbx;                        \
        mulx   rbx, rax, [P1+0x10];             \
        adcx   r11, rax;                        \
        adox   r12, rbx;                        \
        mulx   r13, rax, [P1+0x18];             \
        adcx   r12, rax;                        \
        adox   r13, rdi;                        \
        adcx   r13, rdi;                        \
        xor    edi, edi;                        \
        mov    rdx, [P2+0x10];                  \
        mulx   rbx, rax, [P1];                  \
        adcx   r10, rax;                        \
        adox   r11, rbx;                        \
        mulx   rbx, rax, [P1+0x8];              \
        adcx   r11, rax;                        \
        adox   r12, rbx;                        \
        mulx   rbx, rax, [P1+0x10];             \
        adcx   r12, rax;                        \
        adox   r13, rbx;                        \
        mulx   r14, rax, [P1+0x18];             \
        adcx   r13, rax;                        \
        adox   r14, rdi;                        \
        adcx   r14, rdi;                        \
        xor    edi, edi;                        \
        mov    rdx, [P2+0x18];                  \
        mulx   rbx, rax, [P1];                  \
        adcx   r11, rax;                        \
        adox   r12, rbx;                        \
        mulx   rbx, rax, [P1+0x8];              \
        adcx   r12, rax;                        \
        adox   r13, rbx;                        \
        mulx   rbx, rax, [P1+0x10];             \
        adcx   r13, rax;                        \
        adox   r14, rbx;                        \
        mulx   r15, rax, [P1+0x18];             \
        adcx   r14, rax;                        \
        adox   r15, rdi;                        \
        adcx   r15, rdi;                        \
        mov    edx, 0x26;                       \
        xor    edi, edi;                        \
        mulx   rbx, rax, r12;                   \
        adcx   r8, rax;                         \
        adox   r9, rbx;                         \
        mulx   rbx, rax, r13;                   \
        adcx   r9, rax;                         \
        adox   r10, rbx;                        \
        mulx   rbx, rax, r14;                   \
        adcx   r10, rax;                        \
        adox   r11, rbx;                        \
        mulx   r12, rax, r15;                   \
        adcx   r11, rax;                        \
        adox   r12, rdi;                        \
        adcx   r12, rdi;                        \
        mov    [P0], r8;                        \
        mov    [P0+0x8], r9;                    \
        mov    [P0+0x10], r10;                  \
        mov    [P0+0x18], r11;                  \
        mov    [P0+0x20], r12

// Squaring just giving a result < 2 * p_25519, which is done by
// basically skipping the +1 in the quotient estimate and the final
// optional correction.

#define sqr_4(P0,P1)                            \
        mov    rdx, [P1];                       \
        mulx   r15, r8, rdx;                    \
        mulx   r10, r9, [P1+0x8];               \
        mulx   r12, r11, [P1+0x18];             \
        mov    rdx, [P1+0x10];                  \
        mulx   r14, r13, [P1+0x18];             \
        xor    ebx, ebx;                        \
        mulx   rcx, rax, [P1];                  \
        adcx   r10, rax;                        \
        adox   r11, rcx;                        \
        mulx   rcx, rax, [P1+0x8];              \
        adcx   r11, rax;                        \
        adox   r12, rcx;                        \
        mov    rdx, [P1+0x18];                  \
        mulx   rcx, rax, [P1+0x8];              \
        adcx   r12, rax;                        \
        adox   r13, rcx;                        \
        adcx   r13, rbx;                        \
        adox   r14, rbx;                        \
        adc    r14, rbx;                        \
        xor    ebx, ebx;                        \
        adcx   r9, r9;                          \
        adox   r9, r15;                         \
        mov    rdx, [P1+0x8];                   \
        mulx   rdx, rax, rdx;                   \
        adcx   r10, r10;                        \
        adox   r10, rax;                        \
        adcx   r11, r11;                        \
        adox   r11, rdx;                        \
        mov    rdx, [P1+0x10];                  \
        mulx   rdx, rax, rdx;                   \
        adcx   r12, r12;                        \
        adox   r12, rax;                        \
        adcx   r13, r13;                        \
        adox   r13, rdx;                        \
        mov    rdx, [P1+0x18];                  \
        mulx   r15, rax, rdx;                   \
        adcx   r14, r14;                        \
        adox   r14, rax;                        \
        adcx   r15, rbx;                        \
        adox   r15, rbx;                        \
        mov    edx, 0x26;                       \
        xor    ebx, ebx;                        \
        mulx   rcx, rax, r12;                   \
        adcx   r8, rax;                         \
        adox   r9, rcx;                         \
        mulx   rcx, rax, r13;                   \
        adcx   r9, rax;                         \
        adox   r10, rcx;                        \
        mulx   rcx, rax, r14;                   \
        adcx   r10, rax;                        \
        adox   r11, rcx;                        \
        mulx   r12, rax, r15;                   \
        adcx   r11, rax;                        \
        adox   r12, rbx;                        \
        adcx   r12, rbx;                        \
        shld   r12, r11, 0x1;                   \
        btr    r11, 0x3f;                       \
        mov    edx, 0x13;                       \
        imul   rdx, r12;                        \
        add    r8, rdx;                         \
        adc    r9, rbx;                         \
        adc    r10, rbx;                        \
        adc    r11, rbx;                        \
        mov    [P0], r8;                        \
        mov    [P0+0x8], r9;                    \
        mov    [P0+0x10], r10;                  \
        mov    [P0+0x18], r11

// Plain 4-digit add without any normalization
// With inputs < p_25519 (indeed < 2^255) it still gives a 4-digit result

#define add_4(P0,P1,P2)                         \
        mov     rax, [P1];                      \
        add     rax, [P2];                      \
        mov     [P0], rax;                      \
        mov     rax, [P1+8];                    \
        adc     rax, [P2+8];                    \
        mov     [P0+8], rax;                    \
        mov     rax, [P1+16];                   \
        adc     rax, [P2+16];                   \
        mov     [P0+16], rax;                   \
        mov     rax, [P1+24];                   \
        adc     rax, [P2+24];                   \
        mov     [P0+24], rax

// Add 5-digit inputs and normalize to 4 digits

#define add5_4(P0,P1,P2)                        \
        mov     r8, [P1];                       \
        add     r8, [P2];                       \
        mov     r9, [P1+8];                     \
        adc     r9, [P2+8];                     \
        mov     r10, [P1+16];                   \
        adc     r10, [P2+16];                   \
        mov     r11, [P1+24];                   \
        adc     r11, [P2+24];                   \
        mov     r12, [P1+32];                   \
        adc     r12, [P2+32];                   \
        xor     ebx, ebx;                       \
        shld   r12, r11, 0x1;                   \
        btr    r11, 0x3f;                       \
        mov    edx, 0x13;                       \
        imul   rdx, r12;                        \
        add    r8, rdx;                         \
        adc    r9, rbx;                         \
        adc    r10, rbx;                        \
        adc    r11, rbx;                        \
        mov    [P0], r8;                        \
        mov    [P0+0x8], r9;                    \
        mov    [P0+0x10], r10;                  \
        mov    [P0+0x18], r11

// Subtraction of a pair of numbers < p_25519 just sufficient
// to give a 4-digit result. It actually always does (x - z) + (2^255-19)
// which in turn is done by (x - z) - (2^255+19) discarding the 2^256
// implicitly

#define sub_4(P0,P1,P2)                         \
        mov     r8, [P1];                       \
        sub     r8, [P2];                       \
        mov     r9, [P1+8];                     \
        sbb     r9, [P2+8];                     \
        mov     r10, [P1+16];                   \
        sbb     r10, [P2+16];                   \
        mov     rax, [P1+24];                   \
        sbb     rax, [P2+24];                   \
        sub     r8, 19;                         \
        mov     [P0], r8;                       \
        sbb     r9, 0;                          \
        mov     [P0+8], r9;                     \
        sbb     r10, 0;                         \
        mov     [P0+16], r10;                   \
        sbb     rax, 0;                         \
        btc     rax, 63;                        \
        mov     [P0+24], rax

// Modular subtraction with double modulus 2 * p_25519 = 2^256 - 38

#define sub_twice4(P0,P1,P2)                    \
        mov     r8, [P1];                       \
        xor     ebx, ebx;                       \
        sub     r8, [P2];                       \
        mov     r9, [P1+8];                     \
        sbb     r9, [P2+8];                     \
        mov     ecx, 38;                        \
        mov     r10, [P1+16];                   \
        sbb     r10, [P2+16];                   \
        mov     rax, [P1+24];                   \
        sbb     rax, [P2+24];                   \
        cmovnc  rcx, rbx;                       \
        sub     r8, rcx;                        \
        sbb     r9, rbx;                        \
        sbb     r10, rbx;                       \
        sbb     rax, rbx;                       \
        mov     [P0], r8;                       \
        mov     [P0+8], r9;                     \
        mov     [P0+16], r10;                   \
        mov     [P0+24], rax

// 5-digit subtraction with upward bias to make it positive, adding
// 1000 * (2^255 - 19) = 2^256 * 500 - 19000, then normalizing to 4 digits

#define sub5_4(P0,P1,P2)                        \
        mov     r8, [P1];                       \
        sub     r8, [P2];                       \
        mov     r9, [P1+8];                     \
        sbb     r9, [P2+8];                     \
        mov     r10, [P1+16];                   \
        sbb     r10, [P2+16];                   \
        mov     r11, [P1+24];                   \
        sbb     r11, [P2+24];                   \
        mov     r12, [P1+32];                   \
        sbb     r12, [P2+32];                   \
        xor     ebx, ebx;                       \
        sub     r8, 19000;                      \
        sbb     r9, rbx;                        \
        sbb     r10, rbx;                       \
        sbb     r11, rbx;                       \
        sbb     r12, rbx;                       \
        add     r12, 500;                       \
        shld   r12, r11, 0x1;                   \
        btr    r11, 0x3f;                       \
        mov    edx, 0x13;                       \
        imul   rdx, r12;                        \
        add    r8, rdx;                         \
        adc    r9, rbx;                         \
        adc    r10, rbx;                        \
        adc    r11, rbx;                        \
        mov    [P0], r8;                        \
        mov    [P0+0x8], r9;                    \
        mov    [P0+0x10], r10;                  \
        mov    [P0+0x18], r11

// Combined z = c * x + y with reduction only < 2 * p_25519
// It is assumed that 19 * (c * x + y) < 2^60 * 2^256 so we
// don't need a high mul in the final part.

#define cmadd_4(P0,C1,P2,P3)                    \
        mov     r8, [P3];                       \
        mov     r9, [P3+8];                     \
        mov     r10, [P3+16];                   \
        mov     r11, [P3+24];                   \
        xor     edi, edi;                       \
        mov     rdx, C1;                        \
        mulx    rbx, rax, [P2];                 \
        adcx    r8, rax;                        \
        adox    r9, rbx;                        \
        mulx    rbx, rax, [P2+8];               \
        adcx    r9, rax;                        \
        adox    r10, rbx;                       \
        mulx    rbx, rax, [P2+16];              \
        adcx    r10, rax;                       \
        adox    r11, rbx;                       \
        mulx    rbx, rax, [P2+24];              \
        adcx    r11, rax;                       \
        adox    rbx, rdi;                       \
        adcx    rbx, rdi;                       \
        shld    rbx, r11, 0x1;                  \
        btr     r11, 63;                        \
        mov     edx, 0x13;                      \
        imul    rbx, rdx;                       \
        add     r8, rbx;                        \
        adc     r9, rdi;                        \
        adc     r10, rdi;                       \
        adc     r11, rdi;                       \
        mov     [P0], r8;                       \
        mov     [P0+0x8], r9;                   \
        mov     [P0+0x10], r10;                 \
        mov     [P0+0x18], r11

// Multiplex: z := if NZ then x else y

#define mux_4(P0,P1,P2)                         \
        mov     rax, [P1];                      \
        mov     rcx, [P2];                      \
        cmovz   rax, rcx;                       \
        mov     [P0], rax;                      \
        mov     rax, [P1+8];                    \
        mov     rcx, [P2+8];                    \
        cmovz   rax, rcx;                       \
        mov     [P0+8], rax;                    \
        mov     rax, [P1+16];                   \
        mov     rcx, [P2+16];                   \
        cmovz   rax, rcx;                       \
        mov     [P0+16], rax;                   \
        mov     rax, [P1+24];                   \
        mov     rcx, [P2+24];                   \
        cmovz   rax, rcx;                       \
        mov     [P0+24], rax

S2N_BN_SYMBOL(curve25519_pxscalarmul):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Save registers, make room for temps, preserve input arguments.

        push    rbx
        push    rbp
        push    r12
        push    r13
        push    r14
        push    r15
        sub     rsp, NSPACE

// Move the input arguments to stable places

        mov     res, rdi
        mov     scalar, rsi
        mov     point, rdx

// Initialize (xn,zn) = (1,0) and (xm,zm) = (x,1) with swap = 0

        mov     rax, 1
        mov     [rsp+256], rax
        mov     [rsp], rax
        xor     eax, eax
        mov     swap, rax
        mov     [rsp+96], rax
        mov     [rsp+264], rax
        mov     [rsp+8], rax
        mov     [rsp+104], rax
        mov     [rsp+272], rax
        mov     [rsp+16], rax
        mov     [rsp+112], rax
        mov     [rsp+280], rax
        mov     [rsp+24], rax
        mov     [rsp+120], rax
        mov     rax, [rdx]
        mov     [rsp+192], rax
        mov     rax, [rdx+8]
        mov     [rsp+200], rax
        mov     rax, [rdx+16]
        mov     [rsp+208], rax
        mov     rax, [rdx+24]
        mov     [rsp+216], rax

// The outer loop from i = 255, ..., i = 0 (inclusive)

        mov     eax, 255
        mov     i, rax

curve25519_pxscalarmul_loop:

// sm = xm + zm; sn = xn + zn; dm = xm - zm; dn = xn - zn
// The adds don't need any normalization as they're fed to muls
// Just make sure the subs fit in 4 digits.

        sub_4(dm,xm,zm)
        add_4(sn,xn,zn)
        sub_4(dn,xn,zn)
        add_4(sm,xm,zm)

// ADDING: dmsn = dm * sn; dnsm = sm * dn
// DOUBLING: mux d = xt - zt and s = xt + zt for appropriate choice of (xt,zt)

        mul_5(dmsn,sn,dm)

        mov     rax, scalar
        mov     rdx, i
        mov     rcx, rdx
        shr     rdx, 6
        mov     rdx, [rax+8*rdx]
        shr     rdx, cl
        and     rdx, 1
        cmp     rdx, swap
        mov     swap, rdx

        mux_4(d,dm,dn)
        mux_4(s,sm,sn)

        mul_5(dnsm,sm,dn)

// DOUBLING: d = (xt - zt)^2 normalized only to 4 digits

        sqr_4(d,d)

// ADDING: dpro = (dmsn - dnsm)^2, spro = (dmsn + dnsm)^2
// DOUBLING: s = (xt + zt)^2, normalized only to 4 digits

        sub5_4(dpro,dmsn,dnsm)
        sqr_4(s,s)
        add5_4(spro,dmsn,dnsm)
        sqr_4(dpro,dpro)

// DOUBLING: p = 4 * xt * zt = s - d

        sub_twice4(p,s,d)

// ADDING: xm' = (dmsn + dnsm)^2

        sqr_p25519(xm,spro)

// DOUBLING: e = 121666 * p + d

        cmadd_4(e,0x1db42,p,d)

// DOUBLING: xn' = (xt + zt)^2 * (xt - zt)^2 = s * d

        mul_p25519(xn,s,d)

// ADDING: zm' = x * (dmsn - dnsm)^2

        mov     rbp, point
        mul_p25519(zm,dpro,x)

// DOUBLING: zn' = (4 * xt * zt) * ((xt - zt)^2 + 121666 * (4 * xt * zt))
//               = p * (d + 121666 * p)

        mul_p25519(zn,p,e)

// Loop down as far as 0 (inclusive)

        mov     rax, i
        sub     rax, 1
        mov     i, rax
        jnc     curve25519_pxscalarmul_loop

// The main loop does not handle the special input of the 2-torsion
// point = (0,0). In that case we may get a spurious (0,0) as output
// when we want (0,1) [for odd scalar] or (1,0) [for even scalar].
// Test if x = 0 (this is equivalent for curve25519 to y = 0) and if
// so, patch zm = 1 [for odd multiple], xn = 1 [for even multiple].

        mov     ecx, 1
        mov     rbp, point
        mov     rax, [rbp]
        or      rax, [rbp+8]
        or      rax, [rbp+16]
        or      rax, [rbp+24]
        cmovnz  rax, rcx
        xor     rax, 1
        or      [rsp], rax
        or      [rsp+256], rax

// Multiplex into the final outputs

        mov     rbp, res
        mov     rax, swap
        test    rax, rax

        mux_4(resx,xm,xn)
        mux_4(resz,zm,zn)

// Restore stack and registers

        add     rsp, NSPACE

        pop     r15
        pop     r14
        pop     r13
        pop     r12
        pop     rbp
        pop     rbx

#if WINDOWS_ABI
        pop    rsi
        pop    rdi
#endif
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
