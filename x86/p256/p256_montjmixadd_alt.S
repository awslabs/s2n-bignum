// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Point mixed addition on NIST curve P-256 in Montgomery-Jacobian coordinates
//
//    extern void p256_montjmixadd_alt(uint64_t p3[static 12],
//                                     const uint64_t p1[static 12],
//                                     const uint64_t p2[static 8]);
//
// Does p3 := p1 + p2 where all points are regarded as Jacobian triples with
// each coordinate in the Montgomery domain, i.e. x' = (2^256 * x) mod p_256.
// A Jacobian triple (x',y',z') represents affine point (x/z^2,y/z^3).
// The "mixed" part means that p2 only has x and y coordinates, with the
// implicit z coordinate assumed to be the identity.
//
// Standard x86-64 ABI: RDI = p3, RSI = p1, RDX = p2
// Microsoft x64 ABI:   RCX = p3, RDX = p1, R8 = p2
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        .intel_syntax noprefix
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(p256_montjmixadd_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(p256_montjmixadd_alt)
        .text

// Size of individual field elements

#define NUMSIZE 32

// Pointer-offset pairs for inputs and outputs.
// These assume rdi = p3, rsi = p1 and rbp = p2,
// which needs to be set up explicitly before use.
// The first two hold initially, and the second is
// set up by copying the initial rdx input to rbp.
// Thereafter, no code macro modifies any of them.

#define x_1 rsi+0
#define y_1 rsi+NUMSIZE
#define z_1 rsi+(2*NUMSIZE)

#define x_2 rbp+0
#define y_2 rbp+NUMSIZE

#define x_3 rdi+0
#define y_3 rdi+NUMSIZE
#define z_3 rdi+(2*NUMSIZE)

// Pointer-offset pairs for temporaries, with some aliasing.
// NSPACE is the total stack needed for all temporaries.

#define zp2 rsp+(NUMSIZE*0)
#define ww rsp+(NUMSIZE*0)
#define resx rsp+(NUMSIZE*0)

#define yd rsp+(NUMSIZE*1)
#define y2a rsp+(NUMSIZE*1)

#define x2a rsp+(NUMSIZE*2)
#define zzx2 rsp+(NUMSIZE*2)

#define zz rsp+(NUMSIZE*3)
#define t1 rsp+(NUMSIZE*3)

#define t2 rsp+(NUMSIZE*4)
#define zzx1 rsp+(NUMSIZE*4)
#define resy rsp+(NUMSIZE*4)

#define xd rsp+(NUMSIZE*5)
#define resz rsp+(NUMSIZE*5)

#define NSPACE (NUMSIZE*6)

// Corresponds exactly to bignum_montmul_p256_alt

#define montmul_p256(P0,P1,P2)                  \
        mov     rbx, [P2];                      \
        mov     rax, [P1];                      \
        mul     rbx;                            \
        mov     r8, rax;                        \
        mov     r9, rdx;                        \
        mov     rax, [P1+0x8];                  \
        mul     rbx;                            \
        xor     r10d, r10d;                     \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        mov     rax, [P1+0x10];                 \
        mul     rbx;                            \
        xor     r11d, r11d;                     \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        mov     rax, [P1+0x18];                 \
        mul     rbx;                            \
        xor     r12d, r12d;                     \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        mov     rbx, [P2+0x8];                  \
        xor     r13d, r13d;                     \
        mov     rax, [P1];                      \
        mul     rbx;                            \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        sbb     r14, r14;                       \
        mov     rax, [P1+0x8];                  \
        mul     rbx;                            \
        sub     rdx, r14;                       \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     r14, r14;                       \
        mov     rax, [P1+0x10];                 \
        mul     rbx;                            \
        sub     rdx, r14;                       \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        sbb     r14, r14;                       \
        mov     rax, [P1+0x18];                 \
        mul     rbx;                            \
        sub     rdx, r14;                       \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        xor     r14d, r14d;                     \
        mov     rbx, 0x100000000;               \
        mov     rax, r8;                        \
        mul     rbx;                            \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        sbb     r15, r15;                       \
        mov     rax, r9;                        \
        mul     rbx;                            \
        sub     rdx, r15;                       \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     r15, r15;                       \
        not     rbx;                            \
        lea     rbx, [rbx+0x2];                 \
        mov     rax, r8;                        \
        mul     rbx;                            \
        sub     rdx, r15;                       \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        sbb     r15, r15;                       \
        mov     rax, r9;                        \
        mul     rbx;                            \
        sub     rdx, r15;                       \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, r14;                       \
        mov     rbx, [P2+0x10];                 \
        xor     r15d, r15d;                     \
        mov     rax, [P1];                      \
        mul     rbx;                            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     r8, r8;                         \
        mov     rax, [P1+0x8];                  \
        mul     rbx;                            \
        sub     rdx, r8;                        \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        sbb     r8, r8;                         \
        mov     rax, [P1+0x10];                 \
        mul     rbx;                            \
        sub     rdx, r8;                        \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        sbb     r8, r8;                         \
        mov     rax, [P1+0x18];                 \
        mul     rbx;                            \
        sub     rdx, r8;                        \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        adc     r15, r15;                       \
        mov     rbx, [P2+0x18];                 \
        xor     r8d, r8d;                       \
        mov     rax, [P1];                      \
        mul     rbx;                            \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        sbb     r9, r9;                         \
        mov     rax, [P1+0x8];                  \
        mul     rbx;                            \
        sub     rdx, r9;                        \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        sbb     r9, r9;                         \
        mov     rax, [P1+0x10];                 \
        mul     rbx;                            \
        sub     rdx, r9;                        \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        sbb     r9, r9;                         \
        mov     rax, [P1+0x18];                 \
        mul     rbx;                            \
        sub     rdx, r9;                        \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, r8;                         \
        xor     r9d, r9d;                       \
        mov     rbx, 0x100000000;               \
        mov     rax, r10;                       \
        mul     rbx;                            \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        sbb     rcx, rcx;                       \
        mov     rax, r11;                       \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        sbb     rcx, rcx;                       \
        not     rbx;                            \
        lea     rbx, [rbx+0x2];                 \
        mov     rax, r10;                       \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        sbb     rcx, rcx;                       \
        mov     rax, r11;                       \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, r9;                         \
        mov     ecx, 0x1;                       \
        add     rcx, r12;                       \
        dec     rbx;                            \
        adc     rbx, r13;                       \
        dec     r9;                             \
        mov     rax, r9;                        \
        adc     r9, r14;                        \
        mov     r11d, 0xfffffffe;               \
        adc     r11, r15;                       \
        adc     rax, r8;                        \
        cmovb   r12, rcx;                       \
        cmovb   r13, rbx;                       \
        cmovb   r14, r9;                        \
        cmovb   r15, r11;                       \
        mov     [P0], r12;                      \
        mov     [P0+0x8], r13;                  \
        mov     [P0+0x10], r14;                 \
        mov     [P0+0x18], r15

// Corresponds exactly to bignum_montsqr_p256_alt

#define montsqr_p256(P0,P1)                     \
        mov     rax, [P1];                      \
        mov     rbx, rax;                       \
        mul     rax;                            \
        mov     r8, rax;                        \
        mov     r15, rdx;                       \
        mov     rax, [P1+0x8];                  \
        mul     rbx;                            \
        mov     r9, rax;                        \
        mov     r10, rdx;                       \
        mov     rax, [P1+0x18];                 \
        mov     r13, rax;                       \
        mul     rbx;                            \
        mov     r11, rax;                       \
        mov     r12, rdx;                       \
        mov     rax, [P1+0x10];                 \
        mov     rbx, rax;                       \
        mul     r13;                            \
        mov     r13, rax;                       \
        mov     r14, rdx;                       \
        mov     rax, [P1];                      \
        mul     rbx;                            \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     rcx, rcx;                       \
        mov     rax, [P1+0x8];                  \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        sbb     rcx, rcx;                       \
        mov     rbx, [P1+0x18];                 \
        mov     rax, [P1+0x8];                  \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, 0x0;                       \
        xor     ecx, ecx;                       \
        add     r9, r9;                         \
        adc     r10, r10;                       \
        adc     r11, r11;                       \
        adc     r12, r12;                       \
        adc     r13, r13;                       \
        adc     r14, r14;                       \
        adc     rcx, rcx;                       \
        mov     rax, [P1+0x8];                  \
        mul     rax;                            \
        add     r9, r15;                        \
        adc     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     r15, r15;                       \
        mov     rax, [P1+0x10];                 \
        mul     rax;                            \
        neg     r15;                            \
        adc     r12, rax;                       \
        adc     r13, rdx;                       \
        sbb     r15, r15;                       \
        mov     rax, [P1+0x18];                 \
        mul     rax;                            \
        neg     r15;                            \
        adc     r14, rax;                       \
        adc     rdx, rcx;                       \
        mov     r15, rdx;                       \
        mov     rbx, 0x100000000;               \
        mov     rax, r8;                        \
        mul     rbx;                            \
        add     r9, rax;                        \
        adc     r10, rdx;                       \
        sbb     rcx, rcx;                       \
        mov     rax, r9;                        \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r10, rax;                       \
        adc     r11, rdx;                       \
        sbb     rcx, rcx;                       \
        not     rbx;                            \
        lea     rbx, [rbx+0x2];                 \
        mov     rax, r8;                        \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        sbb     rcx, rcx;                       \
        xor     r8d, r8d;                       \
        mov     rax, r9;                        \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        adc     r14, r8;                        \
        adc     r15, r8;                        \
        adc     r8, r8;                         \
        mov     rbx, 0x100000000;               \
        mov     rax, r10;                       \
        mul     rbx;                            \
        add     r11, rax;                       \
        adc     r12, rdx;                       \
        sbb     rcx, rcx;                       \
        mov     rax, r11;                       \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r12, rax;                       \
        adc     r13, rdx;                       \
        sbb     rcx, rcx;                       \
        not     rbx;                            \
        lea     rbx, [rbx+0x2];                 \
        mov     rax, r10;                       \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r13, rax;                       \
        adc     r14, rdx;                       \
        sbb     rcx, rcx;                       \
        xor     r9d, r9d;                       \
        mov     rax, r11;                       \
        mul     rbx;                            \
        sub     rdx, rcx;                       \
        add     r14, rax;                       \
        adc     r15, rdx;                       \
        adc     r8, r9;                         \
        mov     ecx, 0x1;                       \
        add     rcx, r12;                       \
        lea     rbx, [rbx-0x1];                 \
        adc     rbx, r13;                       \
        lea     r9, [r9-0x1];                   \
        mov     rax, r9;                        \
        adc     r9, r14;                        \
        mov     r11d, 0xfffffffe;               \
        adc     r11, r15;                       \
        adc     rax, r8;                        \
        cmovb   r12, rcx;                       \
        cmovb   r13, rbx;                       \
        cmovb   r14, r9;                        \
        cmovb   r15, r11;                       \
        mov     [P0], r12;                      \
        mov     [P0+0x8], r13;                  \
        mov     [P0+0x10], r14;                 \
        mov     [P0+0x18], r15

// Corresponds exactly to bignum_sub_p256

#define sub_p256(P0,P1,P2)                      \
        mov     rax,[P1];                       \
        sub     rax,[P2];                       \
        mov     rcx,[P1+0x8];                   \
        sbb     rcx,[P2+0x8];                   \
        mov     r8,[P1+0x10];                   \
        sbb     r8,[P2+0x10];                   \
        mov     r9,[P1+0x18];                   \
        sbb     r9,[P2+0x18];                   \
        mov     r10d,0xffffffff;                \
        sbb     r11,r11;                        \
        xor     rdx,rdx;                        \
        and     r10,r11;                        \
        sub     rdx,r10;                        \
        add     rax,r11;                        \
        mov     [P0],rax;                       \
        adc     rcx,r10;                        \
        mov     [P0+0x8],rcx;                   \
        adc     r8,0x0;                         \
        mov     [P0+0x10],r8;                   \
        adc     r9,rdx;                         \
        mov     [P0+0x18],r9

// Additional macros to help with final multiplexing

#define testzero4(P)                            \
        mov     rax, [P];                       \
        mov     rdx, [P+8];                     \
        or      rax, [P+16];                    \
        or      rdx, [P+24];                    \
        or      rax, rdx

#define mux4(r0,r1,r2,r3,PNE,PEQ)               \
        mov     r0, [PNE];                      \
        mov     rax, [PEQ];                     \
        cmovz   r0, rax;                        \
        mov     r1, [PNE+8];                    \
        mov     rax, [PEQ+8];                   \
        cmovz   r1, rax;                        \
        mov     r2, [PNE+16];                   \
        mov     rax, [PEQ+16];                  \
        cmovz   r2, rax;                        \
        mov     r3, [PNE+24];                   \
        mov     rax, [PEQ+24];                  \
        cmovz   r3, rax

#define load4(r0,r1,r2,r3,P)                    \
        mov     r0, [P];                        \
        mov     r1, [P+8];                      \
        mov     r2, [P+16];                     \
        mov     r3, [P+24]

#define store4(P,r0,r1,r2,r3)                   \
        mov     [P], r0;                        \
        mov     [P+8], r1;                      \
        mov     [P+16], r2;                     \
        mov     [P+24], r3

S2N_BN_SYMBOL(p256_montjmixadd_alt):
        _CET_ENDBR

#if WINDOWS_ABI
        push    rdi
        push    rsi
        mov     rdi, rcx
        mov     rsi, rdx
        mov     rdx, r8
#endif

// Save registers and make room on stack for temporary variables
// Put the input y in rbp where it lasts as long as it's needed.

        push   rbx
        push   rbp
        push   r12
        push   r13
        push   r14
        push   r15

        sub     rsp, NSPACE

        mov     rbp, rdx

// Main code, just a sequence of basic field operations
// 8 * multiply + 3 * square + 7 * subtract

        montsqr_p256(zp2,z_1)

        montmul_p256(y2a,z_1,y_2)
        montmul_p256(x2a,zp2,x_2)
        montmul_p256(y2a,zp2,y2a)

        sub_p256(xd,x2a,x_1)

        sub_p256(yd,y2a,y_1)

        montsqr_p256(zz,xd)
        montsqr_p256(ww,yd)

        montmul_p256(zzx1,zz,x_1)
        montmul_p256(zzx2,zz,x2a)

        sub_p256(resx,ww,zzx1)
        sub_p256(t1,zzx2,zzx1)

        montmul_p256(resz,xd,z_1)

        sub_p256(resx,resx,zzx2)

        sub_p256(t2,zzx1,resx)

        montmul_p256(t1,t1,y_1)
        montmul_p256(t2,yd,t2)

        sub_p256(resy,t2,t1)

// Test if z_1 = 0 to decide if p1 = 0 (up to projective equivalence)

        testzero4(z_1)

// Multiplex: if p1 <> 0 just copy the computed result from the staging area.
// If p1 = 0 then return the point p2 augmented with a z = 1 coordinate (in
// Montgomery form so not the simple constant 1 but rather 2^256 - p_256),
// hence giving 0 + p2 = p2 for the final result.

        mux4(r8,r9,r10,r11,resx,x_2)
        mux4(r12,r13,r14,r15,resy,y_2)

        store4(x_3,r8,r9,r10,r11)
        store4(y_3,r12,r13,r14,r15)

        load4(r8,r9,r10,r11,resz)
        mov     eax, 1
        cmovz   r8, rax
        mov     rax, 0xffffffff00000000
        cmovz   r9, rax
        mov     rax, 0xffffffffffffffff
        cmovz   r10, rax
        mov     eax, 0x00000000fffffffe
        cmovz   r11, rax

        store4(z_3,r8,r9,r10,r11)

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
