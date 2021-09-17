/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

// ----------------------------------------------------------------------------
// Reduce modulo group order, z := x mod n_384
// Input x[k]; output z[6]
//
//    extern void bignum_mod_n384
//     (uint64_t z[static 6], uint64_t k, uint64_t *x);
//
// Reduction is modulo the group order of the NIST curve P-384.
//
// Standard x86-64 ABI: RDI = z, RSI = k, RDX = x
// ----------------------------------------------------------------------------


        .globl  bignum_mod_n384
        .text

#define z %rdi
#define k %rsi
#define x %rcx

#define m0 %r8
#define m1 %r9
#define m2 %r10
#define m3 %r11
#define m4 %r12
#define m5 %r13
#define d %r14

#define n0 %rax
#define n1 %rbx
#define n2 %rdx
#define q %rdx

#define n0short %eax
#define qshort %edx


bignum_mod_n384:

// Save extra registers

                pushq   %rbx
                pushq   %r12
                pushq   %r13
                pushq   %r14

// If the input is already <= 5 words long, go to a trivial "copy" path

                cmpq    $6, k
                jc      shortinput

// Otherwise load the top 6 digits (top-down) and reduce k by 6

                subq    $6, k
                movq    40(%rdx,k,8), m5
                movq    32(%rdx,k,8), m4
                movq    24(%rdx,k,8), m3
                movq    16(%rdx,k,8), m2
                movq    8(%rdx,k,8), m1
                movq    (%rdx,k,8), m0

// Move x into another register to leave %rdx free for multiplies and use of n2

                movq    %rdx, x

// Reduce the top 6 digits mod n_384 (a conditional subtraction of n_384)

                movq    $0x1313e695333ad68d, n0
                movq    $0xa7e5f24db74f5885, n1
                movq    $0x389cb27e0bc8d220, n2

                addq    n0, m0
                adcq    n1, m1
                adcq    n2, m2
                adcq    $0, m3
                adcq    $0, m4
                adcq    $0, m5
                sbbq    d, d
                notq    d
                andq    d, n0
                andq    d, n1
                andq    d, n2
                subq    n0, m0
                sbbq    n1, m1
                sbbq    n2, m2
                sbbq    $0, m3
                sbbq    $0, m4
                sbbq    $0, m5

// Now do (k-6) iterations of 7->6 word modular reduction

                testq   k, k
                jz      writeback

loop:

// Compute q = min (m5 + 1) (2^64 - 1)

                movl    $1, qshort
                addq    m5, q
                sbbq    d, d
                orq     d, q

// Load the next digit so current m to reduce = [m5;m4;m3;m2;m1;m0;d]

                movq    -8(x,k,8), d

// Now form [m5;m4;m3;m2;m1;m0;d] = m - q * n_384

                subq    q, m5
                xorq    n0, n0
                movq    $0x1313e695333ad68d, n0
                mulxq   n0, n0, n1
                adcxq   n0, d
                adoxq   n1, m0
                movq    $0xa7e5f24db74f5885, n0
                mulxq   n0, n0, n1
                adcxq   n0, m0
                adoxq   n1, m1
                movq    $0x389cb27e0bc8d220, n0
                mulxq   n0, n0, n1
                adcxq   n0, m1
                movl    $0, n0short
                adoxq   n0, n1
                adcxq   n1, m2
                adcq    $0, m3
                adcq    $0, m4
                adcq    $0, m5

// Now our top word m5 is either zero or all 1s. Use it for a masked
// addition of n_384, which we can do by a *subtraction* of
// 2^384 - n_384 from our portion

                movq    $0x1313e695333ad68d, n0
                andq    m5, n0
                movq    $0xa7e5f24db74f5885, n1
                andq    m5, n1
                movq    $0x389cb27e0bc8d220, n2
                andq    m5, n2

                subq    n0, d
                sbbq    n1, m0
                sbbq    n2, m1
                sbbq    $0, m2
                sbbq    $0, m3
                sbbq    $0, m4

// Now shuffle registers up and loop

                movq    m4, m5
                movq    m3, m4
                movq    m2, m3
                movq    m1, m2
                movq    m0, m1
                movq    d, m0

                decq    k
                jnz     loop

// Write back

writeback:

                movq    m0, (z)
                movq    m1, 8(z)
                movq    m2, 16(z)
                movq    m3, 24(z)
                movq    m4, 32(z)
                movq    m5, 40(z)

// Restore registers and return

                popq    %r14
                popq    %r13
                popq    %r12
                popq    %rbx
                ret

shortinput:

                xorq    m0, m0
                xorq    m1, m1
                xorq    m2, m2
                xorq    m3, m3
                xorq    m4, m4
                xorq    m5, m5

                testq   k, k
                jz      writeback
                movq    (%rdx), m0
                decq    k
                jz      writeback
                movq    8(%rdx), m1
                decq    k
                jz      writeback
                movq    16(%rdx), m2
                decq    k
                jz      writeback
                movq    24(%rdx), m3
                decq    k
                jz      writeback
                movq    32(%rdx), m4
                jmp     writeback

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif