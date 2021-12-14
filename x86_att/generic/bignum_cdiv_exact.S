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
// Divide by a single word, z := x / m *when known to be exact*
// Inputs x[n], m; output z[k]
//
//    extern void bignum_cdiv_exact
//     (uint64_t k, uint64_t *z, uint64_t n, uint64_t *x, uint64_t m);
//
// Does the "z := x / m" operation where x is n digits and result z is k,
// *assuming* that m is nonzero and that the input x is in fact an
// exact multiple of m. (If this isn't known, use the general bignum_cdiv
// function instead.) In general the result is truncated to k digits.
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = n, RCX = x, R8 = m
// ----------------------------------------------------------------------------


        .globl  bignum_cdiv_exact
        .text

#define k %rdi
#define z %rsi
#define m %r8

// These parameters get moved because of special uses for %rcx, %rdx

#define n %r9
#define x %r10

// This needs to be in %rcx for variable shifts with %cl

#define e %rcx

// Other variables

#define w %r11
#define d %r12
#define i %rbx
#define c %r13
#define t %r14

#define a %rax
#define h %rdx

#define ishort %ebx
#define hshort %edx

bignum_cdiv_exact:

                pushq   %rbx
                pushq   %r12
                pushq   %r13
                pushq   %r14

// If k = 0 then there's nothing to be done

                testq   k, k
                jz      end

// Move parameters that need a new home

                movq    %rdx, n
                movq    %rcx, x

// Let e be the number of trailing zeros in m (we can ignore m = 0)

                bsfq    m, e

// Now just shift m right by e bits. So hereafter we can assume m is odd
// but we first need to shift the input right by e bits then divide by m.

                shrq   %cl, m

// Compute the negated modular inverse w with w * m + 1 == 0 (mod 2^64)
// This is essentially the same as word_negmodinv.

                movq    m, a
                movq    m, w
                shlq    $2, a
                subq    a, w
                xorq    $2, w
                movq    w, a
                imulq   m, a
                movl    $2, hshort
                addq    a, h
                addq    $1, a
                imulq   h, w
                imulq   a, a
                movl    $1, hshort
                addq    a, h
                imulq   h, w
                imulq   a, a
                movl    $1, hshort
                addq    a, h
                imulq   h, w
                imulq   a, a
                movl    $1, hshort
                addq    a, h
                imulq   h, w

// Consider x' = x + m and do a Montgomery reduction, keeping the cofactor z.
// This gives us x' + m * z = 2^{64k} * c where c <= m. Assuming x = m * y
// we then have m * y + m + m * z = 2^{64k} * c, i.e.
//
//     m * (y + z + 1) = 2^{64k} * c
//
// This means m * (y + z + 1) == 0 (mod 2^{64k}), even when we truncate
// x to k digits (if in fact k < n). Since m is odd, it's coprime to
// 2^{64k} so we can cancel and get y + z + 1 == 0 (mod 2^{64k}), and
// hence using logical complement y == ~z (mod 2^{64k}). Thus we can
// write back the logical complements of the cofactor as the answer.
// Start with carry word c = m to make the initial tweak x' = x + m.

                 movq    m, c
                 xorl    ishort, ishort

// Unless n = 0, preload the zeroth digit and bump up the x pointer by
// 8 and n down by 1, to ease indexing and comparison using the same
// variable i in the main loop. When n = 0 we leave it alone, as the
// comparison i < n will always fail and the x pointer is unused.

                xorq    d, d
                testq   n, n
                jz      loop
                movq    (x), d
                addq    $8, x
                decq    n

loop:

// Load the next digit up to get [t,d] then shift right e places

                xorq    t, t
                cmpq    n, i
                jnc     noload
                movq    (x,i,8), t
noload:
                shrdq   %cl, t, d
                addq    c, d
                sbbq    c, c
                negq    c

// Now the effective sum is [c,a] where the carry-in has been absorbed.
// Do the main Montgomery step with the (odd) m, writing back ~q. Finally
// set d to the next digit ready for the following iteration.

                movq    w, a
                imulq   d, a
                notq    a
                movq    a, (z,i,8)
                notq    a

                mulq    m
                addq    d, a
                adcq    h, c

                movq    t, d

                incq    i
                cmpq    k, i
                jc      loop

end:
                popq    %r14
                popq    %r13
                popq    %r12
                popq    %rbx
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif