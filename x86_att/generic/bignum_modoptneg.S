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
// Optionally negate modulo m, z := (-x) mod m (if p nonzero) or z := x
// (if p zero), assuming x reduced
// Inputs p, x[k], m[k]; output z[k]
//
//    extern void bignum_modoptneg
//      (uint64_t k, uint64_t *z, uint64_t p, uint64_t *x, uint64_t *m);
//
// Standard x86-64 ABI: RDI = k, RSI = z, RDX = p, RCX = x, R8 = m
// ----------------------------------------------------------------------------


        .globl  bignum_modoptneg
        .text

#define k %rdi
#define z %rsi
#define p %rdx
#define x %rcx
#define m %r8

#define a %r9
#define c %rax
#define b %r10
#define i %r11

bignum_modoptneg:

// Do nothing if k = 0

                testq   k, k
                jz      end

// Make an additional check for zero input, and force p to zero in this case.
// This can be skipped if the input is known not to be zero a priori.

                xorq    i, i
                xorq    a, a
cmploop:
                orq     (x,i,8), a
                incq    i
                cmpq    k, i
                jc      cmploop

                cmpq    $0, a
                cmovzq  a, p

// Turn the input p into a strict bitmask

                negq    p
                sbbq    p, p

// Main loop

                xorq    i, i
                movq    p, c
mainloop:
                movq    (m,i,8), a
                andq    p, a
                movq    (x,i,8), b
                xorq    p, b
                negq    c
                adcq    b, a
                sbbq    c, c
                movq    a, (z,i,8)
                incq    i
                cmpq    k, i
                jc      mainloop

end:
                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif