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
// 256-bit multiplex/select z := x (if p nonzero) or z := y (if p zero)
// Inputs p, x[4], y[4]; output z[4]
//
//    extern void bignum_mux_4
//     (uint64_t p, uint64_t z[static 4],
//      uint64_t x[static 4], uint64_t y[static 4]);
//
// It is assumed that all numbers x, y and z have the same size 4 digits.
//
// Standard x86-64 ABI: RDI = p, RSI = z, RDX = x, RCX = y
// ----------------------------------------------------------------------------


        .globl  bignum_mux_4
        .text

#define p %rdi
#define z %rsi
#define x %rdx
#define y %rcx
#define a %rax
#define b %r8


bignum_mux_4:
                testq   p, p

                movq    (x), a
                movq    (y), b
                cmovzq  b, a
                movq    a, (z)

                movq    8(x), a
                movq    8(y), b
                cmovzq  b, a
                movq    a, 8(z)

                movq    16(x), a
                movq    16(y), b
                cmovzq  b, a
                movq    a, 16(z)

                movq    24(x), a
                movq    24(y), b
                cmovzq  b, a
                movq    a, 24(z)

                ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif