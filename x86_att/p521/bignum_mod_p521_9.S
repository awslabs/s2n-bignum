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
// Reduce modulo field characteristic, z := x mod p_521
// Input x[9]; output z[9]
//
//    extern void bignum_mod_p521_9
//     (uint64_t z[static 9], uint64_t x[static 9]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------


        .globl  bignum_mod_p521_9
        .text

#define z %rdi
#define x %rsi

#define d0 %rax
#define d1 %rcx
#define d2 %r8
#define d3 %r9
#define d4 %r10
#define d5 %r11
#define d6 %rbx

#define d8 %rdx

#define d8short %edx

// Re-use the input pointer as other variable once safe to do so

#define d7 %rsi

bignum_mod_p521_9:

// Save one more register

        pushq   %rbx

// Separate out the input into x = 2^521 * H + L, so that x mod p_521 =
// (H + L) mod p_521 = if H + L >= p_521 then H + L - p_521 else H + L.

        movq    64(x), d0
        movl    $0x1FF, d8short
        andq    d0, d8
        shrq    $9, d0

// Force carry-in to get s = [d8;d7;d6;d5;d4;d3;d2;d1;d0] = H + L + 1.

        stc
        adcq    (x), d0
        movq    8(x), d1
        adcq    $0, d1
        movq    16(x), d2
        adcq    $0, d2
        movq    24(x), d3
        adcq    $0, d3
        movq    32(x), d4
        adcq    $0, d4
        movq    40(x), d5
        adcq    $0, d5
        movq    48(x), d6
        adcq    $0, d6
        movq    56(x), d7
        adcq    $0, d7
        adcq    $0, d8

// Set CF <=> s < 2^521 <=> H + L < p_521, so that if CF is set
// we want H + L = s - 1, otherwise (H + L) - p_521 = s - 2^521.
// This is done with just s - CF then masking to 521 bits.

        cmpq    $512, d8

        sbbq    $0, d0
        movq    d0, (z)
        sbbq    $0, d1
        movq    d1, 8(z)
        sbbq    $0, d2
        movq    d2, 16(z)
        sbbq    $0, d3
        movq    d3, 24(z)
        sbbq    $0, d4
        movq    d4, 32(z)
        sbbq    $0, d5
        movq    d5, 40(z)
        sbbq    $0, d6
        movq    d6, 48(z)
        sbbq    $0, d7
        movq    d7, 56(z)
        sbbq    $0, d8
        andq    $0x1FF, d8
        movq    d8, 64(z)

// Restore register

        popq    %rbx
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif