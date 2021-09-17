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
// Reduce modulo field characteristic, z := x mod p_256
// Input x[4]; output z[4]
//
//    extern void bignum_mod_p256_4
//     (uint64_t z[static 4], uint64_t x[static 4]);
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------


        .globl  bignum_mod_p256_4
        .text

#define z %rdi
#define x %rsi

#define d0 %rdx
#define d1 %rcx
#define d2 %r8
#define d3 %r9

#define n1 %r10
#define n3 %r11
#define c %rax

#define n1short %r10d



bignum_mod_p256_4:

// Load the input and subtract to get [d3;d3;d1;d1] = x - p_256 (modulo 2^256)
// The constants n1 and n3 in [n3; 0; n1; -1] = p_256 are saved for later

        movq    (x), d0
        subq    $-1, d0
        movq    8(x), d1
        movl    $0x00000000ffffffff, n1short
        sbbq    n1, d1
        movq    16(x), d2
        sbbq    $0, d2
        movq    $0xffffffff00000001, n3
        movq    24(x), d3
        sbbq    n3, d3

// Capture the carry to determine whether to add back p_256, and use
// it to create a masked p_256' = [n3; 0; n1; c]

        sbbq    c, c
        andq    c, n1
        andq    c, n3

// Do the corrective addition and copy to output

        addq    c, d0
        movq    d0, (z)
        adcq    n1, d1
        movq    d1, 8(z)
        adcq    $0, d2
        movq    d2, 16(z)
        adcq    n3, d3
        movq    d3, 24(z)

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif