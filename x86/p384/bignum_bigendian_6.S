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
// Convert 6-digit (384-bit) bignum to/from big-endian form
// Input x[6]; output z[6]
//
//    extern void bignum_bigendian_6
//     (uint64_t z[static 6], uint64_t x[static 6]);
//
// The same function is given two other prototypes whose names reflect the
// treatment of one or other argument as a byte array rather than word array:
//
//    extern void bignum_frombytes_6
//     (uint64_t z[static 6], uint8_t x[static 48]);
//
//    extern void bignum_tobytes_6
//     (uint8_t z[static 48], uint64_t x[static 6]);
//
// Since x86 is little-endian, and bignums are stored with little-endian
// word order, this is simply byte reversal and is implemented as such.
//
// Standard x86-64 ABI: RDI = z, RSI = x
// ----------------------------------------------------------------------------

.intel_syntax noprefix

        .globl  bignum_bigendian_6
        .globl  bignum_frombytes_6
        .globl  bignum_tobytes_6
        .text

#define z rdi
#define x rsi
#define a rax
#define b rdx

// All loads and stores are word-sized, then we use BSWAP to
// reverse the byte order, as well as switching round the word order
// when writing back. The reads and writes are organized in mirror-image
// pairs (0-5, 1-4, 2-3) to allow x and z to point to the same buffer
// without using more intermediate registers.

bignum_bigendian_6:
bignum_frombytes_6:
bignum_tobytes_6:

// 0 and 5 words

                mov     a, [x]
                mov     b, [x+8*5]
                bswap   a
                bswap   b
                mov     [z+8*5], a
                mov     [z], b

// 1 and 4 words

                mov     a, [x+8*1]
                mov     b, [x+8*4]
                bswap   a
                bswap   b
                mov     [z+8*4], a
                mov     [z+8*1], b

// 2 and 3 words

                mov     a, [x+8*2]
                mov     b, [x+8*3]
                bswap   a
                bswap   b
                mov     [z+8*3], a
                mov     [z+8*2], b

                ret