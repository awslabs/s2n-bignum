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
// Extended Montgomery reduce, returning results in input-output buffer
// Inputs z[2*k], m[k], w; outputs function return (extra result bit) and z[2*k]
//
//    extern uint64_t bignum_emontredc
//     (uint64_t k, uint64_t *z, uint64_t *m, uint64_t w);
//
// Assumes that z initially holds a 2k-digit bignum z_0, m is a k-digit odd
// bignum and m * w == -1 (mod 2^64). This function also uses z for the output
// as well as returning a carry c of 0 or 1. This encodes two numbers: in the
// lower half of the z buffer we have q = z[0..k-1], while the upper half
// together with the carry gives r = 2^{64k}*c + z[k..2k-1]. These values
// satisfy z_0 + q * m = 2^{64k} * r, i.e. r gives a raw (unreduced) Montgomery
// reduction while q gives the multiplier that was used. Another way of
// thinking of it is that if z' is the output z with the lower half replaced
// with zeros, then z_0 + q * m = 2^{128k} * c + z'.
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = m, X3 = w, returns X0
// ----------------------------------------------------------------------------

#define k x0
#define z x1
#define m x2
#define w x3

#define i x4    // Outer loop counter
#define j x5    // Inner loop counter
#define d x6    // Home for Montgomery multiplier

#define c x7   // Top carry for current window

#define h x8
#define e x9
#define l x10
#define a x11

.text
.globl bignum_emontredc

bignum_emontredc:

// If k = 0 the whole operation is trivial; note we also get a return of c = 0

                cbz     k, end

// Initialize top carry to zero, and launch into the outer loop

                mov     c, xzr
                mov     i, xzr
outerloop:

                ldr     e, [z]
                mul     d, e, w
                ldr     a, [m]
                mul     l, d, a
                umulh   h, d, a
                str     d, [z]
                adds    xzr, e, l       // Will be zero but want the carry
                mov     j, 1
                sub     a, k, 1
                cbz     a, montend
montloop:
                ldr     a, [m, j, LSL 3]
                ldr     e, [z, j, LSL 3]
                mul     l, d, a
                adcs    e, e, h
                umulh   h, d, a
                adc     h, h, xzr
                adds    e, e, l
                str     e, [z, j, LSL 3]
                add     j, j, 1
                sub     a, j, k
                cbnz    a, montloop
montend:
                adcs    h, h, c
                adc     c, xzr, xzr
                ldr     a, [z, k, LSL 3]
                adds    h, h, a
                adc     c, c, xzr
                str     h, [z, k, LSL 3]

// End of outer loop

                add     z, z, 8         // For simple indexing, z pointer moves
                add     i, i, 1
                cmp     i, k
                bcc     outerloop

// Return c in X0

                mov     x0, c

end:
                ret