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
// Convert from (almost-)Montgomery form z := (x / 2^{64k}) mod m
// Inputs x[k], m[k]; output z[k]
//
//    extern void bignum_demont
//     (uint64_t k, uint64_t *z, uint64_t *x, uint64_t *m);
//
// Does z := (x / 2^{64k}) mod m, hence mapping out of Montgomery domain.
// In other words, this is a k-fold Montgomery reduction with same-size input.
// This can handle almost-Montgomery inputs, i.e. any k-digit bignum.
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = x, X3 = m
// ----------------------------------------------------------------------------

#define k x0
#define z x1
#define x x2
#define m x3

#define w x4    // Negated modular inverse
#define i x5    // Outer loop counter
#define j x6    // Inner loop counter
#define d x7    // Home for Montgomery multiplier

#define h x8
#define e x9
#define l x10
#define a x11

// Some more intuitive names for temp regs in initial word-level negmodinv.
// These just use i and j again, which aren't used early on.

#define one x5
#define e1 x5
#define e2 x6
#define e4 x5
#define e8 x6

.text
.globl bignum_demont

bignum_demont:

// If k = 0 the whole operation is trivial

                cbz     k, end

// Compute word-level negated modular inverse w for m == m[0].
// This is essentially the same as word_negmodinv.

                ldr     a, [m]
                lsl     w, a, 2
                sub     w, a, w
                eor     w, w, 2
                mov     one, 1
                madd    e1, a, w, one
                mul     e2, e1, e1
                madd    w, e1, w, w
                mul     e4, e2, e2
                madd    w, e2, w, w
                mul     e8, e4, e4
                madd    w, e4, w, w
                madd    w, e8, w, w

// Initially just copy the input to the output. It would be a little more
// efficient but somewhat fiddlier to tweak the zeroth iteration below instead.

                mov     i, xzr
iloop:
                ldr     a, [x, i, LSL 3]
                str     a, [z, i, LSL 3]
                add     i, i, 1
                cmp     i, k
                bcc     iloop

// Outer loop, just doing a standard Montgomery reduction on z

                mov     i, xzr
outerloop:

                ldr     e, [z]
                mul     d, e, w
                ldr     a, [m]
                mul     l, d, a
                umulh   h, d, a
                adds    e, e, l         // Will be zero but want the carry
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
                sub     l, j, 1
                str     e, [z, l, LSL 3]
                add     j, j, 1
                sub     a, j, k
                cbnz    a, montloop
montend:
                adc     h, xzr, h
                sub     l, j, 1
                str     h, [z, l, LSL 3]

// End of outer loop

                add     i, i, 1
                cmp     i, k
                bcc     outerloop

// Now do a comparison of z with m to set a final correction mask
// indicating that z >= m and so we need to subtract m.

                subs    j, xzr, xzr
cmploop:
                ldr     a, [z, j, LSL 3]
                ldr     e, [m, j, LSL 3]
                sbcs    xzr, a, e
                add     j, j, 1
                sub     a, j, k
                cbnz    a, cmploop
                csetm   h, cs

// Now do a masked subtraction of m for the final reduced result.

                subs    j, xzr, xzr
corrloop:
                ldr     a, [z, j, LSL 3]
                ldr     e, [m, j, LSL 3]
                and     e, e, h
                sbcs    a, a, e
                str     a, [z, j, LSL 3]
                add     j, j, 1
                sub     a, j, k
                cbnz    a, corrloop

end:
                ret