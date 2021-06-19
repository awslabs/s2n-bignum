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
// Multiply-add, z := z + x * y
// Inputs x[m], y[n]; outputs function return (carry-out) and z[k]
//
//    extern uint64_t bignum_madd
//     (uint64_t k, uint64_t *z,
//      uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);
//
// Does the "z := x * y + z" operation, while also returning a "next" or
// "carry" word. In the case where m + n <= p (i.e. the pure product would
// fit in the destination) this is the remainder for the exact result.
//
// Standard ARM ABI: X0 = k, X1 = z, X2 = m, X3 = x, X4 = n, X5 = y, returns X0
// ----------------------------------------------------------------------------

#define p x0
#define z x1
#define m x2
#define x x3
#define n x4
#define y x5
#define l x6
#define h x7
#define c x8
#define k x9
#define i x10
#define a x11
#define b x12
#define d x13
#define xx x14
#define yy x15

.text
.globl bignum_madd

bignum_madd:

// If p = 0 the result is trivial and nothing needs doing
// Note that fortuitously our "carry/remainder" term is still right!
// As it's a multiply-add, could also do this if either argument is trivial

                cbz     p, end

// initialize (h,l) = 0, saving c = 0 for inside the loop

                mov     l, xzr
                mov     h, xzr

// Iterate outer loop from k = 0 ... k = p - 1 producing result digits

                mov     k, xzr
outerloop:

// Add the existing z[k] and (h,l) to get initial (c,h,l) combination

                ldr     c, [z, k, LSL 3]
                adds    l, l, c
                adcs    h, h, xzr
                adc     c, xzr, xzr

// First let a = MAX 0 (k + 1 - n) and b = MIN (k + 1) m
// We want to accumulate all x[i] * y[k - i] for a <= i < b

                add     a, k, 1
                cmp     a, m
                csel    b, a, m, cc
                subs    a, a, n
                csel    a, a, xzr, cs

// Set loop count i = b - a, and skip everything if it's <= 0

                subs    i, b, a
                bls     innerend

// Use temporary pointers xx = x + 8 * a and yy = y + 8 * (k - b)
// Increment xx per iteration but just use loop counter with yy
// So we start with [xx] = x[a] and [yy] = y[(k - b) + (b - a)] = y[k - a]

                lsl     xx, a, 3
                add     xx, xx, x

                sub     yy, k, b
                lsl     yy, yy, 3
                add     yy, yy, y

// And index using the loop counter i = b - a, ..., i = 1

innerloop:
                ldr     a, [xx], #8
                ldr     b, [yy, i, LSL 3]
                mul     d, a, b
                umulh   a, a, b
                adds    l, l, d
                adcs    h, h, a
                adc     c, c, xzr
                subs    i, i, 1
                bne     innerloop

innerend:
                str     l, [z, k, LSL 3]
                mov     l, h
                mov     h, c

                add     k, k, 1
                cmp     k, p
                bcc     outerloop                       // Inverted carry flag!

// Return the "carry/remainder" term

                mov     x0, l

end:
                ret