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
// Standard ARM ABI: X0 = k, X1 = z, X2 = p, X3 = x, X4 = m
// ----------------------------------------------------------------------------

#define k x0
#define z x1
#define p x2
#define x x3
#define m x4
#define i x5
#define a x6
#define b x7

.text
.globl bignum_modoptneg

bignum_modoptneg:

// Do nothing if k = 0

                cbz     k, end

// Make an additional check for zero input, and force p to zero in this case.
// This can be skipped if the input is known not to be zero a priori.

                mov     i, xzr
                mov     a, xzr
cmploop:
                ldr     b, [x, i, LSL 3]
                orr     a, a, b
                add     i, i, 1
                cmp     i, k
                bcc     cmploop

                cmp     a, xzr
                csel    p, p, xzr, ne

// Turn the input p into a strict bitmask

                cmp     p, xzr
                csetm   p, ne

// Main loop

                mov     i, xzr
                adds    xzr, p, p
mainloop:

                ldr     a, [m, i, LSL 3]
                ldr     b, [x, i, LSL 3]
                and     a, a, p
                eor     b, b, p
                adcs    a, a, b
                str     a, [z, i, LSL 3]
                add     i, i, 1
                sub     a, i, k
                cbnz    a, mainloop

end:
                ret