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
// Compare bignums, x <= y
// Inputs x[m], y[n]; output function return
//
//    extern uint64_t bignum_le
//     (uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);
//
// Standard ARM ABI: X0 = m, X1 = x, X2 = n, X3 = y, returns X0
// ----------------------------------------------------------------------------

#define m x0
#define x x1
#define n x2
#define y x3
#define i x4
#define a x5
#define d x6

.text
.globl bignum_le

bignum_le:

// Zero the main index counter for both branches

                mov     i, xzr

// Speculatively form n := n - m and do case split

                subs    n, n, m
                bcc     ylonger

// The case where y is longer or of the same size (n >= m)
// Note that CF=1 initially by the fact that we reach this point

                cbz     m, xtest
xmainloop:
                ldr     a, [y, i, LSL 3]
                ldr     d, [x, i, LSL 3]
                sbcs    xzr, a, d
                add     i, i, 1
                sub     m, m, 1
                cbnz    m, xmainloop
xtest:
                cbz     n, xskip
xtoploop:
                ldr     a, [y, i, LSL 3]
                sbcs    xzr, a, xzr
                add     i, i, 1
                sub     n, n, 1
                cbnz    n, xtoploop
xskip:
                cset    x0, cs
                ret

// The case where x is longer (m > n)
// The first "adds" also makes sure CF=1 initially in this branch

ylonger:
                adds    n, n, m
                cbz     n, ytoploop
                sub     m, m, n
ymainloop:
                ldr     a, [y, i, LSL 3]
                ldr     d, [x, i, LSL 3]
                sbcs    xzr, a, d
                add     i, i, 1
                sub     n, n, 1
                cbnz    n, ymainloop
ytoploop:
                ldr     a, [x, i, LSL 3]
                sbcs    xzr, xzr, a
                add     i, i, 1
                sub     m, m, 1
                cbnz    m, ytoploop

                cset    x0, cs
                ret