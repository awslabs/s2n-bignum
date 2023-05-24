// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

// ----------------------------------------------------------------------------
// Square, z := x^2
// Input x[8]; output z[16]
//
//    extern void bignum_sqr_8_16_neon (uint64_t z[static 16], uint64_t x[static 8]);
//
// Standard ARM ABI: X0 = z, X1 = x
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_sqr_8_16_neon)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_sqr_8_16_neon)
        .text
        .balign 4

// ---------------------------------------------------------------------------
// Macro computing [c,b,a] := [b,a] + (x - y) * (w - z), adding with carry
// to the [b,a] components but leaving CF aligned with the c term, which is
// a sign bitmask for (x - y) * (w - z). Continued add-with-carry operations
// with [c,...,c] will continue the carry chain correctly starting from
// the c position if desired to add to a longer term of the form [...,b,a].
//
// c,h,l,t should all be different and t,h should not overlap w,z.
// ---------------------------------------------------------------------------

.macro muldiffnadd b,a, c,h,l,t, x,y, w,z
        subs    \t, \x, \y
        cneg    \t, \t, cc
        csetm   \c, cc
        subs    \h, \w, \z
        cneg    \h, \h, cc
        mul     \l, \t, \h
        umulh   \h, \t, \h
        cinv    \c, \c, cc
        adds    xzr, \c, #1
        eor     \l, \l, \c
        adcs    \a, \a, \l
        eor     \h, \h, \c
        adcs    \b, \b, \h
.endm

#define z x0
#define x x1

#define a0 x2
#define a1 x3
#define a2 x4
#define a3 x5
#define b0 x6
#define b1 x7
#define b2 x8
#define b3 x9

#define s0 x10
#define s1 x11
#define s2 x12
#define s3 x13
#define s4 x14
#define s5 x15
#define s6 x16
#define s7 x17

#define c  x19
#define h  x20
#define l  x21
#define t  x22

// ---------------------------------------------------------------------------
// Core 4x4->8 ADK multiplication macro
// Does [s7,s6,s5,s4,s3,s2,s1,s0] = [a3,a2,a1,a0] * [b3,b2,b1,b0]
// ---------------------------------------------------------------------------

.macro  mul4

// First accumulate all the "simple" products as [s7,s6,s5,s4,s0]

        mul     s0, a0, b0
        mul     s4, a1, b1
        mul     s5, a2, b2
        mul     s6, a3, b3

        umulh   s7, a0, b0
        adds    s4, s4, s7
        umulh   s7, a1, b1
        adcs    s5, s5, s7
        umulh   s7, a2, b2
        adcs    s6, s6, s7
        umulh   s7, a3, b3
        adc     s7, s7, xzr

// Multiply by B + 1 to get [s7;s6;s5;s4;s1;s0]

        adds    s1, s4, s0
        adcs    s4, s5, s4
        adcs    s5, s6, s5
        adcs    s6, s7, s6
        adc     s7, xzr, s7

// Multiply by B^2 + 1 to get [s7;s6;s5;s4;s3;s2;s1;s0]

        adds    s2, s4, s0
        adcs    s3, s5, s1
        adcs    s4, s6, s4
        adcs    s5, s7, s5
        adcs    s6, xzr, s6
        adc     s7, xzr, s7

// Now add in all the "complicated" terms.

        muldiffnadd s6,s5, c,h,l,t, a2,a3, b3,b2
        adc     s7, s7, c

        muldiffnadd s2,s1, c,h,l,t, a0,a1, b1,b0
        adcs    s3, s3, c
        adcs    s4, s4, c
        adcs    s5, s5, c
        adcs    s6, s6, c
        adc     s7, s7, c

        muldiffnadd s5,s4, c,h,l,t, a1,a3, b3,b1
        adcs    s6, s6, c
        adc     s7, s7, c

        muldiffnadd s3,s2, c,h,l,t, a0,a2, b2,b0
        adcs    s4, s4, c
        adcs    s5, s5, c
        adcs    s6, s6, c
        adc     s7, s7, c

        muldiffnadd s4,s3, c,h,l,t, a0,a3, b3,b0
        adcs    s5, s5, c
        adcs    s6, s6, c
        adc     s7, s7, c
        muldiffnadd s4,s3, c,h,l,t, a1,a2, b2,b1
        adcs    s5, s5, c
        adcs    s6, s6, c
        adc     s7, s7, c
.endm

// ---------------------------------------------------------------------------
// The main code
// ---------------------------------------------------------------------------

S2N_BN_SYMBOL(bignum_sqr_8_16_neon):

// Save registers

        stp     x19, x20, [sp, #-16]!
        stp     x21, x22, [sp, #-16]!

// Load all the inputs first

        ldp     a0, a1, [x]
        ldp     a2, a3, [x, #16]
        ldp     b0, b1, [x, #32]
        ldp     b2, b3, [x, #48]

// Square the lower half with a near-clone of bignum_sqr_4_8
ldr q0, [x]
        mul x17, x2, x4
ldr q7, [x, #16]
        mul x14, x3, x5
movi v4.2d, #0x000000ffffffff
        umulh x20, x2, x4
ext v1.16b, v0.16b, v0.16b, #8
        subs x21, x2, x3
        cneg x21, x21, cc
        csetm x11, cc
        subs x12, x5, x4
        cneg x12, x12, cc
shrn v2.2s, v0.2d, #32
        mul x13, x21, x12
zip1 v0.2s, v0.2s, v1.2s
        umulh x12, x21, x12
umull v5.2d, v2.2s, v2.2s
        cinv x11, x11, cc
umull v6.2d, v2.2s, v0.2s
        eor x13, x13, x11
umull v3.2d, v0.2s, v0.2s
        eor x12, x12, x11
        adds x19, x17, x20
        adc x20, x20, xzr
mov v1.16b, v6.16b
        umulh x21, x3, x5
usra v1.2d, v3.2d, #32
        adds x19, x19, x14
and v4.16b, v1.16b, v4.16b
        adcs x20, x20, x21
add v4.2d, v4.2d, v6.2d
        adc x21, x21, xzr
usra v5.2d, v4.2d, #32
        adds x20, x20, x14
sli v3.2d, v4.2d, #32
        adc x21, x21, xzr
usra v5.2d, v1.2d, #32
        adds xzr, x11, #1
  movi v4.2d, #0x000000ffffffff
        adcs x19, x19, x13
  ext v1.16b, v7.16b, v7.16b, #8
        adcs x20, x20, x12
  shrn v2.2s, v7.2d, #32
        adc x21, x21, x11
  zip1 v0.2s, v7.2s, v1.2s
        adds x17, x17, x17
        adcs x19, x19, x19
        adcs x20, x20, x20
        adcs x21, x21, x21
        adc x10, xzr, xzr
mov x12, v3.d[0]
mov x11, v5.d[0]
        mul x15, x2, x3
mov x13, v3.d[1]
        umulh x16, x2, x3
mov x14, v5.d[1]
        adds x11, x11, x15
  umull v5.2d, v2.2s, v2.2s
        adcs x13, x13, x16
  umull v6.2d, v2.2s, v0.2s
        adc x14, x14, xzr
  umull v3.2d, v0.2s, v0.2s
        adds x11, x11, x15
  mov v1.16b, v6.16b
        adcs x13, x13, x16
  usra v1.2d, v3.2d, #32
        adc x14, x14, xzr
  and v4.16b, v1.16b, v4.16b

        stp x12, x11, [z]
  add v4.2d, v4.2d, v6.2d
        adds x17, x17, x13
  usra v5.2d, v4.2d, #32
        adcs x19, x19, x14
  sli v3.2d, v4.2d, #32
        adcs x20, x20, xzr
  usra v5.2d, v1.2d, #32
        adcs x21, x21, xzr
  mov x12, v3.d[0]
        adc x10, x10, xzr
  mov x11, v5.d[0]
        stp x17, x19, [z, #16]
  mov x13, v3.d[1]

        mul x15, x4, x5
  mov x14, v5.d[1]
        umulh x16, x4, x5
ldr q0, [x, #32]
        adds x11, x11, x15
ldr q7, [x, #48]
        adcs x13, x13, x16
        adc x14, x14, xzr
        adds x11, x11, x15
        adcs x13, x13, x16
        adc x14, x14, xzr
        adds x12, x12, x20
        adcs x11, x11, x21
        stp x12, x11, [z,#32]
        adcs x13, x13, x10
        adc x14, x14, xzr
        stp x13, x14, [z,#48]

// Square the upper half with a slight variant of the previous block

        mul x17, x6, x8
        mul x14, x7, x9
movi v4.2d, #0x000000ffffffff
        umulh x20, x6, x8
ext v1.16b, v0.16b, v0.16b, #8
        subs x21, x6, x7
        cneg x21, x21, cc
        csetm x11, cc
        subs x12, x9, x8
        cneg x12, x12, cc
shrn v2.2s, v0.2d, #32
        mul x13, x21, x12
zip1 v0.2s, v0.2s, v1.2s
        umulh x12, x21, x12
umull v5.2d, v2.2s, v2.2s
        cinv x11, x11, cc
umull v6.2d, v2.2s, v0.2s
        eor x13, x13, x11
umull v3.2d, v0.2s, v0.2s
        eor x12, x12, x11
        adds x19, x17, x20
        adc x20, x20, xzr
mov v1.16b, v6.16b
        umulh x21, x7, x9
usra v1.2d, v3.2d, #32
        adds x19, x19, x14
and v4.16b, v1.16b, v4.16b
        adcs x20, x20, x21
add v4.2d, v4.2d, v6.2d
        adc x21, x21, xzr
usra v5.2d, v4.2d, #32
        adds x20, x20, x14
sli v3.2d, v4.2d, #32
        adc x21, x21, xzr
usra v5.2d, v1.2d, #32
        adds xzr, x11, #1
  movi v4.2d, #0x000000ffffffff
        adcs x19, x19, x13
  ext v1.16b, v7.16b, v7.16b, #8
        adcs x20, x20, x12
  shrn v2.2s, v7.2d, #32
        adc x21, x21, x11
  zip1 v0.2s, v7.2s, v1.2s
        adds x17, x17, x17
        adcs x19, x19, x19
        adcs x20, x20, x20
        adcs x21, x21, x21
        adc x10, xzr, xzr
mov x12, v3.d[0]
mov x11, v5.d[0]
        mul x15, x6, x7
mov x13, v3.d[1]
        umulh x16, x6, x7
mov x14, v5.d[1]
        adds x11, x11, x15
  umull v5.2d, v2.2s, v2.2s
        adcs x13, x13, x16
  umull v6.2d, v2.2s, v0.2s
        adc x14, x14, xzr
  umull v3.2d, v0.2s, v0.2s
        adds x11, x11, x15
  mov v1.16b, v6.16b
        adcs x13, x13, x16
  usra v1.2d, v3.2d, #32
        adc x14, x14, xzr
  and v4.16b, v1.16b, v4.16b

        stp x12, x11, [z, #64]
  add v4.2d, v4.2d, v6.2d
        adds x17, x17, x13
  usra v5.2d, v4.2d, #32
        adcs x19, x19, x14
  sli v3.2d, v4.2d, #32
        adcs x20, x20, xzr
  usra v5.2d, v1.2d, #32
        adcs x21, x21, xzr
  mov x12, v3.d[0]
        adc x10, x10, xzr
  mov x11, v5.d[0]
        stp x17, x19, [z, #80]
  mov x13, v3.d[1]

        mul x15, x8, x9
  mov x14, v5.d[1]
        umulh x16, x8, x9
        adds x11, x11, x15
        adcs x13, x13, x16
        adc x14, x14, xzr
        adds x11, x11, x15
        adcs x13, x13, x16
        adc x14, x14, xzr
        adds x12, x12, x20
        adcs x11, x11, x21
        stp x12, x11, [z,#96]
        adcs x13, x13, x10
        adc x14, x14, xzr
        stp x13, x14, [z,#112]
// Now get the cross-product in [s7,...,s0] and double it as [c,s7,...,s0]

        mul4

        adds    s0, s0, s0
        adcs    s1, s1, s1
        adcs    s2, s2, s2
        adcs    s3, s3, s3
        adcs    s4, s4, s4
        adcs    s5, s5, s5
        adcs    s6, s6, s6
        adcs    s7, s7, s7
        adc     c, xzr, xzr

// Add it back to the buffer

        ldp     a0, a1, [z, #32]
        adds    s0, s0, a0
        adcs    s1, s1, a1
        stp     s0, s1, [z, #32]

        ldp     a0, a1, [z, #48]
        adcs    s2, s2, a0
        adcs    s3, s3, a1
        stp     s2, s3, [z, #48]

        ldp     a0, a1, [z, #64]
        adcs    s4, s4, a0
        adcs    s5, s5, a1
        stp     s4, s5, [z, #64]

        ldp     a0, a1, [z, #80]
        adcs    s6, s6, a0
        adcs    s7, s7, a1
        stp     s6, s7, [z, #80]

        ldp     a0, a1, [z, #96]
        adcs    a0, a0, c
        adcs    a1, a1, xzr
        stp     a0, a1, [z, #96]

        ldp     a0, a1, [z, #112]
        adcs    a0, a0, xzr
        adc     a1, a1, xzr
        stp     a0, a1, [z, #112]

// Restore regs and return

        ldp     x21, x22, [sp], #16
        ldp     x19, x20, [sp], #16

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif

