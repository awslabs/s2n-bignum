// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert from almost-Montgomery form, z := (x / 2^256) mod p_256
// Input x[4]; output z[4]
//
//    extern void bignum_deamont_p256(uint64_t z[static 4],
//                                    const uint64_t x[static 4]);
//
// Convert a 4-digit bignum x out of its (optionally almost) Montgomery form,
// "almost" meaning any 4-digit input will work, with no range restriction.
//
// Standard ARM ABI: X0 = z, X1 = x
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_deamont_p256)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_deamont_p256)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_deamont_p256_alt)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_deamont_p256_alt)
        .text
        .balign 4

// ---------------------------------------------------------------------------
// Core one-step "short" Montgomery reduction macro. Takes input in
// [d3;d2;d1;d0] and returns result in [d4;d3;d2;d1], adding to the
// existing contents of [d3;d2;d1] and generating d4 from zero, re-using
// d0 as a temporary internally together with t0, t1 and t2.
// It is fine for d4 to be the same register as d0, and it often is.
// ---------------------------------------------------------------------------

#define montreds(d4,d3,d2,d1,d0, t2,t1,t0)                                  \
/* Let w = d0, the original word we use as offset; d0 gets recycled      */ \
/* First let [t2;t1] = 2^32 * w                                          */ \
/* then let [d0;t0] = (2^64 - 2^32 + 1) * w (overwrite old d0)           */ \
        lsl     t1, d0, #32 __LF                                       \
        subs    t0, d0, t1 __LF                                        \
        lsr     t2, d0, #32 __LF                                       \
        sbc     d0, d0, t2 __LF                                        \
/* Hence [d4;..;d1] := [d3;d2;d1;0] + (2^256 - 2^224 + 2^192 + 2^96) * w */ \
        adds    d1, d1, t1 __LF                                        \
        adcs    d2, d2, t2 __LF                                        \
        adcs    d3, d3, t0 __LF                                        \
        adc     d4, d0, xzr

// Input parameters

#define z x0
#define x x1

// Rotating registers for the intermediate windows (with repetitions)

#define d0 x2
#define d1 x3
#define d2 x4
#define d3 x5

// Other temporaries

#define u x6
#define v x7
#define w x8

S2N_BN_SYMBOL(bignum_deamont_p256):

S2N_BN_SYMBOL(bignum_deamont_p256_alt):

// Set up an initial window with the input x and an extra leading zero

        ldp     d0, d1, [x]
        ldp     d2, d3, [x, #16]

// Systematically scroll left doing 1-step reductions

        montreds(d0,d3,d2,d1,d0, u,v,w)

        montreds(d1,d0,d3,d2,d1, u,v,w)

        montreds(d2,d1,d0,d3,d2, u,v,w)

        montreds(d3,d2,d1,d0,d3, u,v,w)

// Now compare end result in [d3;d2;d1;d0] with p_256 = [w; 0; v; -1]

        mov     v, #0x00000000ffffffff
        mov     w, #0xffffffff00000001

        subs    xzr, d0, #-1
        sbcs    xzr, d1, v
        sbcs    xzr, d2, xzr
        sbcs    xzr, d3, w

// Convert the condition [d3;d2;d1;d0] >= p_256 into a bitmask
// and do a masked subtraction

        csetm   u, cs

        subs    d0, d0, u
        and     v, v, u
        sbcs    d1, d1, v
        sbcs    d2, d2, xzr
        and     w, w, u
        sbc     d3, d3, w

// Write back result

        stp     d0, d1, [z]
        stp     d2, d3, [z, #16]

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
