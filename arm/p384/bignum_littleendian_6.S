// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Convert 6-digit (384-bit) bignum to/from little-endian form
// Input x[6]; output z[6]
//
//    extern void bignum_littleendian_6(uint64_t z[static 6],
//                                      const uint64_t x[static 6]);
//
// The same function is given two other prototypes whose names reflect the
// treatment of one or other argument as a byte array rather than word array:
//
//    extern void bignum_fromlebytes_6(uint64_t z[static 6],
//                                     const uint8_t x[static 48]);
//
//    extern void bignum_tolebytes_6(uint8_t z[static 48],
//                                   const uint64_t x[static 6]);
//
// The implementation works by loading in bytes and storing in words (i.e.
// stylistically it is "fromlebytes"); in the more common little-endian
// usage of ARM, this is just copying.
//
// Standard ARM ABI: X0 = z, X1 = x
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_littleendian_6)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_littleendian_6)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_fromlebytes_6)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_fromlebytes_6)
        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_tolebytes_6)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_tolebytes_6)

        .text
        .balign 4

#define z x0
#define x x1

#define d x2
#define dshort w2
#define a x3

S2N_BN_SYMBOL(bignum_littleendian_6):
S2N_BN_SYMBOL(bignum_fromlebytes_6):
S2N_BN_SYMBOL(bignum_tolebytes_6):

// word 0

        ldrb    dshort, [x]
        extr    a, d, xzr, #8
        ldrb    dshort, [x, #1]
        extr    a, d, a, #8
        ldrb    dshort, [x, #2]
        extr    a, d, a, #8
        ldrb    dshort, [x, #3]
        extr    a, d, a, #8
        ldrb    dshort, [x, #4]
        extr    a, d, a, #8
        ldrb    dshort, [x, #5]
        extr    a, d, a, #8
        ldrb    dshort, [x, #6]
        extr    a, d, a, #8
        ldrb    dshort, [x, #7]
        extr    a, d, a, #8
        str     a, [z]

// word 1

        ldrb    dshort, [x, #8]
        extr    a, d, xzr, #8
        ldrb    dshort, [x, #9]
        extr    a, d, a, #8
        ldrb    dshort, [x, #10]
        extr    a, d, a, #8
        ldrb    dshort, [x, #11]
        extr    a, d, a, #8
        ldrb    dshort, [x, #12]
        extr    a, d, a, #8
        ldrb    dshort, [x, #13]
        extr    a, d, a, #8
        ldrb    dshort, [x, #14]
        extr    a, d, a, #8
        ldrb    dshort, [x, #15]
        extr    a, d, a, #8
        str     a, [z, #8]

// word 2

        ldrb    dshort, [x, #16]
        extr    a, d, xzr, #8
        ldrb    dshort, [x, #17]
        extr    a, d, a, #8
        ldrb    dshort, [x, #18]
        extr    a, d, a, #8
        ldrb    dshort, [x, #19]
        extr    a, d, a, #8
        ldrb    dshort, [x, #20]
        extr    a, d, a, #8
        ldrb    dshort, [x, #21]
        extr    a, d, a, #8
        ldrb    dshort, [x, #22]
        extr    a, d, a, #8
        ldrb    dshort, [x, #23]
        extr    a, d, a, #8
        str     a, [z, #16]

// word 3

        ldrb    dshort, [x, #24]
        extr    a, d, xzr, #8
        ldrb    dshort, [x, #25]
        extr    a, d, a, #8
        ldrb    dshort, [x, #26]
        extr    a, d, a, #8
        ldrb    dshort, [x, #27]
        extr    a, d, a, #8
        ldrb    dshort, [x, #28]
        extr    a, d, a, #8
        ldrb    dshort, [x, #29]
        extr    a, d, a, #8
        ldrb    dshort, [x, #30]
        extr    a, d, a, #8
        ldrb    dshort, [x, #31]
        extr    a, d, a, #8
        str     a, [z, #24]

// word 4

        ldrb    dshort, [x, #32]
        extr    a, d, xzr, #8
        ldrb    dshort, [x, #33]
        extr    a, d, a, #8
        ldrb    dshort, [x, #34]
        extr    a, d, a, #8
        ldrb    dshort, [x, #35]
        extr    a, d, a, #8
        ldrb    dshort, [x, #36]
        extr    a, d, a, #8
        ldrb    dshort, [x, #37]
        extr    a, d, a, #8
        ldrb    dshort, [x, #38]
        extr    a, d, a, #8
        ldrb    dshort, [x, #39]
        extr    a, d, a, #8
        str     a, [z, #32]

// word 5

        ldrb    dshort, [x, #40]
        extr    a, d, xzr, #8
        ldrb    dshort, [x, #41]
        extr    a, d, a, #8
        ldrb    dshort, [x, #42]
        extr    a, d, a, #8
        ldrb    dshort, [x, #43]
        extr    a, d, a, #8
        ldrb    dshort, [x, #44]
        extr    a, d, a, #8
        ldrb    dshort, [x, #45]
        extr    a, d, a, #8
        ldrb    dshort, [x, #46]
        extr    a, d, a, #8
        ldrb    dshort, [x, #47]
        extr    a, d, a, #8
        str     a, [z, #40]

        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
