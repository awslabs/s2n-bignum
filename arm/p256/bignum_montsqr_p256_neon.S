// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery square, z := (x^2 / 2^256) mod p_256
// Input x[4]; output z[4]
//
//    extern void bignum_montsqr_p256_neon
//     (uint64_t z[static 4], uint64_t x[static 4]);
//
// Does z := (x^2 / 2^256) mod p_256, assuming x^2 <= 2^256 * p_256, which is
// guaranteed in particular if x < p_256 initially (the "intended" case).
//
// Standard ARM ABI: X0 = z, X1 = x
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montsqr_p256_neon)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montsqr_p256_neon)
        .text
        .balign 4

S2N_BN_SYMBOL(bignum_montsqr_p256):

        ldp x12, x3, [x1]
        ldr q31, [x1]
        ldr q29, [x1, #16]
        ldp x9, x8, [x1, #16]
        mul x11, x12, x3
        subs x14, x12, x3
        umull2 v25.2D, v31.4S, v31.4S
        cneg x17, x14, cc
        xtn v24.2S, v31.2D
        csetm x14, cc
        uzp2 v6.4S, v31.4S, v31.4S
        umulh x10, x12, x3
        rev64 v7.4S, v29.4S
        subs x6, x8, x9
        umull v24.2D, v6.2S, v24.2S
        mov x7, v25.d[1]
        umull v6.2D, v31.2S, v31.2S
        mov x4, v25.d[0]
        ldr q23, [x1]
        cneg x2, x6, cc
        lsr x16, x10, #63
        extr x13, x10, x11, #63
        umulh x12, x12, x9
        mov x5, v24.d[0]
        mov x10, v6.d[1]
        mov x6, v6.d[0]
        lsr x15, x5, #31
        cinv x1, x14, cc
        mov x14, v24.d[1]
        adds x5, x6, x5, lsl #33
        adc x10, x10, x15
        lsl x6, x5, #32
        lsr x15, x14, #31
        adds x14, x4, x14, lsl #33
        uzp1 v24.4S, v29.4S, v23.4S
        lsr x4, x5, #32
        mul v29.4S, v7.4S, v23.4S
        adc x7, x7, x15
        adds x15, x10, x11, lsl #1
        mul x11, x17, x2
        uzp1 v16.4S, v23.4S, v23.4S
        adcs x14, x14, x13
        adc x16, x7, x16
        subs x7, x5, x6
        uaddlp v23.2D, v29.4S
        sbc x5, x5, x4
        umulh x13, x17, x2
        adds x6, x15, x6
        shl v29.2D, v23.2D, #32
        adcs x17, x14, x4
        adcs x4, x16, x7
        lsl x14, x6, #32
        umlal v29.2D, v16.2S, v24.2S
        adc x16, x5, xzr
        umulh x10, x3, x8
        lsr x5, x6, #32
        subs x15, x6, x14
        sbc x6, x6, x5
        adds x2, x17, x14
        adcs x17, x4, x5
        mov x4, v29.d[0]
        adcs x7, x16, x15
        mov x16, v29.d[1]
        adc x3, x6, xzr
        adds x6, x4, x12
        adc x14, x12, xzr
        adds x15, x6, x16
        eor x5, x11, x1
        adcs x6, x14, x10
        adc x10, x10, xzr
        adds x11, x6, x16
        adc x6, x10, xzr
        cmn x1, #0x1
        adcs x16, x15, x5
        eor x14, x13, x1
        umulh x10, x9, x8
        adcs x15, x11, x14
        adc x6, x6, x1
        adds x14, x4, x4
        adcs x5, x16, x16
        adcs x4, x15, x15
        mul x11, x9, x8
        adcs x6, x6, x6
        adc x13, xzr, xzr
        adds x2, x14, x2
        lsr x16, x2, #32
        adcs x15, x5, x17
        umulh x17, x9, x9
        adcs x1, x4, x7
        adcs x7, x6, x3
        lsl x14, x2, #32
        adc x12, x13, xzr
        subs x5, x2, x14
        sbc x6, x2, x16
        adds x14, x15, x14
        umulh x13, x8, x8
        adcs x1, x1, x16
        lsr x16, x14, #32
        adcs x5, x7, x5
        adcs x12, x12, x6
        lsl x7, x14, #32
        adc x4, xzr, xzr
        subs x2, x14, x7
        sbc x14, x14, x16
        adds x3, x11, x11
        adcs x10, x10, x10
        mul x11, x9, x9
        adc x9, xzr, xzr
        adds x1, x1, x7
        adcs x15, x5, x16
        mul x6, x8, x8
        adcs x5, x12, x2
        adcs x14, x4, x14
        adc x8, xzr, xzr
        adds x11, x1, x11
        adcs x1, x15, x17
        adcs x5, x5, x6
        adcs x14, x14, x13
        adc x6, x8, xzr
        adds x7, x1, x3
        adcs x4, x5, x10
        adcs x15, x14, x9
        mov x5, #0xffffffff
        adcs x14, x6, xzr
        adds x16, x11, #0x1
        sbcs x5, x7, x5
        mov x13, #0xffffffff00000001
        sbcs x1, x4, xzr
        sbcs x8, x15, x13
        sbcs xzr, x14, xzr
        csel x6, x1, x4, cs
        csel x14, x8, x15, cs
        stp x6, x14, [x0, #16]
        csel x5, x5, x7, cs
        csel x15, x16, x11, cs
        stp x15, x5, [x0]
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
