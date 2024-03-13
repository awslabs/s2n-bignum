// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Montgomery multiply, z := (x * y / 2^256) mod p_256
// Inputs x[4], y[4]; output z[4]
//
//    extern void bignum_montmul_p256_neon
//     (uint64_t z[static 4], uint64_t x[static 4], uint64_t y[static 4]);
//
// Does z := (2^{-256} * x * y) mod p_256, assuming that the inputs x and y
// satisfy x * y <= 2^256 * p_256 (in particular this is true if we are in
// the "usual" case x < p_256 and y < p_256).
//
// Standard ARM ABI: X0 = z, X1 = x, X2 = y
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(bignum_montmul_p256_neon)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(bignum_montmul_p256_neon)
        .text
        .balign 4

S2N_BN_SYMBOL(bignum_montmul_p256_neon):

        ldr q20, [x2]
        ldp x7, x17, [x1]
        ldr q0, [x1]
        ldp x6, x10, [x2]
        ldp x11, x15, [x1, #16]
        rev64 v16.4S, v20.4S
        subs x4, x7, x17
        csetm x3, cc
        cneg x13, x4, cc
        mul v16.4S, v16.4S, v0.4S
        umulh x12, x17, x10
        uzp1 v28.4S, v20.4S, v0.4S
        subs x14, x11, x7
        ldr q20, [x2, #16]
        sbcs x5, x15, x17
        ngc x17, xzr
        subs x8, x11, x15
        uaddlp v27.2D, v16.4S
        umulh x4, x7, x6
        uzp1 v21.4S, v0.4S, v0.4S
        cneg x11, x8, cc
        shl v17.2D, v27.2D, #32
        csetm x15, cc
        subs x9, x10, x6
        eor x7, x14, x17
        umlal v17.2D, v21.2S, v28.2S
        cneg x8, x9, cc
        cinv x9, x3, cc
        cmn x17, #0x1
        ldr q28, [x1, #16]
        adcs x14, x7, xzr
        mul x7, x13, x8
        eor x1, x5, x17
        adcs x5, x1, xzr
        xtn v1.2S, v20.2D
        mov x1, v17.d[0]
        mov x3, v17.d[1]
        uzp2 v16.4S, v20.4S, v20.4S
        umulh x16, x13, x8
        eor x13, x7, x9
        adds x8, x1, x3
        adcs x7, x4, x12
        xtn v0.2S, v28.2D
        adcs x12, x12, xzr
        adds x8, x4, x8
        adcs x3, x3, x7
        ldp x7, x2, [x2, #16]
        adcs x12, x12, xzr
        cmn x9, #0x1
        adcs x8, x8, x13
        eor x13, x16, x9
        adcs x16, x3, x13
        lsl x3, x1, #32
        adc x13, x12, x9
        subs x12, x6, x7
        sbcs x9, x10, x2
        lsr x10, x1, #32
        ngc x4, xzr
        subs x6, x2, x7
        cinv x2, x15, cc
        cneg x6, x6, cc
        subs x7, x1, x3
        eor x9, x9, x4
        sbc x1, x1, x10
        adds x15, x8, x3
        adcs x3, x16, x10
        mul x16, x11, x6
        adcs x8, x13, x7
        eor x13, x12, x4
        adc x10, x1, xzr
        cmn x4, #0x1
        umulh x6, x11, x6
        adcs x11, x13, xzr
        adcs x1, x9, xzr
        lsl x13, x15, #32
        subs x12, x15, x13
        lsr x7, x15, #32
        sbc x15, x15, x7
        adds x9, x3, x13
        adcs x3, x8, x7
        umulh x8, x14, x11
        umull v21.2D, v0.2S, v1.2S
        adcs x12, x10, x12
        umull v3.2D, v0.2S, v16.2S
        adc x15, x15, xzr
        rev64 v24.4S, v20.4S
        stp x12, x15, [x0, #16]
        movi v2.2D, #0x00000000ffffffff
        mul x10, x14, x11
        mul v4.4S, v24.4S, v28.4S
        subs x13, x14, x5
        uzp2 v19.4S, v28.4S, v28.4S
        csetm x15, cc
        usra v3.2D, v21.2D, #32
        mul x7, x5, x1
        umull v21.2D, v19.2S, v16.2S
        cneg x13, x13, cc
        uaddlp v5.2D, v4.4S
        subs x11, x1, x11
        and v16.16B, v3.16B, v2.16B
        umulh x5, x5, x1
        shl v24.2D, v5.2D, #32
        cneg x11, x11, cc
        umlal v16.2D, v19.2S, v1.2S
        cinv x12, x15, cc
        umlal v24.2D, v0.2S, v1.2S
        adds x15, x10, x7
        mul x14, x13, x11
        eor x1, x6, x2
        adcs x6, x8, x5
        stp x9, x3, [x0]
        usra v21.2D, v3.2D, #32
        adcs x9, x5, xzr
        umulh x11, x13, x11
        adds x15, x8, x15
        adcs x7, x7, x6
        eor x8, x14, x12
        usra v21.2D, v16.2D, #32
        adcs x13, x9, xzr
        cmn x12, #0x1
        mov x9, v24.d[1]
        adcs x14, x15, x8
        eor x6, x11, x12
        adcs x6, x7, x6
        mov x5, v24.d[0]
        mov x11, v21.d[1]
        mov x7, v21.d[0]
        adc x3, x13, x12
        adds x12, x5, x9
        adcs x13, x7, x11
        ldp x15, x8, [x0]
        adcs x11, x11, xzr
        adds x12, x7, x12
        eor x16, x16, x2
        adcs x7, x9, x13
        adcs x11, x11, xzr
        cmn x2, #0x1
        ldp x9, x13, [x0, #16]
        adcs x16, x12, x16
        adcs x1, x7, x1
        adc x2, x11, x2
        adds x7, x5, x15
        adcs x15, x16, x8
        eor x5, x17, x4
        adcs x9, x1, x9
        eor x1, x10, x5
        adcs x16, x2, x13
        adc x2, xzr, xzr
        cmn x5, #0x1
        eor x13, x14, x5
        adcs x14, x1, x7
        eor x1, x6, x5
        adcs x6, x13, x15
        adcs x10, x1, x9
        eor x4, x3, x5
        mov x1, #0xffffffff
        adcs x8, x4, x16
        lsr x13, x14, #32
        adcs x17, x2, x5
        adcs x11, x5, xzr
        adc x4, x5, xzr
        adds x12, x10, x7
        adcs x7, x8, x15
        adcs x5, x17, x9
        adcs x9, x11, x16
        lsl x11, x14, #32
        adc x10, x4, x2
        subs x17, x14, x11
        sbc x4, x14, x13
        adds x11, x6, x11
        adcs x12, x12, x13
        lsl x15, x11, #32
        adcs x17, x7, x17
        lsr x7, x11, #32
        adc x13, x4, xzr
        subs x4, x11, x15
        sbc x11, x11, x7
        adds x8, x12, x15
        adcs x15, x17, x7
        adcs x4, x13, x4
        adc x11, x11, xzr
        adds x7, x5, x4
        adcs x17, x9, x11
        adc x13, x10, xzr
        add x12, x13, #0x1
        neg x11, x12
        lsl x4, x12, #32
        adds x17, x17, x4
        sub x4, x4, #0x1
        adc x13, x13, xzr
        subs x11, x8, x11
        sbcs x4, x15, x4
        sbcs x7, x7, xzr
        sbcs x17, x17, x12
        sbcs x13, x13, x12
        mov x12, #0xffffffff00000001
        adds x11, x11, x13
        and x1, x1, x13
        adcs x4, x4, x1
        and x1, x12, x13
        stp x11, x4, [x0]
        adcs x4, x7, xzr
        adc x1, x17, x1
        stp x4, x1, [x0, #16]
        ret

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack,"",%progbits
#endif
