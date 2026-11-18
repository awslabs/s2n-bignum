// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Scalar product of 3-element polynomial vectors in NTT domain, with mulcache
// Inputs a[768], b[768], bt[384] (signed 16-bit words); output r[256]
//
// The inputs a and b are considered as 3-element vectors of linear
// polynomials in the NTT domain (in Montgomery form), and the bt
// argument an analogous 3-element vector of mulcaches for the bi.
// This is the same operation as mlkem_basemul_k3, but this is the code
// for mlkem768_polyvec_basemul_acc_montgomery_cached from mlkem-native's
// portable C implementation as compiled by gcc 12.3.0 with -O2 (see
// README.md for details).
//
// All input elements are assumed <= 2^12 and the bts are
// assumed to be as computed by mlkem_mulcache_compute.
//
// extern void mlkem_native_basemul_k3_gcc12_O2
//      (int16_t r[static 256],const int16_t a[static 768],
//       const int16_t b[static 768], const int16_t bt[static 384]);
//
// Standard ARM ABI: X0 = r, X1 = a, X2 = b, X3 = bt
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_basemul_k3_gcc12_O2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_native_basemul_k3_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_basemul_k3_gcc12_O2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_basemul_k3_gcc12_O2):
        CFI_START

        add     x7, x0, #0x2
        mov     x6, x1
        add     x5, x2, #0x2
        add     x17, x3, #0x100
        mov     w10, #0xfffff301
        mov     w9, #0xfffff2ff
Lmlkem_native_basemul_k3_gcc12_O2_loop0:
        mov     x1, x3
        add     x14, x6, #0x2
        sub     x13, x5, #0x2
        mov     x0, #0x0
        mov     w4, #0x0
        mov     w2, #0x0
Lmlkem_native_basemul_k3_gcc12_O2_loop1:
        ldrsh   w16, [x14, x0]
        add     x1, x1, #0x100
        ldrsh   w15, [x6, x0]
        ldrsh   w8, [x13, x0]
        ldrsh   w11, [x5, x0]
        add     x0, x0, #0x200
        ldursh  w12, [x1, #-256]
        mul     w18, w15, w8
        mul     w8, w16, w8
        madd    w12, w12, w16, w18
        madd    w8, w11, w15, w8
        add     w2, w2, w12
        add     w4, w4, w8
        cmp     x0, #0x600
        b.ne    Lmlkem_native_basemul_k3_gcc12_O2_loop1
        mul     w1, w2, w10
        add     x3, x3, #0x2
        mul     w0, w4, w10
        add     x6, x6, #0x4
        add     x5, x5, #0x4
        sxth    w1, w1
        sxth    w0, w0
        madd    w1, w1, w9, w2
        madd    w0, w0, w9, w4
        asr     w1, w1, #16
        sturh   w1, [x7, #-2]
        asr     w0, w0, #16
        strh    w0, [x7], #4
        cmp     x17, x3
        b.ne    Lmlkem_native_basemul_k3_gcc12_O2_loop0
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_native_basemul_k3_gcc12_O2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
