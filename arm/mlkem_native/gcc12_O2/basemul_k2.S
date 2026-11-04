// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Scalar product of 2-element polynomial vectors in NTT domain, with mulcache
// Inputs a[512], b[512], bt[256] (signed 16-bit words); output r[256]
//
// The inputs a and b are considered as 2-element vectors of linear
// polynomials in the NTT domain (in Montgomery form), and the bt
// argument an analogous 2-element vector of mulcaches for the bi.
// This is the same operation as mlkem_basemul_k2, but this is the code
// for mlkem512_polyvec_basemul_acc_montgomery_cached from mlkem-native's
// portable C implementation as compiled by gcc 12.3.0 with -O2 (see
// README.md for details).
//
// All input elements are assumed <= 2^12 and the bts are
// assumed to be as computed by mlkem_mulcache_compute.
//
// extern void mlkem_native_basemul_k2_gcc12_O2
//      (int16_t r[static 256],const int16_t a[static 512],
//       const int16_t b[static 512], const int16_t bt[static 256]);
//
// Standard ARM ABI: X0 = r, X1 = a, X2 = b, X3 = bt
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_basemul_k2_gcc12_O2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_native_basemul_k2_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_basemul_k2_gcc12_O2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_basemul_k2_gcc12_O2):
        CFI_START

        mov     x4, x1
        mov     x7, x0
        mov     x5, x2
        mov     x6, x3
        add     x13, x1, #0x200
        mov     w12, #0xfffff301
        mov     w11, #0xfffff2ff
        nop
Lmlkem_native_basemul_k2_gcc12_O2_loop:
        ldrsh   w16, [x4, #2]
        add     x4, x4, #0x4
        ldrsh   w0, [x5]
        add     x6, x6, #0x2
        ldrsh   w1, [x5, #512]
        add     x7, x7, #0x4
        ldursh  w10, [x4, #-4]
        add     x5, x5, #0x4
        ldrsh   w15, [x4, #510]
        ldrsh   w14, [x4, #508]
        ldursh  w3, [x6, #-2]
        ldrsh   w9, [x6, #254]
        mul     w18, w10, w0
        ldrsh   w2, [x5, #510]
        mul     w0, w16, w0
        ldursh  w8, [x5, #-2]
        mul     w17, w14, w1
        mul     w1, w15, w1
        madd    w3, w3, w16, w18
        madd    w2, w2, w14, w1
        madd    w0, w8, w10, w0
        madd    w9, w9, w15, w17
        add     w2, w2, w0
        add     w3, w3, w9
        mul     w0, w2, w12
        mul     w1, w3, w12
        sxth    w0, w0
        sxth    w1, w1
        madd    w0, w0, w11, w2
        madd    w1, w1, w11, w3
        asr     w0, w0, #16
        sturh   w0, [x7, #-2]
        asr     w1, w1, #16
        sturh   w1, [x7, #-4]
        cmp     x4, x13
        b.ne    Lmlkem_native_basemul_k2_gcc12_O2_loop
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_native_basemul_k2_gcc12_O2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
