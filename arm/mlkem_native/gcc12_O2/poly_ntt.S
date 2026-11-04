// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Forward number-theoretic transform from ML-KEM
// Input a[256] (signed 16-bit words); output a[256] (signed 16-bit words)
//
// The transform is in-place with input and output a[256], with the output
// in bitreversed order. This is the same operation as mlkem_ntt, but this
// is the code for mlkem_poly_ntt from mlkem-native's portable C
// implementation as compiled by gcc 12.3.0 with -O2 (see README.md for
// details). It uses its own table of zetas, which is the mlk_zetas array
// in mlkem-native, instead of taking tables as arguments.
//
// extern void mlkem_native_poly_ntt_gcc12_O2(int16_t a[static 256]);
//
// Standard ARM ABI: X0 = a
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_poly_ntt_gcc12_O2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_native_poly_ntt_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_poly_ntt_gcc12_O2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_poly_ntt_gcc12_O2):
        CFI_START

#if defined(__ELF__)
        adrp    x12, mlk_zetas
#else
        adrp    x12, mlk_zetas@PAGE
#endif
        mov     x13, x0
#if defined(__ELF__)
        add     x12, x12, :lo12:mlk_zetas
#else
        add     x12, x12, mlk_zetas@PAGEOFF
#endif
        add     x14, x0, #0x2
        mov     w7, #0x0
        mov     w8, #0xfffffd0a
        mov     w16, #0x1
        mov     w17, #0x100
        mov     w11, #0xfffff301
        mov     w10, #0xfffff2ff
        nop
Lmlkem_native_poly_ntt_gcc12_O2_layer:
        add     w15, w7, #0x1
        mov     w4, #0x0
        lsl     w7, w16, w7
        lsr     w6, w17, w15
        lsl     w9, w6, #1
        nop
Lmlkem_native_poly_ntt_gcc12_O2_block:
        add     w7, w7, #0x1
        cmp     w6, w4
        b.ls    Lmlkem_native_poly_ntt_gcc12_O2_blockend
        sub     w2, w6, w4
        mov     w0, w4
        sub     w2, w2, #0x1
        mov     w3, w6
        add     x2, x2, x0
        sub     x3, x3, x0
        add     x1, x13, w4, uxtw #1
        add     x2, x14, x2, lsl #1
        nop
Lmlkem_native_poly_ntt_gcc12_O2_butterfly:
        ldrsh   w5, [x1, x3, lsl #1]
        ldrh    w18, [x1]
        mul     w5, w5, w8
        mul     w0, w5, w11
        sxth    w0, w0
        madd    w0, w0, w10, w5
        asr     w0, w0, #16
        sub     w5, w18, w0
        strh    w5, [x1, x3, lsl #1]
        ldrh    w5, [x1]
        add     w0, w0, w5
        strh    w0, [x1], #2
        cmp     x2, x1
        b.ne    Lmlkem_native_poly_ntt_gcc12_O2_butterfly
Lmlkem_native_poly_ntt_gcc12_O2_blockend:
        add     w4, w4, w9
        add     w6, w6, w9
        cmp     w4, #0xff
        b.hi    Lmlkem_native_poly_ntt_gcc12_O2_layerend
        ldrsh   w8, [x12, w7, uxtw #1]
        b       Lmlkem_native_poly_ntt_gcc12_O2_block
Lmlkem_native_poly_ntt_gcc12_O2_layerend:
        cmp     w15, #0x7
        b.eq    Lmlkem_native_poly_ntt_gcc12_O2_end
        lsl     w0, w16, w15
        mov     w7, w15
        ldrsh   w8, [x12, x0, lsl #1]
        b       Lmlkem_native_poly_ntt_gcc12_O2_layer
Lmlkem_native_poly_ntt_gcc12_O2_end:
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_native_poly_ntt_gcc12_O2)

// The table mlk_zetas from mlkem-native

#if defined(__ELF__)
        .section .rodata
#elif defined(__APPLE__)
        .const_data
#endif
        .balign 32
#if defined(__ELF__)
        .type   mlk_zetas, %object
        .size   mlk_zetas, 256
#endif
mlk_zetas:
        .short  -1044, -758, -359, -1517, 1493, 1422, 287, 202
        .short  -171, 622, 1577, 182, 962, -1202, -1474, 1468
        .short  573, -1325, 264, 383, -829, 1458, -1602, -130
        .short  -681, 1017, 732, 608, -1542, 411, -205, -1571
        .short  1223, 652, -552, 1015, -1293, 1491, -282, -1544
        .short  516, -8, -320, -666, -1618, -1162, 126, 1469
        .short  -853, -90, -271, 830, 107, -1421, -247, -951
        .short  -398, 961, -1508, -725, 448, -1065, 677, -1275
        .short  -1103, 430, 555, 843, -1251, 871, 1550, 105
        .short  422, 587, 177, -235, -291, -460, 1574, 1653
        .short  -246, 778, 1159, -147, -777, 1483, -602, 1119
        .short  -1590, 644, -872, 349, 418, 329, -156, -75
        .short  817, 1097, 603, 610, 1322, -1285, -1465, 384
        .short  -1215, -136, 1218, -1335, -874, 220, -1187, -1659
        .short  -1185, -1530, -1278, 794, -1510, -854, -870, 478
        .short  -108, -308, 996, 991, 958, -1460, 1522, 1628

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
