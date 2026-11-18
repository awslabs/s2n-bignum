// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Inverse number-theoretic transform from ML-KEM
// Input a[256] (signed 16-bit words); output a[256] (signed 16-bit words)
//
// The transform is in-place with input and output a[256], with the input in
// bitreversed order and the output mapped into the Montgomery domain via
// x |-> (2^16 * x) mod 3329. This is the same operation as mlkem_intt, but
// this is the code for mlkem_poly_invntt_tomont from mlkem-native's portable
// C implementation as compiled by gcc 12.3.0 with -O2 (see README.md for
// details). It starts by scaling the coefficients in a loop that the
// compiler has vectorized, using its own vectors of constants, which are the
// anonymous constants at addresses 0x6230 and 0x6240 in the binary. It then
// uses its own table of zetas, which is the mlk_zetas array in mlkem-native,
// instead of taking tables as arguments.
//
// extern void mlkem_native_poly_invntt_tomont_gcc12_O2(int16_t a[static 256]);
//
// Standard ARM ABI: X0 = a
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_poly_invntt_tomont_gcc12_O2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_native_poly_invntt_tomont_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_poly_invntt_tomont_gcc12_O2)
        .text
        .balign 4

// The two tables are separate objects, so that the proofs can allow them
// to be anywhere, as they are in the binary. For ELF they are given global
// (but hidden) symbols, since references to local symbols would become
// references to the section as a whole.

#define CONSTANTS mlkem_native_poly_invntt_tomont_gcc12_O2_constants
#define ZETAS mlkem_native_poly_invntt_tomont_gcc12_O2_zetas

S2N_BN_SYMBOL(mlkem_native_poly_invntt_tomont_gcc12_O2):
        CFI_START

        mov     x15, x0
#if defined(__ELF__)
        adrp    x0, CONSTANTS+16
#else
        adrp    x0, CONSTANTS@PAGE+16
#endif
        mvni    v3.8h, #0xd, lsl #8
        add     x1, x15, #0x200
#if defined(__ELF__)
        ldr     q4, [x0, :lo12:CONSTANTS+16]
        adrp    x0, CONSTANTS
#else
        ldr     q4, [x0, CONSTANTS@PAGEOFF+16]
        adrp    x0, CONSTANTS@PAGE
#endif
        CFI_PUSH2(x19,x30)
#if defined(__ELF__)
        ldr     q5, [x0, :lo12:CONSTANTS]
#else
        ldr     q5, [x0, CONSTANTS@PAGEOFF]
#endif
        mov     x0, x15
Lmlkem_native_poly_invntt_tomont_gcc12_O2_scale:
        ldr     q0, [x0]
        smull   v1.4s, v0.4h, v4.4h
        smull2  v0.4s, v0.8h, v4.8h
        uzp1    v2.8h, v1.8h, v0.8h
        mul     v2.8h, v2.8h, v5.8h
        smlal   v1.4s, v2.4h, v3.4h
        smlal2  v0.4s, v2.8h, v3.8h
        uzp2    v1.8h, v1.8h, v0.8h
        str     q1, [x0], #16
        cmp     x1, x0
        b.ne    Lmlkem_native_poly_invntt_tomont_gcc12_O2_scale
#if defined(__ELF__)
        adrp    x14, ZETAS
#else
        adrp    x14, ZETAS@PAGE
#endif
        add     x16, x15, #0x2
#if defined(__ELF__)
        add     x14, x14, :lo12:ZETAS
#else
        add     x14, x14, ZETAS@PAGEOFF
#endif
        mov     w9, #0x65c
        mov     w17, #0x7
        mov     w30, #0x100
        mov     w18, #0x1
        mov     w13, #0x4ebf
        mov     w12, #0x2000000
        mov     w8, #0xfffff2ff
        mov     w11, #0xfffff301
Lmlkem_native_poly_invntt_tomont_gcc12_O2_layer:
        lsr     w5, w30, w17
        mov     w6, #0x0
        lsl     w7, w18, w17
        lsl     w10, w5, #1
        sub     w7, w7, #0x1
        nop
Lmlkem_native_poly_invntt_tomont_gcc12_O2_block:
        sub     w7, w7, #0x1
        cmp     w6, w5
        b.cs    Lmlkem_native_poly_invntt_tomont_gcc12_O2_blockend
        sub     w3, w5, w6
        mov     w0, w5
        sub     w3, w3, #0x1
        mov     w4, w6
        add     x3, x3, x0
        sub     x4, x4, x0
        add     x2, x15, w5, uxtw #1
        add     x3, x16, x3, lsl #1
        nop
Lmlkem_native_poly_invntt_tomont_gcc12_O2_butterfly:
        ldrsh   w19, [x2, x4, lsl #1]
        ldrh    w0, [x2]
        add     w0, w19, w0
        sxth    w0, w0
        madd    w1, w0, w13, w12
        asr     w1, w1, #26
        madd    w0, w1, w8, w0
        strh    w0, [x2, x4, lsl #1]
        ldrh    w0, [x2]
        sub     w0, w0, w19
        sxth    w0, w0
        mul     w0, w0, w9
        mul     w1, w0, w11
        sxth    w1, w1
        madd    w0, w1, w8, w0
        asr     w0, w0, #16
        strh    w0, [x2], #2
        cmp     x2, x3
        b.ne    Lmlkem_native_poly_invntt_tomont_gcc12_O2_butterfly
Lmlkem_native_poly_invntt_tomont_gcc12_O2_blockend:
        add     w6, w6, w10
        add     w5, w5, w10
        cmp     w6, #0xff
        b.hi    Lmlkem_native_poly_invntt_tomont_gcc12_O2_layerend
        ldrsh   w9, [x14, w7, uxtw #1]
        b       Lmlkem_native_poly_invntt_tomont_gcc12_O2_block
Lmlkem_native_poly_invntt_tomont_gcc12_O2_layerend:
        subs    w17, w17, #0x1
        b.eq    Lmlkem_native_poly_invntt_tomont_gcc12_O2_end
        lsl     w0, w18, w17
        sub     w0, w0, #0x1
        ldrsh   w9, [x14, x0, lsl #1]
        b       Lmlkem_native_poly_invntt_tomont_gcc12_O2_layer
Lmlkem_native_poly_invntt_tomont_gcc12_O2_end:
        CFI_POP2(x19,x30)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_native_poly_invntt_tomont_gcc12_O2)

#if defined(__ELF__)
        .section .rodata
#elif defined(__APPLE__)
        .const_data
#endif

// The vectors of constants: the inverse of 3329 modulo 2^16, as the signed
// value -3327, and 2^25 mod 3329 = 1441, in each 16-bit lane

        .balign 16
#if defined(__ELF__)
        .globl  CONSTANTS
        .hidden CONSTANTS
        .type   CONSTANTS, %object
        .size   CONSTANTS, 32
#endif
CONSTANTS:
        .short  -3327, -3327, -3327, -3327, -3327, -3327, -3327, -3327
        .short  1441, 1441, 1441, 1441, 1441, 1441, 1441, 1441

// The table mlk_zetas from mlkem-native

        .balign 32
#if defined(__ELF__)
        .globl  ZETAS
        .hidden ZETAS
        .type   ZETAS, %object
        .size   ZETAS, 256
#endif
ZETAS:
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
