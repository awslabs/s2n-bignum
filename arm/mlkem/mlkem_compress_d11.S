// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Compress ML-KEM polynomial coefficients to 11 bits and pack them
// Input a[256] (signed 16-bit words); output r[352] (bytes)
//
// The input coefficients are assumed to be in the range 0 <= a[i] < 3329.
// Each is mapped to round(a[i] * 2^11 / 3329) mod 2^11 (Compress_11 of
// FIPS 203, section 4.2.1), and the 256 results are packed as 11-bit
// little-endian fields, 8 to each group of 11 bytes (ByteEncode_11), as in
// mlkem-native's mlk_poly_compress_d11.
//
// extern void mlkem_compress_d11(uint8_t r[S2N_BIGNUM_STATIC 352],
//                                const int16_t a[S2N_BIGNUM_STATIC 256]);
//
// Standard ARM ABI: X0 = r, X1 = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_compress_d11)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_compress_d11)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_compress_d11)
        .text
        .balign 4

// The rounding: with M = round(2^42 / 3329) and x the high half of the
// doubled 32-bit product of a * 2^16 + 16 * 3329 and M (sqdmulh), x lies
// within 1.1 of 2^16 * (a * 2^11 / 3329 + 1/2), which is at least
// 2^16 / (2 * 3329) > 9 from any multiple of 2^16, so the top 16 bits of
// x (uzp2) are the rounded quotient exactly. It is at most 2047, so no
// reduction mod 2^11 is needed. The multiplicand comes from interleaving
// the coefficients with the constant 16 * 3329 (zip).
//
// The packing: the 8 coefficients t_0..t_7 of a group occupy bits 11 * j
// onwards of its 11 bytes. With s_j = t_j * 2^((11 * j) mod 8) in 32-bit
// lanes (a widening multiply, umull, by a vector of powers of 2), each
// output byte is one byte of some s_j ORed with at most one byte of
// another, all in the 32 bytes of two vectors, so two table lookups
// (tbl) and an OR give the 11 bytes. Byte shifts (ext) and ORs combine
// four such 11-byte results into 44 contiguous bytes.
//
// Each iteration takes 32 coefficients to 44 bytes.
//
// Registers: v0-v3 coefficients, v4-v7 packed groups and output, v16-v23
// products, the s_j and lookups, v25 = 16 * 3329 (16-bit lanes), v27 = 0,
// v28 and v29 the table indices, v30 the powers of 2 (16-bit lanes),
// v31 = M (32-bit lanes).

S2N_BN_SYMBOL(mlkem_compress_d11):
        CFI_START
        AARCH64_VALID_CALL_TARGET

        movz    w2, #0xdda0
        movk    w2, #0x4ebe, lsl #16
        dup     v31.4s, w2
        movz    w2, #53264
        dup     v25.8h, w2
        movi    v27.2d, #0
        movz    x2, #0x1
        movk    x2, #0x8, lsl #16
        movk    x2, #0x40, lsl #32
        movk    x2, #0x2, lsl #48
        movz    x3, #0x10
        movk    x3, #0x80, lsl #16
        movk    x3, #0x4, lsl #32
        movk    x3, #0x20, lsl #48
        fmov    d30, x2
        mov     v30.d[1], x3
        movz    x2, #0x100
        movk    x2, #0x905, lsl #16
        movk    x2, #0xd0a, lsl #32
        movk    x2, #0x1511, lsl #48
        movz    x3, #0x1916
        movk    x3, #0xff1d, lsl #16
        movk    x3, #0xffff, lsl #32
        movk    x3, #0xffff, lsl #48
        fmov    d28, x2
        mov     v28.d[1], x3
        movz    x2, #0x4ff
        movk    x2, #0xff08, lsl #16
        movk    x2, #0x100c, lsl #32
        movk    x2, #0xff14, lsl #48
        movz    x3, #0x1c18
        movk    x3, #0xffff, lsl #16
        movk    x3, #0xffff, lsl #32
        movk    x3, #0xffff, lsl #48
        fmov    d29, x2
        mov     v29.d[1], x3
        mov     x4, #8

Lmlkem_compress_d11_loop:
        ldp     q0, q1, [x1], #32
        ldp     q2, q3, [x1], #32

        zip1    v16.8h, v25.8h, v0.8h
        zip2    v17.8h, v25.8h, v0.8h
        zip1    v18.8h, v25.8h, v1.8h
        zip2    v19.8h, v25.8h, v1.8h
        zip1    v20.8h, v25.8h, v2.8h
        zip2    v21.8h, v25.8h, v2.8h
        zip1    v22.8h, v25.8h, v3.8h
        zip2    v23.8h, v25.8h, v3.8h
        sqdmulh v16.4s, v16.4s, v31.4s
        sqdmulh v17.4s, v17.4s, v31.4s
        sqdmulh v18.4s, v18.4s, v31.4s
        sqdmulh v19.4s, v19.4s, v31.4s
        sqdmulh v20.4s, v20.4s, v31.4s
        sqdmulh v21.4s, v21.4s, v31.4s
        sqdmulh v22.4s, v22.4s, v31.4s
        sqdmulh v23.4s, v23.4s, v31.4s
        uzp2    v0.8h, v16.8h, v17.8h
        uzp2    v1.8h, v18.8h, v19.8h
        uzp2    v2.8h, v20.8h, v21.8h
        uzp2    v3.8h, v22.8h, v23.8h
        umull   v16.4s, v0.4h, v30.4h
        umull2  v17.4s, v0.8h, v30.8h
        umull   v18.4s, v1.4h, v30.4h
        umull2  v19.4s, v1.8h, v30.8h
        umull   v20.4s, v2.4h, v30.4h
        umull2  v21.4s, v2.8h, v30.8h
        umull   v22.4s, v3.4h, v30.4h
        umull2  v23.4s, v3.8h, v30.8h
        tbl     v4.16b, {v16.16b, v17.16b}, v28.16b
        tbl     v16.16b, {v16.16b, v17.16b}, v29.16b
        tbl     v5.16b, {v18.16b, v19.16b}, v28.16b
        tbl     v18.16b, {v18.16b, v19.16b}, v29.16b
        tbl     v6.16b, {v20.16b, v21.16b}, v28.16b
        tbl     v20.16b, {v20.16b, v21.16b}, v29.16b
        tbl     v7.16b, {v22.16b, v23.16b}, v28.16b
        tbl     v22.16b, {v22.16b, v23.16b}, v29.16b
        orr     v4.16b, v4.16b, v16.16b
        orr     v5.16b, v5.16b, v18.16b
        orr     v6.16b, v6.16b, v20.16b
        orr     v7.16b, v7.16b, v22.16b

        ext     v17.16b, v27.16b, v5.16b, #5
        ext     v5.16b, v5.16b, v27.16b, #5
        ext     v19.16b, v27.16b, v6.16b, #10
        ext     v6.16b, v6.16b, v27.16b, #10
        ext     v21.16b, v27.16b, v7.16b, #15
        orr     v4.16b, v4.16b, v17.16b
        orr     v5.16b, v5.16b, v19.16b
        orr     v6.16b, v6.16b, v21.16b
        str     q4, [x0], #16
        str     q5, [x0], #16
        str     d6, [x0], #8
        st1     {v6.s}[2], [x0], #4

        subs    x4, x4, #1
        bne     Lmlkem_compress_d11_loop

        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_compress_d11)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
