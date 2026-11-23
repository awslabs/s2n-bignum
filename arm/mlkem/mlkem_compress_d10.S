// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Compress ML-KEM polynomial coefficients to 10 bits and pack them
// Input a[256] (signed 16-bit words); output r[320] (bytes)
//
// The input coefficients are assumed to be in the range 0 <= a[i] < 3329.
// Each is mapped to round(a[i] * 2^10 / 3329) mod 2^10 (Compress_10 of
// FIPS 203, section 4.2.1), and the 256 results are packed as 10-bit
// little-endian fields, 4 to each group of 5 bytes (ByteEncode_10), as in
// mlkem-native's mlk_poly_compress_d10.
//
// extern void mlkem_compress_d10(uint8_t r[S2N_BIGNUM_STATIC 320],
//                                const int16_t a[S2N_BIGNUM_STATIC 256]);
//
// Standard ARM ABI: X0 = r, X1 = a
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_compress_d10)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_compress_d10)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_compress_d10)
        .text
        .balign 4

// The rounding: with M = round(2^41 / 3329) and x the high half of the
// doubled 32-bit product of a * 2^16 and M (sqdmulh), x lies within 1.1
// of 2^16 * a * 2^10 / 3329, while 2^16 * (a * 2^10 / 3329 + 1/2) is at
// least 2^16 / (2 * 3329) > 9 from any multiple of 2^16, so the top 16
// bits of x + 2^15 (raddhn) are the rounded quotient exactly. It is at
// most 2^10 (for a = 3328), and a mask then takes it mod 2^10. The
// products are formed in 32-bit lanes, with a * 2^16 from interleaving
// with zeros (zip).
//
// The packing: each group of four coefficients t_0..t_3 makes 5 bytes,
// the 40-bit number t_0 + 2^10 t_1 + 2^20 t_2 + 2^30 t_3. With
// s_j = t_j * 2^(2j) (a shift of each 16-bit lane by 0, 2, 4 or 6), the
// bytes are lo(s_0), hi(s_0) + lo(s_1), hi(s_1) + lo(s_2),
// hi(s_2) + lo(s_3), hi(s_3), where the additions have no carries, so two
// table lookups (tbl), one of the low bytes and one of the high bytes,
// ORed together give the 10 bytes of the two groups in a vector. Two
// such 10-byte results are combined with byte shifts (ext) into 16 output
// bytes and 4 more.
//
// Each iteration takes 64 coefficients to 80 bytes, the work interleaved
// across eight vectors to keep the pipelines full.
//
// Registers: v0-v7 coefficients and then packed bytes, v8-v23 products,
// lookups and shifted bytes, v24 = M (32-bit lanes), v25 = 0, v26 the
// shifts 0, 2, 4, 6 (16-bit lanes), v27 and v28 the table indices of the
// low and high bytes. The lower halves of v8-v15 are saved and restored as
// the ABI requires.

S2N_BN_SYMBOL(mlkem_compress_d10):
        CFI_START
        AARCH64_VALID_CALL_TARGET
        CFI_PUSH2(d8, d9)
        CFI_PUSH2(d10, d11)
        CFI_PUSH2(d12, d13)
        CFI_PUSH2(d14, d15)

        movz    w2, #0x6ed0
        movk    w2, #0x275f, lsl #16
        dup     v24.4s, w2
        movi    v25.2d, #0
        movz    x2, #0x0
        movk    x2, #0x2, lsl #16
        movk    x2, #0x4, lsl #32
        movk    x2, #0x6, lsl #48
        dup     v26.2d, x2
        movz    x2, #0x200
        movk    x2, #0x604, lsl #16
        movk    x2, #0x8ff, lsl #32
        movk    x2, #0xc0a, lsl #48
        movz    x3, #0xff0e
        movk    x3, #0xffff, lsl #16
        movk    x3, #0xffff, lsl #32
        movk    x3, #0xffff, lsl #48
        fmov    d27, x2
        mov     v27.d[1], x3
        movz    x2, #0x1ff
        movk    x2, #0x503, lsl #16
        movk    x2, #0xff07, lsl #32
        movk    x2, #0xb09, lsl #48
        movz    x3, #0xf0d
        movk    x3, #0xffff, lsl #16
        movk    x3, #0xffff, lsl #32
        movk    x3, #0xffff, lsl #48
        fmov    d28, x2
        mov     v28.d[1], x3

        mov     x4, #4

Lmlkem_compress_d10_loop:
        ldp     q0, q1, [x1], #32
        ldp     q2, q3, [x1], #32
        ldp     q4, q5, [x1], #32
        ldp     q6, q7, [x1], #32

        zip1    v8.8h, v25.8h, v0.8h
        zip2    v9.8h, v25.8h, v0.8h
        zip1    v10.8h, v25.8h, v1.8h
        zip2    v11.8h, v25.8h, v1.8h
        zip1    v12.8h, v25.8h, v2.8h
        zip2    v13.8h, v25.8h, v2.8h
        zip1    v14.8h, v25.8h, v3.8h
        zip2    v15.8h, v25.8h, v3.8h
        zip1    v16.8h, v25.8h, v4.8h
        zip2    v17.8h, v25.8h, v4.8h
        zip1    v18.8h, v25.8h, v5.8h
        zip2    v19.8h, v25.8h, v5.8h
        zip1    v20.8h, v25.8h, v6.8h
        zip2    v21.8h, v25.8h, v6.8h
        zip1    v22.8h, v25.8h, v7.8h
        zip2    v23.8h, v25.8h, v7.8h

        sqdmulh v8.4s, v8.4s, v24.4s
        sqdmulh v9.4s, v9.4s, v24.4s
        sqdmulh v10.4s, v10.4s, v24.4s
        sqdmulh v11.4s, v11.4s, v24.4s
        sqdmulh v12.4s, v12.4s, v24.4s
        sqdmulh v13.4s, v13.4s, v24.4s
        sqdmulh v14.4s, v14.4s, v24.4s
        sqdmulh v15.4s, v15.4s, v24.4s
        sqdmulh v16.4s, v16.4s, v24.4s
        sqdmulh v17.4s, v17.4s, v24.4s
        sqdmulh v18.4s, v18.4s, v24.4s
        sqdmulh v19.4s, v19.4s, v24.4s
        sqdmulh v20.4s, v20.4s, v24.4s
        sqdmulh v21.4s, v21.4s, v24.4s
        sqdmulh v22.4s, v22.4s, v24.4s
        sqdmulh v23.4s, v23.4s, v24.4s

        raddhn  v0.4h, v8.4s, v25.4s
        raddhn2 v0.8h, v9.4s, v25.4s
        raddhn  v1.4h, v10.4s, v25.4s
        raddhn2 v1.8h, v11.4s, v25.4s
        raddhn  v2.4h, v12.4s, v25.4s
        raddhn2 v2.8h, v13.4s, v25.4s
        raddhn  v3.4h, v14.4s, v25.4s
        raddhn2 v3.8h, v15.4s, v25.4s
        raddhn  v4.4h, v16.4s, v25.4s
        raddhn2 v4.8h, v17.4s, v25.4s
        raddhn  v5.4h, v18.4s, v25.4s
        raddhn2 v5.8h, v19.4s, v25.4s
        raddhn  v6.4h, v20.4s, v25.4s
        raddhn2 v6.8h, v21.4s, v25.4s
        raddhn  v7.4h, v22.4s, v25.4s
        raddhn2 v7.8h, v23.4s, v25.4s

        bic     v0.8h, #0xfc, lsl #8
        bic     v1.8h, #0xfc, lsl #8
        bic     v2.8h, #0xfc, lsl #8
        bic     v3.8h, #0xfc, lsl #8
        bic     v4.8h, #0xfc, lsl #8
        bic     v5.8h, #0xfc, lsl #8
        bic     v6.8h, #0xfc, lsl #8
        bic     v7.8h, #0xfc, lsl #8
        ushl    v0.8h, v0.8h, v26.8h
        ushl    v1.8h, v1.8h, v26.8h
        ushl    v2.8h, v2.8h, v26.8h
        ushl    v3.8h, v3.8h, v26.8h
        ushl    v4.8h, v4.8h, v26.8h
        ushl    v5.8h, v5.8h, v26.8h
        ushl    v6.8h, v6.8h, v26.8h
        ushl    v7.8h, v7.8h, v26.8h

        tbl     v8.16b, {v0.16b}, v27.16b
        tbl     v16.16b, {v0.16b}, v28.16b
        tbl     v9.16b, {v1.16b}, v27.16b
        tbl     v17.16b, {v1.16b}, v28.16b
        tbl     v10.16b, {v2.16b}, v27.16b
        tbl     v18.16b, {v2.16b}, v28.16b
        tbl     v11.16b, {v3.16b}, v27.16b
        tbl     v19.16b, {v3.16b}, v28.16b
        tbl     v12.16b, {v4.16b}, v27.16b
        tbl     v20.16b, {v4.16b}, v28.16b
        tbl     v13.16b, {v5.16b}, v27.16b
        tbl     v21.16b, {v5.16b}, v28.16b
        tbl     v14.16b, {v6.16b}, v27.16b
        tbl     v22.16b, {v6.16b}, v28.16b
        tbl     v15.16b, {v7.16b}, v27.16b
        tbl     v23.16b, {v7.16b}, v28.16b

        orr     v0.16b, v8.16b, v16.16b
        orr     v1.16b, v9.16b, v17.16b
        orr     v2.16b, v10.16b, v18.16b
        orr     v3.16b, v11.16b, v19.16b
        orr     v4.16b, v12.16b, v20.16b
        orr     v5.16b, v13.16b, v21.16b
        orr     v6.16b, v14.16b, v22.16b
        orr     v7.16b, v15.16b, v23.16b

        ext     v8.16b, v25.16b, v1.16b, #6
        ext     v12.16b, v1.16b, v25.16b, #6
        ext     v9.16b, v25.16b, v3.16b, #6
        ext     v13.16b, v3.16b, v25.16b, #6
        ext     v10.16b, v25.16b, v5.16b, #6
        ext     v14.16b, v5.16b, v25.16b, #6
        ext     v11.16b, v25.16b, v7.16b, #6
        ext     v15.16b, v7.16b, v25.16b, #6
        orr     v0.16b, v0.16b, v8.16b
        orr     v2.16b, v2.16b, v9.16b
        orr     v4.16b, v4.16b, v10.16b
        orr     v6.16b, v6.16b, v11.16b

        str     q0, [x0], #16
        str     s12, [x0], #4
        str     q2, [x0], #16
        str     s13, [x0], #4
        str     q4, [x0], #16
        str     s14, [x0], #4
        str     q6, [x0], #16
        str     s15, [x0], #4

        subs    x4, x4, #1
        bne     Lmlkem_compress_d10_loop

        CFI_POP2(d14, d15)
        CFI_POP2(d12, d13)
        CFI_POP2(d10, d11)
        CFI_POP2(d8, d9)
        CFI_RET


S2N_BN_SIZE_DIRECTIVE(mlkem_compress_d10)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
