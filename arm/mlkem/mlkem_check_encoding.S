// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Check that bytes encode ML-KEM polynomials with reduced coefficients
// Input a[384*k] (bytes), k; output function return
//
// Returns 1 if each of the 256 * k 12-bit little-endian fields of the
// 384 * k bytes, two to each group of 3 bytes, is less than 3329, and
// 0 otherwise. Thus 1 means that ByteEncode_12(ByteDecode_12(a)) = a for
// each 384-byte polynomial, the modulus check of an encapsulation key in
// FIPS 203 (section 7.2), as done by mlkem-native's mlk_kem_check_pk. The
// time taken depends only on k.
//
// extern uint64_t mlkem_check_encoding(const uint8_t *a, uint64_t k);
//
// Standard ARM ABI: X0 = a, X1 = k
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_check_encoding)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_check_encoding)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_check_encoding)
        .text
        .balign 4

// A table lookup (tbl) gathers, for each of 8 fields from 12 bytes, the 2
// bytes containing it into a 16-bit lane, where it is the low 12 bits for
// an even-numbered field and the high 12 bits for an odd-numbered one. A
// mask of the other 4 bits and the maximum over all lanes, compared with
// 3329 and 3329 * 2^4 (cmhs on the lanes and then their maximum), decide
// the result. The fields are not secret, but the code is in any case
// constant-time.
//
// Each iteration takes 48 bytes, 32 fields; byte shifts (ext) of the three
// loaded vectors give the 12-byte windows at offsets 12, 24, 36.
//
// Registers: v0-v2 input, v3-v6 windows and fields, v16-v19 the maxima
// (four, to keep the dependency chains short),
// v29 the masks 0x0fff, 0xfff0 and then the bounds 3329, 53264,
// v31 the indices (16-bit lanes).

S2N_BN_SYMBOL(mlkem_check_encoding):
        CFI_START
        AARCH64_VALID_CALL_TARGET

        movz    x2, #0x100
        movk    x2, #0x201, lsl #16
        movk    x2, #0x403, lsl #32
        movk    x2, #0x504, lsl #48
        movz    x3, #0x706
        movk    x3, #0x807, lsl #16
        movk    x3, #0xa09, lsl #32
        movk    x3, #0xb0a, lsl #48
        fmov    d31, x2
        mov     v31.d[1], x3
        movz    x2, #0xfff
        movk    x2, #0xfff0, lsl #16
        dup     v29.4s, w2
        movi    v16.2d, #0
        movi    v17.2d, #0
        movi    v18.2d, #0
        movi    v19.2d, #0
        lsl     x4, x1, #3
        cbz     x4, Lmlkem_check_encoding_end

Lmlkem_check_encoding_loop:
        ldp     q0, q1, [x0], #32
        ldr     q2, [x0], #16

        ext     v4.16b, v0.16b, v1.16b, #12
        ext     v5.16b, v1.16b, v2.16b, #8
        ext     v6.16b, v2.16b, v2.16b, #4
        tbl     v3.16b, {v0.16b}, v31.16b
        tbl     v4.16b, {v4.16b}, v31.16b
        tbl     v5.16b, {v5.16b}, v31.16b
        tbl     v6.16b, {v6.16b}, v31.16b
        and     v3.16b, v3.16b, v29.16b
        and     v4.16b, v4.16b, v29.16b
        and     v5.16b, v5.16b, v29.16b
        and     v6.16b, v6.16b, v29.16b
        umax    v16.8h, v16.8h, v3.8h
        umax    v17.8h, v17.8h, v4.8h
        umax    v18.8h, v18.8h, v5.8h
        umax    v19.8h, v19.8h, v6.8h

        subs    x4, x4, #1
        bne     Lmlkem_check_encoding_loop

Lmlkem_check_encoding_end:
        movz    x2, #0xd01
        movk    x2, #0xd010, lsl #16
        umax    v16.8h, v16.8h, v17.8h
        umax    v18.8h, v18.8h, v19.8h
        umax    v16.8h, v16.8h, v18.8h
        dup     v29.4s, w2
        cmhs    v16.8h, v16.8h, v29.8h
        umaxv   h16, v16.8h
        fmov    w2, s16
        cmp     w2, #0
        cset    x0, eq
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_check_encoding)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
