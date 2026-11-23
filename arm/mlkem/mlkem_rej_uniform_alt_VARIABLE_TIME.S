// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// Uniform rejection sampling for ML-KEM, appending to a partial result
// Inputs r[n], n, *buf (unsigned bytes), buflen, table (unsigned bytes);
// output r[256] (signed 16-bit words), return
//
// extern uint64_t mlkem_rej_uniform_alt_VARIABLE_TIME
//                     (int16_t r[S2N_BIGNUM_STATIC 256],uint64_t n,
//                      const uint8_t *buf,uint64_t buflen,
//                      const uint8_t *table);
//
// Like mlkem_rej_uniform_VARIABLE_TIME, with the same table, but starting
// from n <= 256 entries already in r: interprets the buffer as packed
// 12-bit numbers with a length of buflen bytes, assumed to be a multiple
// of 24, and appends to r[0..n-1] those numbers from it that are < 3329,
// in the order of appearance, up to a total of 256, returning the new
// total n'. With n = 0 this is the non-alt function, except that the
// entries r[n'..255] may be overwritten with other values (the non-alt
// version zeroes them). This is not constant time: the time depends on
// how much of the buffer is needed.
//
// Standard ARM ABI: X0 = r, X1 = n, X2 = buf, X3 = buflen, X4 = table
// ----------------------------------------------------------------------------

#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_rej_uniform_alt_VARIABLE_TIME)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_rej_uniform_alt_VARIABLE_TIME)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_rej_uniform_alt_VARIABLE_TIME)
        .text
        .balign 4

// Each 48 bytes give 32 candidates, de-interleaved (ld3), unpacked into
// 16-bit lanes and put in order by interleaving (zip), as in the non-alt
// version. The comparison with 3329 gives a mask in each lane; ANDed with
// the weights 2^j + 2^8 for lane j and summed over each group of 8 lanes
// (three levels of pairwise additions, addp) it gives for each group the
// 8-bit index of the table entry, whose 16 bytes select the accepted
// lanes (tbl) and put them first, plus 2^8 times their number. A single
// move to a general register brings the four such sums out together.
//
// The accepted numbers are stored directly to r while there is room for
// all that the bytes could give: 96 bytes at a time (two chunks of 48,
// interleaved for the pipelines) while there is room for 64 more, then 48
// and 24 bytes at a time, finally through a small buffer on the stack
// when fewer than 16 entries remain.
//
// Registers in the loops by 48 and 24 bytes: v0-v2 input bytes, v4-v7
// unpacked halves, v16-v19 candidates, v20-v23 masks and sums, v24-v27
// table entries; in the loop by 96 bytes the same roles are shared out
// over v0-v7 and v16-v29 for the two chunks; v30 = 3329, v31 the weights
// (16-bit lanes); x1 the count n, x5 the output pointer r + 2 * n.

#define r x0
#define count x1
#define buf x2
#define buflen x3
#define table x4
#define out x5

S2N_BN_SYMBOL(mlkem_rej_uniform_alt_VARIABLE_TIME):
        CFI_START
        AARCH64_VALID_CALL_TARGET
        CFI_DEC_SP(48)

        movz    x6, #0x0101
        movk    x6, #0x0102, lsl #16
        movk    x6, #0x0104, lsl #32
        movk    x6, #0x0108, lsl #48
        movz    x7, #0x0110
        movk    x7, #0x0120, lsl #16
        movk    x7, #0x0140, lsl #32
        movk    x7, #0x0180, lsl #48
        fmov    d31, x6
        mov     v31.d[1], x7
        mov     w6, #3329
        dup     v30.8h, w6
        add     out, r, count, lsl #1

// 96 bytes at a time, two chunks of 48 interleaved, while there is room in
// r for 64 more entries

Lmlkem_rej_uniform_alt_loop96:
        cmp     buflen, #96
        bcc     Lmlkem_rej_uniform_alt_loop48
        cmp     count, #192
        bhi     Lmlkem_rej_uniform_alt_loop48
        sub     buflen, buflen, #96
        ld3     {v0.16b, v1.16b, v2.16b}, [buf], #48
        ld3     {v3.16b, v4.16b, v5.16b}, [buf], #48
        zip1    v6.16b, v0.16b, v1.16b
        zip1    v19.16b, v3.16b, v4.16b
        zip2    v7.16b, v0.16b, v1.16b
        zip2    v20.16b, v3.16b, v4.16b
        zip1    v16.16b, v1.16b, v2.16b
        zip1    v21.16b, v4.16b, v5.16b
        zip2    v17.16b, v1.16b, v2.16b
        zip2    v22.16b, v4.16b, v5.16b
        bic     v6.8h, #0xf0, lsl #8
        bic     v19.8h, #0xf0, lsl #8
        bic     v7.8h, #0xf0, lsl #8
        bic     v20.8h, #0xf0, lsl #8
        ushr    v16.8h, v16.8h, #4
        ushr    v21.8h, v21.8h, #4
        ushr    v17.8h, v17.8h, #4
        ushr    v22.8h, v22.8h, #4
        zip1    v0.8h, v6.8h, v16.8h
        zip1    v3.8h, v19.8h, v21.8h
        zip2    v1.8h, v6.8h, v16.8h
        zip2    v4.8h, v19.8h, v21.8h
        zip1    v2.8h, v7.8h, v17.8h
        zip1    v5.8h, v20.8h, v22.8h
        zip2    v18.8h, v7.8h, v17.8h
        zip2    v23.8h, v20.8h, v22.8h
        cmhi    v6.8h, v30.8h, v0.8h
        cmhi    v19.8h, v30.8h, v3.8h
        cmhi    v7.8h, v30.8h, v1.8h
        cmhi    v20.8h, v30.8h, v4.8h
        cmhi    v16.8h, v30.8h, v2.8h
        cmhi    v21.8h, v30.8h, v5.8h
        cmhi    v17.8h, v30.8h, v18.8h
        cmhi    v22.8h, v30.8h, v23.8h
        and     v6.16b, v6.16b, v31.16b
        and     v19.16b, v19.16b, v31.16b
        and     v7.16b, v7.16b, v31.16b
        and     v20.16b, v20.16b, v31.16b
        and     v16.16b, v16.16b, v31.16b
        and     v21.16b, v21.16b, v31.16b
        and     v17.16b, v17.16b, v31.16b
        and     v22.16b, v22.16b, v31.16b
        addp    v6.8h, v6.8h, v7.8h
        addp    v19.8h, v19.8h, v20.8h
        addp    v16.8h, v16.8h, v17.8h
        addp    v21.8h, v21.8h, v22.8h
        addp    v6.8h, v6.8h, v16.8h
        addp    v19.8h, v19.8h, v21.8h
        addp    v6.8h, v6.8h, v6.8h
        addp    v19.8h, v19.8h, v19.8h
        fmov    x6, d6
        fmov    x15, d19
        ubfx    x7, x6, #0, #8
        ubfx    x9, x6, #16, #8
        ubfx    x11, x6, #32, #8
        ubfx    x13, x6, #48, #8
        ldr     q24, [table, x7, lsl #4]
        ldr     q25, [table, x9, lsl #4]
        ldr     q26, [table, x11, lsl #4]
        ldr     q27, [table, x13, lsl #4]
        ubfx    x7, x15, #0, #8
        ubfx    x9, x15, #16, #8
        ubfx    x11, x15, #32, #8
        ubfx    x13, x15, #48, #8
        ldr     q28, [table, x7, lsl #4]
        ldr     q29, [table, x9, lsl #4]
        ldr     q16, [table, x11, lsl #4]
        ldr     q17, [table, x13, lsl #4]
        tbl     v0.16b, {v0.16b}, v24.16b
        tbl     v1.16b, {v1.16b}, v25.16b
        tbl     v2.16b, {v2.16b}, v26.16b
        tbl     v18.16b, {v18.16b}, v27.16b
        tbl     v3.16b, {v3.16b}, v28.16b
        tbl     v4.16b, {v4.16b}, v29.16b
        tbl     v5.16b, {v5.16b}, v16.16b
        tbl     v23.16b, {v23.16b}, v17.16b
        ubfx    x8, x6, #8, #4
        ubfx    x10, x6, #24, #4
        ubfx    x12, x6, #40, #4
        ubfx    x14, x6, #56, #4
        str     q0, [out]
        add     out, out, x8, lsl #1
        str     q1, [out]
        add     out, out, x10, lsl #1
        str     q2, [out]
        add     out, out, x12, lsl #1
        str     q18, [out]
        add     out, out, x14, lsl #1
        add     x8, x8, x10
        add     x12, x12, x14
        add     count, count, x8
        add     count, count, x12
        ubfx    x8, x15, #8, #4
        ubfx    x10, x15, #24, #4
        ubfx    x12, x15, #40, #4
        ubfx    x14, x15, #56, #4
        str     q3, [out]
        add     out, out, x8, lsl #1
        str     q4, [out]
        add     out, out, x10, lsl #1
        str     q5, [out]
        add     out, out, x12, lsl #1
        str     q23, [out]
        add     out, out, x14, lsl #1
        add     x8, x8, x10
        add     x12, x12, x14
        add     count, count, x8
        add     count, count, x12
        b       Lmlkem_rej_uniform_alt_loop96

// 48 bytes at a time, while there is room in r for 32 more entries

Lmlkem_rej_uniform_alt_loop48:
        cmp     buflen, #48
        bcc     Lmlkem_rej_uniform_alt_loop24
        cmp     count, #224
        bhi     Lmlkem_rej_uniform_alt_loop24
        sub     buflen, buflen, #48
        ld3     {v0.16b, v1.16b, v2.16b}, [buf], #48
        zip1    v4.16b, v0.16b, v1.16b
        zip2    v5.16b, v0.16b, v1.16b
        zip1    v6.16b, v1.16b, v2.16b
        zip2    v7.16b, v1.16b, v2.16b
        bic     v4.8h, #0xf0, lsl #8
        bic     v5.8h, #0xf0, lsl #8
        ushr    v6.8h, v6.8h, #4
        ushr    v7.8h, v7.8h, #4
        zip1    v16.8h, v4.8h, v6.8h
        zip2    v17.8h, v4.8h, v6.8h
        zip1    v18.8h, v5.8h, v7.8h
        zip2    v19.8h, v5.8h, v7.8h
        cmhi    v20.8h, v30.8h, v16.8h
        cmhi    v21.8h, v30.8h, v17.8h
        cmhi    v22.8h, v30.8h, v18.8h
        cmhi    v23.8h, v30.8h, v19.8h
        and     v20.16b, v20.16b, v31.16b
        and     v21.16b, v21.16b, v31.16b
        and     v22.16b, v22.16b, v31.16b
        and     v23.16b, v23.16b, v31.16b
        addp    v20.8h, v20.8h, v21.8h
        addp    v22.8h, v22.8h, v23.8h
        addp    v20.8h, v20.8h, v22.8h
        addp    v20.8h, v20.8h, v20.8h
        fmov    x6, d20
        ubfx    x7, x6, #0, #8
        ubfx    x9, x6, #16, #8
        ubfx    x11, x6, #32, #8
        ubfx    x13, x6, #48, #8
        ldr     q24, [table, x7, lsl #4]
        ldr     q25, [table, x9, lsl #4]
        ldr     q26, [table, x11, lsl #4]
        ldr     q27, [table, x13, lsl #4]
        ubfx    x8, x6, #8, #4
        ubfx    x10, x6, #24, #4
        ubfx    x12, x6, #40, #4
        ubfx    x14, x6, #56, #4
        tbl     v16.16b, {v16.16b}, v24.16b
        tbl     v17.16b, {v17.16b}, v25.16b
        tbl     v18.16b, {v18.16b}, v26.16b
        tbl     v19.16b, {v19.16b}, v27.16b
        str     q16, [out]
        add     out, out, x8, lsl #1
        str     q17, [out]
        add     out, out, x10, lsl #1
        str     q18, [out]
        add     out, out, x12, lsl #1
        str     q19, [out]
        add     out, out, x14, lsl #1
        add     x8, x8, x10
        add     x12, x12, x14
        add     count, count, x8
        add     count, count, x12
        b       Lmlkem_rej_uniform_alt_loop96

// 24 bytes at a time while fewer than 256 entries are found: directly to r
// while there is room for all 16 that the 24 bytes could give, otherwise
// through the buffer on the stack, copying only as many as are needed.

Lmlkem_rej_uniform_alt_loop24:
        cmp     buflen, #24
        bcc     Lmlkem_rej_uniform_alt_end
        cmp     count, #256
        bcs     Lmlkem_rej_uniform_alt_end
        sub     buflen, buflen, #24
        ld3     {v0.8b, v1.8b, v2.8b}, [buf], #24
        zip1    v4.16b, v0.16b, v1.16b
        zip1    v6.16b, v1.16b, v2.16b
        bic     v4.8h, #0xf0, lsl #8
        ushr    v6.8h, v6.8h, #4
        zip1    v16.8h, v4.8h, v6.8h
        zip2    v17.8h, v4.8h, v6.8h
        cmhi    v20.8h, v30.8h, v16.8h
        cmhi    v21.8h, v30.8h, v17.8h
        and     v20.16b, v20.16b, v31.16b
        and     v21.16b, v21.16b, v31.16b
        addp    v20.8h, v20.8h, v21.8h
        addp    v20.8h, v20.8h, v20.8h
        addp    v20.8h, v20.8h, v20.8h
        fmov    w6, s20
        ubfx    x7, x6, #0, #8
        ubfx    x9, x6, #16, #8
        ldr     q24, [table, x7, lsl #4]
        ldr     q25, [table, x9, lsl #4]
        ubfx    x8, x6, #8, #4
        ubfx    x10, x6, #24, #4
        tbl     v16.16b, {v16.16b}, v24.16b
        tbl     v17.16b, {v17.16b}, v25.16b
        cmp     count, #240
        bhi     Lmlkem_rej_uniform_alt_last
        str     q16, [out]
        add     out, out, x8, lsl #1
        str     q17, [out]
        add     out, out, x10, lsl #1
        add     count, count, x8
        add     count, count, x10
        b       Lmlkem_rej_uniform_alt_loop24

Lmlkem_rej_uniform_alt_last:
        str     q16, [sp]
        add     x11, sp, x8, lsl #1
        str     q17, [x11]
        add     x8, x8, x10
        mov     x9, #256
        sub     x9, x9, count
        cmp     x8, x9
        csel    x8, x8, x9, cc
        add     count, count, x8
        mov     x11, sp
        cbz     x8, Lmlkem_rej_uniform_alt_loop24
Lmlkem_rej_uniform_alt_lastcopy:
        ldrh    w12, [x11], #2
        strh    w12, [out], #2
        subs    x8, x8, #1
        bne     Lmlkem_rej_uniform_alt_lastcopy
        b       Lmlkem_rej_uniform_alt_loop24

Lmlkem_rej_uniform_alt_end:
        mov     x0, count
        CFI_INC_SP(48)
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_rej_uniform_alt_VARIABLE_TIME)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
