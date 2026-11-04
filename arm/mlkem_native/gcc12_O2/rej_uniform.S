// Copyright (c) The mlkem-native project authors
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

// ----------------------------------------------------------------------------
// Uniform rejection sampling for ML-KEM
// Inputs r[256] (signed 16-bit words), offset, buf[buflen] (bytes);
// output r[offset...] (signed 16-bit words), returning the new offset
//
// This reads 12-bit values from consecutive groups of 3 bytes of buf, and
// appends those that are less than 3329 to r starting at index offset,
// stopping when there are 256 coefficients or the buffer is exhausted. It
// returns the final number of coefficients. This is the code for
// mlk_rej_uniform_c from mlkem-native's portable C implementation as
// specialized and compiled by gcc 12.3.0 with -O2, the function
// mlk_rej_uniform_c.constprop.0 in the binary (see README.md for details).
// The specialization fixes the target number of coefficients at 256, and
// since all the callers pass a buffer length of 168 or 504, it omits the
// initial test that the buffer has at least one group of 3 bytes. The
// callers also rely on X3 not changing, although the ABI would allow that.
//
// extern unsigned mlkem_native_rej_uniform_gcc12_O2
//   (int16_t r[static 256], unsigned offset, const uint8_t *buf,
//    unsigned buflen);
//
// Standard ARM ABI: X0 = r, X1 = offset, X2 = buf, X3 = buflen, returns X0
// ----------------------------------------------------------------------------
#include "_internal_s2n_bignum_arm.h"

        S2N_BN_SYM_VISIBILITY_DIRECTIVE(mlkem_native_rej_uniform_gcc12_O2)
        S2N_BN_FUNCTION_TYPE_DIRECTIVE(mlkem_native_rej_uniform_gcc12_O2)
        S2N_BN_SYM_PRIVACY_DIRECTIVE(mlkem_native_rej_uniform_gcc12_O2)
        .text
        .balign 4

S2N_BN_SYMBOL(mlkem_native_rej_uniform_gcc12_O2):
        CFI_START

        mov     x8, x0
        mov     w0, w1
        cmp     w1, #0xff
        b.hi    Lmlkem_native_rej_uniform_gcc12_O2_end
        mov     w9, #0x3
        mov     w11, #0xd00
        sub     w9, w9, w2
        mov     w10, #0xff
        b       Lmlkem_native_rej_uniform_gcc12_O2_group
Lmlkem_native_rej_uniform_gcc12_O2_reject0:
        cmp     w1, #0xd00
        mov     w5, w0
        ccmp    w0, w10, #0x2, le
        b.hi    Lmlkem_native_rej_uniform_gcc12_O2_next
Lmlkem_native_rej_uniform_gcc12_O2_accept1:
        add     w0, w5, #0x1
        strh    w1, [x8, w5, uxtw #1]
        cmp     w0, #0x100
        b.eq    Lmlkem_native_rej_uniform_gcc12_O2_end
Lmlkem_native_rej_uniform_gcc12_O2_next:
        add     x2, x2, #0x3
        add     w1, w9, w2
        cmp     w3, w1
        b.cc    Lmlkem_native_rej_uniform_gcc12_O2_end
Lmlkem_native_rej_uniform_gcc12_O2_group:
        ldrb    w4, [x2, #1]
        add     w5, w0, #0x1
        ldrb    w7, [x2]
        ldrb    w1, [x2, #2]
        lsr     w6, w4, #4
        orr     w4, w7, w4, lsl #8
        and     w4, w4, #0xfff
        orr     w1, w6, w1, lsl #4
        cmp     w4, #0xd00
        b.gt    Lmlkem_native_rej_uniform_gcc12_O2_reject0
        strh    w4, [x8, w0, uxtw #1]
        cmp     w5, #0xff
        ccmp    w1, w11, #0x0, ls
        mov     w0, w5
        b.le    Lmlkem_native_rej_uniform_gcc12_O2_accept1
        cmp     w0, #0x100
        b.ne    Lmlkem_native_rej_uniform_gcc12_O2_next
Lmlkem_native_rej_uniform_gcc12_O2_end:
        CFI_RET

S2N_BN_SIZE_DIRECTIVE(mlkem_native_rej_uniform_gcc12_O2)

#if defined(__linux__) && defined(__ELF__)
.section .note.GNU-stack, "", %progbits
#endif
