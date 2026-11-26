(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of four polynomials with coefficients in [-2,2] for ML-DSA-87 by *)
(* rejection: the statement. This is the code for                            *)
(* mldsa87_poly_uniform_eta_4x (mld_poly_uniform_eta_4x in poly_kl.c) from   *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3 as *)
(* a monolithic build with MLD_CONFIG_REDUCE_RAM (see                        *)
(* mldsa_native/README.md). Clang inlined the fourfold SHAKE256 functions    *)
(* and the rejection sampling (mld_rej_eta): the function aligns its frame   *)
(* to 32 bytes, copies the seed of 64 bytes four times with the four nonce   *)
(* bytes and a zero byte, zeroes four Keccak states with memset, XORs the    *)
(* four extended seeds of 66 bytes and the padding into them with straight-  *)
(* line code, permutes each with mldsa_keccakf1600_permute, copies the first *)
(* block of each to a buffer and samples the coefficients from them, and     *)
(* then, while a polynomial has fewer than 256 coefficients, permutes all    *)
(* four states, copies their next blocks and samples from those of the       *)
(* polynomials that need more. It zeroes the states and the buffers with     *)
(* memset and the copies of the seed with stores. It is verified in the      *)
(* whole image (see libmldsa.ml) against mld_poly_uniform_eta of             *)
(* common/mldsa_native_sampling.ml, using the theorem for                    *)
(* mldsa_keccakf1600_permute and the contract memset_full_contract of        *)
(* utils/mlkem_native_libc_full.ml for memset, and assuming that the         *)
(* SHAKE256 output of each extended seed has 256 acceptable nibbles          *)
(* (mld_rej_eta_terminates), without which the code does not terminate. The  *)
(* first three nonces are the low bytes of the sixth to eighth arguments,    *)
(* the fourth the byte that the caller puts on the stack. It is also shown   *)
(* to be constant time and memory safe, with the events depending on the     *)
(* seed only through which nibbles of the SHAKE256 outputs the sampling      *)
(* accepts, which it declassifies (mld_poly_uniform_eta_declass).            *)
(*                                                                           *)
(* The stack is the 2336 bytes below the stack pointer of the caller: the 96 *)
(* bytes of saved registers, the frame of 1952 bytes (the realignment to 32  *)
(* bytes costs up to 16 more) and the 240 bytes of                           *)
(* mldsa_keccakf1600_permute, rounded up. The events depend on whether the   *)
(* stack pointer is a multiple of 32, as the frame is aligned by rounding    *)
(* down.                                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa87_poly_uniform_eta_4x:
       +0x0: stp     x29, x30, [sp, #-96]!
       +0x4: stp     x28, x27, [sp, #16]
       +0x8: stp     x26, x25, [sp, #32]
       +0xc: stp     x24, x23, [sp, #48]
      +0x10: stp     x22, x21, [sp, #64]
      +0x14: stp     x20, x19, [sp, #80]
      +0x18: mov     x29, sp
      +0x1c: sub     x9, sp, #0x7a0
      +0x20: and     sp, x9, #0xffffffffffffffe0
      +0x24: ldr     xzr, [sp]
      +0x28: stp     x2, x3, [sp, #56]
      +0x2c: adrp    x8, <page>
      +0x30: str     x1, [sp, #48]
      +0x34: add     x19, sp, #0x60
      +0x38: mov     w1, wzr
      +0x3c: str     x0, [sp, #88]
      +0x40: add     x0, sp, #0x60
      +0x44: mov     w2, #0x320
      +0x48: ldr     x8, [x8, #4088]
      +0x4c: add     x20, x19, #0x258
      +0x50: ldr     x8, [x8]
      +0x54: str     x8, [sp, #1944]
      +0x58: ldrb    w8, [x29, #96]
      +0x5c: ldp     q0, q1, [x4]
      +0x60: strb    w5, [sp, #960]
      +0x64: ldp     q2, q3, [x4, #32]
      +0x68: strb    w6, [sp, #1056]
      +0x6c: strb    w7, [sp, #1152]
      +0x70: stp     q0, q1, [sp, #896]
      +0x74: stp     q2, q3, [sp, #928]
      +0x78: stp     q0, q1, [sp, #992]
      +0x7c: str     q2, [sp, #1024]
      +0x80: str     q3, [sp, #1040]
      +0x84: str     q3, [sp, #1136]
      +0x88: str     q2, [sp, #1120]
      +0x8c: str     q1, [sp, #1104]
      +0x90: str     q0, [sp, #1088]
      +0x94: str     q1, [sp, #1200]
      +0x98: str     q0, [sp, #1184]
      +0x9c: str     q2, [sp, #1216]
      +0xa0: str     q3, [sp, #1232]
      +0xa4: strb    w8, [sp, #1248]
      +0xa8: strb    wzr, [sp, #961]
      +0xac: strb    wzr, [sp, #1057]
      +0xb0: strb    wzr, [sp, #1153]
      +0xb4: strb    wzr, [sp, #1249]
      +0xb8: bl      <memset>
      +0xbc: ldr     h0, [sp, #960]
      +0xc0: ldr     h1, [sp, #160]
      +0xc4: add     x0, sp, #0x60
      +0xc8: ldp     q2, q3, [sp, #896]
      +0xcc: add     x21, x19, #0xc8
      +0xd0: ldp     q4, q5, [sp, #96]
      +0xd4: uxtl    v0.8h, v0.8b
      +0xd8: uxtl    v1.8h, v1.8b
      +0xdc: ldp     q6, q7, [sp, #928]
      +0xe0: ldp     q16, q17, [sp, #128]
      +0xe4: ldrb    w8, [sp, #162]
      +0xe8: eor     v2.16b, v4.16b, v2.16b
      +0xec: eor     v3.16b, v5.16b, v3.16b
      +0xf0: uxtl    v0.4s, v0.4h
      +0xf4: uxtl    v1.4s, v1.4h
      +0xf8: ldp     q4, q18, [sp, #992]
      +0xfc: eor     v6.16b, v16.16b, v6.16b
     +0x100: eor     v7.16b, v17.16b, v7.16b
     +0x104: ldr     h17, [sp, #1056]
     +0x108: stp     q2, q3, [sp, #96]
     +0x10c: ldr     h2, [sp, #360]
     +0x110: ldur    q3, [x19, #232]
     +0x114: eor     v0.8b, v1.8b, v0.8b
     +0x118: ldr     q1, [sp, #1024]
     +0x11c: ldur    q5, [x19, #200]
     +0x120: stp     q6, q7, [sp, #128]
     +0x124: uxtl    v6.8h, v17.8b
     +0x128: uxtl    v2.8h, v2.8b
     +0x12c: ldur    q16, [x19, #216]
     +0x130: eor     v1.16b, v3.16b, v1.16b
     +0x134: eor     v4.16b, v5.16b, v4.16b
     +0x138: stur    b0, [sp, #160]
     +0x13c: mov     s0, v0.s[1]
     +0x140: ldr     q7, [sp, #1040]
     +0x144: uxtl    v3.4s, v6.4h
     +0x148: uxtl    v2.4s, v2.4h
     +0x14c: eor     v5.16b, v16.16b, v18.16b
     +0x150: ldur    q16, [x19, #248]
     +0x154: stur    q1, [x19, #232]
     +0x158: ldrb    w9, [sp, #362]
     +0x15c: stur    q4, [x19, #200]
     +0x160: eor     w8, w8, #0x1f
     +0x164: ldrb    w10, [sp, #562]
     +0x168: eor     v1.8b, v2.8b, v3.8b
     +0x16c: stur    b0, [sp, #161]
     +0x170: ldr     h0, [sp, #1152]
     +0x174: ldr     h2, [sp, #560]
     +0x178: eor     v4.16b, v16.16b, v7.16b
     +0x17c: stur    q5, [x19, #216]
     +0x180: uxtl    v0.8h, v0.8b
     +0x184: ldr     q3, [sp, #1088]
     +0x188: ldr     q5, [sp, #1104]
     +0x18c: uxtl    v2.8h, v2.8b
     +0x190: str     b1, [sp, #360]
     +0x194: mov     s1, v1.s[1]
     +0x198: stur    q4, [x19, #248]
     +0x19c: ldp     q4, q6, [sp, #496]
     +0x1a0: uxtl    v0.4s, v0.4h
     +0x1a4: ldp     q16, q17, [sp, #528]
     +0x1a8: uxtl    v2.4s, v2.4h
     +0x1ac: ldr     q7, [sp, #1136]
     +0x1b0: strb    w8, [sp, #162]
     +0x1b4: eor     v3.16b, v4.16b, v3.16b
     +0x1b8: str     b1, [sp, #361]
     +0x1bc: eor     v1.16b, v6.16b, v5.16b
     +0x1c0: ldr     h6, [sp, #760]
     +0x1c4: ldr     q4, [sp, #1120]
     +0x1c8: eor     v5.16b, v17.16b, v7.16b
     +0x1cc: eor     v0.8b, v2.8b, v0.8b
     +0x1d0: ldr     h2, [sp, #1248]
     +0x1d4: eor     w8, w9, #0x1f
     +0x1d8: stp     q3, q1, [sp, #496]
     +0x1dc: eor     v4.16b, v16.16b, v4.16b
     +0x1e0: ldrb    w9, [sp, #762]
     +0x1e4: uxtl    v1.8h, v2.8b
     +0x1e8: uxtl    v2.8h, v6.8b
     +0x1ec: strb    w8, [sp, #362]
     +0x1f0: ldp     q6, q7, [x20]
     +0x1f4: mov     s3, v0.s[1]
     +0x1f8: stp     q4, q5, [sp, #528]
     +0x1fc: ldr     q4, [sp, #1184]
     +0x200: ldr     q5, [sp, #1200]
     +0x204: uxtl    v1.4s, v1.4h
     +0x208: uxtl    v2.4s, v2.4h
     +0x20c: str     b0, [sp, #560]
     +0x210: eor     v0.16b, v6.16b, v4.16b
     +0x214: eor     v4.16b, v7.16b, v5.16b
     +0x218: eor     w8, w10, #0x1f
     +0x21c: ldrb    w10, [sp, #231]
     +0x220: ldr     q6, [sp, #1216]
     +0x224: ldr     q7, [sp, #1232]
     +0x228: eor     v1.8b, v2.8b, v1.8b
     +0x22c: ldp     q5, q2, [x20, #32]
     +0x230: strb    w8, [sp, #562]
     +0x234: eor     w8, w9, #0x1f
     +0x238: ldrb    w9, [sp, #431]
     +0x23c: stp     q0, q4, [x20]
     +0x240: mov     s0, v1.s[1]
     +0x244: strb    w8, [sp, #762]
     +0x248: eor     w8, w10, #0x80
     +0x24c: ldrb    w10, [sp, #631]
     +0x250: str     b3, [sp, #561]
     +0x254: eor     v3.16b, v5.16b, v6.16b
     +0x258: eor     v2.16b, v2.16b, v7.16b
     +0x25c: strb    w8, [sp, #231]
     +0x260: eor     w8, w9, #0x80
     +0x264: ldrb    w9, [sp, #831]
     +0x268: strb    w8, [sp, #431]
     +0x26c: eor     w8, w10, #0x80
     +0x270: strb    w8, [sp, #631]
     +0x274: eor     w8, w9, #0x80
     +0x278: add     x9, x19, #0x190
     +0x27c: stp     q3, q2, [x20, #32]
     +0x280: str     b1, [sp, #760]
     +0x284: str     b0, [sp, #761]
     +0x288: str     x9, [sp, #24]
     +0x28c: strb    w8, [sp, #831]
     +0x290: bl      <mldsa_keccakf1600_permute>
     +0x294: add     x0, x19, #0xc8
     +0x298: bl      <mldsa_keccakf1600_permute>
     +0x29c: add     x0, x19, #0x190
     +0x2a0: bl      <mldsa_keccakf1600_permute>
     +0x2a4: add     x0, x19, #0x258
     +0x2a8: bl      <mldsa_keccakf1600_permute>
     +0x2ac: ldp     q0, q1, [sp, #160]
     +0x2b0: add     x9, x19, #0xc8
     +0x2b4: ldr     x10, [sp, #424]
     +0x2b8: str     x9, [sp, #32]
     +0x2bc: mov     x8, xzr
     +0x2c0: ldr     x9, [sp, #224]
     +0x2c4: ldr     x11, [sp, #624]
     +0x2c8: mov     x26, xzr
     +0x2cc: str     q0, [sp, #1344]
     +0x2d0: ldp     q0, q2, [sp, #192]
     +0x2d4: str     q1, [sp, #1360]
     +0x2d8: str     x10, [sp, #1568]
     +0x2dc: ldr     x10, [sp, #824]
     +0x2e0: str     q0, [sp, #1376]
     +0x2e4: ldp     q1, q0, [sp, #96]
     +0x2e8: str     q2, [sp, #1392]
     +0x2ec: str     x9, [sp, #1408]
     +0x2f0: add     x9, sp, #0x500
     +0x2f4: str     q0, [sp, #1296]
     +0x2f8: ldp     q2, q0, [sp, #128]
     +0x2fc: str     q1, [sp, #1280]
     +0x300: add     x28, x9, #0xa0
     +0x304: add     x23, x9, #0x140
     +0x308: str     x10, [sp, #1888]
     +0x30c: add     x0, x9, #0x1e0
     +0x310: mov     w10, #0xcd
     +0x314: str     q0, [sp, #1328]
     +0x318: ldp     q1, q0, [x21, #64]
     +0x31c: str     q2, [sp, #1312]
     +0x320: str     x20, [sp, #40]
     +0x324: str     q0, [sp, #1520]
     +0x328: ldp     q2, q0, [x21, #96]
     +0x32c: str     q1, [sp, #1504]
     +0x330: ldur    q1, [x19, #200]
     +0x334: str     x11, [sp, #1728]
     +0x338: str     q0, [sp, #1552]
     +0x33c: ldur    q0, [x19, #216]
     +0x340: str     q1, [sp, #1440]
     +0x344: str     q0, [sp, #1456]
     +0x348: ldur    q0, [x19, #248]
     +0x34c: str     q2, [sp, #1536]
     +0x350: ldur    q2, [x19, #232]
     +0x354: str     q0, [sp, #1488]
     +0x358: ldp     q1, q0, [sp, #560]
     +0x35c: str     q2, [sp, #1472]
     +0x360: str     q0, [sp, #1680]
     +0x364: ldp     q2, q0, [sp, #592]
     +0x368: str     q1, [sp, #1664]
     +0x36c: str     q0, [sp, #1712]
     +0x370: ldp     q1, q0, [sp, #496]
     +0x374: str     q2, [sp, #1696]
     +0x378: str     q0, [sp, #1616]
     +0x37c: ldp     q2, q0, [sp, #528]
     +0x380: str     q1, [sp, #1600]
     +0x384: str     q0, [sp, #1648]
     +0x388: ldp     q1, q0, [x20, #64]
     +0x38c: str     q2, [sp, #1632]
     +0x390: str     q0, [sp, #1840]
     +0x394: ldp     q2, q0, [x20, #96]
     +0x398: str     q1, [sp, #1824]
     +0x39c: str     q0, [sp, #1872]
     +0x3a0: ldp     q1, q0, [x20]
     +0x3a4: str     q2, [sp, #1856]
     +0x3a8: str     q1, [sp, #1760]
     +0x3ac: str     q0, [sp, #1776]
     +0x3b0: ldp     q1, q0, [x20, #32]
     +0x3b4: str     q1, [sp, #1792]
     +0x3b8: str     q0, [sp, #1808]
     +0x3bc: ldrb    w11, [x9, x8]
     +0x3c0: and     w12, w11, #0xf
     +0x3c4: cmp     w12, #0xf
     +0x3c8: b.ne    <mldsa87_poly_uniform_eta_4x+0x3e0>
     +0x3cc: ldr     x14, [sp, #88]
     +0x3d0: lsr     w11, w11, #4
     +0x3d4: cmp     w11, #0xf
     +0x3d8: b.ne    <mldsa87_poly_uniform_eta_4x+0x410>
     +0x3dc: b       <mldsa87_poly_uniform_eta_4x+0x438>
     +0x3e0: mul     w13, w12, w10
     +0x3e4: ldr     x14, [sp, #88]
     +0x3e8: lsr     w13, w13, #10
     +0x3ec: orr     w13, w13, w13, lsl #2
     +0x3f0: sub     w12, w13, w12
     +0x3f4: add     x13, x26, #0x1
     +0x3f8: add     w12, w12, #0x2
     +0x3fc: str     w12, [x14, x26, lsl #2]
     +0x400: mov     x26, x13
     +0x404: lsr     w11, w11, #4
     +0x408: cmp     w11, #0xf
     +0x40c: b.eq    <mldsa87_poly_uniform_eta_4x+0x438>
     +0x410: cmp     x26, #0xff
     +0x414: b.hi    <mldsa87_poly_uniform_eta_4x+0x438>
     +0x418: mul     w12, w11, w10
     +0x41c: lsr     w12, w12, #10
     +0x420: orr     w12, w12, w12, lsl #2
     +0x424: sub     w11, w12, w11
     +0x428: add     x12, x26, #0x1
     +0x42c: add     w11, w11, #0x2
     +0x430: str     w11, [x14, x26, lsl #2]
     +0x434: mov     x26, x12
     +0x438: cmp     x26, #0x100
     +0x43c: cset    w2, cc
     +0x440: cmp     x26, #0xff
     +0x444: b.hi    <mldsa87_poly_uniform_eta_4x+0x454>
     +0x448: cmp     x8, #0x87
     +0x44c: add     x8, x8, #0x1
     +0x450: b.cc    <mldsa87_poly_uniform_eta_4x+0x3bc>
     +0x454: ldp     x15, x14, [sp, #56]
     +0x458: mov     x8, xzr
     +0x45c: ldr     x16, [sp, #48]
     +0x460: mov     x25, xzr
     +0x464: add     x9, sp, #0x500
     +0x468: mov     w10, #0xcd
     +0x46c: add     x11, x9, x8
     +0x470: ldrb    w11, [x11, #160]
     +0x474: and     w12, w11, #0xf
     +0x478: cmp     w12, #0xf
     +0x47c: b.eq    <mldsa87_poly_uniform_eta_4x+0x4a0>
     +0x480: mul     w13, w12, w10
     +0x484: lsr     w13, w13, #10
     +0x488: orr     w13, w13, w13, lsl #2
     +0x48c: sub     w12, w13, w12
     +0x490: add     x13, x25, #0x1
     +0x494: add     w12, w12, #0x2
     +0x498: str     w12, [x16, x25, lsl #2]
     +0x49c: mov     x25, x13
     +0x4a0: lsr     w11, w11, #4
     +0x4a4: cmp     w11, #0xf
     +0x4a8: b.eq    <mldsa87_poly_uniform_eta_4x+0x4d4>
     +0x4ac: cmp     x25, #0xff
     +0x4b0: b.hi    <mldsa87_poly_uniform_eta_4x+0x4d4>
     +0x4b4: mul     w12, w11, w10
     +0x4b8: lsr     w12, w12, #10
     +0x4bc: orr     w12, w12, w12, lsl #2
     +0x4c0: sub     w11, w12, w11
     +0x4c4: add     x12, x25, #0x1
     +0x4c8: add     w11, w11, #0x2
     +0x4cc: str     w11, [x16, x25, lsl #2]
     +0x4d0: mov     x25, x12
     +0x4d4: cmp     x25, #0x100
     +0x4d8: cset    w1, cc
     +0x4dc: cmp     x25, #0xff
     +0x4e0: b.hi    <mldsa87_poly_uniform_eta_4x+0x4f0>
     +0x4e4: cmp     x8, #0x87
     +0x4e8: add     x8, x8, #0x1
     +0x4ec: b.cc    <mldsa87_poly_uniform_eta_4x+0x46c>
     +0x4f0: mov     x8, xzr
     +0x4f4: mov     x24, xzr
     +0x4f8: add     x9, sp, #0x500
     +0x4fc: mov     w10, #0xcd
     +0x500: add     x11, x9, x8
     +0x504: ldrb    w11, [x11, #320]
     +0x508: and     w12, w11, #0xf
     +0x50c: cmp     w12, #0xf
     +0x510: b.eq    <mldsa87_poly_uniform_eta_4x+0x534>
     +0x514: mul     w13, w12, w10
     +0x518: lsr     w13, w13, #10
     +0x51c: orr     w13, w13, w13, lsl #2
     +0x520: sub     w12, w13, w12
     +0x524: add     x13, x24, #0x1
     +0x528: add     w12, w12, #0x2
     +0x52c: str     w12, [x15, x24, lsl #2]
     +0x530: mov     x24, x13
     +0x534: lsr     w11, w11, #4
     +0x538: cmp     w11, #0xf
     +0x53c: b.eq    <mldsa87_poly_uniform_eta_4x+0x568>
     +0x540: cmp     x24, #0xff
     +0x544: b.hi    <mldsa87_poly_uniform_eta_4x+0x568>
     +0x548: mul     w12, w11, w10
     +0x54c: lsr     w12, w12, #10
     +0x550: orr     w12, w12, w12, lsl #2
     +0x554: sub     w11, w12, w11
     +0x558: add     x12, x24, #0x1
     +0x55c: add     w11, w11, #0x2
     +0x560: str     w11, [x15, x24, lsl #2]
     +0x564: mov     x24, x12
     +0x568: cmp     x24, #0x100
     +0x56c: cset    w16, cc
     +0x570: cmp     x24, #0xff
     +0x574: b.hi    <mldsa87_poly_uniform_eta_4x+0x584>
     +0x578: cmp     x8, #0x87
     +0x57c: add     x8, x8, #0x1
     +0x580: b.cc    <mldsa87_poly_uniform_eta_4x+0x500>
     +0x584: mov     x8, xzr
     +0x588: mov     x19, xzr
     +0x58c: add     x9, sp, #0x500
     +0x590: mov     w10, #0xcd
     +0x594: add     x11, x9, x8
     +0x598: ldrb    w11, [x11, #480]
     +0x59c: and     w12, w11, #0xf
     +0x5a0: cmp     w12, #0xf
     +0x5a4: b.eq    <mldsa87_poly_uniform_eta_4x+0x5c8>
     +0x5a8: mul     w13, w12, w10
     +0x5ac: lsr     w13, w13, #10
     +0x5b0: orr     w13, w13, w13, lsl #2
     +0x5b4: sub     w12, w13, w12
     +0x5b8: add     x13, x19, #0x1
     +0x5bc: add     w12, w12, #0x2
     +0x5c0: str     w12, [x14, x19, lsl #2]
     +0x5c4: mov     x19, x13
     +0x5c8: lsr     w11, w11, #4
     +0x5cc: cmp     w11, #0xf
     +0x5d0: b.eq    <mldsa87_poly_uniform_eta_4x+0x5fc>
     +0x5d4: cmp     x19, #0xff
     +0x5d8: b.hi    <mldsa87_poly_uniform_eta_4x+0x5fc>
     +0x5dc: mul     w12, w11, w10
     +0x5e0: lsr     w12, w12, #10
     +0x5e4: orr     w12, w12, w12, lsl #2
     +0x5e8: sub     w11, w12, w11
     +0x5ec: add     x12, x19, #0x1
     +0x5f0: add     w11, w11, #0x2
     +0x5f4: str     w11, [x14, x19, lsl #2]
     +0x5f8: mov     x19, x12
     +0x5fc: cmp     x19, #0x100
     +0x600: cset    w11, cc
     +0x604: cmp     x19, #0xff
     +0x608: b.hi    <mldsa87_poly_uniform_eta_4x+0x618>
     +0x60c: cmp     x8, #0x87
     +0x610: add     x8, x8, #0x1
     +0x614: b.cc    <mldsa87_poly_uniform_eta_4x+0x594>
     +0x618: cmp     x26, #0x100
     +0x61c: b.cc    <mldsa87_poly_uniform_eta_4x+0x638>
     +0x620: cmp     x25, #0x100
     +0x624: b.cc    <mldsa87_poly_uniform_eta_4x+0x638>
     +0x628: cmp     x24, #0x100
     +0x62c: b.cc    <mldsa87_poly_uniform_eta_4x+0x638>
     +0x630: cmp     x19, #0xff
     +0x634: b.hi    <mldsa87_poly_uniform_eta_4x+0x99c>
     +0x638: ldr     x27, [sp, #24]
     +0x63c: mov     w21, #0xcd
     +0x640: str     x0, [sp, #16]
     +0x644: add     x0, sp, #0x60
     +0x648: stp     w2, w11, [sp, #72]
     +0x64c: stp     w16, w1, [sp, #80]
     +0x650: bl      <mldsa_keccakf1600_permute>
     +0x654: ldr     x20, [sp, #32]
     +0x658: mov     x0, x20
     +0x65c: bl      <mldsa_keccakf1600_permute>
     +0x660: mov     x0, x27
     +0x664: bl      <mldsa_keccakf1600_permute>
     +0x668: ldr     x22, [sp, #40]
     +0x66c: mov     x0, x22
     +0x670: bl      <mldsa_keccakf1600_permute>
     +0x674: ldp     q0, q1, [sp, #160]
     +0x678: ldr     x0, [sp, #16]
     +0x67c: ldr     x8, [sp, #224]
     +0x680: str     q0, [sp, #1344]
     +0x684: ldp     q2, q0, [sp, #192]
     +0x688: str     q1, [sp, #1360]
     +0x68c: str     x8, [sp, #1408]
     +0x690: ldr     x8, [x20, #128]
     +0x694: str     q0, [sp, #1392]
     +0x698: ldp     q1, q0, [sp, #96]
     +0x69c: str     q2, [sp, #1376]
     +0x6a0: str     x8, [x28, #128]
     +0x6a4: ldr     x8, [x27, #128]
     +0x6a8: str     q0, [sp, #1296]
     +0x6ac: ldp     q2, q0, [sp, #128]
     +0x6b0: str     q1, [sp, #1280]
     +0x6b4: str     x8, [x23, #128]
     +0x6b8: ldr     x8, [x22, #128]
     +0x6bc: str     q0, [sp, #1328]
     +0x6c0: ldp     q0, q1, [x20, #64]
     +0x6c4: str     q2, [sp, #1312]
     +0x6c8: str     x8, [x0, #128]
     +0x6cc: ldr     w8, [sp, #72]
     +0x6d0: stp     q0, q1, [x28, #64]
     +0x6d4: ldp     q2, q0, [x20, #96]
     +0x6d8: stp     q2, q0, [x28, #96]
     +0x6dc: ldp     q1, q0, [x20]
     +0x6e0: stp     q1, q0, [x28]
     +0x6e4: ldp     q2, q0, [x20, #32]
     +0x6e8: stp     q2, q0, [x28, #32]
     +0x6ec: ldp     q0, q1, [x27, #64]
     +0x6f0: stp     q0, q1, [x23, #64]
     +0x6f4: ldp     q2, q0, [x27, #96]
     +0x6f8: stp     q2, q0, [x23, #96]
     +0x6fc: ldp     q1, q0, [x27]
     +0x700: stp     q1, q0, [x23]
     +0x704: ldp     q2, q0, [x27, #32]
     +0x708: stp     q2, q0, [x23, #32]
     +0x70c: ldp     q0, q1, [x22, #64]
     +0x710: stp     q0, q1, [x0, #64]
     +0x714: ldp     q2, q0, [x22, #96]
     +0x718: stp     q2, q0, [x0, #96]
     +0x71c: ldp     q1, q0, [x22]
     +0x720: stp     q1, q0, [x0]
     +0x724: ldp     q2, q0, [x22, #32]
     +0x728: stp     q2, q0, [x0, #32]
     +0x72c: tbz     w8, #0, <mldsa87_poly_uniform_eta_4x+0x848>
     +0x730: ldp     x13, x12, [sp, #56]
     +0x734: mov     x8, xzr
     +0x738: ldr     x14, [sp, #48]
     +0x73c: ldr     x15, [sp, #88]
     +0x740: add     x16, sp, #0x500
     +0x744: ldr     w1, [sp, #84]
     +0x748: ldrb    w9, [x16, x8]
     +0x74c: and     w10, w9, #0xf
     +0x750: cmp     w10, #0xf
     +0x754: b.eq    <mldsa87_poly_uniform_eta_4x+0x778>
     +0x758: mul     w11, w10, w21
     +0x75c: lsr     w11, w11, #10
     +0x760: orr     w11, w11, w11, lsl #2
     +0x764: sub     w10, w11, w10
     +0x768: add     x11, x26, #0x1
     +0x76c: add     w10, w10, #0x2
     +0x770: str     w10, [x15, x26, lsl #2]
     +0x774: mov     x26, x11
     +0x778: lsr     w9, w9, #4
     +0x77c: cmp     w9, #0xf
     +0x780: b.eq    <mldsa87_poly_uniform_eta_4x+0x7ac>
     +0x784: cmp     x26, #0xff
     +0x788: b.hi    <mldsa87_poly_uniform_eta_4x+0x7ac>
     +0x78c: mul     w10, w9, w21
     +0x790: lsr     w10, w10, #10
     +0x794: orr     w10, w10, w10, lsl #2
     +0x798: sub     w9, w10, w9
     +0x79c: add     x10, x26, #0x1
     +0x7a0: add     w9, w9, #0x2
     +0x7a4: str     w9, [x15, x26, lsl #2]
     +0x7a8: mov     x26, x10
     +0x7ac: cmp     x26, #0xff
     +0x7b0: b.hi    <mldsa87_poly_uniform_eta_4x+0x7c0>
     +0x7b4: cmp     x8, #0x87
     +0x7b8: add     x8, x8, #0x1
     +0x7bc: b.cc    <mldsa87_poly_uniform_eta_4x+0x748>
     +0x7c0: tbz     w1, #0, <mldsa87_poly_uniform_eta_4x+0x858>
     +0x7c4: ldr     w15, [sp, #80]
     +0x7c8: mov     x8, xzr
     +0x7cc: ldrb    w9, [x28, x8]
     +0x7d0: and     w10, w9, #0xf
     +0x7d4: cmp     w10, #0xf
     +0x7d8: b.eq    <mldsa87_poly_uniform_eta_4x+0x7fc>
     +0x7dc: mul     w11, w10, w21
     +0x7e0: lsr     w11, w11, #10
     +0x7e4: orr     w11, w11, w11, lsl #2
     +0x7e8: sub     w10, w11, w10
     +0x7ec: add     x11, x25, #0x1
     +0x7f0: add     w10, w10, #0x2
     +0x7f4: str     w10, [x14, x25, lsl #2]
     +0x7f8: mov     x25, x11
     +0x7fc: lsr     w9, w9, #4
     +0x800: cmp     w9, #0xf
     +0x804: b.eq    <mldsa87_poly_uniform_eta_4x+0x830>
     +0x808: cmp     x25, #0xff
     +0x80c: b.hi    <mldsa87_poly_uniform_eta_4x+0x830>
     +0x810: mul     w10, w9, w21
     +0x814: lsr     w10, w10, #10
     +0x818: orr     w10, w10, w10, lsl #2
     +0x81c: sub     w9, w10, w9
     +0x820: add     x10, x25, #0x1
     +0x824: add     w9, w9, #0x2
     +0x828: str     w9, [x14, x25, lsl #2]
     +0x82c: mov     x25, x10
     +0x830: cmp     x25, #0xff
     +0x834: b.hi    <mldsa87_poly_uniform_eta_4x+0x85c>
     +0x838: cmp     x8, #0x87
     +0x83c: add     x8, x8, #0x1
     +0x840: b.cc    <mldsa87_poly_uniform_eta_4x+0x7cc>
     +0x844: b       <mldsa87_poly_uniform_eta_4x+0x85c>
     +0x848: ldp     x13, x12, [sp, #56]
     +0x84c: ldr     x14, [sp, #48]
     +0x850: ldr     w1, [sp, #84]
     +0x854: tbnz    w1, #0, <mldsa87_poly_uniform_eta_4x+0x7c4>
     +0x858: ldr     w15, [sp, #80]
     +0x85c: tbz     w15, #0, <mldsa87_poly_uniform_eta_4x+0x8dc>
     +0x860: mov     x8, xzr
     +0x864: ldrb    w9, [x23, x8]
     +0x868: and     w10, w9, #0xf
     +0x86c: cmp     w10, #0xf
     +0x870: b.eq    <mldsa87_poly_uniform_eta_4x+0x894>
     +0x874: mul     w11, w10, w21
     +0x878: lsr     w11, w11, #10
     +0x87c: orr     w11, w11, w11, lsl #2
     +0x880: sub     w10, w11, w10
     +0x884: add     x11, x24, #0x1
     +0x888: add     w10, w10, #0x2
     +0x88c: str     w10, [x13, x24, lsl #2]
     +0x890: mov     x24, x11
     +0x894: lsr     w9, w9, #4
     +0x898: cmp     w9, #0xf
     +0x89c: b.eq    <mldsa87_poly_uniform_eta_4x+0x8c8>
     +0x8a0: cmp     x24, #0xff
     +0x8a4: b.hi    <mldsa87_poly_uniform_eta_4x+0x8c8>
     +0x8a8: mul     w10, w9, w21
     +0x8ac: lsr     w10, w10, #10
     +0x8b0: orr     w10, w10, w10, lsl #2
     +0x8b4: sub     w9, w10, w9
     +0x8b8: add     x10, x24, #0x1
     +0x8bc: add     w9, w9, #0x2
     +0x8c0: str     w9, [x13, x24, lsl #2]
     +0x8c4: mov     x24, x10
     +0x8c8: cmp     x24, #0xff
     +0x8cc: b.hi    <mldsa87_poly_uniform_eta_4x+0x8dc>
     +0x8d0: cmp     x8, #0x87
     +0x8d4: add     x8, x8, #0x1
     +0x8d8: b.cc    <mldsa87_poly_uniform_eta_4x+0x864>
     +0x8dc: ldr     w8, [sp, #76]
     +0x8e0: tbz     w8, #0, <mldsa87_poly_uniform_eta_4x+0x960>
     +0x8e4: mov     x8, xzr
     +0x8e8: ldrb    w9, [x0, x8]
     +0x8ec: and     w10, w9, #0xf
     +0x8f0: cmp     w10, #0xf
     +0x8f4: b.eq    <mldsa87_poly_uniform_eta_4x+0x918>
     +0x8f8: mul     w11, w10, w21
     +0x8fc: lsr     w11, w11, #10
     +0x900: orr     w11, w11, w11, lsl #2
     +0x904: sub     w10, w11, w10
     +0x908: add     x11, x19, #0x1
     +0x90c: add     w10, w10, #0x2
     +0x910: str     w10, [x12, x19, lsl #2]
     +0x914: mov     x19, x11
     +0x918: lsr     w9, w9, #4
     +0x91c: cmp     w9, #0xf
     +0x920: b.eq    <mldsa87_poly_uniform_eta_4x+0x94c>
     +0x924: cmp     x19, #0xff
     +0x928: b.hi    <mldsa87_poly_uniform_eta_4x+0x94c>
     +0x92c: mul     w10, w9, w21
     +0x930: lsr     w10, w10, #10
     +0x934: orr     w10, w10, w10, lsl #2
     +0x938: sub     w9, w10, w9
     +0x93c: add     x10, x19, #0x1
     +0x940: add     w9, w9, #0x2
     +0x944: str     w9, [x12, x19, lsl #2]
     +0x948: mov     x19, x10
     +0x94c: cmp     x19, #0xff
     +0x950: b.hi    <mldsa87_poly_uniform_eta_4x+0x960>
     +0x954: cmp     x8, #0x87
     +0x958: add     x8, x8, #0x1
     +0x95c: b.cc    <mldsa87_poly_uniform_eta_4x+0x8e8>
     +0x960: cmp     x25, #0x100
     +0x964: cset    w1, cc
     +0x968: cmp     x24, #0x100
     +0x96c: cset    w16, cc
     +0x970: cmp     x19, #0x100
     +0x974: cset    w11, cc
     +0x978: cmp     x26, #0x100
     +0x97c: cset    w2, cc
     +0x980: b.cc    <mldsa87_poly_uniform_eta_4x+0x644>
     +0x984: cmp     x25, #0x100
     +0x988: b.cc    <mldsa87_poly_uniform_eta_4x+0x644>
     +0x98c: cmp     x24, #0x100
     +0x990: b.cc    <mldsa87_poly_uniform_eta_4x+0x644>
     +0x994: cmp     x19, #0x100
     +0x998: b.cc    <mldsa87_poly_uniform_eta_4x+0x644>
     +0x99c: add     x0, sp, #0x60
     +0x9a0: mov     w1, wzr
     +0x9a4: mov     w2, #0x320
     +0x9a8: add     x19, sp, #0x60
     +0x9ac: bl      <memset>
     +0x9b0: add     x0, sp, #0x500
     +0x9b4: mov     w1, wzr
     +0x9b8: mov     w2, #0x280
     +0x9bc: add     x19, sp, #0x500
     +0x9c0: bl      <memset>
     +0x9c4: movi    v0.2d, #0x0
     +0x9c8: add     x8, sp, #0x380
     +0x9cc: str     q0, [sp, #1264]
     +0x9d0: str     q0, [sp, #1248]
     +0x9d4: str     q0, [sp, #1232]
     +0x9d8: str     q0, [sp, #1216]
     +0x9dc: str     q0, [sp, #1200]
     +0x9e0: str     q0, [sp, #1184]
     +0x9e4: str     q0, [sp, #1168]
     +0x9e8: str     q0, [sp, #1152]
     +0x9ec: str     q0, [sp, #1136]
     +0x9f0: str     q0, [sp, #1120]
     +0x9f4: str     q0, [sp, #1104]
     +0x9f8: str     q0, [sp, #1088]
     +0x9fc: str     q0, [sp, #1072]
     +0xa00: str     q0, [sp, #1056]
     +0xa04: str     q0, [sp, #1040]
     +0xa08: stp     q0, q0, [sp, #912]
     +0xa0c: stp     q0, q0, [sp, #944]
     +0xa10: stp     q0, q0, [sp, #976]
     +0xa14: stp     q0, q0, [sp, #1008]
     +0xa18: str     q0, [sp, #896]
     +0xa1c: adrp    x8, <page>
     +0xa20: ldr     x8, [x8, #4088]
     +0xa24: ldr     x9, [sp, #1944]
     +0xa28: ldr     x8, [x8]
     +0xa2c: cmp     x8, x9
     +0xa30: b.ne    <mldsa87_poly_uniform_eta_4x+0xa98>
     +0xa34: mov     sp, x29
     +0xa38: ldp     x20, x19, [sp, #80]
     +0xa3c: ldp     x22, x21, [sp, #64]
     +0xa40: ldp     x24, x23, [sp, #48]
     +0xa44: ldp     x26, x25, [sp, #32]
     +0xa48: ldp     x28, x27, [sp, #16]
     +0xa4c: ldp     x29, x30, [sp], #96
     +0xa50: mov     x0, #0x0
     +0xa54: mov     x1, #0x0
     +0xa58: mov     x2, #0x0
     +0xa5c: mov     x3, #0x0
     +0xa60: mov     x4, #0x0
     +0xa64: mov     x5, #0x0
     +0xa68: mov     x6, #0x0
     +0xa6c: mov     x7, #0x0
     +0xa70: mov     x8, #0x0
     +0xa74: mov     x9, #0x0
     +0xa78: mov     x10, #0x0
     +0xa7c: mov     x11, #0x0
     +0xa80: mov     x12, #0x0
     +0xa84: mov     x13, #0x0
     +0xa88: mov     x14, #0x0
     +0xa8c: mov     x15, #0x0
     +0xa90: mov     x16, #0x0
     +0xa94: ret     
     +0xa98: bl      <__stack_chk_fail>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa87_poly_uniform_eta_4x";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The seed is the 64 bytes   *)
(* sd at seed, and polynomial j becomes mld_poly_uniform_eta 2 sd of the     *)
(* nonce j, if the SHAKE256 output of the extended seed has 256 acceptable   *)
(* nibbles. The stack is the 2336 bytes below the stack pointer (see above), *)
(* and the fourth nonce is the byte at the stack pointer.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !r0 r1 r2 r3 seed sd n0 n1 n2 n3 guard pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(n3:byte))) /\
          PAIRWISE nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2336),2336)] /\
          ALLPAIRS nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2336),2336)]
           [(seed,64); (stackpointer,1);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa87_poly_uniform_eta_4x) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r0; r1; r2; r3; seed; n0; n1; n2] s /\
                    read (memory :> bytes8 stackpointer) s = n3 /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,64)) s = sd)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r0 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 2 sd (word_zx n0) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 2 sd (word_zx n1) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 2 sd (word_zx n2) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 2 sd n3 i))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                  memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                  memory :> bytes(word_sub stackpointer (word 2336),2336)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the address of memset, the stack  *)
(* and the lists of the values that mld_rej_eta_c declassifies for each      *)
(* polynomial, with all accesses within the arguments, the stack, the GOT    *)
(* entries and the stack guard, the region (ea,el) that memset may read and  *)
(* the round constants of Keccak, and the writes within the polynomials and  *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e r0 r1 r2 r3 seed sd n0 n1 n2 n3 guard pc stackpointer
                 returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(n3:byte))) /\
          PAIRWISE nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2336),2336)] /\
          ALLPAIRS nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2336),2336)]
           [(seed,64); (stackpointer,1);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa87_poly_uniform_eta_4x) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r0; r1; r2; r3; seed; n0; n1; n2] s /\
                    read (memory :> bytes8 stackpointer) s = n3 /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,64)) s = sd /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r0 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 2 sd (word_zx n0) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 2 sd (word_zx n1) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 2 sd (word_zx n2) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 2 sd n3 i) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events r0 r1 r2 r3 seed
                         (mld_poly_uniform_eta_declass 2
                           (mld_shake256_stream 66
                             (sd + 2 EXP 512 * val(word_zx n0:byte))))
                         (mld_poly_uniform_eta_declass 2
                           (mld_shake256_stream 66
                             (sd + 2 EXP 512 * val(word_zx n1:byte))))
                         (mld_poly_uniform_eta_declass 2
                           (mld_shake256_stream 66
                             (sd + 2 EXP 512 * val(word_zx n2:byte))))
                         (mld_poly_uniform_eta_declass 2
                           (mld_shake256_stream 66
                             (sd + 2 EXP 512 * val(n3:byte))))
                         guard mf pc (word_sub stackpointer (word 2336))
                         returnaddress /\
                       memaccess_inbounds e2
                        [seed,64; stackpointer,1;
                         r0,1024; r1,1024; r2,1024; r3,1024;
                         word_sub stackpointer (word 2336),2336;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [r0,1024; r1,1024; r2,1024; r3,1024;
                         word_sub stackpointer (word 2336),2336]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                  memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                  memory :> bytes(word_sub stackpointer (word 2336),2336)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* seed only through the declassified validity of the nibbles of the         *)
(* streams, as above.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e r0 r1 r2 r3 seed sd n0 n1 n2 n3 guard pc stackpointer
                 returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
          mld_rej_eta_terminates 2
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(n3:byte))) /\
          PAIRWISE nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2336),2336)] /\
          ALLPAIRS nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2336),2336)]
           [(seed,64); (stackpointer,1);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa87_poly_uniform_eta_4x) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r0; r1; r2; r3; seed; n0; n1; n2] s /\
                    read (memory :> bytes8 stackpointer) s = n3 /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,64)) s = sd /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events r0 r1 r2 r3 seed
                         (mld_poly_uniform_eta_declass 2
                           (mld_shake256_stream 66
                             (sd + 2 EXP 512 * val(word_zx n0:byte))))
                         (mld_poly_uniform_eta_declass 2
                           (mld_shake256_stream 66
                             (sd + 2 EXP 512 * val(word_zx n1:byte))))
                         (mld_poly_uniform_eta_declass 2
                           (mld_shake256_stream 66
                             (sd + 2 EXP 512 * val(word_zx n2:byte))))
                         (mld_poly_uniform_eta_declass 2
                           (mld_shake256_stream 66
                             (sd + 2 EXP 512 * val(n3:byte))))
                         guard mf pc (word_sub stackpointer (word 2336))
                         returnaddress /\
                       memaccess_inbounds e2
                        [seed,64; stackpointer,1;
                         r0,1024; r1,1024; r2,1024; r3,1024;
                         word_sub stackpointer (word 2336),2336;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [r0,1024; r1,1024; r2,1024; r3,1024;
                         word_sub stackpointer (word 2336),2336]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                  memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                  memory :> bytes(word_sub stackpointer (word 2336),2336)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
