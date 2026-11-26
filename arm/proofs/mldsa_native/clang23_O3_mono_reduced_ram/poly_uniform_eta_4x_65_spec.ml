(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of four polynomials with coefficients in [-4,4] for ML-DSA-65 by *)
(* rejection: the statement. This is the code for                            *)
(* mldsa65_poly_uniform_eta_4x (mld_poly_uniform_eta_4x in poly_kl.c) from   *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3 as *)
(* a monolithic build with MLD_CONFIG_REDUCE_RAM (see                        *)
(* mldsa_native/README.md). Clang inlined the fourfold SHAKE256 functions    *)
(* and the rejection sampling (mld_rej_eta): the function aligns its frame   *)
(* to 32 bytes, copies the seed of 64 bytes four times with the four nonce   *)
(* bytes and a zero byte, zeroes four Keccak states with memset, XORs the    *)
(* four extended seeds of 66 bytes and the padding into them with straight-  *)
(* line code, permutes each with mldsa_keccakf1600_permute, copies the first *)
(* two blocks of each to a buffer and samples the coefficients from them,    *)
(* and then, while a polynomial has fewer than 256 coefficients, permutes    *)
(* all four states, copies their next blocks and samples from those of the   *)
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
(* The stack is the 2848 bytes below the stack pointer of the caller: the 96 *)
(* bytes of saved registers, the frame of 2464 bytes (the realignment to 32  *)
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

    mldsa65_poly_uniform_eta_4x:
       +0x0: stp     x29, x30, [sp, #-96]!
       +0x4: stp     x28, x27, [sp, #16]
       +0x8: stp     x26, x25, [sp, #32]
       +0xc: stp     x24, x23, [sp, #48]
      +0x10: stp     x22, x21, [sp, #64]
      +0x14: stp     x20, x19, [sp, #80]
      +0x18: mov     x29, sp
      +0x1c: sub     x9, sp, #0x9a0
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
      +0x4c: add     x25, sp, #0x500
      +0x50: add     x24, x19, #0x258
      +0x54: ldr     x8, [x8]
      +0x58: str     x8, [sp, #2456]
      +0x5c: ldrb    w8, [x29, #96]
      +0x60: ldp     q0, q1, [x4]
      +0x64: strb    w5, [sp, #960]
      +0x68: ldp     q2, q3, [x4, #32]
      +0x6c: strb    w6, [sp, #1056]
      +0x70: strb    w7, [sp, #1152]
      +0x74: stp     q0, q1, [sp, #896]
      +0x78: stp     q2, q3, [sp, #928]
      +0x7c: stp     q0, q1, [sp, #992]
      +0x80: str     q2, [sp, #1024]
      +0x84: str     q3, [sp, #1040]
      +0x88: str     q3, [sp, #1136]
      +0x8c: str     q2, [sp, #1120]
      +0x90: str     q1, [sp, #1104]
      +0x94: str     q0, [sp, #1088]
      +0x98: str     q1, [sp, #1200]
      +0x9c: str     q0, [sp, #1184]
      +0xa0: str     q2, [sp, #1216]
      +0xa4: str     q3, [sp, #1232]
      +0xa8: strb    w8, [sp, #1248]
      +0xac: strb    wzr, [sp, #961]
      +0xb0: strb    wzr, [sp, #1057]
      +0xb4: strb    wzr, [sp, #1153]
      +0xb8: strb    wzr, [sp, #1249]
      +0xbc: bl      <memset>
      +0xc0: ldr     h0, [sp, #960]
      +0xc4: ldr     h1, [sp, #160]
      +0xc8: add     x0, sp, #0x60
      +0xcc: ldp     q2, q3, [sp, #896]
      +0xd0: add     x26, x25, #0x360
      +0xd4: ldp     q4, q5, [sp, #96]
      +0xd8: uxtl    v0.8h, v0.8b
      +0xdc: uxtl    v1.8h, v1.8b
      +0xe0: ldp     q6, q7, [sp, #928]
      +0xe4: ldp     q16, q17, [sp, #128]
      +0xe8: add     x27, x25, #0x240
      +0xec: eor     v2.16b, v4.16b, v2.16b
      +0xf0: eor     v3.16b, v5.16b, v3.16b
      +0xf4: uxtl    v0.4s, v0.4h
      +0xf8: uxtl    v1.4s, v1.4h
      +0xfc: ldp     q4, q18, [sp, #992]
     +0x100: eor     v6.16b, v16.16b, v6.16b
     +0x104: eor     v7.16b, v17.16b, v7.16b
     +0x108: ldr     h17, [sp, #1056]
     +0x10c: stp     q2, q3, [sp, #96]
     +0x110: ldr     h2, [sp, #360]
     +0x114: ldur    q3, [x19, #232]
     +0x118: eor     v0.8b, v1.8b, v0.8b
     +0x11c: ldr     q1, [sp, #1024]
     +0x120: ldur    q5, [x19, #200]
     +0x124: stp     q6, q7, [sp, #128]
     +0x128: uxtl    v6.8h, v17.8b
     +0x12c: uxtl    v2.8h, v2.8b
     +0x130: ldur    q16, [x19, #216]
     +0x134: eor     v1.16b, v3.16b, v1.16b
     +0x138: eor     v4.16b, v5.16b, v4.16b
     +0x13c: stur    b0, [sp, #160]
     +0x140: mov     s0, v0.s[1]
     +0x144: ldr     q7, [sp, #1040]
     +0x148: uxtl    v3.4s, v6.4h
     +0x14c: uxtl    v2.4s, v2.4h
     +0x150: eor     v5.16b, v16.16b, v18.16b
     +0x154: ldur    q16, [x19, #248]
     +0x158: stur    q1, [x19, #232]
     +0x15c: ldrb    w8, [sp, #162]
     +0x160: stur    q4, [x19, #200]
     +0x164: ldrb    w9, [sp, #362]
     +0x168: ldrb    w10, [sp, #562]
     +0x16c: eor     v1.8b, v2.8b, v3.8b
     +0x170: stur    b0, [sp, #161]
     +0x174: ldr     h0, [sp, #1152]
     +0x178: ldr     h2, [sp, #560]
     +0x17c: eor     v4.16b, v16.16b, v7.16b
     +0x180: stur    q5, [x19, #216]
     +0x184: uxtl    v0.8h, v0.8b
     +0x188: ldr     q3, [sp, #1088]
     +0x18c: ldr     q5, [sp, #1104]
     +0x190: uxtl    v2.8h, v2.8b
     +0x194: str     b1, [sp, #360]
     +0x198: mov     s1, v1.s[1]
     +0x19c: stur    q4, [x19, #248]
     +0x1a0: ldp     q4, q6, [sp, #496]
     +0x1a4: uxtl    v0.4s, v0.4h
     +0x1a8: ldp     q16, q17, [sp, #528]
     +0x1ac: uxtl    v2.4s, v2.4h
     +0x1b0: ldr     q7, [sp, #1136]
     +0x1b4: eor     w8, w8, #0x1f
     +0x1b8: eor     v3.16b, v4.16b, v3.16b
     +0x1bc: str     b1, [sp, #361]
     +0x1c0: eor     v1.16b, v6.16b, v5.16b
     +0x1c4: ldr     h6, [sp, #760]
     +0x1c8: ldr     q4, [sp, #1120]
     +0x1cc: eor     v5.16b, v17.16b, v7.16b
     +0x1d0: eor     v0.8b, v2.8b, v0.8b
     +0x1d4: ldr     h2, [sp, #1248]
     +0x1d8: strb    w8, [sp, #162]
     +0x1dc: stp     q3, q1, [sp, #496]
     +0x1e0: eor     v4.16b, v16.16b, v4.16b
     +0x1e4: eor     w8, w9, #0x1f
     +0x1e8: uxtl    v1.8h, v2.8b
     +0x1ec: uxtl    v2.8h, v6.8b
     +0x1f0: ldrb    w9, [sp, #762]
     +0x1f4: ldp     q6, q7, [x24]
     +0x1f8: mov     s3, v0.s[1]
     +0x1fc: stp     q4, q5, [sp, #528]
     +0x200: ldr     q4, [sp, #1184]
     +0x204: ldr     q5, [sp, #1200]
     +0x208: uxtl    v1.4s, v1.4h
     +0x20c: uxtl    v2.4s, v2.4h
     +0x210: str     b0, [sp, #560]
     +0x214: eor     v0.16b, v6.16b, v4.16b
     +0x218: eor     v4.16b, v7.16b, v5.16b
     +0x21c: strb    w8, [sp, #362]
     +0x220: eor     w8, w10, #0x1f
     +0x224: ldrb    w10, [sp, #231]
     +0x228: ldr     q6, [sp, #1216]
     +0x22c: eor     v1.8b, v2.8b, v1.8b
     +0x230: ldp     q5, q2, [x24, #32]
     +0x234: ldr     q7, [sp, #1232]
     +0x238: strb    w8, [sp, #562]
     +0x23c: eor     w8, w9, #0x1f
     +0x240: ldrb    w9, [sp, #431]
     +0x244: stp     q0, q4, [x24]
     +0x248: add     x28, x25, #0x120
     +0x24c: mov     s0, v1.s[1]
     +0x250: strb    w8, [sp, #762]
     +0x254: eor     w8, w10, #0x80
     +0x258: ldrb    w10, [sp, #631]
     +0x25c: str     b3, [sp, #561]
     +0x260: eor     v3.16b, v5.16b, v6.16b
     +0x264: eor     v2.16b, v2.16b, v7.16b
     +0x268: strb    w8, [sp, #231]
     +0x26c: eor     w8, w9, #0x80
     +0x270: ldrb    w9, [sp, #831]
     +0x274: strb    w8, [sp, #431]
     +0x278: eor     w8, w10, #0x80
     +0x27c: strb    w8, [sp, #631]
     +0x280: eor     w8, w9, #0x80
     +0x284: add     x9, x19, #0x190
     +0x288: stp     q3, q2, [x24, #32]
     +0x28c: str     b1, [sp, #760]
     +0x290: str     b0, [sp, #761]
     +0x294: str     x9, [sp, #24]
     +0x298: strb    w8, [sp, #831]
     +0x29c: bl      <mldsa_keccakf1600_permute>
     +0x2a0: add     x0, x19, #0xc8
     +0x2a4: bl      <mldsa_keccakf1600_permute>
     +0x2a8: add     x0, x19, #0x190
     +0x2ac: bl      <mldsa_keccakf1600_permute>
     +0x2b0: add     x0, x19, #0x258
     +0x2b4: bl      <mldsa_keccakf1600_permute>
     +0x2b8: ldp     q0, q1, [sp, #160]
     +0x2bc: add     x8, x19, #0xc8
     +0x2c0: ldr     x9, [sp, #424]
     +0x2c4: add     x0, sp, #0x60
     +0x2c8: add     x20, x25, #0x3e8
     +0x2cc: add     x21, x25, #0x2c8
     +0x2d0: add     x22, x25, #0x1a8
     +0x2d4: str     q0, [sp, #1344]
     +0x2d8: ldp     q0, q2, [sp, #192]
     +0x2dc: str     q1, [sp, #1360]
     +0x2e0: str     x9, [sp, #1696]
     +0x2e4: ldr     x9, [sp, #824]
     +0x2e8: str     q0, [sp, #1376]
     +0x2ec: ldp     q1, q0, [sp, #96]
     +0x2f0: str     q2, [sp, #1392]
     +0x2f4: str     x9, [sp, #2272]
     +0x2f8: str     q0, [sp, #1296]
     +0x2fc: ldp     q2, q0, [sp, #128]
     +0x300: str     q1, [sp, #1280]
     +0x304: str     q0, [sp, #1328]
     +0x308: ldp     q1, q0, [x8, #64]
     +0x30c: str     q2, [sp, #1312]
     +0x310: str     q0, [sp, #1648]
     +0x314: ldp     q2, q0, [x8, #96]
     +0x318: str     q1, [sp, #1632]
     +0x31c: ldur    q1, [x19, #200]
     +0x320: ldr     x8, [sp, #224]
     +0x324: str     q0, [sp, #1680]
     +0x328: ldur    q0, [x19, #216]
     +0x32c: str     q1, [sp, #1568]
     +0x330: str     q0, [sp, #1584]
     +0x334: ldur    q0, [x19, #248]
     +0x338: str     q2, [sp, #1664]
     +0x33c: ldur    q2, [x19, #232]
     +0x340: str     q0, [sp, #1616]
     +0x344: ldp     q1, q0, [sp, #560]
     +0x348: str     q2, [sp, #1600]
     +0x34c: str     x8, [sp, #1408]
     +0x350: ldr     x8, [sp, #624]
     +0x354: str     q0, [sp, #1936]
     +0x358: ldp     q2, q0, [sp, #592]
     +0x35c: str     q1, [sp, #1920]
     +0x360: str     x8, [sp, #1984]
     +0x364: str     q0, [sp, #1968]
     +0x368: ldp     q1, q0, [sp, #496]
     +0x36c: str     q2, [sp, #1952]
     +0x370: str     q0, [sp, #1872]
     +0x374: ldp     q2, q0, [sp, #528]
     +0x378: str     q1, [sp, #1856]
     +0x37c: str     q0, [sp, #1904]
     +0x380: ldp     q1, q0, [x24, #64]
     +0x384: str     q2, [sp, #1888]
     +0x388: str     q0, [sp, #2224]
     +0x38c: ldp     q2, q0, [x24, #96]
     +0x390: str     q1, [sp, #2208]
     +0x394: str     q0, [sp, #2256]
     +0x398: ldp     q1, q0, [x24]
     +0x39c: str     q2, [sp, #2240]
     +0x3a0: str     q1, [sp, #2144]
     +0x3a4: str     q0, [sp, #2160]
     +0x3a8: ldp     q1, q0, [x24, #32]
     +0x3ac: str     q1, [sp, #2176]
     +0x3b0: str     q0, [sp, #2192]
     +0x3b4: bl      <mldsa_keccakf1600_permute>
     +0x3b8: add     x0, x19, #0xc8
     +0x3bc: bl      <mldsa_keccakf1600_permute>
     +0x3c0: add     x0, x19, #0x190
     +0x3c4: bl      <mldsa_keccakf1600_permute>
     +0x3c8: add     x0, x19, #0x258
     +0x3cc: bl      <mldsa_keccakf1600_permute>
     +0x3d0: ldp     q0, q1, [sp, #160]
     +0x3d4: add     x10, x19, #0xc8
     +0x3d8: add     x9, x19, #0xc8
     +0x3dc: mov     x8, xzr
     +0x3e0: mov     x23, xzr
     +0x3e4: stp     x9, x24, [sp, #32]
     +0x3e8: ldr     x9, [sp, #224]
     +0x3ec: stur    q0, [x25, #200]
     +0x3f0: ldp     q0, q2, [sp, #192]
     +0x3f4: stur    q1, [x25, #216]
     +0x3f8: str     x9, [sp, #1544]
     +0x3fc: ldr     x9, [sp, #624]
     +0x400: stur    q0, [x25, #232]
     +0x404: ldp     q0, q1, [sp, #96]
     +0x408: stur    q2, [x25, #248]
     +0x40c: str     x9, [sp, #2120]
     +0x410: mov     w9, #0x4
     +0x414: stur    q0, [x25, #136]
     +0x418: stur    q1, [x25, #152]
     +0x41c: ldp     q0, q1, [sp, #128]
     +0x420: stur    q0, [x25, #168]
     +0x424: stur    q1, [x25, #184]
     +0x428: ldp     q0, q1, [x10, #64]
     +0x42c: stp     q0, q1, [x22, #64]
     +0x430: ldp     q2, q0, [x10, #96]
     +0x434: ldur    q1, [x19, #200]
     +0x438: ldr     x10, [sp, #424]
     +0x43c: stp     q2, q0, [x22, #96]
     +0x440: ldur    q0, [x19, #216]
     +0x444: ldur    q2, [x19, #232]
     +0x448: str     x10, [sp, #1832]
     +0x44c: ldr     x10, [sp, #824]
     +0x450: stp     q1, q0, [x22]
     +0x454: ldur    q0, [x19, #248]
     +0x458: str     x10, [sp, #2408]
     +0x45c: stp     q2, q0, [x22, #32]
     +0x460: ldp     q0, q1, [sp, #560]
     +0x464: stp     q0, q1, [x21, #64]
     +0x468: ldp     q2, q0, [sp, #592]
     +0x46c: stp     q2, q0, [x21, #96]
     +0x470: ldp     q1, q0, [sp, #496]
     +0x474: stp     q1, q0, [x21]
     +0x478: ldp     q2, q0, [sp, #528]
     +0x47c: stp     q2, q0, [x21, #32]
     +0x480: ldp     q0, q1, [x24, #64]
     +0x484: stp     q0, q1, [x20, #64]
     +0x488: ldp     q2, q0, [x24, #96]
     +0x48c: stp     q2, q0, [x20, #96]
     +0x490: ldp     q1, q0, [x24]
     +0x494: stp     q1, q0, [x20]
     +0x498: ldp     q2, q0, [x24, #32]
     +0x49c: stp     q2, q0, [x20, #32]
     +0x4a0: ldrb    w10, [x25, x8]
     +0x4a4: and     w11, w10, #0xf
     +0x4a8: cmp     w11, #0x8
     +0x4ac: b.hi    <mldsa65_poly_uniform_eta_4x+0x4d0>
     +0x4b0: ldr     x13, [sp, #88]
     +0x4b4: add     x12, x23, #0x1
     +0x4b8: sub     w11, w9, w11
     +0x4bc: str     w11, [x13, x23, lsl #2]
     +0x4c0: mov     x23, x12
     +0x4c4: cmp     w10, #0x8f
     +0x4c8: b.ls    <mldsa65_poly_uniform_eta_4x+0x4dc>
     +0x4cc: b       <mldsa65_poly_uniform_eta_4x+0x4f8>
     +0x4d0: ldr     x13, [sp, #88]
     +0x4d4: cmp     w10, #0x8f
     +0x4d8: b.hi    <mldsa65_poly_uniform_eta_4x+0x4f8>
     +0x4dc: cmp     x23, #0xff
     +0x4e0: b.hi    <mldsa65_poly_uniform_eta_4x+0x4f8>
     +0x4e4: lsr     w10, w10, #4
     +0x4e8: add     x11, x23, #0x1
     +0x4ec: sub     w10, w9, w10
     +0x4f0: str     w10, [x13, x23, lsl #2]
     +0x4f4: mov     x23, x11
     +0x4f8: cmp     x23, #0x100
     +0x4fc: cset    w18, cc
     +0x500: cmp     x23, #0xff
     +0x504: b.hi    <mldsa65_poly_uniform_eta_4x+0x514>
     +0x508: cmp     x8, #0x10f
     +0x50c: add     x8, x8, #0x1
     +0x510: b.cc    <mldsa65_poly_uniform_eta_4x+0x4a0>
     +0x514: ldp     x15, x14, [sp, #56]
     +0x518: mov     x8, xzr
     +0x51c: ldr     x16, [sp, #48]
     +0x520: mov     x25, xzr
     +0x524: add     x9, sp, #0x500
     +0x528: mov     w10, #0x4
     +0x52c: add     x11, x9, x8
     +0x530: ldrb    w11, [x11, #288]
     +0x534: and     w12, w11, #0xf
     +0x538: cmp     w12, #0x8
     +0x53c: b.hi    <mldsa65_poly_uniform_eta_4x+0x550>
     +0x540: add     x13, x25, #0x1
     +0x544: sub     w12, w10, w12
     +0x548: str     w12, [x16, x25, lsl #2]
     +0x54c: mov     x25, x13
     +0x550: cmp     w11, #0x8f
     +0x554: b.hi    <mldsa65_poly_uniform_eta_4x+0x574>
     +0x558: cmp     x25, #0xff
     +0x55c: b.hi    <mldsa65_poly_uniform_eta_4x+0x574>
     +0x560: lsr     w11, w11, #4
     +0x564: add     x12, x25, #0x1
     +0x568: sub     w11, w10, w11
     +0x56c: str     w11, [x16, x25, lsl #2]
     +0x570: mov     x25, x12
     +0x574: cmp     x25, #0x100
     +0x578: cset    w17, cc
     +0x57c: cmp     x25, #0xff
     +0x580: b.hi    <mldsa65_poly_uniform_eta_4x+0x590>
     +0x584: cmp     x8, #0x10f
     +0x588: add     x8, x8, #0x1
     +0x58c: b.cc    <mldsa65_poly_uniform_eta_4x+0x52c>
     +0x590: mov     x8, xzr
     +0x594: mov     x24, xzr
     +0x598: add     x9, sp, #0x500
     +0x59c: mov     w10, #0x4
     +0x5a0: add     x11, x9, x8
     +0x5a4: ldrb    w11, [x11, #576]
     +0x5a8: and     w12, w11, #0xf
     +0x5ac: cmp     w12, #0x8
     +0x5b0: b.hi    <mldsa65_poly_uniform_eta_4x+0x5c4>
     +0x5b4: add     x13, x24, #0x1
     +0x5b8: sub     w12, w10, w12
     +0x5bc: str     w12, [x15, x24, lsl #2]
     +0x5c0: mov     x24, x13
     +0x5c4: cmp     w11, #0x8f
     +0x5c8: b.hi    <mldsa65_poly_uniform_eta_4x+0x5e8>
     +0x5cc: cmp     x24, #0xff
     +0x5d0: b.hi    <mldsa65_poly_uniform_eta_4x+0x5e8>
     +0x5d4: lsr     w11, w11, #4
     +0x5d8: add     x12, x24, #0x1
     +0x5dc: sub     w11, w10, w11
     +0x5e0: str     w11, [x15, x24, lsl #2]
     +0x5e4: mov     x24, x12
     +0x5e8: cmp     x24, #0x100
     +0x5ec: cset    w16, cc
     +0x5f0: cmp     x24, #0xff
     +0x5f4: b.hi    <mldsa65_poly_uniform_eta_4x+0x604>
     +0x5f8: cmp     x8, #0x10f
     +0x5fc: add     x8, x8, #0x1
     +0x600: b.cc    <mldsa65_poly_uniform_eta_4x+0x5a0>
     +0x604: mov     x8, xzr
     +0x608: mov     x19, xzr
     +0x60c: add     x9, sp, #0x500
     +0x610: mov     w10, #0x4
     +0x614: add     x11, x9, x8
     +0x618: ldrb    w11, [x11, #864]
     +0x61c: and     w12, w11, #0xf
     +0x620: cmp     w12, #0x8
     +0x624: b.hi    <mldsa65_poly_uniform_eta_4x+0x638>
     +0x628: add     x13, x19, #0x1
     +0x62c: sub     w12, w10, w12
     +0x630: str     w12, [x14, x19, lsl #2]
     +0x634: mov     x19, x13
     +0x638: cmp     w11, #0x8f
     +0x63c: b.hi    <mldsa65_poly_uniform_eta_4x+0x65c>
     +0x640: cmp     x19, #0xff
     +0x644: b.hi    <mldsa65_poly_uniform_eta_4x+0x65c>
     +0x648: lsr     w11, w11, #4
     +0x64c: add     x12, x19, #0x1
     +0x650: sub     w11, w10, w11
     +0x654: str     w11, [x14, x19, lsl #2]
     +0x658: mov     x19, x12
     +0x65c: cmp     x19, #0x100
     +0x660: cset    w11, cc
     +0x664: cmp     x19, #0xff
     +0x668: b.hi    <mldsa65_poly_uniform_eta_4x+0x678>
     +0x66c: cmp     x8, #0x10f
     +0x670: add     x8, x8, #0x1
     +0x674: b.cc    <mldsa65_poly_uniform_eta_4x+0x614>
     +0x678: cmp     x23, #0x100
     +0x67c: b.cc    <mldsa65_poly_uniform_eta_4x+0x698>
     +0x680: cmp     x25, #0x100
     +0x684: b.cc    <mldsa65_poly_uniform_eta_4x+0x698>
     +0x688: cmp     x24, #0x100
     +0x68c: b.cc    <mldsa65_poly_uniform_eta_4x+0x698>
     +0x690: cmp     x19, #0xff
     +0x694: b.hi    <mldsa65_poly_uniform_eta_4x+0x97c>
     +0x698: mov     w21, #0x4
     +0x69c: str     x26, [sp, #16]
     +0x6a0: add     x0, sp, #0x60
     +0x6a4: stp     w18, w11, [sp, #72]
     +0x6a8: stp     w16, w17, [sp, #80]
     +0x6ac: bl      <mldsa_keccakf1600_permute>
     +0x6b0: ldr     x20, [sp, #32]
     +0x6b4: mov     x0, x20
     +0x6b8: bl      <mldsa_keccakf1600_permute>
     +0x6bc: ldr     x26, [sp, #24]
     +0x6c0: mov     x0, x26
     +0x6c4: bl      <mldsa_keccakf1600_permute>
     +0x6c8: ldr     x22, [sp, #40]
     +0x6cc: mov     x0, x22
     +0x6d0: bl      <mldsa_keccakf1600_permute>
     +0x6d4: ldp     q0, q1, [sp, #160]
     +0x6d8: ldr     x8, [sp, #224]
     +0x6dc: str     x8, [sp, #1408]
     +0x6e0: ldr     x8, [x20, #128]
     +0x6e4: str     q0, [sp, #1344]
     +0x6e8: ldp     q2, q0, [sp, #192]
     +0x6ec: str     q1, [sp, #1360]
     +0x6f0: str     x8, [x28, #128]
     +0x6f4: ldr     x8, [x26, #128]
     +0x6f8: str     q0, [sp, #1392]
     +0x6fc: ldp     q1, q0, [sp, #96]
     +0x700: str     q2, [sp, #1376]
     +0x704: str     x8, [x27, #128]
     +0x708: ldr     x8, [x22, #128]
     +0x70c: str     q0, [sp, #1296]
     +0x710: ldp     q2, q0, [sp, #128]
     +0x714: str     q1, [sp, #1280]
     +0x718: str     q0, [sp, #1328]
     +0x71c: ldp     q0, q1, [x20, #64]
     +0x720: str     q2, [sp, #1312]
     +0x724: stp     q0, q1, [x28, #64]
     +0x728: ldp     q2, q0, [x20, #96]
     +0x72c: stp     q2, q0, [x28, #96]
     +0x730: ldp     q1, q0, [x20]
     +0x734: stp     q1, q0, [x28]
     +0x738: ldp     q2, q0, [x20, #32]
     +0x73c: stp     q2, q0, [x28, #32]
     +0x740: ldp     q0, q1, [x26, #64]
     +0x744: stp     q0, q1, [x27, #64]
     +0x748: ldp     q2, q0, [x26, #96]
     +0x74c: stp     q2, q0, [x27, #96]
     +0x750: ldp     q1, q0, [x26]
     +0x754: stp     q1, q0, [x27]
     +0x758: ldp     q2, q0, [x26, #32]
     +0x75c: ldr     x26, [sp, #16]
     +0x760: stp     q2, q0, [x27, #32]
     +0x764: ldp     q0, q1, [x22, #64]
     +0x768: str     x8, [x26, #128]
     +0x76c: ldr     w8, [sp, #72]
     +0x770: stp     q0, q1, [x26, #64]
     +0x774: ldp     q2, q0, [x22, #96]
     +0x778: stp     q2, q0, [x26, #96]
     +0x77c: ldp     q1, q0, [x22]
     +0x780: stp     q1, q0, [x26]
     +0x784: ldp     q2, q0, [x22, #32]
     +0x788: stp     q2, q0, [x26, #32]
     +0x78c: tbz     w8, #0, <mldsa65_poly_uniform_eta_4x+0x868>
     +0x790: ldp     x13, x12, [sp, #56]
     +0x794: mov     x8, xzr
     +0x798: ldr     x14, [sp, #48]
     +0x79c: ldr     x15, [sp, #88]
     +0x7a0: add     x16, sp, #0x500
     +0x7a4: ldr     w17, [sp, #84]
     +0x7a8: ldrb    w9, [x16, x8]
     +0x7ac: and     w10, w9, #0xf
     +0x7b0: cmp     w10, #0x8
     +0x7b4: b.hi    <mldsa65_poly_uniform_eta_4x+0x7c8>
     +0x7b8: add     x11, x23, #0x1
     +0x7bc: sub     w10, w21, w10
     +0x7c0: str     w10, [x15, x23, lsl #2]
     +0x7c4: mov     x23, x11
     +0x7c8: cmp     w9, #0x8f
     +0x7cc: b.hi    <mldsa65_poly_uniform_eta_4x+0x7ec>
     +0x7d0: cmp     x23, #0xff
     +0x7d4: b.hi    <mldsa65_poly_uniform_eta_4x+0x7ec>
     +0x7d8: lsr     w9, w9, #4
     +0x7dc: add     x10, x23, #0x1
     +0x7e0: sub     w9, w21, w9
     +0x7e4: str     w9, [x15, x23, lsl #2]
     +0x7e8: mov     x23, x10
     +0x7ec: cmp     x23, #0xff
     +0x7f0: b.hi    <mldsa65_poly_uniform_eta_4x+0x800>
     +0x7f4: cmp     x8, #0x87
     +0x7f8: add     x8, x8, #0x1
     +0x7fc: b.cc    <mldsa65_poly_uniform_eta_4x+0x7a8>
     +0x800: tbz     w17, #0, <mldsa65_poly_uniform_eta_4x+0x878>
     +0x804: ldr     w15, [sp, #80]
     +0x808: mov     x8, xzr
     +0x80c: ldrb    w9, [x28, x8]
     +0x810: and     w10, w9, #0xf
     +0x814: cmp     w10, #0x8
     +0x818: b.hi    <mldsa65_poly_uniform_eta_4x+0x82c>
     +0x81c: add     x11, x25, #0x1
     +0x820: sub     w10, w21, w10
     +0x824: str     w10, [x14, x25, lsl #2]
     +0x828: mov     x25, x11
     +0x82c: cmp     w9, #0x8f
     +0x830: b.hi    <mldsa65_poly_uniform_eta_4x+0x850>
     +0x834: cmp     x25, #0xff
     +0x838: b.hi    <mldsa65_poly_uniform_eta_4x+0x850>
     +0x83c: lsr     w9, w9, #4
     +0x840: add     x10, x25, #0x1
     +0x844: sub     w9, w21, w9
     +0x848: str     w9, [x14, x25, lsl #2]
     +0x84c: mov     x25, x10
     +0x850: cmp     x25, #0xff
     +0x854: b.hi    <mldsa65_poly_uniform_eta_4x+0x87c>
     +0x858: cmp     x8, #0x87
     +0x85c: add     x8, x8, #0x1
     +0x860: b.cc    <mldsa65_poly_uniform_eta_4x+0x80c>
     +0x864: b       <mldsa65_poly_uniform_eta_4x+0x87c>
     +0x868: ldp     x13, x12, [sp, #56]
     +0x86c: ldr     x14, [sp, #48]
     +0x870: ldr     w17, [sp, #84]
     +0x874: tbnz    w17, #0, <mldsa65_poly_uniform_eta_4x+0x804>
     +0x878: ldr     w15, [sp, #80]
     +0x87c: tbz     w15, #0, <mldsa65_poly_uniform_eta_4x+0x8dc>
     +0x880: mov     x8, xzr
     +0x884: ldrb    w9, [x27, x8]
     +0x888: and     w10, w9, #0xf
     +0x88c: cmp     w10, #0x8
     +0x890: b.hi    <mldsa65_poly_uniform_eta_4x+0x8a4>
     +0x894: add     x11, x24, #0x1
     +0x898: sub     w10, w21, w10
     +0x89c: str     w10, [x13, x24, lsl #2]
     +0x8a0: mov     x24, x11
     +0x8a4: cmp     w9, #0x8f
     +0x8a8: b.hi    <mldsa65_poly_uniform_eta_4x+0x8c8>
     +0x8ac: cmp     x24, #0xff
     +0x8b0: b.hi    <mldsa65_poly_uniform_eta_4x+0x8c8>
     +0x8b4: lsr     w9, w9, #4
     +0x8b8: add     x10, x24, #0x1
     +0x8bc: sub     w9, w21, w9
     +0x8c0: str     w9, [x13, x24, lsl #2]
     +0x8c4: mov     x24, x10
     +0x8c8: cmp     x24, #0xff
     +0x8cc: b.hi    <mldsa65_poly_uniform_eta_4x+0x8dc>
     +0x8d0: cmp     x8, #0x87
     +0x8d4: add     x8, x8, #0x1
     +0x8d8: b.cc    <mldsa65_poly_uniform_eta_4x+0x884>
     +0x8dc: ldr     w8, [sp, #76]
     +0x8e0: tbz     w8, #0, <mldsa65_poly_uniform_eta_4x+0x940>
     +0x8e4: mov     x8, xzr
     +0x8e8: ldrb    w9, [x26, x8]
     +0x8ec: and     w10, w9, #0xf
     +0x8f0: cmp     w10, #0x8
     +0x8f4: b.hi    <mldsa65_poly_uniform_eta_4x+0x908>
     +0x8f8: add     x11, x19, #0x1
     +0x8fc: sub     w10, w21, w10
     +0x900: str     w10, [x12, x19, lsl #2]
     +0x904: mov     x19, x11
     +0x908: cmp     w9, #0x8f
     +0x90c: b.hi    <mldsa65_poly_uniform_eta_4x+0x92c>
     +0x910: cmp     x19, #0xff
     +0x914: b.hi    <mldsa65_poly_uniform_eta_4x+0x92c>
     +0x918: lsr     w9, w9, #4
     +0x91c: add     x10, x19, #0x1
     +0x920: sub     w9, w21, w9
     +0x924: str     w9, [x12, x19, lsl #2]
     +0x928: mov     x19, x10
     +0x92c: cmp     x19, #0xff
     +0x930: b.hi    <mldsa65_poly_uniform_eta_4x+0x940>
     +0x934: cmp     x8, #0x87
     +0x938: add     x8, x8, #0x1
     +0x93c: b.cc    <mldsa65_poly_uniform_eta_4x+0x8e8>
     +0x940: cmp     x25, #0x100
     +0x944: cset    w17, cc
     +0x948: cmp     x24, #0x100
     +0x94c: cset    w16, cc
     +0x950: cmp     x19, #0x100
     +0x954: cset    w11, cc
     +0x958: cmp     x23, #0x100
     +0x95c: cset    w18, cc
     +0x960: b.cc    <mldsa65_poly_uniform_eta_4x+0x6a0>
     +0x964: cmp     x25, #0x100
     +0x968: b.cc    <mldsa65_poly_uniform_eta_4x+0x6a0>
     +0x96c: cmp     x24, #0x100
     +0x970: b.cc    <mldsa65_poly_uniform_eta_4x+0x6a0>
     +0x974: cmp     x19, #0x100
     +0x978: b.cc    <mldsa65_poly_uniform_eta_4x+0x6a0>
     +0x97c: add     x0, sp, #0x60
     +0x980: mov     w1, wzr
     +0x984: mov     w2, #0x320
     +0x988: add     x19, sp, #0x60
     +0x98c: bl      <memset>
     +0x990: add     x0, sp, #0x500
     +0x994: mov     w1, wzr
     +0x998: mov     w2, #0x480
     +0x99c: add     x19, sp, #0x500
     +0x9a0: bl      <memset>
     +0x9a4: movi    v0.2d, #0x0
     +0x9a8: add     x8, sp, #0x380
     +0x9ac: str     q0, [sp, #1264]
     +0x9b0: str     q0, [sp, #1248]
     +0x9b4: str     q0, [sp, #1232]
     +0x9b8: str     q0, [sp, #1216]
     +0x9bc: str     q0, [sp, #1200]
     +0x9c0: str     q0, [sp, #1184]
     +0x9c4: str     q0, [sp, #1168]
     +0x9c8: str     q0, [sp, #1152]
     +0x9cc: str     q0, [sp, #1136]
     +0x9d0: str     q0, [sp, #1120]
     +0x9d4: str     q0, [sp, #1104]
     +0x9d8: str     q0, [sp, #1088]
     +0x9dc: str     q0, [sp, #1072]
     +0x9e0: str     q0, [sp, #1056]
     +0x9e4: str     q0, [sp, #1040]
     +0x9e8: stp     q0, q0, [sp, #912]
     +0x9ec: stp     q0, q0, [sp, #944]
     +0x9f0: stp     q0, q0, [sp, #976]
     +0x9f4: stp     q0, q0, [sp, #1008]
     +0x9f8: str     q0, [sp, #896]
     +0x9fc: adrp    x8, <page>
     +0xa00: ldr     x8, [x8, #4088]
     +0xa04: ldr     x9, [sp, #2456]
     +0xa08: ldr     x8, [x8]
     +0xa0c: cmp     x8, x9
     +0xa10: b.ne    <mldsa65_poly_uniform_eta_4x+0xa80>
     +0xa14: mov     sp, x29
     +0xa18: ldp     x20, x19, [sp, #80]
     +0xa1c: ldp     x22, x21, [sp, #64]
     +0xa20: ldp     x24, x23, [sp, #48]
     +0xa24: ldp     x26, x25, [sp, #32]
     +0xa28: ldp     x28, x27, [sp, #16]
     +0xa2c: ldp     x29, x30, [sp], #96
     +0xa30: mov     x0, #0x0
     +0xa34: mov     x1, #0x0
     +0xa38: mov     x2, #0x0
     +0xa3c: mov     x3, #0x0
     +0xa40: mov     x4, #0x0
     +0xa44: mov     x5, #0x0
     +0xa48: mov     x6, #0x0
     +0xa4c: mov     x7, #0x0
     +0xa50: mov     x8, #0x0
     +0xa54: mov     x9, #0x0
     +0xa58: mov     x10, #0x0
     +0xa5c: mov     x11, #0x0
     +0xa60: mov     x12, #0x0
     +0xa64: mov     x13, #0x0
     +0xa68: mov     x14, #0x0
     +0xa6c: mov     x15, #0x0
     +0xa70: mov     x16, #0x0
     +0xa74: mov     x17, #0x0
     +0xa78: mov     x18, #0x0
     +0xa7c: ret     
     +0xa80: bl      <__stack_chk_fail>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa65_poly_uniform_eta_4x";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The seed is the 64 bytes   *)
(* sd at seed, and polynomial j becomes mld_poly_uniform_eta 4 sd of the     *)
(* nonce j, if the SHAKE256 output of the extended seed has 256 acceptable   *)
(* nibbles. The stack is the 2848 bytes below the stack pointer (see above), *)
(* and the fourth nonce is the byte at the stack pointer.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !r0 r1 r2 r3 seed sd n0 n1 n2 n3 guard pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(n3:byte))) /\
          PAIRWISE nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2848),2848)] /\
          ALLPAIRS nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2848),2848)]
           [(seed,64); (stackpointer,1);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa65_poly_uniform_eta_4x) /\
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
                             mld_poly_uniform_eta 4 sd (word_zx n0) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 4 sd (word_zx n1) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 4 sd (word_zx n2) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 4 sd n3 i))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                  memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                  memory :> bytes(word_sub stackpointer (word 2848),2848)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the address of memset, the stack  *)
(* and the lists of the values that mld_rej_eta_c declassifies for each      *)
(* polynomial, with all accesses within the arguments, the stack, the GOT    *)
(* entries and the stack guard, the region (ea,el) that memset may read and  *)
(* the round constants of Keccak, and the writes within the polynomials and  *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e r0 r1 r2 r3 seed sd n0 n1 n2 n3 guard pc stackpointer
                 returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(n3:byte))) /\
          PAIRWISE nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2848),2848)] /\
          ALLPAIRS nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2848),2848)]
           [(seed,64); (stackpointer,1);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa65_poly_uniform_eta_4x) /\
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
                             mld_poly_uniform_eta 4 sd (word_zx n0) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 4 sd (word_zx n1) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 4 sd (word_zx n2) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                               s =
                             mld_poly_uniform_eta 4 sd n3 i) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events r0 r1 r2 r3 seed
                         (mld_poly_uniform_eta_declass 4
                           (mld_shake256_stream 66
                             (sd + 2 EXP 512 * val(word_zx n0:byte))))
                         (mld_poly_uniform_eta_declass 4
                           (mld_shake256_stream 66
                             (sd + 2 EXP 512 * val(word_zx n1:byte))))
                         (mld_poly_uniform_eta_declass 4
                           (mld_shake256_stream 66
                             (sd + 2 EXP 512 * val(word_zx n2:byte))))
                         (mld_poly_uniform_eta_declass 4
                           (mld_shake256_stream 66
                             (sd + 2 EXP 512 * val(n3:byte))))
                         guard mf pc (word_sub stackpointer (word 2848))
                         returnaddress /\
                       memaccess_inbounds e2
                        [seed,64; stackpointer,1;
                         r0,1024; r1,1024; r2,1024; r3,1024;
                         word_sub stackpointer (word 2848),2848;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [r0,1024; r1,1024; r2,1024; r3,1024;
                         word_sub stackpointer (word 2848),2848]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                  memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                  memory :> bytes(word_sub stackpointer (word 2848),2848)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* seed only through the declassified validity of the nibbles of the         *)
(* streams, as above.                                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e r0 r1 r2 r3 seed sd n0 n1 n2 n3 guard pc stackpointer
                 returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n0:byte))) /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n1:byte))) /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(word_zx n2:byte))) /\
          mld_rej_eta_terminates 4
            (mld_shake256_stream 66 (sd + 2 EXP 512 * val(n3:byte))) /\
          PAIRWISE nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2848),2848)] /\
          ALLPAIRS nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 2848),2848)]
           [(seed,64); (stackpointer,1);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa65_poly_uniform_eta_4x) /\
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
                         (mld_poly_uniform_eta_declass 4
                           (mld_shake256_stream 66
                             (sd + 2 EXP 512 * val(word_zx n0:byte))))
                         (mld_poly_uniform_eta_declass 4
                           (mld_shake256_stream 66
                             (sd + 2 EXP 512 * val(word_zx n1:byte))))
                         (mld_poly_uniform_eta_declass 4
                           (mld_shake256_stream 66
                             (sd + 2 EXP 512 * val(word_zx n2:byte))))
                         (mld_poly_uniform_eta_declass 4
                           (mld_shake256_stream 66
                             (sd + 2 EXP 512 * val(n3:byte))))
                         guard mf pc (word_sub stackpointer (word 2848))
                         returnaddress /\
                       memaccess_inbounds e2
                        [seed,64; stackpointer,1;
                         r0,1024; r1,1024; r2,1024; r3,1024;
                         word_sub stackpointer (word 2848),2848;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [r0,1024; r1,1024; r2,1024; r3,1024;
                         word_sub stackpointer (word 2848),2848]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                  memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                  memory :> bytes(word_sub stackpointer (word 2848),2848)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_ETA_4X_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
