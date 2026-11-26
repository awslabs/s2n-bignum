(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse number-theoretic transform with the factor mont / 256: the        *)
(* statement. This is the code for mldsa_poly_invntt_tomont                  *)
(* (mld_poly_invntt_tomont in poly.c, which calls mld_poly_invntt_tomont_c)  *)
(* from mldsa-native's portable C implementation compiled by clang 23 with   *)
(* -O3 as a monolithic build with MLD_CONFIG_REDUCE_RAM (see                 *)
(* mldsa_native/README.md). Clang has unrolled and fused the loops: the      *)
(* first two layers (blocks of 2 and 4 coefficients) are vector loops with   *)
(* ld2/ld4/st2/st4 and the zetas of the table in the read-only data; layers  *)
(* 3 to 5 are loops of one or more blocks per iteration (with the zeta from  *)
(* the table, and spills to the stack in the last of them); layers 6 to 8    *)
(* are 7 loops with the zeta in immediates (two butterflies per iteration);  *)
(* a last loop scales the coefficients by mont^2 / 256. The function saves   *)
(* x19 to x30 in a frame of 208 bytes and clears the scratch registers,      *)
(* including x18, which MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI does not   *)
(* cover (the frame has MAYCHANGE [X18] added). The gcc code had no frame    *)
(* and the statements gain the stack pointer. It is verified in the whole    *)
(* image (see libmldsa.ml) against mld_poly_invntt_tomont of                 *)
(* common/mldsa_native_poly.ml, and shown to be constant time and memory     *)
(* safe.                                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_ntt.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_invntt_tomont:
       +0x0: sub     sp, sp, #0xd0
       +0x4: stp     x29, x30, [sp, #112]
       +0x8: stp     x28, x27, [sp, #128]
       +0xc: stp     x26, x25, [sp, #144]
      +0x10: stp     x24, x23, [sp, #160]
      +0x14: stp     x22, x21, [sp, #176]
      +0x18: stp     x20, x19, [sp, #192]
      +0x1c: mov     w8, #0xff801fff
      +0x20: mov     x10, #0x200100000000
      +0x24: mov     w9, #0x3f0
      +0x28: dup     v0.2s, w8
      +0x2c: adrp    x8, <page>
      +0x30: add     x8, x8, #0x728
      +0x34: movk    x10, #0x380, lsl #48
      +0x38: mov     x11, x0
      +0x3c: ldr     q1, [x8, x9]
      +0x40: ld2     {v2.4s-v3.4s}, [x11]
      +0x44: sub     x9, x9, #0x10
      +0x48: cmp     x9, #0x1f0
      +0x4c: neg     v1.4s, v1.4s
      +0x50: sub     v4.4s, v2.4s, v3.4s
      +0x54: add     v2.4s, v3.4s, v2.4s
      +0x58: rev64   v1.4s, v1.4s
      +0x5c: ext     v1.16b, v1.16b, v1.16b, #8
      +0x60: smull   v5.2d, v4.2s, v1.2s
      +0x64: smull2  v1.2d, v4.4s, v1.4s
      +0x68: fmov    x13, d5
      +0x6c: mov     x12, v5.d[1]
      +0x70: fmov    x15, d1
      +0x74: mov     x14, v1.d[1]
      +0x78: mul     x13, x13, x10
      +0x7c: mul     x12, x12, x10
      +0x80: mul     x15, x15, x10
      +0x84: fmov    d4, x13
      +0x88: mul     x13, x14, x10
      +0x8c: mov     v4.d[1], x12
      +0x90: fmov    d6, x15
      +0x94: mov     v6.d[1], x13
      +0x98: shrn    v4.2s, v4.2d, #32
      +0x9c: smull   v4.2d, v4.2s, v0.2s
      +0xa0: shrn    v6.2s, v6.2d, #32
      +0xa4: smull   v6.2d, v6.2s, v0.2s
      +0xa8: addhn   v3.2s, v4.2d, v5.2d
      +0xac: addhn2  v3.4s, v6.2d, v1.2d
      +0xb0: st2     {v2.4s-v3.4s}, [x11], #32
      +0xb4: b.ne    <mldsa_poly_invntt_tomont+0x3c>
      +0xb8: mov     w9, #0xff801fff
      +0xbc: mov     x10, #0x200100000000
      +0xc0: mov     x11, x0
      +0xc4: dup     v0.2s, w9
      +0xc8: mov     w9, #0x1f0
      +0xcc: movk    x10, #0x380, lsl #48
      +0xd0: ldr     q1, [x8, x9]
      +0xd4: sub     x9, x9, #0x10
      +0xd8: cmp     x9, #0xf0
      +0xdc: neg     v5.4s, v1.4s
      +0xe0: ld4     {v1.4s-v4.4s}, [x11]
      +0xe4: rev64   v5.4s, v5.4s
      +0xe8: sub     v6.4s, v2.4s, v4.4s
      +0xec: sub     v17.4s, v1.4s, v3.4s
      +0xf0: add     v21.4s, v3.4s, v1.4s
      +0xf4: add     v22.4s, v4.4s, v2.4s
      +0xf8: ext     v16.16b, v5.16b, v5.16b, #8
      +0xfc: smull   v7.2d, v6.2s, v16.2s
     +0x100: smull2  v6.2d, v6.4s, v16.4s
     +0x104: smull   v5.2d, v17.2s, v16.2s
     +0x108: smull2  v16.2d, v17.4s, v16.4s
     +0x10c: fmov    x14, d7
     +0x110: mov     x13, v7.d[1]
     +0x114: fmov    x17, d6
     +0x118: fmov    x12, d5
     +0x11c: mov     x15, v6.d[1]
     +0x120: mov     x16, v5.d[1]
     +0x124: mul     x14, x14, x10
     +0x128: mul     x13, x13, x10
     +0x12c: mul     x17, x17, x10
     +0x130: fmov    d17, x14
     +0x134: mov     x14, v16.d[1]
     +0x138: mul     x12, x12, x10
     +0x13c: mov     v17.d[1], x13
     +0x140: fmov    x13, d16
     +0x144: mul     x15, x15, x10
     +0x148: fmov    d19, x17
     +0x14c: mul     x16, x16, x10
     +0x150: fmov    d18, x12
     +0x154: mul     x13, x13, x10
     +0x158: shrn    v17.2s, v17.2d, #32
     +0x15c: mov     v19.d[1], x15
     +0x160: mul     x12, x14, x10
     +0x164: mov     v18.d[1], x16
     +0x168: smull   v17.2d, v17.2s, v0.2s
     +0x16c: fmov    d20, x13
     +0x170: shrn    v19.2s, v19.2d, #32
     +0x174: shrn    v18.2s, v18.2d, #32
     +0x178: addhn   v24.2s, v17.2d, v7.2d
     +0x17c: mov     v20.d[1], x12
     +0x180: smull   v1.2d, v19.2s, v0.2s
     +0x184: smull   v2.2d, v18.2s, v0.2s
     +0x188: shrn    v3.2s, v20.2d, #32
     +0x18c: addhn2  v24.4s, v1.2d, v6.2d
     +0x190: addhn   v23.2s, v2.2d, v5.2d
     +0x194: smull   v1.2d, v3.2s, v0.2s
     +0x198: addhn2  v23.4s, v1.2d, v16.2d
     +0x19c: st4     {v21.4s-v24.4s}, [x11], #64
     +0x1a0: b.ne    <mldsa_poly_invntt_tomont+0xd0>
     +0x1a4: mov     x8, #0x200100000000
     +0x1a8: adrp    x9, <page>
     +0x1ac: add     x9, x9, #0x824
     +0x1b0: movk    x8, #0x380, lsl #48
     +0x1b4: add     x10, x0, #0x10
     +0x1b8: mov     x11, #0xfffffffffffffff8
     +0x1bc: mov     x12, #0xffffffffff801fff
     +0x1c0: ldp     w13, w17, [x10]
     +0x1c4: ldp     w14, w16, [x10, #-16]
     +0x1c8: ldr     w15, [x9], #-4
     +0x1cc: add     x11, x11, #0x8
     +0x1d0: ldp     w3, w6, [x10, #8]
     +0x1d4: neg     w15, w15
     +0x1d8: sub     w18, w14, w13
     +0x1dc: sub     w1, w16, w17
     +0x1e0: smull   x5, w18, w15
     +0x1e4: add     w13, w13, w14
     +0x1e8: add     w16, w17, w16
     +0x1ec: smull   x4, w1, w15
     +0x1f0: stp     w13, w16, [x10, #-16]
     +0x1f4: cmp     x11, #0xf8
     +0x1f8: mul     x22, x5, x8
     +0x1fc: ldp     w2, w5, [x10, #-8]
     +0x200: mul     x4, x4, x8
     +0x204: sub     w7, w2, w3
     +0x208: sub     w20, w5, w6
     +0x20c: add     w16, w6, w5
     +0x210: smull   x19, w7, w15
     +0x214: asr     x22, x22, #32
     +0x218: smull   x21, w20, w15
     +0x21c: asr     x4, x4, #32
     +0x220: smull   x22, w22, w12
     +0x224: mul     x19, x19, x8
     +0x228: mul     x21, x21, x8
     +0x22c: smull   x4, w4, w12
     +0x230: asr     x19, x19, #32
     +0x234: smaddl  x1, w1, w15, x4
     +0x238: smaddl  x18, w18, w15, x22
     +0x23c: asr     x4, x21, #32
     +0x240: smull   x19, w19, w12
     +0x244: smaddl  x14, w7, w15, x19
     +0x248: smull   x13, w4, w12
     +0x24c: lsr     x17, x18, #32
     +0x250: smaddl  x13, w20, w15, x13
     +0x254: add     w15, w3, w2
     +0x258: stp     w15, w16, [x10, #-8]
     +0x25c: lsr     x15, x1, #32
     +0x260: lsr     x14, x14, #32
     +0x264: lsr     x13, x13, #32
     +0x268: stp     w17, w15, [x10]
     +0x26c: stp     w14, w13, [x10, #8]
     +0x270: add     x10, x10, #0x20
     +0x274: b.cc    <mldsa_poly_invntt_tomont+0x1c0>
     +0x278: adrp    x9, <page>
     +0x27c: add     x9, x9, #0x7a4
     +0x280: add     x10, x0, #0x20
     +0x284: mov     x11, #0xfffffffffffffff0
     +0x288: mov     x26, #0xffffffffff801fff
     +0x28c: str     x0, [sp]
     +0x290: ldp     w14, w17, [x10]
     +0x294: ldp     w15, w16, [x10, #-32]
     +0x298: ldr     w13, [x9], #-4
     +0x29c: add     x11, x11, #0x10
     +0x2a0: ldp     w0, w4, [x10, #8]
     +0x2a4: neg     w13, w13
     +0x2a8: sub     w12, w15, w14
     +0x2ac: sub     w27, w15, w14
     +0x2b0: smull   x3, w12, w13
     +0x2b4: sub     w12, w16, w17
     +0x2b8: add     w14, w14, w15
     +0x2bc: smull   x5, w12, w13
     +0x2c0: cmp     x11, #0xf0
     +0x2c4: mul     x19, x3, x8
     +0x2c8: ldp     w18, w3, [x10, #-24]
     +0x2cc: mul     x28, x5, x8
     +0x2d0: ldp     w5, w21, [x10, #-16]
     +0x2d4: sub     w12, w18, w0
     +0x2d8: smull   x6, w12, w13
     +0x2dc: sub     w12, w3, w4
     +0x2e0: asr     x19, x19, #32
     +0x2e4: smull   x23, w12, w13
     +0x2e8: asr     x28, x28, #32
     +0x2ec: smull   x19, w19, w26
     +0x2f0: mul     x25, x6, x8
     +0x2f4: ldp     w6, w22, [x10, #16]
     +0x2f8: mul     x29, x23, x8
     +0x2fc: ldp     w23, w1, [x10, #-8]
     +0x300: sub     w12, w5, w6
     +0x304: smaddl  x19, w27, w13, x19
     +0x308: sub     w27, w16, w17
     +0x30c: smull   x24, w12, w13
     +0x310: sub     w12, w21, w22
     +0x314: asr     x25, x25, #32
     +0x318: smull   x12, w12, w13
     +0x31c: add     w16, w17, w16
     +0x320: smull   x28, w28, w26
     +0x324: lsr     x15, x19, #32
     +0x328: stp     w14, w16, [x10, #-32]
     +0x32c: mul     x30, x24, x8
     +0x330: ldp     w24, w2, [x10, #24]
     +0x334: smaddl  x28, w27, w13, x28
     +0x338: sub     w27, w18, w0
     +0x33c: smull   x19, w25, w26
     +0x340: asr     x25, x29, #32
     +0x344: sub     w7, w23, w24
     +0x348: sub     w29, w1, w2
     +0x34c: mul     x12, x12, x8
     +0x350: lsr     x14, x28, #32
     +0x354: smull   x20, w7, w13
     +0x358: smull   x17, w29, w13
     +0x35c: stp     w15, w14, [x10]
     +0x360: asr     x14, x30, #32
     +0x364: smull   x16, w25, w26
     +0x368: sub     w25, w3, w4
     +0x36c: mul     x20, x20, x8
     +0x370: asr     x12, x12, #32
     +0x374: mul     x15, x17, x8
     +0x378: add     w17, w0, w18
     +0x37c: add     w18, w4, w3
     +0x380: stp     w17, w18, [x10, #-24]
     +0x384: sub     w17, w5, w6
     +0x388: sub     w18, w21, w22
     +0x38c: smull   x14, w14, w26
     +0x390: smull   x12, w12, w26
     +0x394: smaddl  x14, w17, w13, x14
     +0x398: asr     x17, x20, #32
     +0x39c: smaddl  x12, w18, w13, x12
     +0x3a0: asr     x15, x15, #32
     +0x3a4: add     w18, w22, w21
     +0x3a8: smaddl  x19, w27, w13, x19
     +0x3ac: smaddl  x16, w25, w13, x16
     +0x3b0: lsr     x14, x14, #32
     +0x3b4: smull   x17, w17, w26
     +0x3b8: lsr     x12, x12, #32
     +0x3bc: smull   x15, w15, w26
     +0x3c0: lsr     x0, x19, #32
     +0x3c4: smaddl  x17, w7, w13, x17
     +0x3c8: lsr     x16, x16, #32
     +0x3cc: stp     w14, w12, [x10, #16]
     +0x3d0: smaddl  x13, w29, w13, x15
     +0x3d4: add     w12, w24, w23
     +0x3d8: add     w14, w2, w1
     +0x3dc: stp     w12, w14, [x10, #-8]
     +0x3e0: lsr     x15, x17, #32
     +0x3e4: stp     w0, w16, [x10, #8]
     +0x3e8: add     w16, w6, w5
     +0x3ec: lsr     x12, x13, #32
     +0x3f0: stp     w16, w18, [x10, #-16]
     +0x3f4: stp     w15, w12, [x10, #24]
     +0x3f8: add     x10, x10, #0x40
     +0x3fc: b.cc    <mldsa_poly_invntt_tomont+0x290>
     +0x400: ldr     x9, [sp]
     +0x404: adrp    x11, <page>
     +0x408: add     x11, x11, #0x764
     +0x40c: mov     x27, #0xffffffffffffffe0
     +0x410: mov     x12, #0xffffffffff801fff
     +0x414: add     x10, x9, #0x40
     +0x418: ldr     w9, [x11], #-4
     +0x41c: str     x11, [sp, #104]
     +0x420: ldp     w21, w1, [x10, #-56]
     +0x424: ldp     w15, w5, [x10, #8]
     +0x428: ldp     w11, w20, [x10]
     +0x42c: ldp     w4, w19, [x10, #-64]
     +0x430: neg     w13, w9
     +0x434: stp     w1, w15, [sp, #96]
     +0x438: sub     w15, w21, w15
     +0x43c: smull   x17, w15, w13
     +0x440: sub     w28, w1, w5
     +0x444: add     x27, x27, #0x20
     +0x448: sub     w25, w19, w20
     +0x44c: sub     w9, w4, w11
     +0x450: add     w19, w20, w19
     +0x454: ldp     w6, w23, [x10, #-48]
     +0x458: ldp     w7, w24, [x10, #16]
     +0x45c: smull   x16, w25, w13
     +0x460: cmp     x27, #0xe0
     +0x464: mul     x18, x17, x8
     +0x468: sub     w17, w6, w7
     +0x46c: mul     x0, x16, x8
     +0x470: ldp     w2, w26, [x10, #24]
     +0x474: smull   x16, w28, w13
     +0x478: smull   x17, w17, w13
     +0x47c: smull   x14, w9, w13
     +0x480: mul     x1, x16, x8
     +0x484: mul     x16, x17, x8
     +0x488: ldp     w17, w3, [x10, #-40]
     +0x48c: mul     x14, x14, x8
     +0x490: stp     w17, w2, [sp, #88]
     +0x494: sub     w17, w17, w2
     +0x498: str     x16, [sp, #56]
     +0x49c: sub     w16, w23, w24
     +0x4a0: smull   x16, w16, w13
     +0x4a4: str     w17, [sp, #44]
     +0x4a8: smull   x17, w17, w13
     +0x4ac: stp     w3, w26, [sp, #80]
     +0x4b0: asr     x14, x14, #32
     +0x4b4: mul     x16, x16, x8
     +0x4b8: smull   x14, w14, w12
     +0x4bc: smaddl  x14, w9, w13, x14
     +0x4c0: str     x16, [sp, #16]
     +0x4c4: mul     x16, x17, x8
     +0x4c8: str     x16, [sp, #32]
     +0x4cc: sub     w16, w3, w26
     +0x4d0: ldp     w17, w26, [x10, #-32]
     +0x4d4: ldp     w2, w3, [x10, #32]
     +0x4d8: stp     w16, w17, [sp, #68]
     +0x4dc: smull   x16, w16, w13
     +0x4e0: sub     w17, w17, w2
     +0x4e4: str     w2, [sp, #76]
     +0x4e8: str     w17, [sp, #64]
     +0x4ec: smull   x17, w17, w13
     +0x4f0: str     w3, [sp, #12]
     +0x4f4: mul     x16, x16, x8
     +0x4f8: mul     x17, x17, x8
     +0x4fc: str     x17, [sp, #48]
     +0x500: asr     x17, x0, #32
     +0x504: smull   x9, w17, w12
     +0x508: smaddl  x17, w25, w13, x9
     +0x50c: asr     x9, x18, #32
     +0x510: sub     w18, w26, w3
     +0x514: smull   x18, w18, w13
     +0x518: smull   x9, w9, w12
     +0x51c: smaddl  x2, w15, w13, x9
     +0x520: asr     x15, x1, #32
     +0x524: add     w1, w11, w4
     +0x528: mul     x18, x18, x8
     +0x52c: lsr     x4, x14, #32
     +0x530: lsr     x20, x17, #32
     +0x534: ldp     w30, w25, [x10, #-24]
     +0x538: ldp     w9, w29, [x10, #40]
     +0x53c: smull   x15, w15, w12
     +0x540: stp     w1, w19, [x10, #-64]
     +0x544: smaddl  x3, w28, w13, x15
     +0x548: stp     w4, w20, [x10]
     +0x54c: add     w20, w24, w23
     +0x550: str     x18, [sp, #24]
     +0x554: sub     w18, w30, w9
     +0x558: smull   x18, w18, w13
     +0x55c: lsr     x3, x3, #32
     +0x560: ldp     w19, w4, [sp, #96]
     +0x564: mul     x15, x18, x8
     +0x568: sub     w18, w25, w29
     +0x56c: ldp     w28, w14, [x10, #-16]
     +0x570: smull   x11, w18, w13
     +0x574: add     w5, w5, w19
     +0x578: sub     w19, w6, w7
     +0x57c: add     w4, w4, w21
     +0x580: stp     w4, w5, [x10, #-56]
     +0x584: mul     x17, x11, x8
     +0x588: lsr     x11, x2, #32
     +0x58c: ldr     x2, [sp, #56]
     +0x590: ldp     w0, w18, [x10, #48]
     +0x594: stp     w11, w3, [x10, #8]
     +0x598: ldr     x11, [sp, #16]
     +0x59c: asr     x2, x2, #32
     +0x5a0: add     w3, w7, w6
     +0x5a4: asr     x15, x15, #32
     +0x5a8: asr     x11, x11, #32
     +0x5ac: smull   x2, w2, w12
     +0x5b0: stp     w3, w20, [x10, #-48]
     +0x5b4: smaddl  x19, w19, w13, x2
     +0x5b8: sub     w2, w23, w24
     +0x5bc: sub     w22, w28, w0
     +0x5c0: smull   x11, w11, w12
     +0x5c4: asr     x17, x17, #32
     +0x5c8: smaddl  x11, w2, w13, x11
     +0x5cc: ldr     x2, [sp, #32]
     +0x5d0: smull   x1, w22, w13
     +0x5d4: sub     w22, w14, w18
     +0x5d8: asr     x4, x2, #32
     +0x5dc: sub     w2, w14, w18
     +0x5e0: smull   x15, w15, w12
     +0x5e4: lsr     x11, x11, #32
     +0x5e8: smull   x7, w2, w13
     +0x5ec: ldr     w2, [sp, #44]
     +0x5f0: smull   x3, w4, w12
     +0x5f4: lsr     x4, x19, #32
     +0x5f8: asr     x19, x16, #32
     +0x5fc: smaddl  x3, w2, w13, x3
     +0x600: ldr     x2, [sp, #48]
     +0x604: add     w14, w18, w14
     +0x608: stp     w4, w11, [x10, #16]
     +0x60c: ldr     w11, [sp, #68]
     +0x610: smull   x19, w19, w12
     +0x614: mul     x23, x7, x8
     +0x618: lsr     x3, x3, #32
     +0x61c: smaddl  x11, w11, w13, x19
     +0x620: ldp     w20, w19, [sp, #88]
     +0x624: ldp     w5, w16, [x10, #-8]
     +0x628: lsr     x11, x11, #32
     +0x62c: mul     x1, x1, x8
     +0x630: add     w19, w19, w20
     +0x634: asr     x20, x2, #32
     +0x638: ldp     w2, w21, [sp, #80]
     +0x63c: smull   x20, w20, w12
     +0x640: stp     w3, w11, [x10, #24]
     +0x644: ldp     w6, w7, [x10, #56]
     +0x648: add     w21, w21, w2
     +0x64c: ldr     x2, [sp, #24]
     +0x650: smull   x17, w17, w12
     +0x654: stp     w19, w21, [x10, #-40]
     +0x658: ldr     w21, [sp, #12]
     +0x65c: asr     x19, x2, #32
     +0x660: ldr     w2, [sp, #64]
     +0x664: sub     w24, w5, w6
     +0x668: sub     w11, w26, w21
     +0x66c: smull   x4, w24, w13
     +0x670: add     w21, w21, w26
     +0x674: smaddl  x20, w2, w13, x20
     +0x678: smull   x19, w19, w12
     +0x67c: smaddl  x11, w11, w13, x19
     +0x680: ldp     w3, w2, [sp, #72]
     +0x684: lsr     x19, x20, #32
     +0x688: sub     w20, w16, w7
     +0x68c: mul     x4, x4, x8
     +0x690: lsr     x11, x11, #32
     +0x694: smull   x26, w20, w13
     +0x698: add     w3, w2, w3
     +0x69c: sub     w2, w30, w9
     +0x6a0: smaddl  x15, w2, w13, x15
     +0x6a4: sub     w2, w25, w29
     +0x6a8: stp     w19, w11, [x10, #32]
     +0x6ac: smaddl  x17, w2, w13, x17
     +0x6b0: asr     x11, x1, #32
     +0x6b4: stp     w3, w21, [x10, #-32]
     +0x6b8: mul     x1, x26, x8
     +0x6bc: add     w9, w9, w30
     +0x6c0: add     w3, w29, w25
     +0x6c4: asr     x19, x23, #32
     +0x6c8: stp     w9, w3, [x10, #-24]
     +0x6cc: sub     w9, w28, w0
     +0x6d0: smull   x11, w11, w12
     +0x6d4: lsr     x15, x15, #32
     +0x6d8: smaddl  x9, w9, w13, x11
     +0x6dc: lsr     x11, x17, #32
     +0x6e0: asr     x17, x4, #32
     +0x6e4: smull   x3, w19, w12
     +0x6e8: stp     w15, w11, [x10, #40]
     +0x6ec: smaddl  x15, w22, w13, x3
     +0x6f0: asr     x18, x1, #32
     +0x6f4: add     w11, w0, w28
     +0x6f8: smull   x17, w17, w12
     +0x6fc: lsr     x9, x9, #32
     +0x700: stp     w11, w14, [x10, #-16]
     +0x704: smull   x14, w18, w12
     +0x708: smaddl  x17, w24, w13, x17
     +0x70c: lsr     x11, x15, #32
     +0x710: smaddl  x13, w20, w13, x14
     +0x714: stp     w9, w11, [x10, #48]
     +0x718: add     w9, w6, w5
     +0x71c: add     w11, w7, w16
     +0x720: lsr     x14, x17, #32
     +0x724: stp     w9, w11, [x10, #-8]
     +0x728: ldr     x11, [sp, #104]
     +0x72c: lsr     x9, x13, #32
     +0x730: stp     w14, w9, [x10, #56]
     +0x734: add     x10, x10, #0x80
     +0x738: b.cc    <mldsa_poly_invntt_tomont+0x418>
     +0x73c: ldr     x2, [sp]
     +0x740: mov     x8, #0xffffffffffffe1dc
     +0x744: mov     x9, #0x61dc00000000
     +0x748: movk    x8, #0xfff8, lsl #16
     +0x74c: movk    x9, #0x9e34, lsl #48
     +0x750: mov     w11, #0x20
     +0x754: add     x10, x2, #0x84
     +0x758: mov     x12, #0xffffffffff801fff
     +0x75c: ldp     w13, w16, [x10, #-4]
     +0x760: ldp     w14, w15, [x10, #-132]
     +0x764: subs    x11, x11, #0x2
     +0x768: sub     w17, w14, w13
     +0x76c: sub     w0, w15, w16
     +0x770: add     w13, w13, w14
     +0x774: sxtw    x18, w17
     +0x778: sxtw    x1, w0
     +0x77c: add     w14, w16, w15
     +0x780: stp     w13, w14, [x10, #-132]
     +0x784: mul     x18, x18, x9
     +0x788: mul     x1, x1, x9
     +0x78c: asr     x18, x18, #32
     +0x790: asr     x1, x1, #32
     +0x794: smull   x18, w18, w12
     +0x798: smaddl  x17, w8, w17, x18
     +0x79c: smull   x18, w1, w12
     +0x7a0: smaddl  x18, w8, w0, x18
     +0x7a4: lsr     x15, x17, #32
     +0x7a8: lsr     x13, x18, #32
     +0x7ac: stp     w15, w13, [x10, #-4]
     +0x7b0: add     x10, x10, #0x8
     +0x7b4: b.ne    <mldsa_poly_invntt_tomont+0x75c>
     +0x7b8: mov     x8, #0x5ed800000000
     +0x7bc: mov     w9, #0x5ed8
     +0x7c0: add     x10, x2, #0x184
     +0x7c4: movk    x8, #0x9fe8, lsl #48
     +0x7c8: movk    w9, #0xd, lsl #16
     +0x7cc: mov     w11, #0x20
     +0x7d0: mov     x12, #0xffffffffff801fff
     +0x7d4: ldp     w13, w16, [x10, #-4]
     +0x7d8: ldp     w14, w15, [x10, #-132]
     +0x7dc: subs    x11, x11, #0x2
     +0x7e0: sub     w17, w14, w13
     +0x7e4: sub     w0, w15, w16
     +0x7e8: add     w13, w13, w14
     +0x7ec: sxtw    x18, w17
     +0x7f0: sxtw    x1, w0
     +0x7f4: add     w14, w16, w15
     +0x7f8: stp     w13, w14, [x10, #-132]
     +0x7fc: mul     x18, x18, x8
     +0x800: mul     x1, x1, x8
     +0x804: asr     x18, x18, #32
     +0x808: asr     x1, x1, #32
     +0x80c: smull   x18, w18, w12
     +0x810: smaddl  x17, w9, w17, x18
     +0x814: smull   x18, w1, w12
     +0x818: smaddl  x18, w9, w0, x18
     +0x81c: lsr     x15, x17, #32
     +0x820: lsr     x13, x18, #32
     +0x824: stp     w15, w13, [x10, #-4]
     +0x828: add     x10, x10, #0x8
     +0x82c: b.ne    <mldsa_poly_invntt_tomont+0x7d4>
     +0x830: mov     x8, #0xdee800000000
     +0x834: mov     w9, #0xdee8
     +0x838: add     x10, x2, #0x284
     +0x83c: movk    x8, #0xa7e8, lsl #48
     +0x840: movk    w9, #0xb, lsl #16
     +0x844: mov     w11, #0x20
     +0x848: mov     x12, #0xffffffffff801fff
     +0x84c: ldp     w13, w16, [x10, #-4]
     +0x850: ldp     w14, w15, [x10, #-132]
     +0x854: subs    x11, x11, #0x2
     +0x858: sub     w17, w14, w13
     +0x85c: sub     w0, w15, w16
     +0x860: add     w13, w13, w14
     +0x864: sxtw    x18, w17
     +0x868: sxtw    x1, w0
     +0x86c: add     w14, w16, w15
     +0x870: stp     w13, w14, [x10, #-132]
     +0x874: mul     x18, x18, x8
     +0x878: mul     x1, x1, x8
     +0x87c: asr     x18, x18, #32
     +0x880: asr     x1, x1, #32
     +0x884: smull   x18, w18, w12
     +0x888: smaddl  x17, w9, w17, x18
     +0x88c: smull   x18, w1, w12
     +0x890: smaddl  x18, w9, w0, x18
     +0x894: lsr     x15, x17, #32
     +0x898: lsr     x13, x18, #32
     +0x89c: stp     w15, w13, [x10, #-4]
     +0x8a0: add     x10, x10, #0x8
     +0x8a4: b.ne    <mldsa_poly_invntt_tomont+0x84c>
     +0x8a8: mov     x8, #0xffffffffffff61bc
     +0x8ac: mov     x9, #0xe1bc00000000
     +0x8b0: add     x10, x2, #0x384
     +0x8b4: movk    x8, #0xfffc, lsl #16
     +0x8b8: movk    x9, #0x9e33, lsl #48
     +0x8bc: mov     w11, #0x20
     +0x8c0: mov     x12, #0xffffffffff801fff
     +0x8c4: ldp     w13, w16, [x10, #-4]
     +0x8c8: ldp     w14, w15, [x10, #-132]
     +0x8cc: subs    x11, x11, #0x2
     +0x8d0: sub     w17, w14, w13
     +0x8d4: sub     w0, w15, w16
     +0x8d8: add     w13, w13, w14
     +0x8dc: sxtw    x18, w17
     +0x8e0: sxtw    x1, w0
     +0x8e4: add     w14, w16, w15
     +0x8e8: stp     w13, w14, [x10, #-132]
     +0x8ec: mul     x18, x18, x9
     +0x8f0: mul     x1, x1, x9
     +0x8f4: asr     x18, x18, #32
     +0x8f8: asr     x1, x1, #32
     +0x8fc: smull   x18, w18, w12
     +0x900: smaddl  x17, w8, w17, x18
     +0x904: smull   x18, w1, w12
     +0x908: smaddl  x18, w8, w0, x18
     +0x90c: lsr     x15, x17, #32
     +0x910: lsr     x13, x18, #32
     +0x914: stp     w15, w13, [x10, #-4]
     +0x918: add     x10, x10, #0x8
     +0x91c: b.ne    <mldsa_poly_invntt_tomont+0x8c4>
     +0x920: mov     x8, #0x8afd00000000
     +0x924: mov     w9, #0xeafd
     +0x928: add     x10, x2, #0x100
     +0x92c: movk    x8, #0x72e7, lsl #48
     +0x930: movk    w9, #0x7, lsl #16
     +0x934: mov     w11, #0x40
     +0x938: mov     x12, #0xffffffffff801fff
     +0x93c: ldp     w13, w16, [x10]
     +0x940: ldp     w14, w15, [x10, #-256]
     +0x944: subs    x11, x11, #0x2
     +0x948: sub     w17, w14, w13
     +0x94c: sub     w0, w15, w16
     +0x950: add     w13, w13, w14
     +0x954: sxtw    x18, w17
     +0x958: sxtw    x1, w0
     +0x95c: add     w14, w16, w15
     +0x960: stp     w13, w14, [x10, #-256]
     +0x964: mul     x18, x18, x8
     +0x968: mul     x1, x1, x8
     +0x96c: asr     x18, x18, #32
     +0x970: asr     x1, x1, #32
     +0x974: smull   x18, w18, w12
     +0x978: smaddl  x17, w9, w17, x18
     +0x97c: smull   x18, w1, w12
     +0x980: smaddl  x18, w9, w0, x18
     +0x984: lsr     x15, x17, #32
     +0x988: lsr     x13, x18, #32
     +0x98c: stp     w15, w13, [x10], #8
     +0x990: b.ne    <mldsa_poly_invntt_tomont+0x93c>
     +0x994: mov     x8, #0x8efe00000000
     +0x998: mov     w9, #0xcefe
     +0x99c: add     x10, x2, #0x200
     +0x9a0: movk    x8, #0x7307, lsl #48
     +0x9a4: movk    w9, #0x27, lsl #16
     +0x9a8: mov     w11, #0x40
     +0x9ac: mov     x12, #0xffffffffff801fff
     +0x9b0: ldp     w14, w15, [x10]
     +0x9b4: ldr     w13, [x10, #256]
     +0x9b8: ldr     w16, [x10, #260]
     +0x9bc: subs    x11, x11, #0x2
     +0x9c0: sub     w17, w14, w13
     +0x9c4: sub     w0, w15, w16
     +0x9c8: add     w13, w13, w14
     +0x9cc: sxtw    x18, w17
     +0x9d0: sxtw    x1, w0
     +0x9d4: add     w14, w16, w15
     +0x9d8: stp     w13, w14, [x10]
     +0x9dc: mul     x18, x18, x8
     +0x9e0: mul     x1, x1, x8
     +0x9e4: asr     x18, x18, #32
     +0x9e8: asr     x1, x1, #32
     +0x9ec: smull   x18, w18, w12
     +0x9f0: smaddl  x17, w9, w17, x18
     +0x9f4: smull   x18, w1, w12
     +0x9f8: smaddl  x18, w9, w0, x18
     +0x9fc: lsr     x15, x17, #32
     +0xa00: lsr     x13, x18, #32
     +0xa04: str     w15, [x10, #256]
     +0xa08: str     w13, [x10, #260]
     +0xa0c: add     x10, x10, #0x8
     +0xa10: b.ne    <mldsa_poly_invntt_tomont+0x9b0>
     +0xa14: mov     x8, #0xbb0900000000
     +0xa18: mov     w9, #0x80
     +0xa1c: mov     x10, #0xffffffffff801fff
     +0xa20: movk    x8, #0x92e0, lsl #48
     +0xa24: mov     w11, #0xffff9b09
     +0xa28: mov     x12, x2
     +0xa2c: ldp     w14, w15, [x12]
     +0xa30: ldr     w13, [x12, #512]
     +0xa34: ldr     w16, [x12, #516]
     +0xa38: subs    x9, x9, #0x2
     +0xa3c: sub     w17, w14, w13
     +0xa40: sub     w0, w15, w16
     +0xa44: add     w13, w13, w14
     +0xa48: sxtw    x18, w17
     +0xa4c: sxtw    x1, w0
     +0xa50: add     w14, w16, w15
     +0xa54: stp     w13, w14, [x12]
     +0xa58: mul     x18, x18, x8
     +0xa5c: mul     x1, x1, x8
     +0xa60: asr     x18, x18, #32
     +0xa64: asr     x1, x1, #32
     +0xa68: smull   x18, w18, w10
     +0xa6c: smaddl  x17, w17, w11, x18
     +0xa70: smull   x18, w1, w10
     +0xa74: smaddl  x18, w0, w11, x18
     +0xa78: lsr     x15, x17, #32
     +0xa7c: lsr     x13, x18, #32
     +0xa80: str     w15, [x12, #512]
     +0xa84: str     w13, [x12, #516]
     +0xa88: add     x12, x12, #0x8
     +0xa8c: b.ne    <mldsa_poly_invntt_tomont+0xa2c>
     +0xa90: mov     x8, #0xe3fa00000000
     +0xa94: add     x9, x2, #0x8
     +0xa98: mov     w10, #0x100
     +0xa9c: movk    x8, #0xff7f, lsl #48
     +0xaa0: mov     w11, #0xa3fa
     +0xaa4: mov     x12, #0xffffffffff801fff
     +0xaa8: ldpsw   x13, x14, [x9, #-8]
     +0xaac: ldpsw   x17, x18, [x9]
     +0xab0: subs    x10, x10, #0x4
     +0xab4: mul     x15, x13, x8
     +0xab8: mul     x16, x14, x8
     +0xabc: mul     x0, x17, x8
     +0xac0: asr     x15, x15, #32
     +0xac4: mul     x1, x18, x8
     +0xac8: asr     x16, x16, #32
     +0xacc: smull   x13, w13, w11
     +0xad0: smull   x14, w14, w11
     +0xad4: asr     x0, x0, #32
     +0xad8: smaddl  x13, w15, w12, x13
     +0xadc: asr     x15, x1, #32
     +0xae0: smaddl  x14, w16, w12, x14
     +0xae4: smull   x17, w17, w11
     +0xae8: smull   x18, w18, w11
     +0xaec: lsr     x13, x13, #32
     +0xaf0: smaddl  x16, w0, w12, x17
     +0xaf4: lsr     x14, x14, #32
     +0xaf8: smaddl  x15, w15, w12, x18
     +0xafc: stp     w13, w14, [x9, #-8]
     +0xb00: lsr     x16, x16, #32
     +0xb04: lsr     x13, x15, #32
     +0xb08: stp     w16, w13, [x9], #16
     +0xb0c: b.ne    <mldsa_poly_invntt_tomont+0xaa8>
     +0xb10: ldp     x20, x19, [sp, #192]
     +0xb14: ldp     x22, x21, [sp, #176]
     +0xb18: ldp     x24, x23, [sp, #160]
     +0xb1c: ldp     x26, x25, [sp, #144]
     +0xb20: ldp     x28, x27, [sp, #128]
     +0xb24: ldp     x29, x30, [sp, #112]
     +0xb28: add     sp, sp, #0xd0
     +0xb2c: mov     x0, #0x0
     +0xb30: mov     x1, #0x0
     +0xb34: mov     x2, #0x0
     +0xb38: mov     x3, #0x0
     +0xb3c: mov     x4, #0x0
     +0xb40: mov     x5, #0x0
     +0xb44: mov     x6, #0x0
     +0xb48: mov     x7, #0x0
     +0xb4c: mov     x8, #0x0
     +0xb50: mov     x9, #0x0
     +0xb54: mov     x10, #0x0
     +0xb58: mov     x11, #0x0
     +0xb5c: mov     x12, #0x0
     +0xb60: mov     x13, #0x0
     +0xb64: mov     x14, #0x0
     +0xb68: mov     x15, #0x0
     +0xb6c: mov     x16, #0x0
     +0xb70: mov     x17, #0x0
     +0xb74: mov     x18, #0x0
     +0xb78: ret     
 ***)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa_poly_invntt_tomont"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomial x at a, 256 coefficients of 32 bits each,     *)
(* becomes mld_poly_invntt_tomont x. The function saves x19 to x29 and x30   *)
(* in a frame of 208 bytes below the stack pointer, which the clang code     *)
(* needs and the gcc code did not; the frame also holds its spills.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(a,1024); (word_sub stackpointer (word 208),208)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 208),208)]
         [(word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mldsa_poly_invntt_tomont) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i))))
                            s = mld_poly_invntt_tomont x i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 208),208)])`;;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* polynomial, the frame and the table of zetas in the image, and the writes *)
(* within the polynomial and the frame.                                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(a,1024); (word_sub stackpointer (word 208),208)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 208),208)]
         [(word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mldsa_poly_invntt_tomont) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = mld_poly_invntt_tomont x i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc (word_sub stackpointer (word 208))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; word(pc + rodata_mld_zetas),1024;
                       word_sub stackpointer (word 208),208]
                      [a,1024; word_sub stackpointer (word 208),208]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 208),208)])`;;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(a,1024); (word_sub stackpointer (word 208),208)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 208),208)]
         [(word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mldsa_poly_invntt_tomont) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc (word_sub stackpointer (word 208))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; word(pc + rodata_mld_zetas),1024;
                       word_sub stackpointer (word 208),208]
                      [a,1024; word_sub stackpointer (word 208),208]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 208),208)])`;;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_INVNTT_TOMONT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
