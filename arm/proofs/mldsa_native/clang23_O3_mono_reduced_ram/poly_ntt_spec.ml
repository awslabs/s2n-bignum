(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number-theoretic transform: the statement. This is the code for   *)
(* mldsa_poly_ntt (mld_poly_ntt in poly.c, which calls mld_poly_ntt_c) from  *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3 as *)
(* a monolithic build with MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md). *)
(* Clang has unrolled the butterflies of a layer and fused the loops: the    *)
(* first three layers are 7 loops of 32 or 64 iterations with the zeta in    *)
(* immediates (two butterflies per iteration); layers 4 to 8 have one loop   *)
(* each, an iteration of which does one block (layer 4 to 6) or several      *)
(* blocks, with the zetas from the table in the read-only data. The function *)
(* saves x19 to x24 in a frame of 48 bytes and clears the scratch registers, *)
(* including x18, which MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI does not   *)
(* cover (the frame has MAYCHANGE [X18] added). The gcc code had no frame and *)
(* the statements gain the stack pointer. It is verified in the whole image  *)
(* (see libmldsa.ml) against mld_poly_ntt of common/mldsa_native_poly.ml, and *)
(* shown to be constant time and memory safe.                                *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_ntt.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_ntt:
       +0x0: stp     x24, x23, [sp, #-48]!
       +0x4: stp     x22, x21, [sp, #16]
       +0x8: stp     x20, x19, [sp, #32]
       +0xc: mov     x8, #0x44f700000000
      +0x10: add     x9, x0, #0x4
      +0x14: mov     w10, #0x80
      +0x18: movk    x8, #0x6d1f, lsl #48
      +0x1c: mov     w11, #0x64f7
      +0x20: mov     x12, #0xffffffffff801fff
      +0x24: ldrsw   x13, [x9, #508]
      +0x28: ldrsw   x14, [x9, #512]
      +0x2c: subs    x10, x10, #0x2
      +0x30: mul     x15, x13, x8
      +0x34: mul     x16, x14, x8
      +0x38: smull   x13, w13, w11
      +0x3c: asr     x15, x15, #32
      +0x40: smull   x14, w14, w11
      +0x44: asr     x16, x16, #32
      +0x48: smaddl  x13, w15, w12, x13
      +0x4c: smaddl  x14, w16, w12, x14
      +0x50: ldp     w15, w16, [x9, #-4]
      +0x54: lsr     x13, x13, #32
      +0x58: lsr     x14, x14, #32
      +0x5c: sub     w17, w15, w13
      +0x60: add     w13, w15, w13
      +0x64: sub     w18, w16, w14
      +0x68: add     w14, w16, w14
      +0x6c: str     w17, [x9, #508]
      +0x70: str     w18, [x9, #512]
      +0x74: stp     w13, w14, [x9, #-4]
      +0x78: add     x9, x9, #0x8
      +0x7c: b.ne    <mldsa_poly_ntt+0x24>
      +0x80: mov     x8, #0xffffffffffff3102
      +0x84: mov     x9, #0x710200000000
      +0x88: add     x10, x0, #0x4
      +0x8c: movk    x8, #0xffd8, lsl #16
      +0x90: movk    x9, #0x8cf8, lsl #48
      +0x94: mov     w11, #0x40
      +0x98: mov     x12, #0xffffffffff801fff
      +0x9c: ldpsw   x13, x14, [x10, #252]
      +0xa0: subs    x11, x11, #0x2
      +0xa4: mul     x15, x13, x9
      +0xa8: mul     x16, x14, x9
      +0xac: smull   x13, w13, w8
      +0xb0: asr     x15, x15, #32
      +0xb4: smull   x14, w14, w8
      +0xb8: asr     x16, x16, #32
      +0xbc: smaddl  x13, w15, w12, x13
      +0xc0: smaddl  x14, w16, w12, x14
      +0xc4: ldp     w15, w16, [x10, #-4]
      +0xc8: lsr     x13, x13, #32
      +0xcc: lsr     x14, x14, #32
      +0xd0: sub     w17, w15, w13
      +0xd4: add     w13, w15, w13
      +0xd8: sub     w18, w16, w14
      +0xdc: add     w14, w16, w14
      +0xe0: stp     w17, w18, [x10, #252]
      +0xe4: stp     w13, w14, [x10, #-4]
      +0xe8: add     x10, x10, #0x8
      +0xec: b.ne    <mldsa_poly_ntt+0x9c>
      +0xf0: mov     x8, #0xffffffffffff1503
      +0xf4: mov     x9, #0x750300000000
      +0xf8: add     x10, x0, #0x200
      +0xfc: movk    x8, #0xfff8, lsl #16
     +0x100: movk    x9, #0x8d18, lsl #48
     +0x104: mov     w11, #0x40
     +0x108: mov     x12, #0xffffffffff801fff
     +0x10c: ldrsw   x13, [x10, #256]
     +0x110: ldrsw   x14, [x10, #260]
     +0x114: subs    x11, x11, #0x2
     +0x118: mul     x15, x13, x9
     +0x11c: mul     x16, x14, x9
     +0x120: smull   x13, w13, w8
     +0x124: asr     x15, x15, #32
     +0x128: smull   x14, w14, w8
     +0x12c: asr     x16, x16, #32
     +0x130: smaddl  x13, w15, w12, x13
     +0x134: smaddl  x14, w16, w12, x14
     +0x138: ldp     w15, w16, [x10]
     +0x13c: lsr     x13, x13, #32
     +0x140: lsr     x14, x14, #32
     +0x144: sub     w17, w15, w13
     +0x148: add     w13, w15, w13
     +0x14c: sub     w18, w16, w14
     +0x150: add     w14, w16, w14
     +0x154: str     w17, [x10, #256]
     +0x158: str     w18, [x10, #260]
     +0x15c: stp     w13, w14, [x10], #8
     +0x160: b.ne    <mldsa_poly_ntt+0x10c>
     +0x164: mov     x8, #0x1e4400000000
     +0x168: mov     w9, #0x9e44
     +0x16c: add     x10, x0, #0x4
     +0x170: movk    x8, #0x61cc, lsl #48
     +0x174: movk    w9, #0x3, lsl #16
     +0x178: mov     w11, #0x20
     +0x17c: mov     x12, #0xffffffffff801fff
     +0x180: ldpsw   x13, x14, [x10, #124]
     +0x184: subs    x11, x11, #0x2
     +0x188: mul     x15, x13, x8
     +0x18c: mul     x16, x14, x8
     +0x190: smull   x13, w13, w9
     +0x194: asr     x15, x15, #32
     +0x198: smull   x14, w14, w9
     +0x19c: asr     x16, x16, #32
     +0x1a0: smaddl  x13, w15, w12, x13
     +0x1a4: smaddl  x14, w16, w12, x14
     +0x1a8: ldp     w15, w16, [x10, #-4]
     +0x1ac: lsr     x13, x13, #32
     +0x1b0: lsr     x14, x14, #32
     +0x1b4: sub     w17, w15, w13
     +0x1b8: add     w13, w15, w13
     +0x1bc: sub     w18, w16, w14
     +0x1c0: add     w14, w16, w14
     +0x1c4: stp     w17, w18, [x10, #124]
     +0x1c8: stp     w13, w14, [x10, #-4]
     +0x1cc: add     x10, x10, #0x8
     +0x1d0: b.ne    <mldsa_poly_ntt+0x180>
     +0x1d4: mov     x8, #0xffffffffffff2118
     +0x1d8: mov     x9, #0x211800000000
     +0x1dc: add     x10, x0, #0x184
     +0x1e0: movk    x8, #0xfff4, lsl #16
     +0x1e4: movk    x9, #0x5817, lsl #48
     +0x1e8: mov     w11, #0x20
     +0x1ec: mov     x12, #0xffffffffff801fff
     +0x1f0: ldpsw   x13, x14, [x10, #-4]
     +0x1f4: subs    x11, x11, #0x2
     +0x1f8: mul     x15, x13, x9
     +0x1fc: mul     x16, x14, x9
     +0x200: smull   x13, w13, w8
     +0x204: asr     x15, x15, #32
     +0x208: smull   x14, w14, w8
     +0x20c: asr     x16, x16, #32
     +0x210: smaddl  x13, w15, w12, x13
     +0x214: smaddl  x14, w16, w12, x14
     +0x218: ldp     w15, w16, [x10, #-132]
     +0x21c: lsr     x13, x13, #32
     +0x220: lsr     x14, x14, #32
     +0x224: sub     w17, w15, w13
     +0x228: add     w13, w15, w13
     +0x22c: sub     w18, w16, w14
     +0x230: add     w14, w16, w14
     +0x234: stp     w17, w18, [x10, #-4]
     +0x238: stp     w13, w14, [x10, #-132]
     +0x23c: add     x10, x10, #0x8
     +0x240: b.ne    <mldsa_poly_ntt+0x1f0>
     +0x244: mov     x8, #0xffffffffffffa128
     +0x248: mov     x9, #0xa12800000000
     +0x24c: add     x10, x0, #0x284
     +0x250: movk    x8, #0xfff2, lsl #16
     +0x254: movk    x9, #0x6017, lsl #48
     +0x258: mov     w11, #0x20
     +0x25c: mov     x12, #0xffffffffff801fff
     +0x260: ldpsw   x13, x14, [x10, #-4]
     +0x264: subs    x11, x11, #0x2
     +0x268: mul     x15, x13, x9
     +0x26c: mul     x16, x14, x9
     +0x270: smull   x13, w13, w8
     +0x274: asr     x15, x15, #32
     +0x278: smull   x14, w14, w8
     +0x27c: asr     x16, x16, #32
     +0x280: smaddl  x13, w15, w12, x13
     +0x284: smaddl  x14, w16, w12, x14
     +0x288: ldp     w15, w16, [x10, #-132]
     +0x28c: lsr     x13, x13, #32
     +0x290: lsr     x14, x14, #32
     +0x294: sub     w17, w15, w13
     +0x298: add     w13, w15, w13
     +0x29c: sub     w18, w16, w14
     +0x2a0: add     w14, w16, w14
     +0x2a4: stp     w17, w18, [x10, #-4]
     +0x2a8: stp     w13, w14, [x10, #-132]
     +0x2ac: add     x10, x10, #0x8
     +0x2b0: b.ne    <mldsa_poly_ntt+0x260>
     +0x2b4: mov     x8, #0x9e2400000000
     +0x2b8: mov     w9, #0x1e24
     +0x2bc: add     x10, x0, #0x384
     +0x2c0: movk    x8, #0x61cb, lsl #48
     +0x2c4: movk    w9, #0x7, lsl #16
     +0x2c8: mov     w11, #0x20
     +0x2cc: mov     x12, #0xffffffffff801fff
     +0x2d0: ldpsw   x13, x14, [x10, #-4]
     +0x2d4: subs    x11, x11, #0x2
     +0x2d8: mul     x15, x13, x8
     +0x2dc: mul     x16, x14, x8
     +0x2e0: smull   x13, w13, w9
     +0x2e4: asr     x15, x15, #32
     +0x2e8: smull   x14, w14, w9
     +0x2ec: asr     x16, x16, #32
     +0x2f0: smaddl  x13, w15, w12, x13
     +0x2f4: smaddl  x14, w16, w12, x14
     +0x2f8: ldp     w15, w16, [x10, #-132]
     +0x2fc: lsr     x13, x13, #32
     +0x300: lsr     x14, x14, #32
     +0x304: sub     w17, w15, w13
     +0x308: add     w13, w15, w13
     +0x30c: sub     w18, w16, w14
     +0x310: add     w14, w16, w14
     +0x314: stp     w17, w18, [x10, #-4]
     +0x318: stp     w13, w14, [x10, #-132]
     +0x31c: add     x10, x10, #0x8
     +0x320: b.ne    <mldsa_poly_ntt+0x2d0>
     +0x324: mov     x9, #0x200100000000
     +0x328: mov     x10, xzr
     +0x32c: add     x11, x0, #0x40
     +0x330: movk    x9, #0x380, lsl #48
     +0x334: adrp    x8, <page>
     +0x338: add     x8, x8, #0x728
     +0x33c: mov     x12, #0xffffffffff801fff
     +0x340: add     x13, x8, x10
     +0x344: add     x10, x10, #0x4
     +0x348: ldpsw   x14, x15, [x11]
     +0x34c: ldrsw   x13, [x13, #32]
     +0x350: cmp     x10, #0x20
     +0x354: ldpsw   x21, x23, [x11, #32]
     +0x358: smull   x17, w14, w13
     +0x35c: smull   x14, w15, w13
     +0x360: ldpsw   x15, x16, [x11, #8]
     +0x364: mul     x18, x17, x9
     +0x368: smull   x5, w15, w13
     +0x36c: mul     x1, x14, x9
     +0x370: smull   x3, w16, w13
     +0x374: asr     x18, x18, #32
     +0x378: ldpsw   x15, x16, [x11, #16]
     +0x37c: mul     x6, x5, x9
     +0x380: smull   x2, w15, w13
     +0x384: mul     x7, x3, x9
     +0x388: smull   x15, w16, w13
     +0x38c: asr     x6, x6, #32
     +0x390: smaddl  x17, w18, w12, x17
     +0x394: asr     x18, x1, #32
     +0x398: ldpsw   x16, x19, [x11, #24]
     +0x39c: mul     x4, x2, x9
     +0x3a0: asr     x7, x7, #32
     +0x3a4: mul     x20, x15, x9
     +0x3a8: smaddl  x14, w18, w12, x14
     +0x3ac: lsr     x18, x17, #32
     +0x3b0: smull   x16, w16, w13
     +0x3b4: asr     x4, x4, #32
     +0x3b8: smaddl  x5, w6, w12, x5
     +0x3bc: ldp     w6, w22, [x11, #-64]
     +0x3c0: smull   x17, w19, w13
     +0x3c4: lsr     x19, x14, #32
     +0x3c8: asr     x20, x20, #32
     +0x3cc: smaddl  x3, w7, w12, x3
     +0x3d0: lsr     x5, x5, #32
     +0x3d4: mul     x1, x16, x9
     +0x3d8: sub     w7, w6, w18
     +0x3dc: add     w6, w6, w18
     +0x3e0: smull   x14, w21, w13
     +0x3e4: sub     w21, w22, w19
     +0x3e8: add     w19, w22, w19
     +0x3ec: stp     w7, w21, [x11]
     +0x3f0: mul     x7, x17, x9
     +0x3f4: lsr     x3, x3, #32
     +0x3f8: ldp     w21, w22, [x11, #-56]
     +0x3fc: smaddl  x4, w4, w12, x2
     +0x400: stp     w6, w19, [x11, #-64]
     +0x404: asr     x1, x1, #32
     +0x408: smaddl  x19, w20, w12, x15
     +0x40c: smull   x2, w23, w13
     +0x410: sub     w6, w21, w5
     +0x414: sub     w20, w22, w3
     +0x418: ldpsw   x24, x23, [x11, #40]
     +0x41c: add     w5, w21, w5
     +0x420: add     w3, w22, w3
     +0x424: lsr     x4, x4, #32
     +0x428: ldp     w21, w22, [x11, #-48]
     +0x42c: lsr     x19, x19, #32
     +0x430: smull   x15, w24, w13
     +0x434: stp     w6, w20, [x11, #8]
     +0x438: mul     x6, x2, x9
     +0x43c: asr     x7, x7, #32
     +0x440: stp     w5, w3, [x11, #-56]
     +0x444: sub     w5, w21, w4
     +0x448: smaddl  x1, w1, w12, x16
     +0x44c: smull   x16, w23, w13
     +0x450: sub     w23, w22, w19
     +0x454: add     w19, w22, w19
     +0x458: stp     w5, w23, [x11, #16]
     +0x45c: mul     x18, x14, x9
     +0x460: ldpsw   x3, x5, [x11, #48]
     +0x464: smaddl  x7, w7, w12, x17
     +0x468: asr     x6, x6, #32
     +0x46c: mul     x20, x15, x9
     +0x470: smull   x17, w3, w13
     +0x474: add     w3, w21, w4
     +0x478: lsr     x7, x7, #32
     +0x47c: ldp     w21, w22, [x11, #-40]
     +0x480: mul     x4, x16, x9
     +0x484: stp     w3, w19, [x11, #-48]
     +0x488: lsr     x3, x1, #32
     +0x48c: asr     x19, x18, #32
     +0x490: smull   x18, w5, w13
     +0x494: sub     w5, w21, w3
     +0x498: add     w3, w21, w3
     +0x49c: smaddl  x2, w6, w12, x2
     +0x4a0: sub     w6, w22, w7
     +0x4a4: add     w7, w22, w7
     +0x4a8: stp     w5, w6, [x11, #24]
     +0x4ac: asr     x5, x20, #32
     +0x4b0: mul     x1, x17, x9
     +0x4b4: asr     x4, x4, #32
     +0x4b8: stp     w3, w7, [x11, #-40]
     +0x4bc: smaddl  x14, w19, w12, x14
     +0x4c0: lsr     x2, x2, #32
     +0x4c4: smaddl  x15, w5, w12, x15
     +0x4c8: ldpsw   x19, x5, [x11, #56]
     +0x4cc: mul     x6, x18, x9
     +0x4d0: lsr     x14, x14, #32
     +0x4d4: asr     x1, x1, #32
     +0x4d8: lsr     x15, x15, #32
     +0x4dc: smaddl  x16, w4, w12, x16
     +0x4e0: ldp     w20, w4, [x11, #-32]
     +0x4e4: smull   x19, w19, w13
     +0x4e8: smull   x13, w5, w13
     +0x4ec: asr     x6, x6, #32
     +0x4f0: lsr     x16, x16, #32
     +0x4f4: sub     w3, w20, w14
     +0x4f8: sub     w5, w4, w2
     +0x4fc: add     w2, w4, w2
     +0x500: stp     w3, w5, [x11, #32]
     +0x504: mul     x3, x19, x9
     +0x508: add     w14, w20, w14
     +0x50c: stp     w14, w2, [x11, #-32]
     +0x510: mul     x4, x13, x9
     +0x514: smaddl  x17, w1, w12, x17
     +0x518: ldp     w5, w1, [x11, #-24]
     +0x51c: smaddl  x14, w6, w12, x18
     +0x520: lsr     x17, x17, #32
     +0x524: sub     w18, w5, w15
     +0x528: sub     w2, w1, w16
     +0x52c: add     w16, w1, w16
     +0x530: stp     w18, w2, [x11, #40]
     +0x534: asr     x18, x3, #32
     +0x538: asr     x3, x4, #32
     +0x53c: ldp     w1, w2, [x11, #-16]
     +0x540: add     w15, w5, w15
     +0x544: lsr     x14, x14, #32
     +0x548: smaddl  x13, w3, w12, x13
     +0x54c: stp     w15, w16, [x11, #-24]
     +0x550: smaddl  x16, w18, w12, x19
     +0x554: sub     w15, w1, w17
     +0x558: sub     w18, w2, w14
     +0x55c: add     w14, w2, w14
     +0x560: stp     w15, w18, [x11, #48]
     +0x564: add     w15, w1, w17
     +0x568: lsr     x13, x13, #32
     +0x56c: ldp     w17, w18, [x11, #-8]
     +0x570: lsr     x16, x16, #32
     +0x574: stp     w15, w14, [x11, #-16]
     +0x578: sub     w14, w17, w16
     +0x57c: sub     w15, w18, w13
     +0x580: add     w13, w18, w13
     +0x584: stp     w14, w15, [x11, #56]
     +0x588: add     w14, w17, w16
     +0x58c: stp     w14, w13, [x11, #-8]
     +0x590: add     x11, x11, #0x80
     +0x594: b.ne    <mldsa_poly_ntt+0x340>
     +0x598: mov     x10, xzr
     +0x59c: add     x11, x0, #0x20
     +0x5a0: mov     x12, #0xffffffffff801fff
     +0x5a4: add     x13, x8, x10
     +0x5a8: add     x10, x10, #0x4
     +0x5ac: ldpsw   x14, x15, [x11]
     +0x5b0: ldrsw   x13, [x13, #64]
     +0x5b4: cmp     x10, #0x40
     +0x5b8: ldpsw   x3, x4, [x11, #16]
     +0x5bc: smull   x16, w14, w13
     +0x5c0: smull   x14, w15, w13
     +0x5c4: ldpsw   x15, x18, [x11, #8]
     +0x5c8: mul     x17, x16, x9
     +0x5cc: smull   x1, w15, w13
     +0x5d0: smull   x15, w18, w13
     +0x5d4: mul     x2, x14, x9
     +0x5d8: asr     x17, x17, #32
     +0x5dc: mul     x18, x1, x9
     +0x5e0: mul     x5, x15, x9
     +0x5e4: smull   x3, w3, w13
     +0x5e8: smaddl  x16, w17, w12, x16
     +0x5ec: asr     x17, x2, #32
     +0x5f0: asr     x18, x18, #32
     +0x5f4: smull   x4, w4, w13
     +0x5f8: smaddl  x14, w17, w12, x14
     +0x5fc: asr     x17, x5, #32
     +0x600: ldpsw   x7, x5, [x11, #24]
     +0x604: mul     x6, x3, x9
     +0x608: lsr     x16, x16, #32
     +0x60c: lsr     x14, x14, #32
     +0x610: smaddl  x18, w18, w12, x1
     +0x614: ldp     w1, w19, [x11, #-32]
     +0x618: mul     x2, x4, x9
     +0x61c: lsr     x18, x18, #32
     +0x620: smull   x7, w7, w13
     +0x624: smull   x13, w5, w13
     +0x628: sub     w5, w19, w14
     +0x62c: add     w14, w19, w14
     +0x630: smaddl  x15, w17, w12, x15
     +0x634: sub     w17, w1, w16
     +0x638: add     w16, w1, w16
     +0x63c: stp     w17, w5, [x11]
     +0x640: mul     x17, x7, x9
     +0x644: asr     x1, x6, #32
     +0x648: asr     x2, x2, #32
     +0x64c: stp     w16, w14, [x11, #-32]
     +0x650: mul     x5, x13, x9
     +0x654: lsr     x15, x15, #32
     +0x658: smaddl  x1, w1, w12, x3
     +0x65c: ldp     w6, w3, [x11, #-24]
     +0x660: smaddl  x14, w2, w12, x4
     +0x664: asr     x17, x17, #32
     +0x668: sub     w16, w6, w18
     +0x66c: sub     w2, w3, w15
     +0x670: add     w15, w3, w15
     +0x674: stp     w16, w2, [x11, #8]
     +0x678: lsr     x16, x1, #32
     +0x67c: asr     x3, x5, #32
     +0x680: ldp     w1, w2, [x11, #-16]
     +0x684: lsr     x14, x14, #32
     +0x688: smaddl  x17, w17, w12, x7
     +0x68c: add     w18, w6, w18
     +0x690: smaddl  x13, w3, w12, x13
     +0x694: stp     w18, w15, [x11, #-24]
     +0x698: sub     w15, w1, w16
     +0x69c: sub     w18, w2, w14
     +0x6a0: add     w14, w2, w14
     +0x6a4: stp     w15, w18, [x11, #16]
     +0x6a8: add     w15, w1, w16
     +0x6ac: lsr     x16, x17, #32
     +0x6b0: ldp     w17, w18, [x11, #-8]
     +0x6b4: lsr     x13, x13, #32
     +0x6b8: stp     w15, w14, [x11, #-16]
     +0x6bc: sub     w14, w17, w16
     +0x6c0: sub     w15, w18, w13
     +0x6c4: add     w13, w18, w13
     +0x6c8: stp     w14, w15, [x11, #24]
     +0x6cc: add     w14, w17, w16
     +0x6d0: stp     w14, w13, [x11, #-8]
     +0x6d4: add     x11, x11, #0x40
     +0x6d8: b.ne    <mldsa_poly_ntt+0x5a4>
     +0x6dc: mov     x10, xzr
     +0x6e0: add     x11, x0, #0x10
     +0x6e4: mov     x12, #0xffffffffff801fff
     +0x6e8: add     x13, x8, x10
     +0x6ec: add     x10, x10, #0x4
     +0x6f0: ldpsw   x14, x15, [x11]
     +0x6f4: ldrsw   x13, [x13, #128]
     +0x6f8: cmp     x10, #0x80
     +0x6fc: ldpsw   x17, x18, [x11, #8]
     +0x700: smull   x14, w14, w13
     +0x704: smull   x15, w15, w13
     +0x708: smull   x17, w17, w13
     +0x70c: mul     x16, x14, x9
     +0x710: mul     x1, x15, x9
     +0x714: smull   x13, w18, w13
     +0x718: mul     x18, x17, x9
     +0x71c: asr     x16, x16, #32
     +0x720: mul     x2, x13, x9
     +0x724: asr     x1, x1, #32
     +0x728: smaddl  x14, w16, w12, x14
     +0x72c: asr     x16, x18, #32
     +0x730: smaddl  x15, w1, w12, x15
     +0x734: asr     x18, x2, #32
     +0x738: smaddl  x16, w16, w12, x17
     +0x73c: lsr     x14, x14, #32
     +0x740: ldp     w17, w1, [x11, #-16]
     +0x744: lsr     x15, x15, #32
     +0x748: smaddl  x13, w18, w12, x13
     +0x74c: lsr     x16, x16, #32
     +0x750: sub     w18, w17, w14
     +0x754: add     w14, w17, w14
     +0x758: sub     w17, w1, w15
     +0x75c: add     w15, w1, w15
     +0x760: stp     w18, w17, [x11]
     +0x764: lsr     x13, x13, #32
     +0x768: stp     w14, w15, [x11, #-16]
     +0x76c: ldp     w14, w18, [x11, #-8]
     +0x770: sub     w17, w14, w16
     +0x774: sub     w15, w18, w13
     +0x778: add     w14, w14, w16
     +0x77c: add     w13, w18, w13
     +0x780: stp     w17, w15, [x11, #8]
     +0x784: stp     w14, w13, [x11, #-8]
     +0x788: add     x11, x11, #0x20
     +0x78c: b.ne    <mldsa_poly_ntt+0x6e8>
     +0x790: mov     w10, #0xff801fff
     +0x794: mov     x9, xzr
     +0x798: mov     x11, x0
     +0x79c: dup     v0.2s, w10
     +0x7a0: mov     x10, #0x200100000000
     +0x7a4: movk    x10, #0x380, lsl #48
     +0x7a8: ld4     {v1.4s-v4.4s}, [x11]
     +0x7ac: add     x12, x8, x9
     +0x7b0: add     x9, x9, #0x10
     +0x7b4: cmp     x9, #0x100
     +0x7b8: ldr     q7, [x12, #256]
     +0x7bc: smull   v6.2d, v3.2s, v7.2s
     +0x7c0: smull   v16.2d, v4.2s, v7.2s
     +0x7c4: smull2  v5.2d, v3.4s, v7.4s
     +0x7c8: smull2  v7.2d, v4.4s, v7.4s
     +0x7cc: fmov    x14, d6
     +0x7d0: mov     x15, v6.d[1]
     +0x7d4: fmov    x17, d16
     +0x7d8: fmov    x12, d5
     +0x7dc: mov     x16, v16.d[1]
     +0x7e0: mov     x13, v5.d[1]
     +0x7e4: fmov    x1, d7
     +0x7e8: mov     x18, v7.d[1]
     +0x7ec: mul     x14, x14, x10
     +0x7f0: mul     x17, x17, x10
     +0x7f4: mul     x15, x15, x10
     +0x7f8: fmov    d17, x14
     +0x7fc: mul     x12, x12, x10
     +0x800: fmov    d18, x17
     +0x804: mul     x16, x16, x10
     +0x808: mov     v17.d[1], x15
     +0x80c: mul     x14, x1, x10
     +0x810: fmov    d19, x12
     +0x814: mul     x13, x13, x10
     +0x818: mov     v18.d[1], x16
     +0x81c: shrn    v17.2s, v17.2d, #32
     +0x820: mul     x15, x18, x10
     +0x824: fmov    d20, x14
     +0x828: smull   v17.2d, v17.2s, v0.2s
     +0x82c: mov     v19.d[1], x13
     +0x830: shrn    v18.2s, v18.2d, #32
     +0x834: mov     v20.d[1], x15
     +0x838: smull   v18.2d, v18.2s, v0.2s
     +0x83c: addhn   v6.2s, v17.2d, v6.2d
     +0x840: shrn    v19.2s, v19.2d, #32
     +0x844: shrn    v20.2s, v20.2d, #32
     +0x848: smull   v19.2d, v19.2s, v0.2s
     +0x84c: addhn   v16.2s, v18.2d, v16.2d
     +0x850: smull   v17.2d, v20.2s, v0.2s
     +0x854: addhn2  v6.4s, v19.2d, v5.2d
     +0x858: addhn2  v16.4s, v17.2d, v7.2d
     +0x85c: sub     v19.4s, v1.4s, v6.4s
     +0x860: add     v17.4s, v1.4s, v6.4s
     +0x864: sub     v20.4s, v2.4s, v16.4s
     +0x868: add     v18.4s, v2.4s, v16.4s
     +0x86c: st4     {v17.4s-v20.4s}, [x11], #64
     +0x870: b.ne    <mldsa_poly_ntt+0x7a8>
     +0x874: mov     w10, #0xff801fff
     +0x878: mov     x9, xzr
     +0x87c: dup     v0.2s, w10
     +0x880: mov     x10, #0x200100000000
     +0x884: movk    x10, #0x380, lsl #48
     +0x888: ld2     {v1.4s-v2.4s}, [x0]
     +0x88c: add     x11, x8, x9
     +0x890: add     x9, x9, #0x10
     +0x894: cmp     x9, #0x200
     +0x898: ldr     q3, [x11, #512]
     +0x89c: smull   v4.2d, v2.2s, v3.2s
     +0x8a0: smull2  v3.2d, v2.4s, v3.4s
     +0x8a4: fmov    x12, d4
     +0x8a8: mov     x11, v4.d[1]
     +0x8ac: fmov    x14, d3
     +0x8b0: mov     x13, v3.d[1]
     +0x8b4: mul     x12, x12, x10
     +0x8b8: mul     x11, x11, x10
     +0x8bc: mul     x14, x14, x10
     +0x8c0: fmov    d5, x12
     +0x8c4: mul     x12, x13, x10
     +0x8c8: mov     v5.d[1], x11
     +0x8cc: fmov    d6, x14
     +0x8d0: mov     v6.d[1], x12
     +0x8d4: shrn    v5.2s, v5.2d, #32
     +0x8d8: smull   v5.2d, v5.2s, v0.2s
     +0x8dc: shrn    v6.2s, v6.2d, #32
     +0x8e0: smull   v6.2d, v6.2s, v0.2s
     +0x8e4: addhn   v4.2s, v5.2d, v4.2d
     +0x8e8: addhn2  v4.4s, v6.2d, v3.2d
     +0x8ec: sub     v6.4s, v1.4s, v4.4s
     +0x8f0: add     v5.4s, v1.4s, v4.4s
     +0x8f4: st2     {v5.4s-v6.4s}, [x0], #32
     +0x8f8: b.ne    <mldsa_poly_ntt+0x888>
     +0x8fc: ldp     x20, x19, [sp, #32]
     +0x900: ldp     x22, x21, [sp, #16]
     +0x904: ldp     x24, x23, [sp], #48
     +0x908: mov     x0, #0x0
     +0x90c: mov     x1, #0x0
     +0x910: mov     x2, #0x0
     +0x914: mov     x3, #0x0
     +0x918: mov     x4, #0x0
     +0x91c: mov     x5, #0x0
     +0x920: mov     x6, #0x0
     +0x924: mov     x7, #0x0
     +0x928: mov     x8, #0x0
     +0x92c: mov     x9, #0x0
     +0x930: mov     x10, #0x0
     +0x934: mov     x11, #0x0
     +0x938: mov     x12, #0x0
     +0x93c: mov     x13, #0x0
     +0x940: mov     x14, #0x0
     +0x944: mov     x15, #0x0
     +0x948: mov     x16, #0x0
     +0x94c: mov     x17, #0x0
     +0x950: mov     x18, #0x0
     +0x954: ret     
 ***)

let MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa_poly_ntt"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomial x at a, 256 coefficients of 32 bits each,     *)
(* becomes mld_poly_ntt x. The function saves x19 to x24 in a frame of 48    *)
(* bytes below the stack pointer, which the clang code needs and the gcc     *)
(* code did not.                                                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(a,1024); (word_sub stackpointer (word 48),48)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 48),48)]
         [(word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mldsa_poly_ntt) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i))))
                            s = mld_poly_ntt x i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* polynomial, the frame and the table of zetas in the image, and the writes *)
(* within the polynomial and the frame.                                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(a,1024); (word_sub stackpointer (word 48),48)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 48),48)]
         [(word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mldsa_poly_ntt) /\
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
                             s = mld_poly_ntt x i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc (word_sub stackpointer (word 48))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; word(pc + rodata_mld_zetas),1024;
                       word_sub stackpointer (word 48),48]
                      [a,1024; word_sub stackpointer (word 48),48]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(a,1024); (word_sub stackpointer (word 48),48)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 48),48)]
         [(word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mldsa_poly_ntt) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc (word_sub stackpointer (word 48))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; word(pc + rodata_mld_zetas),1024;
                       word_sub stackpointer (word 48),48]
                      [a,1024; word_sub stackpointer (word 48),48]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_NTT_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
