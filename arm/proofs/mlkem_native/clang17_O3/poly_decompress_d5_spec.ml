(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 5 bits per coefficient. This is the    *)
(* code for mlkem_poly_decompress_d5 from mlkem-native's portable C          *)
(* implementation compiled by clang 17 with -O3 (see mlkem_native/README.md).*)
(* It is verified in the whole image (see libmlkem.ml).                      *)
(*                                                                           *)
(* The compiler has vectorized the loop completely: after a check that the   *)
(* input and the output do not overlap, with one branch for each of the two  *)
(* orders of the arrays (if they overlap, the code falls back to a scalar    *)
(* loop, which cannot run under the specification), straight-line code      *)
(* loads the 160 bytes, gathers the bytes of the fields with 104 TBL using   *)
(* 30 vectors of indices from the read-only data, extracts the fields with   *)
(* shifts and masks, computes all 256 coefficients with UMULL and RSHRN #5,  *)
(* puts them in order with more TBL, and stores them. It saves D8 to D15 and *)
(* X29 and spills vectors to the stack, all in a frame of 784 bytes, which   *)
(* the specifications therefore have (unlike those of gcc12_O2, which have   *)
(* none).                                                                    *)
(*                                                                           *)
(* The registers are kept in the bit-level normal form of bitnorm.ml during  *)
(* the simulation, so that each lane before the product with 3329 is a       *)
(* 5-bit field of the 160 bytes, and each stored lane the rounded product.   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/overlap.ml";;
needs "arm/proofs/mlkem_native/bitnorm.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_decompress_d5:
        +0x0: stp     d15, d14, [sp, #-80]!
        +0x4: stp     d13, d12, [sp, #16]
        +0x8: stp     d11, d10, [sp, #32]
        +0xc: stp     d9, d8, [sp, #48]
       +0x10: str     x29, [sp, #64]
       +0x14: sub     sp, sp, #0x2c0
       +0x18: add     x8, x1, #0xa0
       +0x1c: cmp     x8, x0
       +0x20: b.ls    join1
       +0x24: add     x8, x0, #0x200
       +0x28: cmp     x8, x1
       +0x2c: b.ls    join1
       +0x30: adrp    x9, <page>
       +0x34: adrp    x10, <page>
       +0x38: mov     w11, #0xd01
       +0x3c: movi    d0, #0xff000000ff
       +0x40: mov     x8, xzr
       +0x44: ldr     d1, [x9, #1632]
                    // mlkem_poly_decompress_d5_const31
       +0x48: add     x9, x1, #0x2
       +0x4c: ldr     d2, [x10, #1640]
                    // mlkem_poly_decompress_d5_const32
       +0x50: dup     v3.8h, w11
       +0x54: ldrb    w10, [x9]
       +0x58: ldrb    w11, [x9, #1]
       +0x5c: fmov    s4, w10
       +0x60: ldurb   w10, [x9, #-2]
       +0x64: mov     v4.s[1], w11
       +0x68: ldurb   w11, [x9, #-1]
       +0x6c: and     w12, w10, #0x1f
       +0x70: lsr     w10, w10, #5
       +0x74: dup     v5.2s, w11
       +0x78: bfi     w10, w11, #3, #2
       +0x7c: fmov    w13, s4
       +0x80: fmov    s6, w12
       +0x84: mov     w14, v4.s[1]
       +0x88: ldrb    w11, [x9, #2]
       +0x8c: ushl    v4.2s, v4.2s, v2.2s
       +0x90: add     x9, x9, #0x5
       +0x94: ubfiz   w13, w13, #1, #4
       +0x98: and     v5.8b, v5.8b, v0.8b
       +0x9c: mov     v6.b[1], w10
       +0xa0: ushl    v5.2s, v5.2s, v1.2s
       +0xa4: ubfiz   w12, w14, #4, #1
       +0xa8: ubfiz   w10, w11, #2, #3
       +0xac: dup     v7.2s, w13
       +0xb0: fmov    s16, w12
       +0xb4: orr     v7.8b, v5.8b, v7.8b
       +0xb8: bic     v5.2s, #0x20
       +0xbc: mov     w13, v7.s[1]
       +0xc0: fmov    s7, w10
       +0xc4: mov     v6.b[2], v5.b[0]
       +0xc8: orr     v16.8b, v4.8b, v16.8b
       +0xcc: bic     v4.2s, #0xe0
       +0xd0: lsr     w10, w14, #6
       +0xd4: mov     v17.16b, v7.16b
       +0xd8: mov     w12, v4.s[1]
       +0xdc: mov     v17.s[1], w11
       +0xe0: mov     v6.b[3], w13
       +0xe4: fmov    s4, w10
       +0xe8: and     v17.8b, v17.8b, v0.8b
       +0xec: mov     v6.b[4], v16.b[0]
       +0xf0: ushr    v17.2s, v17.2s, #3
       +0xf4: orr     v4.8b, v7.8b, v4.8b
       +0xf8: mov     w10, v17.s[1]
       +0xfc: mov     v6.b[5], w12
      +0x100: mov     v6.b[6], v4.b[0]
      +0x104: mov     v6.b[7], w10
      +0x108: uxtl    v6.8h, v6.8b
      +0x10c: umull   v7.4s, v6.4h, v3.4h
      +0x110: umull2  v6.4s, v6.8h, v3.8h
      +0x114: rshrn   v7.4h, v7.4s, #5
      +0x118: rshrn2  v7.8h, v6.4s, #5
      +0x11c: str     q7, [x0, x8]
      +0x120: add     x8, x8, #0x10
      +0x124: cmp     x8, #0x200
      +0x128: b.ne    loop1
      +0x12c: b       join2
      +0x130: adrp    x8, <page>
      +0x134: adrp    x9, <page>
      +0x138: ldp     q5, q2, [x1, #16]
      +0x13c: adrp    x10, <page>
      +0x140: adrp    x11, <page>
      +0x144: movi    v24.16b, #0x1f
      +0x148: ldp     q3, q7, [x1, #48]
      +0x14c: ldr     q0, [x8, #544]
                    // mlkem_poly_decompress_d5_const1
      +0x150: adrp    x8, <page>
      +0x154: ldr     q4, [x1]
      +0x158: ldr     q16, [x9, #560]
                    // mlkem_poly_decompress_d5_const2
      +0x15c: adrp    x9, <page>
      +0x160: str     q0, [sp, #688]
      +0x164: ldr     q19, [x10, #576]
                    // mlkem_poly_decompress_d5_const3
      +0x168: tbl     v1.16b, {v2.16b-v3.16b}, v0.16b
      +0x16c: ldr     q21, [x11, #624]
                    // mlkem_poly_decompress_d5_const6
      +0x170: str     q16, [sp, #576]
      +0x174: ldr     q20, [x8, #592]
                    // mlkem_poly_decompress_d5_const4
      +0x178: tbl     v0.16b, {v4.16b-v5.16b}, v16.16b
      +0x17c: ldr     q16, [x9, #608]
                    // mlkem_poly_decompress_d5_const5
      +0x180: adrp    x9, <page>
      +0x184: adrp    x8, <page>
      +0x188: stp     q21, q16, [sp, #544]
      +0x18c: adrp    x10, <page>
      +0x190: adrp    x11, <page>
      +0x194: tbl     v17.16b, {v2.16b-v3.16b}, v16.16b
      +0x198: ldr     q18, [x9, #640]
                    // mlkem_poly_decompress_d5_const7
      +0x19c: adrp    x9, <page>
      +0x1a0: str     q19, [sp, #336]
      +0x1a4: tbl     v6.16b, {v0.16b-v1.16b}, v19.16b
      +0x1a8: ldr     q1, [x8, #656]
                    // mlkem_poly_decompress_d5_const8
      +0x1ac: tbl     v16.16b, {v4.16b-v5.16b}, v21.16b
      +0x1b0: adrp    x8, <page>
      +0x1b4: ldr     q21, [x9, #672]
                    // mlkem_poly_decompress_d5_const9
      +0x1b8: adrp    x9, <page>
      +0x1bc: str     q20, [sp, #416]
      +0x1c0: ldr     q30, [x11, #928]
                    // mlkem_poly_decompress_d5_const25
      +0x1c4: tbl     v0.16b, {v6.16b-v7.16b}, v20.16b
      +0x1c8: stp     q21, q1, [sp, #480]
      +0x1cc: tbl     v6.16b, {v16.16b-v17.16b}, v19.16b
      +0x1d0: tbl     v17.16b, {v2.16b-v3.16b}, v1.16b
      +0x1d4: ldr     q19, [x10, #688]
                    // mlkem_poly_decompress_d5_const10
      +0x1d8: tbl     v16.16b, {v4.16b-v5.16b}, v21.16b
      +0x1dc: ldr     q21, [x8, #720]
                    // mlkem_poly_decompress_d5_const12
      +0x1e0: ldr     q20, [x9, #736]
                    // mlkem_poly_decompress_d5_const13
      +0x1e4: adrp    x10, <page>
      +0x1e8: adrp    x8, <page>
      +0x1ec: adrp    x9, <page>
      +0x1f0: tbl     v1.16b, {v6.16b-v7.16b}, v18.16b
      +0x1f4: str     q18, [sp, #464]
      +0x1f8: tbl     v6.16b, {v16.16b-v17.16b}, v19.16b
      +0x1fc: str     q20, [sp, #528]
      +0x200: tbl     v17.16b, {v2.16b-v3.16b}, v21.16b
      +0x204: ldr     q18, [x10, #704]
                    // mlkem_poly_decompress_d5_const11
      +0x208: tbl     v16.16b, {v4.16b-v5.16b}, v20.16b
      +0x20c: ldr     q20, [x8, #768]
                    // mlkem_poly_decompress_d5_const15
      +0x210: str     q21, [sp, #512]
      +0x214: ldr     q21, [x9, #784]
                    // mlkem_poly_decompress_d5_const16
      +0x218: mov     v22.16b, v19.16b
      +0x21c: adrp    x10, <page>
      +0x220: adrp    x8, <page>
      +0x224: str     q19, [sp, #320]
      +0x228: tbl     v19.16b, {v6.16b-v7.16b}, v18.16b
      +0x22c: str     q18, [sp, #400]
      +0x230: tbl     v6.16b, {v16.16b-v17.16b}, v22.16b
      +0x234: ldr     q18, [x10, #752]
                    // mlkem_poly_decompress_d5_const14
      +0x238: tbl     v17.16b, {v2.16b-v3.16b}, v20.16b
      +0x23c: ldr     q2, [x8, #800]
                    // mlkem_poly_decompress_d5_const17
      +0x240: tbl     v16.16b, {v4.16b-v5.16b}, v21.16b
      +0x244: adrp    x8, <page>
      +0x248: movi    v4.16b, #0x18
      +0x24c: str     q21, [sp, #448]
      +0x250: tbl     v3.16b, {v6.16b-v7.16b}, v18.16b
      +0x254: stp     q2, q18, [sp, #352]
      +0x258: movi    v5.16b, #0x1e
      +0x25c: tbl     v6.16b, {v16.16b-v17.16b}, v2.16b
      +0x260: ldr     q2, [x8, #816]
                    // mlkem_poly_decompress_d5_const18
      +0x264: mov     w8, #0xd01
      +0x268: str     q20, [sp, #432]
      +0x26c: and     v29.16b, v0.16b, v24.16b
      +0x270: adrp    x9, <page>
      +0x274: str     q2, [sp, #384]
      +0x278: adrp    x10, <page>
      +0x27c: tbl     v10.16b, {v6.16b-v7.16b}, v2.16b
      +0x280: shl     v2.16b, v1.16b, #3
      +0x284: dup     v28.8h, w8
      +0x288: adrp    x8, <page>
      +0x28c: and     v9.16b, v2.16b, v4.16b
      +0x290: ushr    v2.16b, v1.16b, #2
      +0x294: movi    v4.16b, #0x10
      +0x298: ldr     q27, [x10, #896]
                    // mlkem_poly_decompress_d5_const23
      +0x29c: and     v6.16b, v2.16b, v24.16b
      +0x2a0: adrp    x10, <page>
      +0x2a4: shl     v2.16b, v3.16b, #4
      +0x2a8: adrp    x11, <page>
      +0x2ac: shl     v7.16b, v10.16b, #2
      +0x2b0: and     v2.16b, v2.16b, v4.16b
      +0x2b4: movi    v4.16b, #0x1c
      +0x2b8: usra    v2.16b, v19.16b, #4
      +0x2bc: usra    v9.16b, v0.16b, #5
      +0x2c0: add     v0.16b, v19.16b, v19.16b
      +0x2c4: and     v17.16b, v7.16b, v4.16b
      +0x2c8: usra    v17.16b, v3.16b, #6
      +0x2cc: uxtl    v7.8h, v2.8b
      +0x2d0: uxtl    v16.8h, v29.8b
      +0x2d4: uxtl    v21.8h, v17.8b
      +0x2d8: umull   v22.4s, v7.4h, v28.4h
      +0x2dc: umull   v23.4s, v21.4h, v28.4h
      +0x2e0: uxtl    v18.8h, v6.8b
      +0x2e4: and     v19.16b, v0.16b, v5.16b
      +0x2e8: umull   v0.4s, v16.4h, v28.4h
      +0x2ec: rshrn   v4.4h, v22.4s, #5
      +0x2f0: uxtl2   v22.8h, v2.16b
      +0x2f4: rshrn   v5.4h, v23.4s, #5
      +0x2f8: uxtl2   v2.8h, v17.16b
      +0x2fc: uxtl    v17.8h, v9.8b
      +0x300: str     q22, [sp, #144]
      +0x304: umull   v20.4s, v18.4h, v28.4h
      +0x308: umull   v23.4s, v17.4h, v28.4h
      +0x30c: usra    v19.16b, v1.16b, #7
      +0x310: rshrn   v0.4h, v0.4s, #5
      +0x314: rshrn   v1.4h, v20.4s, #5
      +0x318: ushr    v3.16b, v3.16b, #1
      +0x31c: rshrn2  v0.8h, v23.4s, #5
      +0x320: str     q19, [sp, #64]
      +0x324: uxtl    v23.8h, v19.8b
      +0x328: umull2  v20.4s, v21.8h, v28.8h
      +0x32c: umull   v21.4s, v22.4h, v28.4h
      +0x330: umull   v22.4s, v2.4h, v28.4h
      +0x334: and     v11.16b, v3.16b, v24.16b
      +0x338: ldr     q24, [x9, #864]
                    // mlkem_poly_decompress_d5_const21
      +0x33c: umull   v3.4s, v23.4h, v28.4h
      +0x340: adrp    x9, <page>
      +0x344: rshrn2  v5.8h, v20.4s, #5
      +0x348: rshrn   v20.4h, v21.4s, #5
      +0x34c: umull2  v2.4s, v2.8h, v28.8h
      +0x350: rshrn   v21.4h, v22.4s, #5
      +0x354: rshrn2  v1.8h, v3.4s, #5
      +0x358: ldr     q3, [x8, #832]
                    // mlkem_poly_decompress_d5_const19
      +0x35c: uxtl2   v19.8h, v29.16b
      +0x360: adrp    x8, <page>
      +0x364: uxtl2   v6.8h, v6.16b
      +0x368: rshrn2  v21.8h, v2.4s, #5
      +0x36c: tbl     v2.16b, {v0.16b-v1.16b}, v3.16b
      +0x370: mov     v26.16b, v3.16b
      +0x374: tbl     v3.16b, {v0.16b-v1.16b}, v27.16b
      +0x378: umull2  v7.4s, v7.8h, v28.8h
      +0x37c: str     q2, [sp, #208]
      +0x380: tbl     v2.16b, {v0.16b-v1.16b}, v24.16b
      +0x384: tbl     v0.16b, {v0.16b-v1.16b}, v30.16b
      +0x388: str     q3, [sp, #160]
      +0x38c: umull2  v1.4s, v16.8h, v28.8h
      +0x390: umull2  v16.4s, v17.8h, v28.8h
      +0x394: umull   v17.4s, v6.4h, v28.4h
      +0x398: stp     q0, q2, [sp, #176]
      +0x39c: rshrn   v12.4h, v7.4s, #5
      +0x3a0: umull   v0.4s, v19.4h, v28.4h
      +0x3a4: uxtl    v25.8h, v11.8b
      +0x3a8: umull2  v18.4s, v18.8h, v28.8h
      +0x3ac: umull   v22.4s, v25.4h, v28.4h
      +0x3b0: rshrn   v2.4h, v0.4s, #5
      +0x3b4: rshrn   v3.4h, v17.4s, #5
      +0x3b8: rshrn   v0.4h, v1.4s, #5
      +0x3bc: umull2  v17.4s, v25.8h, v28.8h
      +0x3c0: rshrn   v1.4h, v18.4s, #5
      +0x3c4: ushr    v18.16b, v10.16b, #3
      +0x3c8: rshrn2  v4.8h, v22.4s, #5
      +0x3cc: ldr     q22, [x10, #912]
                    // mlkem_poly_decompress_d5_const24
      +0x3d0: uxtl    v10.8h, v18.8b
      +0x3d4: str     q18, [sp, #16]
      +0x3d8: rshrn2  v12.8h, v17.4s, #5
      +0x3dc: ldr     q17, [x8, #848]
                    // mlkem_poly_decompress_d5_const20
      +0x3e0: rshrn2  v0.8h, v16.4s, #5
      +0x3e4: ldr     q18, [x9, #880]
                    // mlkem_poly_decompress_d5_const22
      +0x3e8: umull   v7.4s, v10.4h, v28.4h
      +0x3ec: str     q22, [sp, #656]
      +0x3f0: umull2  v16.4s, v23.8h, v28.8h
      +0x3f4: str     q17, [sp, #624]
      +0x3f8: tbl     v23.16b, {v4.16b-v5.16b}, v17.16b
      +0x3fc: ldr     q17, [x11, #944]
                    // mlkem_poly_decompress_d5_const26
      +0x400: str     q18, [sp, #672]
      +0x404: adrp    x8, <page>
      +0x408: tbl     v18.16b, {v4.16b-v5.16b}, v18.16b
      +0x40c: rshrn   v7.4h, v7.4s, #5
      +0x410: tbl     v22.16b, {v4.16b-v5.16b}, v22.16b
      +0x414: adrp    x9, <page>
      +0x418: tbl     v4.16b, {v4.16b-v5.16b}, v17.16b
      +0x41c: adrp    x10, <page>
      +0x420: rshrn2  v1.8h, v16.4s, #5
      +0x424: ldr     q31, [x8, #960]
                    // mlkem_poly_decompress_d5_const27
      +0x428: mov     v13.16b, v5.16b
      +0x42c: adrp    x8, <page>
      +0x430: mov     v23.h[7], v7.h[0]
      +0x434: str     q17, [sp, #640]
      +0x438: mov     v18.h[7], v7.h[1]
      +0x43c: ldr     q8, [x9, #976]
                    // mlkem_poly_decompress_d5_const28
      +0x440: mov     v22.h[7], v7.h[2]
      +0x444: ldr     q15, [x10, #992]
                    // mlkem_poly_decompress_d5_const29
      +0x448: mov     v4.h[7], v7.h[3]
      +0x44c: ldr     q17, [x8, #1008]
                    // mlkem_poly_decompress_d5_const30
      +0x450: tbl     v7.16b, {v0.16b-v1.16b}, v26.16b
      +0x454: stp     q31, q8, [sp, #224]
      +0x458: tbl     v5.16b, {v0.16b-v1.16b}, v24.16b
      +0x45c: stp     q18, q23, [sp, #112]
      +0x460: uxtl2   v9.8h, v9.16b
      +0x464: str     q17, [sp, #608]
      +0x468: tbl     v14.16b, {v0.16b-v1.16b}, v30.16b
      +0x46c: stp     q4, q22, [sp, #80]
      +0x470: tbl     v29.16b, {v12.16b-v13.16b}, v8.16b
      +0x474: add     x8, sp, #0x240
      +0x478: stp     q5, q7, [sp, #32]
      +0x47c: tbl     v7.16b, {v0.16b-v1.16b}, v27.16b
      +0x480: umull   v1.4s, v9.4h, v28.4h
      +0x484: umull2  v0.4s, v10.8h, v28.8h
      +0x488: tbl     v10.16b, {v12.16b-v13.16b}, v31.16b
      +0x48c: tbl     v25.16b, {v12.16b-v13.16b}, v15.16b
      +0x490: str     q7, [sp]
      +0x494: rshrn2  v2.8h, v1.4s, #5
      +0x498: ldr     q1, [sp, #64]
      +0x49c: tbl     v12.16b, {v12.16b-v13.16b}, v17.16b
      +0x4a0: rshrn   v0.4h, v0.4s, #5
      +0x4a4: uxtl2   v23.8h, v1.16b
      +0x4a8: mov     v7.16b, v30.16b
      +0x4ac: umull   v13.4s, v23.4h, v28.4h
      +0x4b0: mov     v10.h[7], v0.h[0]
      +0x4b4: mov     v29.h[7], v0.h[1]
      +0x4b8: mov     v25.h[7], v0.h[2]
      +0x4bc: mov     v12.h[7], v0.h[3]
      +0x4c0: ldr     q0, [sp, #144]
      +0x4c4: rshrn2  v3.8h, v13.4s, #5
      +0x4c8: uxtl2   v13.8h, v11.16b
      +0x4cc: umull2  v19.4s, v19.8h, v28.8h
      +0x4d0: umull   v30.4s, v13.4h, v28.4h
      +0x4d4: umull2  v11.4s, v0.8h, v28.8h
      +0x4d8: mov     v4.16b, v26.16b
      +0x4dc: mov     v16.16b, v24.16b
      +0x4e0: mov     v5.16b, v27.16b
      +0x4e4: stp     q16, q4, [sp, #288]
      +0x4e8: rshrn2  v20.8h, v30.4s, #5
      +0x4ec: stp     q7, q5, [sp, #256]
      +0x4f0: rshrn   v0.4h, v19.4s, #5
      +0x4f4: rshrn   v26.4h, v11.4s, #5
      +0x4f8: tbl     v30.16b, {v2.16b-v3.16b}, v4.16b
      +0x4fc: tbl     v19.16b, {v2.16b-v3.16b}, v16.16b
      +0x500: mov     v22.16b, v16.16b
      +0x504: tbl     v11.16b, {v2.16b-v3.16b}, v5.16b
      +0x508: tbl     v16.16b, {v2.16b-v3.16b}, v7.16b
      +0x50c: ldr     q2, [sp, #16]
      +0x510: umull2  v6.4s, v6.8h, v28.8h
      +0x514: mov     v18.16b, v5.16b
      +0x518: uxtl2   v3.8h, v2.16b
      +0x51c: ldr     q2, [sp, #624]
      +0x520: mov     v24.16b, v4.16b
      +0x524: rshrn   v1.4h, v6.4s, #5
      +0x528: umull2  v6.4s, v13.8h, v28.8h
      +0x52c: tbl     v13.16b, {v20.16b-v21.16b}, v2.16b
      +0x530: ldr     q2, [sp, #672]
      +0x534: mov     v17.16b, v7.16b
      +0x538: mov     v14.d[1], v12.d[1]
      +0x53c: tbl     v5.16b, {v20.16b-v21.16b}, v2.16b
      +0x540: ldr     q2, [sp, #656]
      +0x544: rshrn2  v26.8h, v6.4s, #5
      +0x548: umull2  v6.4s, v9.8h, v28.8h
      +0x54c: umull   v9.4s, v3.4h, v28.4h
      +0x550: tbl     v4.16b, {v20.16b-v21.16b}, v2.16b
      +0x554: ldr     q2, [sp, #640]
      +0x558: mov     v27.16b, v21.16b
      +0x55c: rshrn2  v0.8h, v6.4s, #5
      +0x560: tbl     v20.16b, {v20.16b-v21.16b}, v2.16b
      +0x564: ldr     q2, [sp, #608]
      +0x568: umull2  v6.4s, v23.8h, v28.8h
      +0x56c: rshrn   v21.4h, v9.4s, #5
      +0x570: umull2  v3.4s, v3.8h, v28.8h
      +0x574: tbl     v7.16b, {v26.16b-v27.16b}, v8.16b
      +0x578: mov     v13.h[7], v21.h[0]
      +0x57c: mov     v5.h[7], v21.h[1]
      +0x580: mov     v4.h[7], v21.h[2]
      +0x584: mov     v20.h[7], v21.h[3]
      +0x588: rshrn2  v1.8h, v6.4s, #5
      +0x58c: tbl     v6.16b, {v26.16b-v27.16b}, v31.16b
      +0x590: tbl     v21.16b, {v26.16b-v27.16b}, v15.16b
      +0x594: tbl     v26.16b, {v26.16b-v27.16b}, v2.16b
      +0x598: rshrn   v3.4h, v3.4s, #5
      +0x59c: tbl     v27.16b, {v0.16b-v1.16b}, v24.16b
      +0x5a0: tbl     v9.16b, {v0.16b-v1.16b}, v22.16b
      +0x5a4: tbl     v2.16b, {v0.16b-v1.16b}, v18.16b
      +0x5a8: tbl     v0.16b, {v0.16b-v1.16b}, v17.16b
      +0x5ac: ldr     q1, [sp]
      +0x5b0: mov     v26.h[7], v3.h[3]
      +0x5b4: mov     v21.h[7], v3.h[2]
      +0x5b8: mov     v7.h[7], v3.h[1]
      +0x5bc: mov     v6.h[7], v3.h[0]
      +0x5c0: mov     v0.d[1], v26.d[1]
      +0x5c4: mov     v2.d[1], v21.d[1]
      +0x5c8: mov     v11.d[1], v4.d[1]
      +0x5cc: mov     v19.d[1], v5.d[1]
      +0x5d0: ldp     q4, q5, [sp, #32]
      +0x5d4: stp     q2, q0, [x0, #224]
      +0x5d8: mov     v1.d[1], v25.d[1]
      +0x5dc: mov     v9.d[1], v7.d[1]
      +0x5e0: mov     v4.d[1], v29.d[1]
      +0x5e4: mov     v27.d[1], v6.d[1]
      +0x5e8: ldp     q2, q3, [sp, #160]
      +0x5ec: mov     v5.d[1], v10.d[1]
      +0x5f0: stp     q1, q14, [x0, #96]
      +0x5f4: mov     v16.d[1], v20.d[1]
      +0x5f8: mov     v30.d[1], v13.d[1]
      +0x5fc: stp     q27, q9, [x0, #192]
      +0x600: mov     v31.16b, v15.16b
      +0x604: stp     q5, q4, [x0, #64]
      +0x608: ldr     q0, [sp, #80]
      +0x60c: stp     q11, q16, [x0, #160]
      +0x610: ldr     q1, [sp, #192]
      +0x614: stp     q30, q19, [x0, #128]
      +0x618: mov     v3.d[1], v0.d[1]
      +0x61c: ldr     q0, [sp, #96]
      +0x620: ldr     q6, [sp, #688]
      +0x624: ldr     q16, [sp, #576]
      +0x628: mov     v2.d[1], v0.d[1]
      +0x62c: ldp     q0, q4, [sp, #112]
      +0x630: ldp     q19, q17, [sp, #320]
      +0x634: mov     v1.d[1], v0.d[1]
      +0x638: stp     q2, q3, [x0, #32]
      +0x63c: ldr     q0, [sp, #208]
      +0x640: mov     v0.d[1], v4.d[1]
      +0x644: stp     q0, q1, [x0]
      +0x648: ldp     q5, q0, [x1, #96]
      +0x64c: ldp     q1, q3, [x1, #128]
      +0x650: tbl     v7.16b, {v0.16b-v1.16b}, v6.16b
      +0x654: ldr     q4, [x1, #80]
      +0x658: tbl     v6.16b, {v4.16b-v5.16b}, v16.16b
      +0x65c: tbl     v2.16b, {v6.16b-v7.16b}, v17.16b
      +0x660: ldp     q16, q6, [sp, #544]
      +0x664: tbl     v7.16b, {v0.16b-v1.16b}, v6.16b
      +0x668: tbl     v6.16b, {v4.16b-v5.16b}, v16.16b
      +0x66c: ldr     q16, [sp, #416]
      +0x670: tbl     v16.16b, {v2.16b-v3.16b}, v16.16b
      +0x674: tbl     v2.16b, {v6.16b-v7.16b}, v17.16b
      +0x678: ldp     q17, q6, [sp, #480]
      +0x67c: tbl     v7.16b, {v0.16b-v1.16b}, v6.16b
      +0x680: tbl     v6.16b, {v4.16b-v5.16b}, v17.16b
      +0x684: ldr     q17, [sp, #464]
      +0x688: tbl     v17.16b, {v2.16b-v3.16b}, v17.16b
      +0x68c: tbl     v2.16b, {v6.16b-v7.16b}, v19.16b
      +0x690: ldp     q6, q18, [sp, #512]
      +0x694: tbl     v7.16b, {v0.16b-v1.16b}, v6.16b
      +0x698: tbl     v6.16b, {v4.16b-v5.16b}, v18.16b
      +0x69c: ldr     q18, [sp, #400]
      +0x6a0: tbl     v18.16b, {v2.16b-v3.16b}, v18.16b
      +0x6a4: tbl     v2.16b, {v6.16b-v7.16b}, v19.16b
      +0x6a8: ldr     q6, [sp, #432]
      +0x6ac: tbl     v1.16b, {v0.16b-v1.16b}, v6.16b
      +0x6b0: ldr     q6, [sp, #448]
      +0x6b4: tbl     v0.16b, {v4.16b-v5.16b}, v6.16b
      +0x6b8: ldr     q4, [sp, #368]
      +0x6bc: tbl     v7.16b, {v2.16b-v3.16b}, v4.16b
      +0x6c0: ldr     q4, [sp, #352]
      +0x6c4: tbl     v2.16b, {v0.16b-v1.16b}, v4.16b
      +0x6c8: ldr     q0, [sp, #384]
      +0x6cc: tbl     v4.16b, {v2.16b-v3.16b}, v0.16b
      +0x6d0: shl     v0.16b, v17.16b, #3
      +0x6d4: movi    v3.16b, #0x18
      +0x6d8: movi    v2.16b, #0x1f
      +0x6dc: and     v21.16b, v0.16b, v3.16b
      +0x6e0: ushr    v0.16b, v17.16b, #2
      +0x6e4: and     v1.16b, v16.16b, v2.16b
      +0x6e8: and     v6.16b, v0.16b, v2.16b
      +0x6ec: movi    v2.16b, #0x1e
      +0x6f0: add     v0.16b, v18.16b, v18.16b
      +0x6f4: movi    v3.16b, #0x1f
      +0x6f8: usra    v21.16b, v16.16b, #5
      +0x6fc: and     v23.16b, v0.16b, v2.16b
      +0x700: movi    v2.16b, #0x10
      +0x704: shl     v0.16b, v7.16b, #4
      +0x708: usra    v23.16b, v17.16b, #7
      +0x70c: and     v16.16b, v0.16b, v2.16b
      +0x710: ushr    v0.16b, v7.16b, #1
      +0x714: usra    v16.16b, v18.16b, #4
      +0x718: and     v5.16b, v0.16b, v3.16b
      +0x71c: movi    v0.16b, #0x1c
      +0x720: shl     v2.16b, v4.16b, #2
      +0x724: uxtl    v3.8h, v1.8b
      +0x728: ushr    v4.16b, v4.16b, #3
      +0x72c: uxtl    v22.8h, v5.8b
      +0x730: and     v0.16b, v2.16b, v0.16b
      +0x734: usra    v0.16b, v7.16b, #6
      +0x738: uxtl2   v7.8h, v1.16b
      +0x73c: uxtl    v1.8h, v16.8b
      +0x740: uxtl2   v16.8h, v16.16b
      +0x744: umull   v18.4s, v1.4h, v28.4h
      +0x748: umull   v19.4s, v16.4h, v28.4h
      +0x74c: umull2  v1.4s, v1.8h, v28.8h
      +0x750: umull2  v20.4s, v16.8h, v28.8h
      +0x754: rshrn   v25.4h, v18.4s, #5
      +0x758: uxtl    v18.8h, v0.8b
      +0x75c: rshrn   v8.4h, v19.4s, #5
      +0x760: uxtl2   v0.8h, v0.16b
      +0x764: umull   v24.4s, v18.4h, v28.4h
      +0x768: umull2  v16.4s, v22.8h, v28.8h
      +0x76c: rshrn   v14.4h, v1.4s, #5
      +0x770: uxtl2   v1.8h, v5.16b
      +0x774: rshrn   v10.4h, v20.4s, #5
      +0x778: rshrn   v26.4h, v24.4s, #5
      +0x77c: umull   v24.4s, v0.4h, v28.4h
      +0x780: umull2  v0.4s, v0.8h, v28.8h
      +0x784: umull2  v18.4s, v18.8h, v28.8h
      +0x788: ldp     q17, q5, [sp, #224]
      +0x78c: rshrn   v9.4h, v24.4s, #5
      +0x790: umull   v22.4s, v22.4h, v28.4h
      +0x794: rshrn2  v14.8h, v16.4s, #5
      +0x798: rshrn2  v9.8h, v0.4s, #5
      +0x79c: umull2  v0.4s, v1.8h, v28.8h
      +0x7a0: umull   v16.4s, v1.4h, v28.4h
      +0x7a4: rshrn2  v26.8h, v18.4s, #5
      +0x7a8: rshrn2  v25.8h, v22.4s, #5
      +0x7ac: rshrn2  v10.8h, v0.4s, #5
      +0x7b0: ldr     q0, [sp, #608]
      +0x7b4: mov     v15.16b, v26.16b
      +0x7b8: rshrn2  v8.8h, v16.4s, #5
      +0x7bc: st1     {v25.2d-v26.2d}, [x8]
      +0x7c0: mov     v11.16b, v9.16b
      +0x7c4: tbl     v1.16b, {v14.16b-v15.16b}, v17.16b
      +0x7c8: tbl     v16.16b, {v14.16b-v15.16b}, v5.16b
      +0x7cc: tbl     v19.16b, {v14.16b-v15.16b}, v31.16b
      +0x7d0: tbl     v20.16b, {v14.16b-v15.16b}, v0.16b
      +0x7d4: tbl     v22.16b, {v10.16b-v11.16b}, v17.16b
      +0x7d8: str     q1, [sp, #688]
      +0x7dc: tbl     v15.16b, {v10.16b-v11.16b}, v5.16b
      +0x7e0: tbl     v12.16b, {v10.16b-v11.16b}, v31.16b
      +0x7e4: tbl     v24.16b, {v10.16b-v11.16b}, v0.16b
      +0x7e8: uxtl2   v11.8h, v23.16b
      +0x7ec: uxtl    v23.8h, v23.8b
      +0x7f0: ldr     q17, [sp, #688]
      +0x7f4: umull2  v0.4s, v11.8h, v28.8h
      +0x7f8: uxtl    v18.8h, v6.8b
      +0x7fc: umull   v2.4s, v3.4h, v28.4h
      +0x800: umull2  v3.4s, v3.8h, v28.8h
      +0x804: str     q0, [sp, #496]
      +0x808: umull   v0.4s, v23.4h, v28.4h
      +0x80c: umull2  v25.4s, v18.8h, v28.8h
      +0x810: umull   v18.4s, v18.4h, v28.4h
      +0x814: uxtl2   v6.8h, v6.16b
      +0x818: uxtl    v14.8h, v4.8b
      +0x81c: stp     q0, q22, [sp, #544]
      +0x820: umull2  v29.4s, v7.8h, v28.8h
      +0x824: rshrn   v26.4h, v3.4s, #5
      +0x828: rshrn   v2.4h, v2.4s, #5
      +0x82c: rshrn   v27.4h, v25.4s, #5
      +0x830: umull   v10.4s, v6.4h, v28.4h
      +0x834: rshrn   v3.4h, v18.4s, #5
      +0x838: umull2  v6.4s, v6.8h, v28.8h
      +0x83c: umull   v0.4s, v14.4h, v28.4h
      +0x840: umull2  v14.4s, v14.8h, v28.8h
      +0x844: uxtl2   v18.8h, v21.16b
      +0x848: uxtl    v21.8h, v21.8b
      +0x84c: uxtl2   v4.8h, v4.16b
      +0x850: str     q0, [sp, #608]
      +0x854: umull   v30.4s, v7.4h, v28.4h
      +0x858: mov     v1.16b, v31.16b
      +0x85c: umull2  v25.4s, v18.8h, v28.8h
      +0x860: umull   v18.4s, v18.4h, v28.4h
      +0x864: umull2  v31.4s, v21.8h, v28.8h
      +0x868: umull   v21.4s, v21.4h, v28.4h
      +0x86c: umull   v11.4s, v11.4h, v28.4h
      +0x870: umull2  v13.4s, v23.8h, v28.8h
      +0x874: umull   v7.4s, v4.4h, v28.4h
      +0x878: umull2  v5.4s, v4.8h, v28.8h
      +0x87c: rshrn   v28.4h, v29.4s, #5
      +0x880: rshrn   v29.4h, v6.4s, #5
      +0x884: rshrn   v6.4h, v14.4s, #5
      +0x888: rshrn   v0.4h, v30.4s, #5
      +0x88c: rshrn2  v26.8h, v31.4s, #5
      +0x890: rshrn   v1.4h, v10.4s, #5
      +0x894: mov     v17.h[7], v6.h[0]
      +0x898: mov     v16.h[7], v6.h[1]
      +0x89c: mov     v20.h[7], v6.h[3]
      +0x8a0: rshrn2  v27.8h, v13.4s, #5
      +0x8a4: rshrn2  v0.8h, v18.4s, #5
      +0x8a8: str     q17, [sp, #688]
      +0x8ac: ldp     q14, q13, [sp, #288]
      +0x8b0: stp     q16, q20, [sp, #512]
      +0x8b4: mov     v16.16b, v19.16b
      +0x8b8: rshrn2  v1.8h, v11.4s, #5
      +0x8bc: rshrn2  v2.8h, v21.4s, #5
      +0x8c0: tbl     v21.16b, {v26.16b-v27.16b}, v14.16b
      +0x8c4: ldp     q4, q23, [sp, #256]
      +0x8c8: tbl     v22.16b, {v26.16b-v27.16b}, v13.16b
      +0x8cc: mov     v16.h[7], v6.h[2]
      +0x8d0: tbl     v6.16b, {v0.16b-v1.16b}, v13.16b
      +0x8d4: rshrn2  v28.8h, v25.4s, #5
      +0x8d8: ldp     q18, q17, [sp, #656]
      +0x8dc: tbl     v30.16b, {v26.16b-v27.16b}, v23.16b
      +0x8e0: tbl     v26.16b, {v26.16b-v27.16b}, v4.16b
      +0x8e4: tbl     v27.16b, {v0.16b-v1.16b}, v14.16b
      +0x8e8: tbl     v31.16b, {v0.16b-v1.16b}, v23.16b
      +0x8ec: tbl     v0.16b, {v0.16b-v1.16b}, v4.16b
      +0x8f0: ldp     q20, q19, [sp, #624]
      +0x8f4: rshrn   v1.4h, v7.4s, #5
      +0x8f8: tbl     v25.16b, {v8.16b-v9.16b}, v17.16b
      +0x8fc: tbl     v10.16b, {v8.16b-v9.16b}, v18.16b
      +0x900: tbl     v7.16b, {v8.16b-v9.16b}, v20.16b
      +0x904: mov     v30.d[1], v16.d[1]
      +0x908: tbl     v8.16b, {v8.16b-v9.16b}, v19.16b
      +0x90c: ldr     q9, [sp, #496]
      +0x910: mov     v25.h[7], v1.h[1]
      +0x914: mov     v7.h[7], v1.h[0]
      +0x918: rshrn2  v29.8h, v9.4s, #5
      +0x91c: mov     v10.h[7], v1.h[2]
      +0x920: mov     v8.h[7], v1.h[3]
      +0x924: rshrn   v1.4h, v5.4s, #5
      +0x928: mov     v27.d[1], v25.d[1]
      +0x92c: mov     v6.d[1], v7.d[1]
      +0x930: tbl     v5.16b, {v28.16b-v29.16b}, v13.16b
      +0x934: tbl     v9.16b, {v28.16b-v29.16b}, v14.16b
      +0x938: tbl     v11.16b, {v28.16b-v29.16b}, v23.16b
      +0x93c: tbl     v28.16b, {v28.16b-v29.16b}, v4.16b
      +0x940: stp     q6, q27, [x0, #384]
      +0x944: mov     v29.16b, v4.16b
      +0x948: ldp     q6, q4, [sp, #544]
      +0x94c: mov     v24.h[7], v1.h[3]
      +0x950: mov     v15.h[7], v1.h[1]
      +0x954: mov     v4.h[7], v1.h[0]
      +0x958: mov     v0.d[1], v8.d[1]
      +0x95c: mov     v28.d[1], v24.d[1]
      +0x960: ld1     {v24.2d-v25.2d}, [x8]
      +0x964: mov     v31.d[1], v10.d[1]
      +0x968: rshrn2  v3.8h, v6.4s, #5
      +0x96c: mov     v9.d[1], v15.d[1]
      +0x970: ldr     q6, [sp, #688]
      +0x974: mov     v5.d[1], v4.d[1]
      +0x978: stp     q31, q0, [x0, #416]
      +0x97c: mov     v12.h[7], v1.h[2]
      +0x980: ldp     q1, q0, [sp, #512]
      +0x984: mov     v22.d[1], v6.d[1]
      +0x988: ldr     q6, [sp, #608]
      +0x98c: stp     q5, q9, [x0, #448]
      +0x990: mov     v21.d[1], v1.d[1]
      +0x994: mov     v26.d[1], v0.d[1]
      +0x998: tbl     v0.16b, {v24.16b-v25.16b}, v20.16b
      +0x99c: tbl     v1.16b, {v24.16b-v25.16b}, v17.16b
      +0x9a0: tbl     v4.16b, {v24.16b-v25.16b}, v18.16b
      +0x9a4: stp     q22, q21, [x0, #320]
      +0x9a8: tbl     v5.16b, {v24.16b-v25.16b}, v19.16b
      +0x9ac: stp     q30, q26, [x0, #352]
      +0x9b0: rshrn   v6.4h, v6.4s, #5
      +0x9b4: tbl     v7.16b, {v2.16b-v3.16b}, v13.16b
      +0x9b8: tbl     v16.16b, {v2.16b-v3.16b}, v14.16b
      +0x9bc: tbl     v17.16b, {v2.16b-v3.16b}, v23.16b
      +0x9c0: tbl     v2.16b, {v2.16b-v3.16b}, v29.16b
      +0x9c4: mov     v5.h[7], v6.h[3]
      +0x9c8: mov     v4.h[7], v6.h[2]
      +0x9cc: mov     v1.h[7], v6.h[1]
      +0x9d0: mov     v0.h[7], v6.h[0]
      +0x9d4: mov     v11.d[1], v12.d[1]
      +0x9d8: mov     v2.d[1], v5.d[1]
      +0x9dc: mov     v17.d[1], v4.d[1]
      +0x9e0: mov     v16.d[1], v1.d[1]
      +0x9e4: mov     v7.d[1], v0.d[1]
      +0x9e8: stp     q11, q28, [x0, #480]
      +0x9ec: stp     q17, q2, [x0, #288]
      +0x9f0: stp     q7, q16, [x0, #256]
      +0x9f4: add     sp, sp, #0x2c0
      +0x9f8: ldp     d9, d8, [sp, #48]
      +0x9fc: ldp     d11, d10, [sp, #32]
      +0xa00: ldp     d13, d12, [sp, #16]
      +0xa04: ldr     x29, [sp, #64]
      +0xa08: ldp     d15, d14, [sp], #80
      +0xa0c: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_decompress_d5"];;

(*** The 30 vectors of constants of the vector code ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O3_CONSTANTS =
  map (fun k ->
    MLKEM_NATIVE_IMAGE_CONST_RULE
     (layout("mlkem_poly_decompress_d5_const" ^ string_of_int k)) 128)
   (1--30);;

let DECOMPRESS_D5_CONSTANTS_TAC =
  MAP_EVERY (fun th -> FIRST_ASSUM(fun ath ->
      if can (term_match [] `aligned_bytes_loaded s0 (word pc)
                               mlkem_native_libmlkem_clang17_O3_mc`)
             (concl ath)
      then ASSUME_TAC(MATCH_MP th ath) else failwith ""))
    MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O3_CONSTANTS;;

(* ------------------------------------------------------------------------- *)
(* The 160 bytes as a 1280-bit word w, with the ten 128-bit parts that the   *)
(* loads read as parts of w.                                                 *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES128_OF_NUM_STMT =
  `!a:int64 m n k s:armstate.
        read (memory :> bytes(a,m)) s = n /\ k + 16 <= m
        ==> read (memory :> bytes128(word_add a (word k))) s =
            word((n DIV 2 EXP (8 * k)) MOD 2 EXP 128)`;;

let READ_MEMORY_BYTES128_OF_NUM =
  assume_spec READ_MEMORY_BYTES128_OF_NUM_STMT;;

let D5_WIN_STMT =
  `!a n s k.
        read (memory :> bytes(a,160)) s = n /\ k < 10
        ==> read (memory :> bytes128(word_add a (word(16 * k)))) s =
            word_subword (word n:1280 word) (128 * k,128)`;;

let D5_WIN = assume_spec D5_WIN_STMT;;

let DECOMPRESS_D5_INPUT_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(a,160)) s0 = n`) (concl th)
    then MAP_EVERY (fun k ->
      ASSUME_TAC(CONV_RULE(DEPTH_CONV NUM_MULT_CONV THENC
                           REWRITE_CONV[WORD_ADD_0])
        (MATCH_MP D5_WIN
           (CONJ th (ARITH_RULE(mk_binop `(<):num->num->bool`
                       (mk_small_numeral k) `10`)))))) (0--9)
    else failwith "DECOMPRESS_D5_INPUT_TAC") THEN
  ABBREV_TAC `w:1280 word = word n`;;

(*** The 5-bit field k of w as part of the number for the input ***)

let D5_FIELD_STMT =
  `!n k. k + 5 <= 1280
         ==> val(word_subword (word n:1280 word) (k,5):5 word) =
             (n DIV 2 EXP k) MOD 2 EXP 5`;;

let D5_FIELD = assume_spec D5_FIELD_STMT;;

(* ------------------------------------------------------------------------- *)
(* The check for overlap has one branch for each order of the arrays: with   *)
(* the input a (160 bytes) and the output r (512 bytes), the scalar loop is  *)
(* taken unless a + 160 <= r or r + 512 <= a. In either case the vector code *)
(* is entered at join1, after 3 or 6 steps (after the 6 steps of the         *)
(* prologue) respectively.                                                   *)
(* ------------------------------------------------------------------------- *)

let DECOMPRESS_D5_RESOLVE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_FLAG; VAL_WORD_SUB_EQ_0]) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read PC s = if p then x else y`) c then
      let p = rand(rator(rator(rand c))) in
      let decide q = SUBGOAL_THEN q (fun th' ->
        ASSUME_TAC(REWRITE_RULE[th'] th)) THENL [ASM_ARITH_TAC; ALL_TAC] in
      decide p ORELSE decide (mk_neg p)
    else failwith "DECOMPRESS_D5_RESOLVE_TAC");;

let DECOMPRESS_D5_CHECK_TAC (body:int->tactic) =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O3_EXEC (1--6) THEN
  MP_TAC(SPECL [`r:int64`; `a:int64`; `512`; `160`]
                NONOVERLAPPING_ALIAS_CHECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O3_EXEC (7--9) THEN
  ASM_CASES_TAC `val(word_add a (word 160):int64) <= val(r:int64)` THENL
   [DECOMPRESS_D5_RESOLVE_TAC THEN body 9;
    DECOMPRESS_D5_RESOLVE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O3_EXEC
     (10--12) THEN
    DECOMPRESS_D5_RESOLVE_TAC THEN body 12];;

(*** The vector code from join1 to the return, 568 steps, with the page of
 *** the constants computed by ADRP in the steps at the labels adrp3 to
 *** adrp32 ***)

let DECOMPRESS_D5_ADRP_STEPS =
  let j = layout "mlkem_poly_decompress_d5_join1" in
  map (fun i ->
    (layout("mlkem_poly_decompress_d5_adrp" ^ string_of_int i) - j) / 4 + 1)
   (3--32);;

let DECOMPRESS_D5_BODY_TAC (simp:tactic) off =
  let n = (layout "mlkem_poly_decompress_d5_ret" -
           layout "mlkem_poly_decompress_d5_join1") / 4 + 1 in
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O3_EXEC [k + off] THEN
    (if mem k DECOMPRESS_D5_ADRP_STEPS then MLKEM_NATIVE_ADRP_TAC
     else ALL_TAC) THEN
    simp) (1--n);;

(*** The restored D registers, as zero extensions of the 64 bits saved, in
 *** the form of the simulation and in normal form ***)

let DECOMPRESS_D5_DREG_STMT =
  `(!x:int64. word_zx(word_zx x:int128):int64 = x) /\
   (!x:int64. word_zx(word_join (word 0:64 word) x:int128):int64 = x)`;;

let DECOMPRESS_D5_DREG = assume_spec DECOMPRESS_D5_DREG_STMT;;

(* ------------------------------------------------------------------------- *)
(* The stored coefficients. With the registers in the normal form of         *)
(* bitnorm.ml after each step, each 16-bit part of what is stored is         *)
(* (x * 3329 + 16) >> 5 for a 32-bit x made by bit operations from the 1280  *)
(* bits w of the input, a maximal subterm that is the zero extension of a    *)
(* field of 5 bits k of w: the field is found from the bits of x and checked *)
(* by bit-blasting, and what is left is a function of the field, checked     *)
(* for all 32 values (as for D11_LANE_FIELD_RULE in poly_decompress_d11.ml). *)
(* ------------------------------------------------------------------------- *)

let d5_pure w t =
  (match type_of t with Tyapp("word",_) -> true | _ -> false) &&
  free_in w t &&
  not(can (find_term (fun x -> match x with
        Const(("val"|"word_mul"|"word_add"),_) -> true | _ -> false)) t);;

let rec d5_max_pure w t acc =
  if d5_pure w t then t::acc else
  match t with
    Comb(f,x) -> d5_max_pure w f (d5_max_pure w x acc)
  | Abs(_,b) -> d5_max_pure w b acc
  | _ -> acc;;

let d5_lane_cache : (term * thm) list ref = ref [];;

let D5_LANE_FIELD_RULE th =
  let w = `w:1280 word` and fv = `f:5 word` in
  let l = rand(concl th) in
  let q = match setify(d5_max_pure w l []) with
      [q] -> q | _ -> failwith "D5_LANE_FIELD_RULE: no unique input" in
  let zx = inst [`:5`,`:A`; hd(snd(dest_type(type_of q))),`:B`]
                `word_zx:A word->B word` in
  let k = match filter (fun b -> b >= 0)
                       (Array.to_list(bits_eval (ref [w]) q)) with
            b::_ -> b / 5
          | [] -> failwith "D5_LANE_FIELD_RULE: no field" in
  let f = mk_comb(mk_comb(`word_subword:1280 word->num#num->5 word`,w),
                  mk_pair(mk_small_numeral(5 * k),`5`)) in
  let qth = BITBLAST_RULE(mk_eq(q,mk_comb(zx,f))) in
  let lgen = subst [mk_comb(zx,fv),q] l in
  let lem =
    try assoc lgen !d5_lane_cache with Failure _ ->
      let vv = `v:num` in
      let stmt_v = mk_forall(vv,mk_imp(`v < 32`,
        mk_eq(subst [mk_comb(`word:num->5 word`,vv),fv] lgen,
              `word((3329 * v + 16) DIV 32):int16`))) in
      let lem = prove(mk_eq(lgen,
                  `word((3329 * val(f:5 word) + 16) DIV 32):int16`),
        SUBGOAL_THEN stmt_v (MP_TAC o SPEC `val(f:5 word)`) THENL
         [CONV_TAC EXPAND_CASES_CONV THEN
          CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV));
          REWRITE_TAC[WORD_VAL] THEN DISCH_THEN MATCH_MP_TAC THEN
          MP_TAC(ISPEC `f:5 word` VAL_BOUND) THEN
          CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC]) in
      d5_lane_cache := (lgen,lem)::!d5_lane_cache; lem in
  let e1 = PURE_REWRITE_CONV [qth] l in
  CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
                                   GSYM ADD_ASSOC] THENC NUM_REDUCE_CONV))
   (TRANS th (TRANS e1 (INST [f,fv] lem)));;

(*** After each step: the usual simplification of the new vector register
 *** and every register and memory fact in normal form ***)

let DECOMPRESS_D5_SIMD_TAC =
  SIMD_SIMPLIFY_TAC[] THEN BITS_NORM_TAC;;

(*** The stored coefficients, from the 32 stores of 16 bytes ***)

let DECOMPRESS_D5_STORES_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (fun th -> can (term_match []
                     `read (memory :> bytes128 a) s = x`) (concl th) &&
                     free_in `r:int64` (lhand(concl th))))) THEN
  REPEAT(DISCH_THEN(fun th ->
    MAP_EVERY (ASSUME_TAC o D5_LANE_FIELD_RULE o
               CONV_RULE(RAND_CONV BITS_NORM_CONV)) (CONJUNCTS th)));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 5 in common/fips203.ml, the    *)
(* result for a 5-bit field y is the integer closest to 3329 * y / 32,       *)
(* rounding up on ties, i.e. (3329 * y + 16) DIV 32.                         *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,512); (a,160); (word_sub stackpointer (word 784),784)] /\
        ALLPAIRS nonoverlapping
         [(r,512); (word_sub stackpointer (word 784),784)]
         [(word pc,libmlkem_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_poly_decompress_d5) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,160)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (5 * i)) MOD 2 EXP 5 +
                                16) DIV 32))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512);
                         memory :> bytes(word_sub stackpointer
                                                  (word 784),784)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. This is stated directly rather     *)
(* than by mk_safety_spec, with the events depending on the stack frame, as  *)
(* for poly_compress_d4. The safety theorem has the constants of the         *)
(* function among the regions read (unlike at gcc 12 -O2, 30 vectors).       *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e r a pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,512; a,160; word_sub stackpointer (word 784),784] /\
       ALLPAIRS nonoverlapping
        [r,512; word_sub stackpointer (word 784),784]
        [word pc,libmlkem_size]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_clang17_O3_mc /\
                 read PC s = word (pc + mlkem_poly_decompress_d5) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [r; a] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a r pc
                           (word_sub stackpointer (word 784)) returnaddress /\
                    memaccess_inbounds e2
                     [a,160; r,512; word_sub stackpointer (word 784),784;
                      word(pc + mlkem_poly_decompress_d5_consts),
                      mlkem_poly_decompress_d5_consts_size]
                     [r,512; word_sub stackpointer (word 784),784]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,512);
                        memory :> bytes(word_sub stackpointer (word 784),
                                        784)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
