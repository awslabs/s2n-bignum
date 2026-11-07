(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a polynomial to a 32-byte message, one bit per coefficient. *)
(* This is the code for mlkem_poly_tomsg from mlkem-native's portable C      *)
(* implementation compiled by clang 17 with -O3 (see mlkem_native/README.md).*)
(* It is verified in the whole image (see libmlkem.ml).                      *)
(*                                                                           *)
(* The compiler has vectorized the loop completely, with 32-bit lanes,       *)
(* after a check that the input and the output do not overlap, with one      *)
(* branch for each of the two orders of the arrays; if they overlap, the     *)
(* code falls back to a scalar loop. Since the specification requires them   *)
(* not to overlap, only the vector code runs. It saves D8 to D15 and X29 and *)
(* spills vectors to the stack, all in a frame of 272 bytes, which the       *)
(* specifications therefore have (gcc12_O2 has none). It reads six vectors   *)
(* of byte indices for TBL from the read-only data; they are the same as     *)
(* those of mlkem_poly_compress_d4.                                          *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/overlap.ml";;
needs "arm/proofs/mlkem_native/interleave.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_tomsg:
        +0x0: sub     sp, sp, #0x110
        +0x4: stp     d15, d14, [sp, #192]
        +0x8: stp     d13, d12, [sp, #208]
        +0xc: stp     d11, d10, [sp, #224]
       +0x10: stp     d9, d8, [sp, #240]
       +0x14: str     x29, [sp, #256]
       +0x18: add     x8, x1, #0x200
       +0x1c: cmp     x8, x0
       +0x20: b.ls    join1
       +0x24: add     x8, x0, #0x20
       +0x28: cmp     x8, x1
       +0x2c: b.ls    join1
       +0x30: mov     w9, #0xafb8
       +0x34: mov     x8, xzr
       +0x38: movk    w9, #0x13, lsl #16
       +0x3c: add     x10, x1, #0x8
       +0x40: mov     w11, #0x40000000
       +0x44: strb    wzr, [x0, x8]
       +0x48: ldursh  w12, [x10, #-8]
       +0x4c: madd    w12, w12, w9, w11
       +0x50: lsr     w13, w12, #31
       +0x54: strb    w13, [x0, x8]
       +0x58: ldursh  w13, [x10, #-6]
       +0x5c: madd    w13, w13, w9, w11
       +0x60: lsr     w13, w13, #30
       +0x64: and     w13, w13, #0x2
       +0x68: bfxil   w13, w12, #31, #1
       +0x6c: strb    w13, [x0, x8]
       +0x70: ldursh  w12, [x10, #-4]
       +0x74: madd    w12, w12, w9, w11
       +0x78: lsr     w12, w12, #31
       +0x7c: orr     w12, w13, w12, lsl #2
       +0x80: strb    w12, [x0, x8]
       +0x84: ldursh  w13, [x10, #-2]
       +0x88: madd    w13, w13, w9, w11
       +0x8c: lsr     w13, w13, #31
       +0x90: orr     w12, w12, w13, lsl #3
       +0x94: strb    w12, [x0, x8]
       +0x98: ldrsh   w13, [x10]
       +0x9c: madd    w13, w13, w9, w11
       +0xa0: lsr     w13, w13, #31
       +0xa4: orr     w12, w12, w13, lsl #4
       +0xa8: strb    w12, [x0, x8]
       +0xac: ldrsh   w13, [x10, #2]
       +0xb0: madd    w13, w13, w9, w11
       +0xb4: lsr     w13, w13, #31
       +0xb8: orr     w12, w12, w13, lsl #5
       +0xbc: strb    w12, [x0, x8]
       +0xc0: ldrsh   w13, [x10, #4]
       +0xc4: madd    w13, w13, w9, w11
       +0xc8: lsr     w13, w13, #31
       +0xcc: orr     w12, w12, w13, lsl #6
       +0xd0: strb    w12, [x0, x8]
       +0xd4: ldrsh   w13, [x10, #6]
       +0xd8: add     x10, x10, #0x10
       +0xdc: madd    w13, w13, w9, w11
       +0xe0: lsr     w13, w13, #31
       +0xe4: orr     w12, w12, w13, lsl #7
       +0xe8: strb    w12, [x0, x8]
       +0xec: add     x8, x8, #0x1
       +0xf0: cmp     x8, #0x20
       +0xf4: b.ne    loop1
       +0xf8: b       join2
       +0xfc: movi    v0.2d, #0x0
      +0x100: mov     w8, #0xafb8
      +0x104: movk    w8, #0x13, lsl #16
      +0x108: adrp    x9, <page>
      +0x10c: movi    v4.4s, #0x40, lsl #24
      +0x110: movi    v1.4s, #0x40, lsl #24
      +0x114: str     q0, [x0]
      +0x118: dup     v22.4s, w8
      +0x11c: ldp     q25, q26, [x1, #32]
      +0x120: movi    v2.4s, #0x40, lsl #24
      +0x124: adrp    x8, <page>
      +0x128: movi    v6.4s, #0x40, lsl #24
      +0x12c: ldp     q23, q24, [x1]
      +0x130: zip1    v5.4h, v25.4h, v26.4h
      +0x134: ext     v20.8b, v25.8b, v5.8b, #4
      +0x138: ldp     q29, q30, [x1, #128]
      +0x13c: zip1    v17.4h, v23.4h, v24.4h
      +0x140: mov     v17.s[1], v20.s[1]
      +0x144: ldp     q7, q8, [x1, #160]
      +0x148: trn2    v0.4h, v29.4h, v30.4h
      +0x14c: zip1    v31.4h, v29.4h, v30.4h
      +0x150: sxtl    v17.4s, v17.4h
      +0x154: mla     v4.4s, v17.4s, v22.4s
      +0x158: ldp     q27, q28, [x1, #192]
      +0x15c: zip1    v3.4h, v7.4h, v8.4h
      +0x160: ushr    v4.4s, v4.4s, #31
      +0x164: mov     v0.s[1], v3.s[1]
      +0x168: ext     v3.8b, v7.8b, v3.8b, #4
      +0x16c: ldp     q11, q12, [x1, #224]
      +0x170: trn2    v13.4h, v27.4h, v28.4h
      +0x174: zip1    v20.4h, v27.4h, v28.4h
      +0x178: mov     v31.s[1], v3.s[1]
      +0x17c: sxtl    v3.4s, v0.4h
      +0x180: ldp     q9, q10, [x1, #96]
      +0x184: zip1    v14.4h, v11.4h, v12.4h
      +0x188: sxtl    v17.4s, v31.4h
      +0x18c: movi    v31.4s, #0x40, lsl #24
      +0x190: mla     v1.4s, v17.4s, v22.4s
      +0x194: mov     v13.s[1], v14.s[1]
      +0x198: ldp     q18, q19, [x1, #64]
      +0x19c: zip1    v16.4h, v9.4h, v10.4h
      +0x1a0: ext     v14.8b, v11.8b, v14.8b, #4
      +0x1a4: ushr    v0.4s, v1.4s, #31
      +0x1a8: sxtl    v17.4s, v13.4h
      +0x1ac: zip2    v13.4h, v25.4h, v26.4h
      +0x1b0: movi    v1.16b, #0x2
      +0x1b4: ext     v15.8b, v9.8b, v16.8b, #4
      +0x1b8: zip1    v21.4h, v18.4h, v19.4h
      +0x1bc: mov     v20.s[1], v14.s[1]
      +0x1c0: trn2    v14.4h, v23.4h, v24.4h
      +0x1c4: mov     v21.s[1], v15.s[1]
      +0x1c8: trn2    v15.4h, v18.4h, v19.4h
      +0x1cc: sxtl    v20.4s, v20.4h
      +0x1d0: mov     v14.s[1], v5.s[1]
      +0x1d4: mla     v2.4s, v20.4s, v22.4s
      +0x1d8: sxtl    v21.4s, v21.4h
      +0x1dc: mov     v15.s[1], v16.s[1]
      +0x1e0: mla     v6.4s, v21.4s, v22.4s
      +0x1e4: ushr    v2.4s, v2.4s, #31
      +0x1e8: movi    v16.4s, #0x40, lsl #24
      +0x1ec: movi    v20.4s, #0x40, lsl #24
      +0x1f0: movi    v21.4s, #0x40, lsl #24
      +0x1f4: ushr    v5.4s, v6.4s, #31
      +0x1f8: uzp1    v0.8h, v0.8h, v2.8h
      +0x1fc: sxtl    v2.4s, v14.4h
      +0x200: sxtl    v6.4s, v15.4h
      +0x204: mla     v16.4s, v3.4s, v22.4s
      +0x208: mla     v20.4s, v17.4s, v22.4s
      +0x20c: mla     v21.4s, v2.4s, v22.4s
      +0x210: mla     v31.4s, v6.4s, v22.4s
      +0x214: uzp1    v2.8h, v4.8h, v5.8h
      +0x218: ushr    v3.4s, v20.4s, #30
      +0x21c: ushr    v4.4s, v16.4s, #30
      +0x220: ushr    v6.4s, v21.4s, #30
      +0x224: ushr    v5.4s, v31.4s, #30
      +0x228: zip2    v16.4h, v29.4h, v30.4h
      +0x22c: uzp1    v3.8h, v4.8h, v3.8h
      +0x230: zip2    v17.4h, v27.4h, v28.4h
      +0x234: uzp1    v4.8h, v6.8h, v5.8h
      +0x238: uzp1    v0.16b, v2.16b, v0.16b
      +0x23c: mov     v5.16b, v7.16b
      +0x240: mov     v5.h[3], v8.h[2]
      +0x244: uzp1    v2.16b, v4.16b, v3.16b
      +0x248: mov     v3.16b, v11.16b
      +0x24c: mov     v3.h[3], v12.h[2]
      +0x250: mov     v4.16b, v25.16b
      +0x254: mov     v4.h[3], v26.h[2]
      +0x258: zip2    v20.4h, v23.4h, v24.4h
      +0x25c: mov     v16.s[1], v5.s[1]
      +0x260: zip2    v21.4h, v18.4h, v19.4h
      +0x264: mov     v17.s[1], v3.s[1]
      +0x268: mov     v6.16b, v9.16b
      +0x26c: mov     v6.h[3], v10.h[2]
      +0x270: mov     v20.s[1], v4.s[1]
      +0x274: sxtl    v3.4s, v16.4h
      +0x278: sxtl    v4.4s, v17.4h
      +0x27c: movi    v16.4s, #0x40, lsl #24
      +0x280: movi    v17.4s, #0x40, lsl #24
      +0x284: mov     v21.s[1], v6.s[1]
      +0x288: sxtl    v5.4s, v20.4h
      +0x28c: movi    v20.4s, #0x40, lsl #24
      +0x290: mla     v16.4s, v3.4s, v22.4s
      +0x294: mla     v17.4s, v4.4s, v22.4s
      +0x298: sxtl    v6.4s, v21.4h
      +0x29c: movi    v21.4s, #0x40, lsl #24
      +0x2a0: mla     v20.4s, v5.4s, v22.4s
      +0x2a4: ushr    v3.4s, v17.4s, #29
      +0x2a8: ushr    v4.4s, v16.4s, #29
      +0x2ac: uzp2    v5.4h, v27.4h, v28.4h
      +0x2b0: mla     v21.4s, v6.4s, v22.4s
      +0x2b4: uzp2    v16.4h, v23.4h, v24.4h
      +0x2b8: uzp1    v3.8h, v4.8h, v3.8h
      +0x2bc: uzp2    v4.4h, v29.4h, v30.4h
      +0x2c0: ushr    v17.4s, v20.4s, #29
      +0x2c4: uzp2    v20.4h, v18.4h, v19.4h
      +0x2c8: ushr    v6.4s, v21.4s, #29
      +0x2cc: zip2    v21.4h, v7.4h, v8.4h
      +0x2d0: zip2    v31.4h, v11.4h, v12.4h
      +0x2d4: uzp2    v5.4h, v5.4h, v27.4h
      +0x2d8: uzp2    v4.4h, v4.4h, v29.4h
      +0x2dc: uzp2    v16.4h, v16.4h, v23.4h
      +0x2e0: zip2    v14.4h, v9.4h, v10.4h
      +0x2e4: uzp2    v20.4h, v20.4h, v18.4h
      +0x2e8: and     v2.16b, v2.16b, v1.16b
      +0x2ec: mov     v5.s[1], v31.s[1]
      +0x2f0: mov     v4.s[1], v21.s[1]
      +0x2f4: mov     v16.s[1], v13.s[1]
      +0x2f8: mov     v20.s[1], v14.s[1]
      +0x2fc: movi    v21.4s, #0x40, lsl #24
      +0x300: movi    v31.4s, #0x40, lsl #24
      +0x304: movi    v13.4s, #0x40, lsl #24
      +0x308: movi    v14.4s, #0x40, lsl #24
      +0x30c: sxtl    v4.4s, v4.4h
      +0x310: sxtl    v5.4s, v5.4h
      +0x314: sxtl    v16.4s, v16.4h
      +0x318: sxtl    v20.4s, v20.4h
      +0x31c: mla     v21.4s, v4.4s, v22.4s
      +0x320: mla     v31.4s, v5.4s, v22.4s
      +0x324: mla     v13.4s, v16.4s, v22.4s
      +0x328: mla     v14.4s, v20.4s, v22.4s
      +0x32c: uzp1    v4.8h, v17.8h, v6.8h
      +0x330: ushr    v5.4s, v31.4s, #28
      +0x334: ushr    v6.4s, v21.4s, #28
      +0x338: ushr    v17.4s, v13.4s, #28
      +0x33c: ushr    v16.4s, v14.4s, #28
      +0x340: ldr     q13, [x9, #400]
                    // mlkem_poly_compress_d4_const4
      +0x344: uzp1    v5.8h, v6.8h, v5.8h
      +0x348: adrp    x9, <page>
      +0x34c: uzp1    v6.8h, v17.8h, v16.8h
      +0x350: uzp1    v3.16b, v4.16b, v3.16b
      +0x354: movi    v16.16b, #0x4
      +0x358: movi    v1.16b, #0x8
      +0x35c: uzp1    v4.16b, v6.16b, v5.16b
      +0x360: ldr     q6, [x8, #352]
                    // mlkem_poly_compress_d4_const1
      +0x364: zip2    v17.8h, v23.8h, v24.8h
      +0x368: adrp    x8, <page>
      +0x36c: and     v3.16b, v3.16b, v16.16b
      +0x370: mov     v20.16b, v6.16b
      +0x374: str     q6, [sp, #176]
      +0x378: orr     v2.16b, v2.16b, v3.16b
      +0x37c: tbl     v3.16b, {v7.16b-v8.16b}, v6.16b
      +0x380: tbl     v5.16b, {v11.16b-v12.16b}, v6.16b
      +0x384: zip2    v6.8h, v27.8h, v28.8h
      +0x388: tbl     v16.16b, {v25.16b-v26.16b}, v20.16b
      +0x38c: orr     v0.16b, v2.16b, v0.16b
      +0x390: and     v2.16b, v4.16b, v1.16b
      +0x394: zip2    v4.8h, v29.8h, v30.8h
      +0x398: mov     v6.s[1], v5.s[1]
      +0x39c: mov     v17.s[1], v16.s[1]
      +0x3a0: orr     v1.16b, v0.16b, v2.16b
      +0x3a4: ldr     q0, [x8, #368]
                    // mlkem_poly_compress_d4_const2
      +0x3a8: mov     v4.s[1], v3.s[1]
      +0x3ac: adrp    x8, <page>
      +0x3b0: tbl     v2.16b, {v9.16b-v10.16b}, v20.16b
      +0x3b4: zip2    v3.8h, v18.8h, v19.8h
      +0x3b8: str     q0, [sp, #128]
      +0x3bc: sxtl    v5.4s, v6.4h
      +0x3c0: sxtl    v6.4s, v17.4h
      +0x3c4: movi    v17.4s, #0x40, lsl #24
      +0x3c8: movi    v20.4s, #0x40, lsl #24
      +0x3cc: sxtl    v4.4s, v4.4h
      +0x3d0: mov     v3.s[1], v2.s[1]
      +0x3d4: movi    v2.4s, #0x40, lsl #24
      +0x3d8: mla     v17.4s, v4.4s, v22.4s
      +0x3dc: mla     v20.4s, v5.4s, v22.4s
      +0x3e0: movi    v4.4s, #0x40, lsl #24
      +0x3e4: mla     v2.4s, v6.4s, v22.4s
      +0x3e8: ushr    v6.4s, v17.4s, #27
      +0x3ec: ushr    v5.4s, v20.4s, #27
      +0x3f0: zip2    v17.8h, v7.8h, v8.8h
      +0x3f4: tbl     v20.16b, {v29.16b-v30.16b}, v0.16b
      +0x3f8: sxtl    v3.4s, v3.4h
      +0x3fc: zip2    v21.8h, v11.8h, v12.8h
      +0x400: tbl     v31.16b, {v27.16b-v28.16b}, v0.16b
      +0x404: mla     v4.4s, v3.4s, v22.4s
      +0x408: uzp1    v3.8h, v6.8h, v5.8h
      +0x40c: mov     v20.s[1], v17.s[1]
      +0x410: zip2    v5.8h, v25.8h, v26.8h
      +0x414: tbl     v6.16b, {v23.16b-v24.16b}, v0.16b
      +0x418: movi    v14.4s, #0x40, lsl #24
      +0x41c: mov     v31.s[1], v21.s[1]
      +0x420: zip2    v17.8h, v9.8h, v10.8h
      +0x424: tbl     v21.16b, {v18.16b-v19.16b}, v0.16b
      +0x428: ldr     q0, [x8, #384]
                    // mlkem_poly_compress_d4_const3
      +0x42c: mov     v6.s[1], v5.s[1]
      +0x430: adrp    x8, <page>
      +0x434: sxtl    v5.4s, v20.4h
      +0x438: sxtl    v20.4s, v31.4h
      +0x43c: str     q0, [sp, #160]
      +0x440: mla     v14.4s, v5.4s, v22.4s
      +0x444: movi    v5.4s, #0x40, lsl #24
      +0x448: mov     v21.s[1], v17.s[1]
      +0x44c: movi    v17.4s, #0x40, lsl #24
      +0x450: sxtl    v6.4s, v6.4h
      +0x454: mla     v5.4s, v20.4s, v22.4s
      +0x458: movi    v20.4s, #0x40, lsl #24
      +0x45c: sxtl    v21.4s, v21.4h
      +0x460: ushr    v4.4s, v4.4s, #27
      +0x464: mla     v17.4s, v21.4s, v22.4s
      +0x468: ushr    v2.4s, v2.4s, #27
      +0x46c: mla     v20.4s, v6.4s, v22.4s
      +0x470: uzp1    v2.8h, v2.8h, v4.8h
      +0x474: ushr    v5.4s, v5.4s, #26
      +0x478: ushr    v4.4s, v17.4s, #26
      +0x47c: ushr    v17.4s, v14.4s, #26
      +0x480: ushr    v20.4s, v20.4s, #26
      +0x484: uzp1    v5.8h, v17.8h, v5.8h
      +0x488: ldr     q17, [x8, #416]
                    // mlkem_poly_compress_d4_const5
      +0x48c: uzp1    v4.8h, v20.8h, v4.8h
      +0x490: tbl     v20.16b, {v7.16b-v8.16b}, v0.16b
      +0x494: tbl     v21.16b, {v29.16b-v30.16b}, v13.16b
      +0x498: str     q17, [sp, #144]
      +0x49c: tbl     v31.16b, {v11.16b-v12.16b}, v0.16b
      +0x4a0: tbl     v14.16b, {v27.16b-v28.16b}, v13.16b
      +0x4a4: uzp1    v2.16b, v2.16b, v3.16b
      +0x4a8: uzp1    v3.16b, v4.16b, v5.16b
      +0x4ac: mov     v21.s[1], v20.s[1]
      +0x4b0: tbl     v4.16b, {v25.16b-v26.16b}, v0.16b
      +0x4b4: tbl     v5.16b, {v23.16b-v24.16b}, v13.16b
      +0x4b8: movi    v15.4s, #0x40, lsl #24
      +0x4bc: mov     v14.s[1], v31.s[1]
      +0x4c0: tbl     v20.16b, {v9.16b-v10.16b}, v0.16b
      +0x4c4: tbl     v31.16b, {v18.16b-v19.16b}, v13.16b
      +0x4c8: mov     v5.s[1], v4.s[1]
      +0x4cc: sxtl    v4.4s, v21.4h
      +0x4d0: movi    v0.4s, #0x40, lsl #24
      +0x4d4: mla     v15.4s, v4.4s, v22.4s
      +0x4d8: movi    v4.4s, #0x40, lsl #24
      +0x4dc: mov     v31.s[1], v20.s[1]
      +0x4e0: sxtl    v20.4s, v14.4h
      +0x4e4: sxtl    v5.4s, v5.4h
      +0x4e8: mla     v4.4s, v20.4s, v22.4s
      +0x4ec: ldr     q20, [x9, #432]
                    // mlkem_poly_compress_d4_const6
      +0x4f0: mla     v0.4s, v5.4s, v22.4s
      +0x4f4: sxtl    v5.4s, v31.4h
      +0x4f8: movi    v31.4s, #0x40, lsl #24
      +0x4fc: str     q20, [sp, #112]
      +0x500: tbl     v25.16b, {v25.16b-v26.16b}, v17.16b
      +0x504: tbl     v23.16b, {v23.16b-v24.16b}, v20.16b
      +0x508: tbl     v27.16b, {v27.16b-v28.16b}, v20.16b
      +0x50c: mla     v31.4s, v5.4s, v22.4s
      +0x510: tbl     v5.16b, {v7.16b-v8.16b}, v17.16b
      +0x514: tbl     v7.16b, {v29.16b-v30.16b}, v20.16b
      +0x518: tbl     v29.16b, {v11.16b-v12.16b}, v17.16b
      +0x51c: tbl     v24.16b, {v9.16b-v10.16b}, v17.16b
      +0x520: tbl     v18.16b, {v18.16b-v19.16b}, v20.16b
      +0x524: mov     v23.s[1], v25.s[1]
      +0x528: mov     v7.s[1], v5.s[1]
      +0x52c: mov     v27.s[1], v29.s[1]
      +0x530: mov     v18.s[1], v24.s[1]
      +0x534: sxtl    v19.4s, v23.4h
      +0x538: movi    v23.4s, #0x40, lsl #24
      +0x53c: movi    v24.4s, #0x40, lsl #24
      +0x540: movi    v25.4s, #0x40, lsl #24
      +0x544: movi    v26.4s, #0x40, lsl #24
      +0x548: sxtl    v5.4s, v7.4h
      +0x54c: sxtl    v7.4s, v27.4h
      +0x550: sxtl    v18.4s, v18.4h
      +0x554: mla     v23.4s, v5.4s, v22.4s
      +0x558: mla     v24.4s, v7.4s, v22.4s
      +0x55c: mla     v25.4s, v19.4s, v22.4s
      +0x560: mla     v26.4s, v18.4s, v22.4s
      +0x564: ushr    v4.4s, v4.4s, #25
      +0x568: ushr    v21.4s, v15.4s, #25
      +0x56c: ushr    v30.4s, v31.4s, #25
      +0x570: ushr    v0.4s, v0.4s, #25
      +0x574: ushr    v5.4s, v24.4s, #24
      +0x578: uzp1    v4.8h, v21.8h, v4.8h
      +0x57c: ushr    v7.4s, v23.4s, #24
      +0x580: uzp1    v0.8h, v0.8h, v30.8h
      +0x584: ushr    v18.4s, v26.4s, #24
      +0x588: ushr    v19.4s, v25.4s, #24
      +0x58c: movi    v16.16b, #0x10
      +0x590: movi    v6.16b, #0x20
      +0x594: uzp1    v5.8h, v7.8h, v5.8h
      +0x598: uzp1    v7.8h, v19.8h, v18.8h
      +0x59c: uzp1    v0.16b, v0.16b, v4.16b
      +0x5a0: movi    v4.16b, #0x40
      +0x5a4: and     v2.16b, v2.16b, v16.16b
      +0x5a8: and     v3.16b, v3.16b, v6.16b
      +0x5ac: orr     v2.16b, v2.16b, v3.16b
      +0x5b0: uzp1    v3.16b, v7.16b, v5.16b
      +0x5b4: movi    v5.16b, #0x80
      +0x5b8: and     v0.16b, v0.16b, v4.16b
      +0x5bc: orr     v0.16b, v2.16b, v0.16b
      +0x5c0: orr     v0.16b, v1.16b, v0.16b
      +0x5c4: and     v2.16b, v3.16b, v5.16b
      +0x5c8: orr     v1.16b, v0.16b, v2.16b
      +0x5cc: movi    v0.2d, #0x0
      +0x5d0: stp     q1, q0, [x0]
      +0x5d4: ldp     q26, q27, [x1, #416]
      +0x5d8: ldp     q28, q29, [x1, #480]
      +0x5dc: zip1    v16.4h, v26.4h, v27.4h
      +0x5e0: ext     v5.8b, v26.8b, v16.8b, #4
      +0x5e4: ldp     q24, q25, [x1, #352]
      +0x5e8: zip1    v6.4h, v28.4h, v29.4h
      +0x5ec: ext     v18.8b, v28.8b, v6.8b, #4
      +0x5f0: ldp     q20, q21, [x1, #288]
      +0x5f4: zip1    v4.4h, v24.4h, v25.4h
      +0x5f8: ext     v2.8b, v24.8b, v4.8b, #4
      +0x5fc: ldp     q8, q9, [x1, #448]
      +0x600: zip1    v3.4h, v20.4h, v21.4h
      +0x604: ext     v10.8b, v20.8b, v3.8b, #4
      +0x608: ldp     q14, q15, [x1, #384]
      +0x60c: zip1    v19.4h, v8.4h, v9.4h
      +0x610: tbl     v23.16b, {v8.16b-v9.16b}, v13.16b
      +0x614: mov     v19.s[1], v18.s[1]
      +0x618: ldp     q30, q31, [x1, #320]
      +0x61c: zip1    v7.4h, v14.4h, v15.4h
      +0x620: zip2    v17.8h, v14.8h, v15.8h
      +0x624: sxtl    v18.4s, v19.4h
      +0x628: mov     v7.s[1], v5.s[1]
      +0x62c: ldp     q11, q12, [x1, #256]
      +0x630: zip1    v0.4h, v30.4h, v31.4h
      +0x634: movi    v5.4s, #0x40, lsl #24
      +0x638: sxtl    v7.4s, v7.4h
      +0x63c: mov     v0.s[1], v2.s[1]
      +0x640: zip1    v1.4h, v11.4h, v12.4h
      +0x644: movi    v2.4s, #0x40, lsl #24
      +0x648: mla     v5.4s, v18.4s, v22.4s
      +0x64c: movi    v18.4s, #0x40, lsl #24
      +0x650: mov     v1.s[1], v10.s[1]
      +0x654: mla     v2.4s, v7.4s, v22.4s
      +0x658: movi    v7.4s, #0x40, lsl #24
      +0x65c: sxtl    v0.4s, v0.4h
      +0x660: sxtl    v1.4s, v1.4h
      +0x664: mla     v18.4s, v0.4s, v22.4s
      +0x668: mla     v7.4s, v1.4s, v22.4s
      +0x66c: ushr    v0.4s, v5.4s, #31
      +0x670: ushr    v1.4s, v2.4s, #31
      +0x674: trn2    v2.4h, v14.4h, v15.4h
      +0x678: movi    v10.4s, #0x40, lsl #24
      +0x67c: uzp1    v5.8h, v1.8h, v0.8h
      +0x680: ushr    v0.4s, v18.4s, #31
      +0x684: ushr    v1.4s, v7.4s, #31
      +0x688: zip2    v7.4h, v14.4h, v15.4h
      +0x68c: mov     v2.s[1], v16.s[1]
      +0x690: zip2    v16.4h, v8.4h, v9.4h
      +0x694: uzp1    v0.8h, v1.8h, v0.8h
      +0x698: trn2    v1.4h, v11.4h, v12.4h
      +0x69c: movi    v18.4s, #0x40, lsl #24
      +0x6a0: sxtl    v2.4s, v2.4h
      +0x6a4: stp     q0, q5, [sp, #80]
      +0x6a8: trn2    v0.4h, v8.4h, v9.4h
      +0x6ac: trn2    v5.4h, v30.4h, v31.4h
      +0x6b0: mov     v1.s[1], v3.s[1]
      +0x6b4: movi    v3.4s, #0x40, lsl #24
      +0x6b8: mov     v0.s[1], v6.s[1]
      +0x6bc: movi    v6.4s, #0x40, lsl #24
      +0x6c0: mov     v5.s[1], v4.s[1]
      +0x6c4: sxtl    v1.4s, v1.4h
      +0x6c8: sxtl    v0.4s, v0.4h
      +0x6cc: mla     v6.4s, v2.4s, v22.4s
      +0x6d0: movi    v2.4s, #0x40, lsl #24
      +0x6d4: mla     v3.4s, v1.4s, v22.4s
      +0x6d8: mov     v1.16b, v28.16b
      +0x6dc: sxtl    v4.4s, v5.4h
      +0x6e0: mla     v2.4s, v0.4s, v22.4s
      +0x6e4: mov     v0.16b, v26.16b
      +0x6e8: mov     v0.h[3], v27.h[2]
      +0x6ec: movi    v5.4s, #0x40, lsl #24
      +0x6f0: mov     v1.h[3], v29.h[2]
      +0x6f4: ushr    v2.4s, v2.4s, #30
      +0x6f8: mov     v7.s[1], v0.s[1]
      +0x6fc: ushr    v6.4s, v6.4s, #30
      +0x700: mov     v0.16b, v20.16b
      +0x704: mla     v5.4s, v4.4s, v22.4s
      +0x708: mov     v0.h[3], v21.h[2]
      +0x70c: zip2    v4.4h, v11.4h, v12.4h
      +0x710: mov     v16.s[1], v1.s[1]
      +0x714: ushr    v3.4s, v3.4s, #30
      +0x718: mov     v1.16b, v24.16b
      +0x71c: uzp1    v2.8h, v6.8h, v2.8h
      +0x720: mov     v1.h[3], v25.h[2]
      +0x724: zip2    v6.4h, v30.4h, v31.4h
      +0x728: mov     v4.s[1], v0.s[1]
      +0x72c: ushr    v5.4s, v5.4s, #30
      +0x730: sxtl    v0.4s, v7.4h
      +0x734: sxtl    v7.4s, v16.4h
      +0x738: mov     v6.s[1], v1.s[1]
      +0x73c: movi    v1.4s, #0x40, lsl #24
      +0x740: sxtl    v4.4s, v4.4h
      +0x744: mla     v18.4s, v0.4s, v22.4s
      +0x748: movi    v0.4s, #0x40, lsl #24
      +0x74c: mla     v1.4s, v4.4s, v22.4s
      +0x750: movi    v4.4s, #0x40, lsl #24
      +0x754: sxtl    v6.4s, v6.4h
      +0x758: mla     v0.4s, v7.4s, v22.4s
      +0x75c: uzp1    v3.8h, v3.8h, v5.8h
      +0x760: mla     v4.4s, v6.4s, v22.4s
      +0x764: ushr    v5.4s, v18.4s, #29
      +0x768: ushr    v0.4s, v0.4s, #29
      +0x76c: ushr    v1.4s, v1.4s, #29
      +0x770: zip2    v6.4h, v20.4h, v21.4h
      +0x774: zip2    v7.4h, v24.4h, v25.4h
      +0x778: ushr    v4.4s, v4.4s, #29
      +0x77c: uzp1    v0.8h, v5.8h, v0.8h
      +0x780: zip2    v5.4h, v28.4h, v29.4h
      +0x784: uzp1    v1.8h, v1.8h, v4.8h
      +0x788: uzp1    v4.16b, v3.16b, v2.16b
      +0x78c: uzp2    v2.4h, v14.4h, v15.4h
      +0x790: uzp2    v3.4h, v8.4h, v9.4h
      +0x794: uzp1    v0.16b, v1.16b, v0.16b
      +0x798: uzp2    v1.4h, v30.4h, v31.4h
      +0x79c: uzp2    v2.4h, v2.4h, v14.4h
      +0x7a0: uzp2    v3.4h, v3.4h, v8.4h
      +0x7a4: stp     q0, q4, [sp, #48]
      +0x7a8: uzp2    v0.4h, v11.4h, v12.4h
      +0x7ac: zip2    v4.4h, v26.4h, v27.4h
      +0x7b0: uzp2    v1.4h, v1.4h, v30.4h
      +0x7b4: mov     v3.s[1], v5.s[1]
      +0x7b8: uzp2    v0.4h, v0.4h, v11.4h
      +0x7bc: mov     v2.s[1], v4.s[1]
      +0x7c0: movi    v4.4s, #0x40, lsl #24
      +0x7c4: mov     v1.s[1], v7.s[1]
      +0x7c8: mov     v0.s[1], v6.s[1]
      +0x7cc: sxtl    v2.4s, v2.4h
      +0x7d0: movi    v5.4s, #0x40, lsl #24
      +0x7d4: mla     v4.4s, v2.4s, v22.4s
      +0x7d8: movi    v2.4s, #0x40, lsl #24
      +0x7dc: sxtl    v0.4s, v0.4h
      +0x7e0: sxtl    v1.4s, v1.4h
      +0x7e4: sxtl    v3.4s, v3.4h
      +0x7e8: mla     v2.4s, v0.4s, v22.4s
      +0x7ec: mla     v10.4s, v1.4s, v22.4s
      +0x7f0: ldp     q1, q0, [sp, #112]
      +0x7f4: mla     v5.4s, v3.4s, v22.4s
      +0x7f8: str     q2, [sp]
      +0x7fc: tbl     v7.16b, {v14.16b-v15.16b}, v13.16b
      +0x800: tbl     v19.16b, {v14.16b-v15.16b}, v1.16b
      +0x804: zip2    v6.8h, v8.8h, v9.8h
      +0x808: stp     q5, q4, [sp, #16]
      +0x80c: ldr     q2, [sp, #176]
      +0x810: tbl     v18.16b, {v14.16b-v15.16b}, v0.16b
      +0x814: tbl     v16.16b, {v8.16b-v9.16b}, v0.16b
      +0x818: tbl     v8.16b, {v8.16b-v9.16b}, v1.16b
      +0x81c: zip2    v9.8h, v11.8h, v12.8h
      +0x820: tbl     v14.16b, {v11.16b-v12.16b}, v0.16b
      +0x824: tbl     v15.16b, {v11.16b-v12.16b}, v13.16b
      +0x828: tbl     v11.16b, {v11.16b-v12.16b}, v1.16b
      +0x82c: tbl     v12.16b, {v30.16b-v31.16b}, v0.16b
      +0x830: tbl     v13.16b, {v30.16b-v31.16b}, v13.16b
      +0x834: tbl     v3.16b, {v30.16b-v31.16b}, v1.16b
      +0x838: zip2    v30.8h, v30.8h, v31.8h
      +0x83c: tbl     v31.16b, {v26.16b-v27.16b}, v2.16b
      +0x840: tbl     v0.16b, {v28.16b-v29.16b}, v2.16b
      +0x844: tbl     v1.16b, {v20.16b-v21.16b}, v2.16b
      +0x848: tbl     v2.16b, {v24.16b-v25.16b}, v2.16b
      +0x84c: mov     v17.s[1], v31.s[1]
      +0x850: mov     v6.s[1], v0.s[1]
      +0x854: mov     v9.s[1], v1.s[1]
      +0x858: movi    v31.4s, #0x40, lsl #24
      +0x85c: movi    v1.4s, #0x40, lsl #24
      +0x860: mov     v30.s[1], v2.s[1]
      +0x864: sxtl    v2.4s, v17.4h
      +0x868: sxtl    v6.4s, v6.4h
      +0x86c: ldp     q0, q5, [sp, #144]
      +0x870: mla     v31.4s, v2.4s, v22.4s
      +0x874: mla     v1.4s, v6.4s, v22.4s
      +0x878: movi    v2.4s, #0x40, lsl #24
      +0x87c: movi    v6.4s, #0x40, lsl #24
      +0x880: sxtl    v17.4s, v9.4h
      +0x884: sxtl    v30.4s, v30.4h
      +0x888: mla     v2.4s, v17.4s, v22.4s
      +0x88c: mla     v6.4s, v30.4s, v22.4s
      +0x890: zip2    v17.8h, v26.8h, v27.8h
      +0x894: tbl     v30.16b, {v26.16b-v27.16b}, v5.16b
      +0x898: tbl     v26.16b, {v26.16b-v27.16b}, v0.16b
      +0x89c: zip2    v27.8h, v28.8h, v29.8h
      +0x8a0: tbl     v4.16b, {v28.16b-v29.16b}, v5.16b
      +0x8a4: tbl     v28.16b, {v28.16b-v29.16b}, v0.16b
      +0x8a8: zip2    v29.8h, v20.8h, v21.8h
      +0x8ac: tbl     v9.16b, {v20.16b-v21.16b}, v5.16b
      +0x8b0: tbl     v20.16b, {v20.16b-v21.16b}, v0.16b
      +0x8b4: tbl     v21.16b, {v24.16b-v25.16b}, v5.16b
      +0x8b8: tbl     v5.16b, {v24.16b-v25.16b}, v0.16b
      +0x8bc: zip2    v24.8h, v24.8h, v25.8h
      +0x8c0: mov     v16.s[1], v27.s[1]
      +0x8c4: mov     v8.s[1], v28.s[1]
      +0x8c8: mov     v18.s[1], v17.s[1]
      +0x8cc: mov     v12.s[1], v24.s[1]
      +0x8d0: movi    v24.4s, #0x40, lsl #24
      +0x8d4: mov     v14.s[1], v29.s[1]
      +0x8d8: sxtl    v16.4s, v16.4h
      +0x8dc: mov     v11.s[1], v20.s[1]
      +0x8e0: movi    v20.4s, #0x40, lsl #24
      +0x8e4: movi    v17.4s, #0x40, lsl #24
      +0x8e8: mla     v24.4s, v16.4s, v22.4s
      +0x8ec: movi    v16.4s, #0x40, lsl #24
      +0x8f0: mov     v7.s[1], v30.s[1]
      +0x8f4: mov     v19.s[1], v26.s[1]
      +0x8f8: mov     v3.s[1], v5.s[1]
      +0x8fc: sxtl    v26.4s, v8.4h
      +0x900: sxtl    v18.4s, v18.4h
      +0x904: sxtl    v25.4s, v14.4h
      +0x908: mov     v23.s[1], v4.s[1]
      +0x90c: mov     v13.s[1], v21.s[1]
      +0x910: movi    v21.4s, #0x40, lsl #24
      +0x914: mla     v20.4s, v26.4s, v22.4s
      +0x918: movi    v26.4s, #0x40, lsl #24
      +0x91c: mla     v17.4s, v18.4s, v22.4s
      +0x920: movi    v18.4s, #0x40, lsl #24
      +0x924: mla     v16.4s, v25.4s, v22.4s
      +0x928: mov     v15.s[1], v9.s[1]
      +0x92c: movi    v25.4s, #0x40, lsl #24
      +0x930: sxtl    v7.4s, v7.4h
      +0x934: movi    v5.4s, #0x40, lsl #24
      +0x938: sxtl    v3.4s, v3.4h
      +0x93c: sxtl    v27.4s, v12.4h
      +0x940: sxtl    v23.4s, v23.4h
      +0x944: mla     v21.4s, v7.4s, v22.4s
      +0x948: movi    v7.4s, #0x40, lsl #24
      +0x94c: sxtl    v4.4s, v19.4h
      +0x950: mla     v26.4s, v3.4s, v22.4s
      +0x954: ldp     q3, q0, [sp, #80]
      +0x958: mla     v18.4s, v27.4s, v22.4s
      +0x95c: ushr    v1.4s, v1.4s, #27
      +0x960: mla     v25.4s, v23.4s, v22.4s
      +0x964: movi    v23.4s, #0x40, lsl #24
      +0x968: sxtl    v27.4s, v15.4h
      +0x96c: mla     v5.4s, v4.4s, v22.4s
      +0x970: movi    v4.4s, #0x40, lsl #24
      +0x974: sxtl    v29.4s, v13.4h
      +0x978: mla     v7.4s, v27.4s, v22.4s
      +0x97c: sxtl    v27.4s, v11.4h
      +0x980: mla     v23.4s, v29.4s, v22.4s
      +0x984: mla     v4.4s, v27.4s, v22.4s
      +0x988: movi    v22.16b, #0x2
      +0x98c: uzp1    v3.16b, v3.16b, v0.16b
      +0x990: ldr     q0, [sp, #64]
      +0x994: movi    v27.16b, #0x4
      +0x998: ushr    v6.4s, v6.4s, #27
      +0x99c: and     v22.16b, v0.16b, v22.16b
      +0x9a0: ldr     q0, [sp, #48]
      +0x9a4: ushr    v2.4s, v2.4s, #27
      +0x9a8: ushr    v19.4s, v10.4s, #28
      +0x9ac: ushr    v16.4s, v16.4s, #26
      +0x9b0: and     v27.16b, v0.16b, v27.16b
      +0x9b4: ldr     q0, [sp, #16]
      +0x9b8: ushr    v7.4s, v7.4s, #25
      +0x9bc: ushr    v5.4s, v5.4s, #24
      +0x9c0: ushr    v4.4s, v4.4s, #24
      +0x9c4: ushr    v28.4s, v0.4s, #28
      +0x9c8: ldr     q0, [sp, #32]
      +0x9cc: ushr    v29.4s, v0.4s, #28
      +0x9d0: ldr     q0, [sp]
      +0x9d4: uzp1    v28.8h, v29.8h, v28.8h
      +0x9d8: ushr    v30.4s, v0.4s, #28
      +0x9dc: ushr    v0.4s, v31.4s, #27
      +0x9e0: uzp1    v19.8h, v30.8h, v19.8h
      +0x9e4: uzp1    v0.8h, v0.8h, v1.8h
      +0x9e8: uzp1    v1.8h, v2.8h, v6.8h
      +0x9ec: ushr    v6.4s, v17.4s, #26
      +0x9f0: ushr    v17.4s, v18.4s, #26
      +0x9f4: orr     v2.16b, v22.16b, v27.16b
      +0x9f8: uzp1    v0.16b, v1.16b, v0.16b
      +0x9fc: ushr    v1.4s, v24.4s, #26
      +0xa00: orr     v2.16b, v2.16b, v3.16b
      +0xa04: uzp1    v3.16b, v19.16b, v28.16b
      +0xa08: uzp1    v1.8h, v6.8h, v1.8h
      +0xa0c: uzp1    v6.8h, v16.8h, v17.8h
      +0xa10: movi    v16.16b, #0x8
      +0xa14: uzp1    v1.16b, v6.16b, v1.16b
      +0xa18: ushr    v6.4s, v21.4s, #25
      +0xa1c: and     v3.16b, v3.16b, v16.16b
      +0xa20: orr     v2.16b, v2.16b, v3.16b
      +0xa24: movi    v3.16b, #0x10
      +0xa28: ushr    v16.4s, v23.4s, #25
      +0xa2c: and     v0.16b, v0.16b, v3.16b
      +0xa30: ushr    v3.4s, v25.4s, #25
      +0xa34: uzp1    v3.8h, v6.8h, v3.8h
      +0xa38: uzp1    v6.8h, v7.8h, v16.8h
      +0xa3c: ushr    v7.4s, v20.4s, #24
      +0xa40: ushr    v16.4s, v26.4s, #24
      +0xa44: uzp1    v5.8h, v5.8h, v7.8h
      +0xa48: uzp1    v3.16b, v6.16b, v3.16b
      +0xa4c: movi    v6.16b, #0x20
      +0xa50: uzp1    v4.8h, v4.8h, v16.8h
      +0xa54: and     v1.16b, v1.16b, v6.16b
      +0xa58: orr     v0.16b, v0.16b, v1.16b
      +0xa5c: uzp1    v1.16b, v4.16b, v5.16b
      +0xa60: movi    v4.16b, #0x40
      +0xa64: and     v3.16b, v3.16b, v4.16b
      +0xa68: orr     v0.16b, v0.16b, v3.16b
      +0xa6c: orr     v0.16b, v2.16b, v0.16b
      +0xa70: movi    v2.16b, #0x80
      +0xa74: and     v1.16b, v1.16b, v2.16b
      +0xa78: orr     v0.16b, v0.16b, v1.16b
      +0xa7c: str     q0, [x0, #16]
      +0xa80: ldp     d9, d8, [sp, #240]
      +0xa84: ldp     d11, d10, [sp, #224]
      +0xa88: ldp     d13, d12, [sp, #208]
      +0xa8c: ldp     d15, d14, [sp, #192]
      +0xa90: ldr     x29, [sp, #256]
      +0xa94: add     sp, sp, #0x110
      +0xa98: ret
 ***)

let MLKEM_NATIVE_POLY_TOMSG_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_tomsg"];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to one bit, as computed in a 32-bit lane *)
(* (COMPRESS_D1_ARITH is that of gcc12_O2), and the 32 bytes of the result   *)
(* from the eight bits in each.                                              *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D1_ARITH = prove
 (`!v. v < 3329
       ==> (1073741824 + v * 1290168) DIV 2147483648 =
           (4 * v + 3329) DIV 6658`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`4 * v + 3329`; `6658`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`(4 * v + 3329) MOD 6658`,`r:num`) THEN
  SPEC_TAC(`(4 * v + 3329) DIV 6658`,`q:num`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `(1073741824 + v * 1290168) - q * 2147483648` THEN
  ASM_ARITH_TAC);;

let TOMSG_LANE = prove
 (`!y:int16.
        val y < 3329
        ==> word_subword (word_add (word 1073741824)
                                   (word_mul (word_sx y) (word 1290168)):int32)
                         (31,1):1 word =
            word((4 * val y + 3329) DIV 6658)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[WORD_SX_SMALL; ARITH_RULE `y < 3329 ==> y < 32768`] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_ADD; VAL_WORD_MUL;
              VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_16;
              DIMINDEX_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `y < 3329 ==> y < 4294967296`;
               ARITH_RULE `y < 3329 ==> y * 1290168 < 4294967296`] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2147483648 * 2`; GSYM DIV_MOD] THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN ASM_SIMP_TAC[COMPRESS_D1_ARITH]);;

let TOMSG_PACK = prove
 (`!r s (c:num->num).
     (!j. j < 32
          ==> read (memory :> bytes8 (word_add r (word j))) s =
              (word_join
                (word_join
                  (word_join (word(c(8 * j + 7)):1 word)
                             (word(c(8 * j + 6)):1 word):2 word)
                  (word_join (word(c(8 * j + 5)):1 word)
                             (word(c(8 * j + 4)):1 word):2 word):4 word)
                (word_join
                  (word_join (word(c(8 * j + 3)):1 word)
                             (word(c(8 * j + 2)):1 word):2 word)
                  (word_join (word(c(8 * j + 1)):1 word)
                             (word(c(8 * j)):1 word):2 word):4 word)):byte)
     ==> read (memory :> bytes(r,32)) s =
         nsum {i | i < 256} (\i. c i MOD 2 * 2 EXP i)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!k. k <= 32
        ==> read (memory :> bytes(r,k)) s =
            nsum {i | i < 8 * k} (\i. (c:num->num) i MOD 2 * 2 EXP i)`
   (MP_TAC o SPEC `32`) THENL
   [ALL_TAC; CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; NSUM_CLAUSES_NUMSEG_LT;
                READ_MEMORY_BYTES_TRIVIAL];
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `SUC k <= 32` THEN ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `SUC k <= 32` THEN ARITH_TAC; DISCH_TAC] THEN
  ASM_REWRITE_TAC[ADD1; READ_MEMORY_BYTES_SNOC] THEN
  REWRITE_TAC[ARITH_RULE
   `8 * (k + 1) = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC(8 * k))))))))`] THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  SIMP_TAC[VAL_WORD_JOIN_SIMPLE; DIMINDEX_1; DIMINDEX_2; DIMINDEX_4;
           DIMINDEX_8; ARITH] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_1; EXP_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`nsum {i | i < 8 * k} (\i. (c:num->num) i MOD 2 * 2 EXP i)`,
           `n:num`) THEN
  CONV_TAC NUM_RING);;

(*** The 256 coefficients, merged into the 128-bit parts that the loads
 *** read ***)

let TOMSG_MERGES = map (fun k ->
  let addr = if k = 0 then `a:int64` else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`a:int64`),
            mk_comb(`word:num->int64`, mk_small_numeral(16 * k))) in
  READ_MEMORY_MERGE_CONV 3
   (vsubst [addr,`x:int64`] `read (memory :> bytes128 x) s0`)) (0--31);;

let TOMSG_INPUT_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_forall(concl th) && free_in `x:num->int16` (concl th))) THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  MAP_EVERY MP_TAC TOMSG_MERGES THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`];;

(*** The six vectors of byte indices for TBL ***)

let MLKEM_NATIVE_POLY_TOMSG_CLANG17_O3_CONSTANTS =
  map (fun k ->
    MLKEM_NATIVE_IMAGE_CONST_RULE
     (layout("mlkem_poly_tomsg_const" ^ string_of_int k)) 128) (1--6);;

let TOMSG_CONSTANTS_TAC =
  MAP_EVERY (fun th -> FIRST_ASSUM(fun ath ->
      if can (term_match [] `aligned_bytes_loaded s0 (word pc)
                               mlkem_native_libmlkem_clang17_O3_mc`)
             (concl ath)
      then ASSUME_TAC(MATCH_MP th ath) else failwith ""))
    MLKEM_NATIVE_POLY_TOMSG_CLANG17_O3_CONSTANTS;;

(* ------------------------------------------------------------------------- *)
(* The check for overlap has one branch for each order of the arrays: with   *)
(* the input a (512 bytes) and the output r (32 bytes), the scalar loop is  *)
(* taken unless a + 512 <= r or r + 32 <= a. In either case the vector code *)
(* is entered at the same instruction, after 3 or 6 steps (after the 6 steps *)
(* of the prologue) respectively.                                            *)
(* ------------------------------------------------------------------------- *)

let TOMSG_RESOLVE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_FLAG; VAL_WORD_SUB_EQ_0]) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read PC s = if p then x else y`) c then
      let p = rand(rator(rator(rand c))) in
      let decide q = SUBGOAL_THEN q (fun th' ->
        ASSUME_TAC(REWRITE_RULE[th'] th)) THENL [ASM_ARITH_TAC; ALL_TAC] in
      decide p ORELSE decide (mk_neg p)
    else failwith "TOMSG_RESOLVE_TAC");;

let TOMSG_CHECK_TAC (body:int->tactic) =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_CLANG17_O3_EXEC (1--6) THEN
  MP_TAC(SPECL [`r:int64`; `a:int64`; `32`; `512`]
                NONOVERLAPPING_ALIAS_CHECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_CLANG17_O3_EXEC (7--9) THEN
  ASM_CASES_TAC `val(word_add a (word 512):int64) <= val(r:int64)` THENL
   [TOMSG_RESOLVE_TAC THEN body 9;
    TOMSG_RESOLVE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_CLANG17_O3_EXEC (10--12) THEN
    TOMSG_RESOLVE_TAC THEN body 12];;

(*** The vector code from join1 on: 615 steps and the return ***)

let TOMSG_BODY_TAC (simp:tactic) off =
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_CLANG17_O3_EXEC [k + off] THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    simp) (1--616);;

(*** The restored D registers, as zero extensions of the 64 bits saved ***)

let TOMSG_DREG = prove
 (`!x:int64. word_zx(word_zx x:int128):int64 = x`,
  BITBLAST_TAC);;

(*** The lanes of the multiply-accumulates in the stores come out of the
 *** simulation with the 16-bit operand of the SXTL as a join of the bytes
 *** of coefficients (EXT works on bytes); find which coefficient x k it is
 *** by bit-blasting and replace it by x k ***)

let TOMSG_NORMALIZE_LANES lanepat th =
  let v = rand(concl th) in
  let ms = setify(find_terms (can (term_match [] lanepat)) v) in
  let eths = mapfilter (fun m ->
    let y = rand(rand(rator(rand(rator(rand m))))) in
    if is_comb y && rator y = `x:num->int16` then failwith "plain" else
    let cands = setify(find_terms (fun t -> is_comb t &&
                                            rator t = `x:num->int16`) y) in
    tryfind (fun c -> BITBLAST_RULE(mk_eq(y,c))) cands) ms in
  if eths = [] then th else CONV_RULE(RAND_CONV(REWRITE_CONV eths)) th;;

(*** After each step: the registers loaded by LD1-LD4 and the 128-bit parts
 *** of the memory written by ST4 as joins, and the subwords taken through
 *** AND and OR to the lanes ***)

let TOMSG_SIMPLIFY_CONV =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC REWR_CONV WORD_SUBWORD_OR ORELSEC
    WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV;;

let TOMSG_SIMD_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> match t with
              Const(("word_subdeinterleave"|"word_interleave"),_) -> true
            | _ -> false)) (concl th)
    then CONV_RULE(RAND_CONV TOMSG_SIMPLIFY_CONV)
          (CONV_RULE(TOP_DEPTH_CONV MLKEM_NATIVE_INTERLEAVE_CONV) th)
    else th) THEN
  SIMD_SIMPLIFY_TAC[];;

(*** After the simulation, the subwords of the stores taken through AND and
 *** OR to the lanes ***)


(*** Each stored byte as the bits 31 of the eight lanes for it, found by
 *** bit-blasting with the lanes, multiply-accumulates, as variables ***)

let tomsg_lanepat =
  `word_add (word 1073741824)
            (word_mul (word_shl (word_sx (y:int16)) 0) (word 1290168)):int32`;;

let TOMSG_BYTE_RULE th =
  let v = rand(concl th) in
  let ms = setify(find_terms (can (term_match [] tomsg_lanepat)) v) in
  let idx m = dest_small_numeral(rand(find_term
    (fun t -> is_comb t && rator t = `x:num->int16`) m)) in
  let ims = sort (fun (i,_) (j,_) -> i < j) (map (fun m -> idx m,m) ms) in
  if length ims <> 8 then
    (print_term v; Format.print_newline(); failwith "TOMSG_BYTE_RULE") else
  let gs = map (fun _ -> genvar `:int32`) ims in
  let v' = subst (zip gs (map snd ims)) v in
  let bit g = mk_comb(mk_comb(`word_subword:int32->num#num->1 word`,g),
                      `(31,1)`) in
  let j2 a b = mk_comb(mk_comb(`word_join:1 word->1 word->2 word`,a),b)
  and j4 a b = mk_comb(mk_comb(`word_join:2 word->2 word->4 word`,a),b)
  and j8 a b = mk_comb(mk_comb(`word_join:4 word->4 word->byte`,a),b) in
  let b k = bit(el k gs) in
  let tgt = j8 (j4 (j2 (b 7) (b 6)) (j2 (b 5) (b 4)))
               (j4 (j2 (b 3) (b 2)) (j2 (b 1) (b 0))) in
  let bth = BITBLAST_RULE(mk_eq(v',tgt)) in
  CONV_RULE(RAND_CONV(REWRITE_CONV[WORD_SHL_ZERO]))
   (TRANS th (INST (zip (map snd ims) gs) bth));;

(*** The stored bytes, from the 2 stores of 16 bytes ***)

let TOMSG_STORES_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
    check (fun th -> can (term_match []
                     `read (memory :> bytes128 a) s = x`) (concl th) &&
                     free_in `r:int64` (concl th)))) THEN
  REPEAT(DISCH_THEN(fun th ->
    MAP_EVERY (ASSUME_TAC o TOMSG_BYTE_RULE o
        TOMSG_NORMALIZE_LANES tomsg_lanepat o
      CONV_RULE(RAND_CONV TOMSG_SIMPLIFY_CONV) o
      CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
                                       WORD_ADD_0]
                          THENC NUM_REDUCE_CONV)))
     (CONJUNCTS th)));;

(*** The bit of each coefficient, given the bounds ***)

let TOMSG_BITS_TAC =
  DISCH_THEN(fun bth ->
    let lths = map (fun k ->
      let kt = mk_small_numeral k in
      MP (SPEC (mk_comb(`x:num->int16`,kt)) TOMSG_LANE)
         (MP (SPEC kt bth)
             (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool` kt
                                            `256`))))) (0--255) in
    RULE_ASSUM_TAC(REWRITE_RULE lths));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 1 in common/fips203.ml, the bit  *)
(* for a coefficient x in [0,3329) is the integer closest to 2 * x / 3329,   *)
(* rounding up on ties, modulo 2, i.e. ((4 * x + 3329) DIV 6658) MOD 2, and  *)
(* as for mlkem_encode 1 the bits are put together little-endian. Like the   *)
(* C code, this relies on the coefficients being in [0,3329).                *)
(* ------------------------------------------------------------------------- *)


let MLKEM_NATIVE_POLY_TOMSG_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (r,32)) [(word pc,libmlkem_size); (a,512)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 272),272))
            [(word pc,libmlkem_size); (a,512); (r,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_poly_tomsg) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                          x i)
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,32)) s =
                       nsum {i | i < 256}
                            (\i. ((4 * val(x i) + 3329) DIV 6658) MOD 2 *
                                 2 EXP i)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,32);
                         memory :> bytes(word_sub stackpointer
                                                 (word 272),272)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `x:num->int16`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 272 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29` THEN
  MAP_EVERY (fun (n,d) -> ENSURES_PRESERVED_DREG_TAC n d)
   [("d8_init",`D8`); ("d9_init",`D9`); ("d10_init",`D10`);
    ("d11_init",`D11`); ("d12_init",`D12`); ("d13_init",`D13`);
    ("d14_init",`D14`); ("d15_init",`D15`)] THEN
  ENSURES_INIT_TAC "s0" THEN
  TOMSG_INPUT_TAC THEN
  TOMSG_CONSTANTS_TAC THEN

  (*** The prologue, the overlap check, and the vector code ***)

  TOMSG_CHECK_TAC (TOMSG_BODY_TAC TOMSG_SIMD_TAC) THEN
  TOMSG_STORES_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[TOMSG_DREG] THEN

  (*** Each byte from the bits of its eight coefficients ***)

  TOMSG_BITS_TAC THEN
  W(fun (_,w) ->
    MP_TAC(ISPECL [`r:int64`; rand(lhand w);
                   `\i. (4 * val((x:num->int16) i) + 3329) DIV 6658`]
                  TOMSG_PACK)) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_THEN MATCH_MP_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_TOMSG_CLANG17_O3_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (r,32)) [word pc,libmlkem_size; a,512] /\
           ALL (nonoverlapping (word_sub stackpointer (word 272),272))
               [word pc,libmlkem_size; a,512; r,32]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_poly_tomsg) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc (word_sub stackpointer (word 272))
                                       returnaddress /\
                         memaccess_inbounds e2
                          [a,512; r,32;
                           word (pc + mlkem_poly_tomsg_consts),
                           mlkem_poly_tomsg_consts_size;
                           word_sub stackpointer (word 272),272]
                          [r,32; word_sub stackpointer (word 272),272]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,32);
                           memory :> bytes(word_sub stackpointer
                                                   (word 272),272)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      (if val(word_add a (word 512):int64) <= val r
       then f_ev1 a r pc stackpointer returnaddress
       else f_ev2 a r pc stackpointer returnaddress):(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_TOMSG_CLANG17_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_PRESERVED_TAC "x29_init" `X29` THEN
  MAP_EVERY (fun (n,d) -> ENSURES_PRESERVED_DREG_TAC n d)
   [("d8_init",`D8`); ("d9_init",`D9`); ("d10_init",`D10`);
    ("d11_init",`D11`); ("d12_init",`D12`); ("d13_init",`D13`);
    ("d14_init",`D14`); ("d15_init",`D15`)] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  TOMSG_CONSTANTS_TAC THEN
  TOMSG_CHECK_TAC (TOMSG_BODY_TAC ALL_TAC) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[TOMSG_DREG] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
