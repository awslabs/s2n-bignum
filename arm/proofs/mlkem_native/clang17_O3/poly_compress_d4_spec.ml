(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 4 bits per coefficient. This is the code   *)
(* for mlkem_poly_compress_d4 from mlkem-native's portable C implementation  *)
(* compiled by clang 17 with -O3 (see mlkem_native/README.md). It is         *)
(* verified in the whole image (see libmlkem.ml).                            *)
(*                                                                           *)
(* The compiler has vectorized the loop completely, with 32-bit lanes,       *)
(* after a check that the input and the output do not overlap, with one      *)
(* branch for each of the two orders of the arrays; if they overlap, the     *)
(* code falls back to a scalar loop. Since the specification requires them   *)
(* not to overlap, only the vector code runs. It saves D8 to D15 and X29 and *)
(* spills vectors to the stack, all in a frame of 304 bytes, which the       *)
(* specifications therefore have (unlike those of gcc12_O2, which have a     *)
(* frame of 32 bytes). The code has no stack guard. It reads six vectors of  *)
(* byte indices for TBL from the read-only data.                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/overlap.ml";;
needs "arm/proofs/mlkem_native/interleave.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_compress_d4:
        +0x0: sub     sp, sp, #0x130
        +0x4: stp     d15, d14, [sp, #224]
        +0x8: stp     d13, d12, [sp, #240]
        +0xc: stp     d11, d10, [sp, #256]
       +0x10: stp     d9, d8, [sp, #272]
       +0x14: str     x29, [sp, #288]
       +0x18: add     x8, x1, #0x200
       +0x1c: cmp     x8, x0
       +0x20: b.ls    join1
       +0x24: add     x8, x0, #0x80
       +0x28: cmp     x8, x1
       +0x2c: b.ls    join1
       +0x30: mov     w10, #0xafb0
       +0x34: mov     x8, xzr
       +0x38: movk    w10, #0x13, lsl #16
       +0x3c: add     x9, x1, #0x8
       +0x40: dup     v0.4s, w10
       +0x44: ldurh   w10, [x9, #-8]
       +0x48: sub     x11, x9, #0x4
       +0x4c: sub     x12, x9, #0x2
       +0x50: movi    v3.4s, #0x8, lsl #24
       +0x54: fmov    s1, w10
       +0x58: ldurh   w10, [x9, #-6]
       +0x5c: movi    v4.4s, #0x8, lsl #24
       +0x60: ld1     {v1.h}[1], [x11]
       +0x64: mov     x11, x9
       +0x68: fmov    s2, w10
       +0x6c: add     x10, x9, #0x6
       +0x70: ld1     {v1.h}[2], [x11], #2
       +0x74: ld1     {v2.h}[1], [x12]
       +0x78: ld1     {v2.h}[2], [x11]
       +0x7c: add     x11, x9, #0x4
       +0x80: add     x9, x9, #0x10
       +0x84: ld1     {v1.h}[3], [x11]
       +0x88: ld1     {v2.h}[3], [x10]
       +0x8c: sxtl    v1.4s, v1.4h
       +0x90: sxtl    v2.4s, v2.4h
       +0x94: mla     v4.4s, v1.4s, v0.4s
       +0x98: mla     v3.4s, v2.4s, v0.4s
       +0x9c: ushr    v2.4s, v4.4s, #28
       +0xa0: ushr    v1.4s, v3.4s, #24
       +0xa4: xtn     v2.4h, v2.4s
       +0xa8: xtn     v1.4h, v1.4s
       +0xac: bic     v1.4h, #0xf
       +0xb0: orr     v1.8b, v1.8b, v2.8b
       +0xb4: xtn     v1.8b, v1.8h
       +0xb8: str     s1, [x0, x8]
       +0xbc: add     x8, x8, #0x4
       +0xc0: cmp     x8, #0x80
       +0xc4: b.ne    loop1
       +0xc8: b       join2
       +0xcc: ldp     q13, q14, [x1, #32]
       +0xd0: mov     w8, #0xafb0
       +0xd4: adrp    x9, <page>
       +0xd8: movk    w8, #0x13, lsl #16
       +0xdc: movi    v11.4s, #0x8, lsl #24
       +0xe0: movi    v27.4s, #0x8, lsl #24
       +0xe4: dup     v26.4s, w8
       +0xe8: adrp    x8, <page>
       +0xec: ldp     q18, q19, [x1]
       +0xf0: zip1    v1.4h, v13.4h, v14.4h
       +0xf4: movi    v15.4s, #0x8, lsl #24
       +0xf8: ext     v0.8b, v13.8b, v1.8b, #4
       +0xfc: ldp     q22, q23, [x1, #96]
      +0x100: zip1    v2.4h, v18.4h, v19.4h
      +0x104: mov     v2.s[1], v0.s[1]
      +0x108: ldp     q24, q25, [x1, #224]
      +0x10c: zip1    v3.4h, v22.4h, v23.4h
      +0x110: sxtl    v2.4s, v2.4h
      +0x114: ext     v0.8b, v22.8b, v3.8b, #4
      +0x118: ldp     q29, q30, [x1, #160]
      +0x11c: zip1    v5.4h, v24.4h, v25.4h
      +0x120: mla     v11.4s, v2.4s, v26.4s
      +0x124: movi    v2.4s, #0x8, lsl #24
      +0x128: ext     v31.8b, v24.8b, v5.8b, #4
      +0x12c: ldp     q16, q17, [x1, #64]
      +0x130: zip1    v4.4h, v29.4h, v30.4h
      +0x134: ext     v7.8b, v29.8b, v4.8b, #4
      +0x138: ldp     q20, q21, [x1, #192]
      +0x13c: zip1    v6.4h, v16.4h, v17.4h
      +0x140: mov     v6.s[1], v0.s[1]
      +0x144: ldp     q8, q9, [x1, #128]
      +0x148: zip1    v10.4h, v20.4h, v21.4h
      +0x14c: sxtl    v6.4s, v6.4h
      +0x150: mov     v10.s[1], v31.s[1]
      +0x154: zip1    v28.4h, v8.4h, v9.4h
      +0x158: movi    v31.4s, #0x8, lsl #24
      +0x15c: trn2    v12.4h, v8.4h, v9.4h
      +0x160: mla     v2.4s, v6.4s, v26.4s
      +0x164: sxtl    v10.4s, v10.4h
      +0x168: mov     v28.s[1], v7.s[1]
      +0x16c: movi    v7.4s, #0x8, lsl #24
      +0x170: mla     v31.4s, v10.4s, v26.4s
      +0x174: ushr    v10.4s, v11.4s, #28
      +0x178: sxtl    v28.4s, v28.4h
      +0x17c: ushr    v2.4s, v2.4s, #28
      +0x180: mov     v12.s[1], v4.s[1]
      +0x184: mla     v7.4s, v28.4s, v26.4s
      +0x188: ushr    v31.4s, v31.4s, #28
      +0x18c: trn2    v4.4h, v18.4h, v19.4h
      +0x190: trn2    v28.4h, v20.4h, v21.4h
      +0x194: uzp1    v2.8h, v10.8h, v2.8h
      +0x198: trn2    v6.4h, v16.4h, v17.4h
      +0x19c: ushr    v7.4s, v7.4s, #28
      +0x1a0: zip2    v10.4h, v16.4h, v17.4h
      +0x1a4: uzp1    v7.8h, v7.8h, v31.8h
      +0x1a8: mov     v4.s[1], v1.s[1]
      +0x1ac: mov     v28.s[1], v5.s[1]
      +0x1b0: mov     v6.s[1], v3.s[1]
      +0x1b4: uzp1    v0.16b, v2.16b, v7.16b
      +0x1b8: movi    v7.4s, #0x8, lsl #24
      +0x1bc: sxtl    v4.4s, v4.4h
      +0x1c0: sxtl    v5.4s, v12.4h
      +0x1c4: str     q0, [sp, #128]
      +0x1c8: movi    v0.4s, #0x8, lsl #24
      +0x1cc: mla     v7.4s, v4.4s, v26.4s
      +0x1d0: sxtl    v2.4s, v28.4h
      +0x1d4: mov     v3.16b, v29.16b
      +0x1d8: mla     v0.4s, v5.4s, v26.4s
      +0x1dc: mla     v27.4s, v2.4s, v26.4s
      +0x1e0: str     q7, [sp, #80]
      +0x1e4: mov     v2.16b, v24.16b
      +0x1e8: mov     v5.16b, v22.16b
      +0x1ec: sxtl    v1.4s, v6.4h
      +0x1f0: mov     v3.h[3], v30.h[2]
      +0x1f4: stp     q27, q0, [sp, #96]
      +0x1f8: mov     v2.h[3], v25.h[2]
      +0x1fc: zip2    v6.4h, v8.4h, v9.4h
      +0x200: zip2    v7.4h, v20.4h, v21.4h
      +0x204: zip2    v28.4h, v18.4h, v19.4h
      +0x208: mov     v5.h[3], v23.h[2]
      +0x20c: mov     v4.16b, v13.16b
      +0x210: mov     v4.h[3], v14.h[2]
      +0x214: mov     v6.s[1], v3.s[1]
      +0x218: mov     v7.s[1], v2.s[1]
      +0x21c: mov     v10.s[1], v5.s[1]
      +0x220: mov     v28.s[1], v4.s[1]
      +0x224: sxtl    v2.4s, v6.4h
      +0x228: sxtl    v3.4s, v7.4h
      +0x22c: sxtl    v5.4s, v10.4h
      +0x230: movi    v6.4s, #0x8, lsl #24
      +0x234: movi    v7.4s, #0x8, lsl #24
      +0x238: movi    v10.4s, #0x8, lsl #24
      +0x23c: movi    v11.4s, #0x8, lsl #24
      +0x240: sxtl    v4.4s, v28.4h
      +0x244: mla     v6.4s, v2.4s, v26.4s
      +0x248: mla     v7.4s, v5.4s, v26.4s
      +0x24c: mla     v10.4s, v3.4s, v26.4s
      +0x250: mla     v11.4s, v4.4s, v26.4s
      +0x254: movi    v0.4s, #0x8, lsl #24
      +0x258: ushr    v2.4s, v7.4s, #28
      +0x25c: ushr    v3.4s, v10.4s, #28
      +0x260: ushr    v4.4s, v6.4s, #28
      +0x264: ushr    v5.4s, v11.4s, #28
      +0x268: uzp2    v6.4h, v8.4h, v9.4h
      +0x26c: uzp1    v3.8h, v4.8h, v3.8h
      +0x270: zip2    v4.4h, v29.4h, v30.4h
      +0x274: uzp1    v2.8h, v5.8h, v2.8h
      +0x278: mla     v0.4s, v1.4s, v26.4s
      +0x27c: uzp2    v5.4h, v6.4h, v8.4h
      +0x280: mov     v27.16b, v18.16b
      +0x284: uzp2    v1.4h, v20.4h, v21.4h
      +0x288: mov     v28.16b, v19.16b
      +0x28c: str     q0, [sp, #48]
      +0x290: uzp2    v6.4h, v16.4h, v17.4h
      +0x294: uzp1    v0.16b, v2.16b, v3.16b
      +0x298: uzp2    v2.4h, v27.4h, v28.4h
      +0x29c: mov     v5.s[1], v4.s[1]
      +0x2a0: zip2    v3.4h, v24.4h, v25.4h
      +0x2a4: uzp2    v1.4h, v1.4h, v20.4h
      +0x2a8: zip2    v4.4h, v13.4h, v14.4h
      +0x2ac: str     q0, [sp, #64]
      +0x2b0: uzp2    v2.4h, v2.4h, v27.4h
      +0x2b4: movi    v0.4s, #0x8, lsl #24
      +0x2b8: uzp2    v6.4h, v6.4h, v16.4h
      +0x2bc: sxtl    v5.4s, v5.4h
      +0x2c0: mov     v1.s[1], v3.s[1]
      +0x2c4: mov     v2.s[1], v4.s[1]
      +0x2c8: mla     v0.4s, v5.4s, v26.4s
      +0x2cc: zip2    v3.4h, v22.4h, v23.4h
      +0x2d0: movi    v12.4s, #0x8, lsl #24
      +0x2d4: sxtl    v1.4s, v1.4h
      +0x2d8: str     q0, [sp, #32]
      +0x2dc: ldr     q0, [x8, #352]
                    // mlkem_poly_compress_d4_const1
      +0x2e0: sxtl    v2.4s, v2.4h
      +0x2e4: adrp    x8, <page>
      +0x2e8: mov     v6.s[1], v3.s[1]
      +0x2ec: tbl     v3.16b, {v29.16b-v30.16b}, v0.16b
      +0x2f0: str     q0, [sp, #208]
      +0x2f4: zip2    v4.8h, v8.8h, v9.8h
      +0x2f8: tbl     v7.16b, {v24.16b-v25.16b}, v0.16b
      +0x2fc: zip2    v10.8h, v20.8h, v21.8h
      +0x300: mla     v12.4s, v1.4s, v26.4s
      +0x304: mla     v15.4s, v2.4s, v26.4s
      +0x308: tbl     v1.16b, {v13.16b-v14.16b}, v0.16b
      +0x30c: zip2    v2.8h, v27.8h, v28.8h
      +0x310: mov     v4.s[1], v3.s[1]
      +0x314: mov     v10.s[1], v7.s[1]
      +0x318: tbl     v3.16b, {v22.16b-v23.16b}, v0.16b
      +0x31c: ldr     q0, [x8, #368]
                    // mlkem_poly_compress_d4_const2
      +0x320: zip2    v7.8h, v16.8h, v17.8h
      +0x324: adrp    x8, <page>
      +0x328: mov     v2.s[1], v1.s[1]
      +0x32c: movi    v11.4s, #0x8, lsl #24
      +0x330: str     q0, [sp, #144]
      +0x334: sxtl    v1.4s, v4.4h
      +0x338: mov     v7.s[1], v3.s[1]
      +0x33c: movi    v3.4s, #0x8, lsl #24
      +0x340: sxtl    v2.4s, v2.4h
      +0x344: mla     v11.4s, v1.4s, v26.4s
      +0x348: movi    v1.4s, #0x8, lsl #24
      +0x34c: mla     v3.4s, v2.4s, v26.4s
      +0x350: movi    v2.4s, #0x8, lsl #24
      +0x354: sxtl    v4.4s, v10.4h
      +0x358: sxtl    v7.4s, v7.4h
      +0x35c: mla     v1.4s, v4.4s, v26.4s
      +0x360: movi    v31.4s, #0x8, lsl #24
      +0x364: mla     v2.4s, v7.4s, v26.4s
      +0x368: sxtl    v6.4s, v6.4h
      +0x36c: ushr    v1.4s, v1.4s, #28
      +0x370: mla     v31.4s, v6.4s, v26.4s
      +0x374: ushr    v6.4s, v11.4s, #28
      +0x378: ushr    v2.4s, v2.4s, #28
      +0x37c: ushr    v3.4s, v3.4s, #28
      +0x380: uzp1    v1.8h, v6.8h, v1.8h
      +0x384: uzp1    v3.8h, v3.8h, v2.8h
      +0x388: zip2    v7.8h, v29.8h, v30.8h
      +0x38c: tbl     v10.16b, {v8.16b-v9.16b}, v0.16b
      +0x390: mov     v18.16b, v16.16b
      +0x394: mov     v19.16b, v17.16b
      +0x398: zip2    v11.8h, v24.8h, v25.8h
      +0x39c: tbl     v16.16b, {v20.16b-v21.16b}, v0.16b
      +0x3a0: tbl     v17.16b, {v27.16b-v28.16b}, v0.16b
      +0x3a4: mov     v6.16b, v0.16b
      +0x3a8: uzp1    v0.16b, v3.16b, v1.16b
      +0x3ac: zip2    v2.8h, v13.8h, v14.8h
      +0x3b0: mov     v10.s[1], v7.s[1]
      +0x3b4: mov     v16.s[1], v11.s[1]
      +0x3b8: str     q0, [sp, #16]
      +0x3bc: ldr     q0, [x8, #384]
                    // mlkem_poly_compress_d4_const3
      +0x3c0: mov     v11.16b, v19.16b
      +0x3c4: adrp    x8, <page>
      +0x3c8: tbl     v6.16b, {v18.16b-v19.16b}, v6.16b
      +0x3cc: ldr     q19, [x9, #400]
                    // mlkem_poly_compress_d4_const4
      +0x3d0: mov     v17.s[1], v2.s[1]
      +0x3d4: adrp    x9, <page>
      +0x3d8: sxtl    v5.4s, v10.4h
      +0x3dc: str     q0, [sp, #192]
      +0x3e0: mov     v10.16b, v18.16b
      +0x3e4: str     q19, [sp, #160]
      +0x3e8: movi    v18.4s, #0x8, lsl #24
      +0x3ec: tbl     v7.16b, {v29.16b-v30.16b}, v0.16b
      +0x3f0: tbl     v2.16b, {v8.16b-v9.16b}, v19.16b
      +0x3f4: zip2    v4.8h, v22.8h, v23.8h
      +0x3f8: tbl     v3.16b, {v24.16b-v25.16b}, v0.16b
      +0x3fc: tbl     v1.16b, {v20.16b-v21.16b}, v19.16b
      +0x400: mla     v18.4s, v5.4s, v26.4s
      +0x404: mov     v2.s[1], v7.s[1]
      +0x408: tbl     v5.16b, {v22.16b-v23.16b}, v0.16b
      +0x40c: tbl     v7.16b, {v10.16b-v11.16b}, v19.16b
      +0x410: mov     v6.s[1], v4.s[1]
      +0x414: mov     v1.s[1], v3.s[1]
      +0x418: tbl     v3.16b, {v13.16b-v14.16b}, v0.16b
      +0x41c: ldr     q0, [x8, #416]
                    // mlkem_poly_compress_d4_const5
      +0x420: tbl     v4.16b, {v27.16b-v28.16b}, v19.16b
      +0x424: mov     v7.s[1], v5.s[1]
      +0x428: movi    v19.4s, #0x8, lsl #24
      +0x42c: str     q0, [sp, #176]
      +0x430: sxtl    v2.4s, v2.4h
      +0x434: mov     v4.s[1], v3.s[1]
      +0x438: movi    v3.4s, #0x8, lsl #24
      +0x43c: sxtl    v5.4s, v7.4h
      +0x440: mla     v19.4s, v2.4s, v26.4s
      +0x444: movi    v2.4s, #0x8, lsl #24
      +0x448: mla     v3.4s, v5.4s, v26.4s
      +0x44c: movi    v5.4s, #0x8, lsl #24
      +0x450: sxtl    v1.4s, v1.4h
      +0x454: sxtl    v4.4s, v4.4h
      +0x458: mla     v2.4s, v1.4s, v26.4s
      +0x45c: movi    v1.4s, #0x8, lsl #24
      +0x460: mla     v5.4s, v4.4s, v26.4s
      +0x464: sxtl    v7.4s, v16.4h
      +0x468: ushr    v3.4s, v3.4s, #28
      +0x46c: mla     v1.4s, v7.4s, v26.4s
      +0x470: ldr     q7, [x9, #432]
                    // mlkem_poly_compress_d4_const6
      +0x474: ushr    v2.4s, v2.4s, #28
      +0x478: ushr    v4.4s, v19.4s, #28
      +0x47c: ushr    v16.4s, v5.4s, #28
      +0x480: movi    v19.4s, #0x8, lsl #24
      +0x484: ushr    v18.4s, v18.4s, #24
      +0x488: uzp1    v2.8h, v4.8h, v2.8h
      +0x48c: uzp1    v3.8h, v16.8h, v3.8h
      +0x490: tbl     v4.16b, {v29.16b-v30.16b}, v0.16b
      +0x494: tbl     v16.16b, {v8.16b-v9.16b}, v7.16b
      +0x498: movi    v29.4s, #0x8, lsl #24
      +0x49c: sxtl    v17.4s, v17.4h
      +0x4a0: sxtl    v6.4s, v6.4h
      +0x4a4: mla     v19.4s, v17.4s, v26.4s
      +0x4a8: mla     v29.4s, v6.4s, v26.4s
      +0x4ac: mov     v16.s[1], v4.s[1]
      +0x4b0: tbl     v4.16b, {v20.16b-v21.16b}, v7.16b
      +0x4b4: tbl     v6.16b, {v13.16b-v14.16b}, v0.16b
      +0x4b8: tbl     v17.16b, {v27.16b-v28.16b}, v7.16b
      +0x4bc: tbl     v20.16b, {v22.16b-v23.16b}, v0.16b
      +0x4c0: tbl     v21.16b, {v10.16b-v11.16b}, v7.16b
      +0x4c4: uzp1    v2.16b, v3.16b, v2.16b
      +0x4c8: tbl     v3.16b, {v24.16b-v25.16b}, v0.16b
      +0x4cc: ldr     q0, [sp, #96]
      +0x4d0: mov     v17.s[1], v6.s[1]
      +0x4d4: mov     v21.s[1], v20.s[1]
      +0x4d8: ushr    v20.4s, v0.4s, #24
      +0x4dc: ldr     q0, [sp, #112]
      +0x4e0: mov     v4.s[1], v3.s[1]
      +0x4e4: ushr    v24.4s, v31.4s, #24
      +0x4e8: sxtl    v6.4s, v17.4h
      +0x4ec: sxtl    v17.4s, v21.4h
      +0x4f0: ushr    v21.4s, v0.4s, #24
      +0x4f4: ldp     q5, q0, [sp, #32]
      +0x4f8: movi    v3.4s, #0x8, lsl #24
      +0x4fc: ushr    v25.4s, v15.4s, #24
      +0x500: sxtl    v16.4s, v16.4h
      +0x504: sxtl    v4.4s, v4.4h
      +0x508: uzp1    v20.8h, v21.8h, v20.8h
      +0x50c: mla     v3.4s, v16.4s, v26.4s
      +0x510: ushr    v22.4s, v0.4s, #24
      +0x514: ldr     q0, [sp, #80]
      +0x518: movi    v16.4s, #0x8, lsl #24
      +0x51c: ushr    v1.4s, v1.4s, #24
      +0x520: ushr    v19.4s, v19.4s, #24
      +0x524: ushr    v23.4s, v0.4s, #24
      +0x528: ushr    v3.4s, v3.4s, #24
      +0x52c: movi    v0.16b, #0xf0
      +0x530: uzp1    v21.8h, v23.8h, v22.8h
      +0x534: mla     v16.4s, v4.4s, v26.4s
      +0x538: movi    v4.4s, #0x8, lsl #24
      +0x53c: movi    v22.4s, #0x8, lsl #24
      +0x540: uzp1    v20.16b, v21.16b, v20.16b
      +0x544: ushr    v21.4s, v12.4s, #24
      +0x548: mla     v4.4s, v6.4s, v26.4s
      +0x54c: ushr    v23.4s, v5.4s, #24
      +0x550: mla     v22.4s, v17.4s, v26.4s
      +0x554: ldr     q5, [sp, #128]
      +0x558: and     v6.16b, v20.16b, v0.16b
      +0x55c: ushr    v20.4s, v29.4s, #24
      +0x560: uzp1    v21.8h, v23.8h, v21.8h
      +0x564: ushr    v16.4s, v16.4s, #24
      +0x568: uzp1    v23.8h, v25.8h, v24.8h
      +0x56c: uzp1    v1.8h, v18.8h, v1.8h
      +0x570: uzp1    v18.8h, v19.8h, v20.8h
      +0x574: ushr    v19.4s, v22.4s, #24
      +0x578: ushr    v4.4s, v4.4s, #24
      +0x57c: uzp1    v3.8h, v3.8h, v16.8h
      +0x580: uzp1    v4.8h, v4.8h, v19.8h
      +0x584: uzp1    v17.16b, v23.16b, v21.16b
      +0x588: uzp1    v1.16b, v18.16b, v1.16b
      +0x58c: orr     v19.16b, v6.16b, v5.16b
      +0x590: uzp1    v3.16b, v4.16b, v3.16b
      +0x594: ldr     q4, [sp, #64]
      +0x598: and     v6.16b, v17.16b, v0.16b
      +0x59c: and     v1.16b, v1.16b, v0.16b
      +0x5a0: orr     v20.16b, v6.16b, v4.16b
      +0x5a4: ldr     q4, [sp, #16]
      +0x5a8: movi    v5.4s, #0x8, lsl #24
      +0x5ac: orr     v21.16b, v1.16b, v4.16b
      +0x5b0: and     v1.16b, v3.16b, v0.16b
      +0x5b4: orr     v22.16b, v1.16b, v2.16b
      +0x5b8: st4     {v19.16b-v22.16b}, [x0], #64
      +0x5bc: ldp     q20, q21, [x1, #416]
      +0x5c0: ldp     q22, q23, [x1, #480]
      +0x5c4: zip1    v1.4h, v20.4h, v21.4h
      +0x5c8: ext     v6.8b, v20.8b, v1.8b, #4
      +0x5cc: ldp     q16, q17, [x1, #288]
      +0x5d0: zip1    v2.4h, v22.4h, v23.4h
      +0x5d4: ext     v9.8b, v22.8b, v2.8b, #4
      +0x5d8: ldp     q18, q19, [x1, #352]
      +0x5dc: zip1    v3.4h, v16.4h, v17.4h
      +0x5e0: ext     v13.8b, v16.8b, v3.8b, #4
      +0x5e4: ldp     q10, q11, [x1, #448]
      +0x5e8: zip1    v4.4h, v18.4h, v19.4h
      +0x5ec: ext     v15.8b, v18.8b, v4.8b, #4
      +0x5f0: ldp     q30, q31, [x1, #384]
      +0x5f4: zip1    v12.4h, v10.4h, v11.4h
      +0x5f8: mov     v12.s[1], v9.s[1]
      +0x5fc: ldp     q24, q25, [x1, #320]
      +0x600: zip1    v8.4h, v30.4h, v31.4h
      +0x604: movi    v9.4s, #0x8, lsl #24
      +0x608: sxtl    v12.4s, v12.4h
      +0x60c: mov     v8.s[1], v6.s[1]
      +0x610: ldp     q28, q29, [x1, #256]
      +0x614: zip1    v0.4h, v24.4h, v25.4h
      +0x618: movi    v6.4s, #0x8, lsl #24
      +0x61c: sxtl    v8.4s, v8.4h
      +0x620: mla     v9.4s, v12.4s, v26.4s
      +0x624: mov     v0.s[1], v15.s[1]
      +0x628: zip1    v14.4h, v28.4h, v29.4h
      +0x62c: mla     v6.4s, v8.4s, v26.4s
      +0x630: movi    v8.4s, #0x8, lsl #24
      +0x634: movi    v12.4s, #0x8, lsl #24
      +0x638: mov     v14.s[1], v13.s[1]
      +0x63c: sxtl    v0.4s, v0.4h
      +0x640: ushr    v6.4s, v6.4s, #28
      +0x644: mla     v12.4s, v0.4s, v26.4s
      +0x648: ushr    v0.4s, v9.4s, #28
      +0x64c: sxtl    v13.4s, v14.4h
      +0x650: trn2    v9.4h, v30.4h, v31.4h
      +0x654: mla     v8.4s, v13.4s, v26.4s
      +0x658: zip2    v13.4h, v24.4h, v25.4h
      +0x65c: ushr    v12.4s, v12.4s, #28
      +0x660: uzp1    v0.8h, v6.8h, v0.8h
      +0x664: mov     v9.s[1], v1.s[1]
      +0x668: ushr    v8.4s, v8.4s, #28
      +0x66c: trn2    v1.4h, v28.4h, v29.4h
      +0x670: uzp1    v6.8h, v8.8h, v12.8h
      +0x674: trn2    v8.4h, v10.4h, v11.4h
      +0x678: mov     v14.16b, v18.16b
      +0x67c: zip2    v12.4h, v28.4h, v29.4h
      +0x680: mov     v1.s[1], v3.s[1]
      +0x684: uzp1    v0.16b, v6.16b, v0.16b
      +0x688: mov     v8.s[1], v2.s[1]
      +0x68c: trn2    v2.4h, v24.4h, v25.4h
      +0x690: movi    v6.4s, #0x8, lsl #24
      +0x694: str     q0, [sp, #128]
      +0x698: sxtl    v0.4s, v9.4h
      +0x69c: zip2    v9.4h, v10.4h, v11.4h
      +0x6a0: sxtl    v3.4s, v8.4h
      +0x6a4: mov     v2.s[1], v4.s[1]
      +0x6a8: mov     v4.16b, v20.16b
      +0x6ac: mla     v5.4s, v0.4s, v26.4s
      +0x6b0: mov     v0.16b, v22.16b
      +0x6b4: mla     v6.4s, v3.4s, v26.4s
      +0x6b8: mov     v4.h[3], v21.h[2]
      +0x6bc: mov     v0.h[3], v23.h[2]
      +0x6c0: zip2    v8.4h, v30.4h, v31.4h
      +0x6c4: mov     v3.16b, v16.16b
      +0x6c8: stp     q6, q5, [sp, #96]
      +0x6cc: mov     v3.h[3], v17.h[2]
      +0x6d0: mov     v15.16b, v19.16b
      +0x6d4: mov     v6.16b, v14.16b
      +0x6d8: mov     v6.h[3], v15.h[2]
      +0x6dc: mov     v8.s[1], v4.s[1]
      +0x6e0: mov     v9.s[1], v0.s[1]
      +0x6e4: mov     v12.s[1], v3.s[1]
      +0x6e8: movi    v0.4s, #0x8, lsl #24
      +0x6ec: movi    v3.4s, #0x8, lsl #24
      +0x6f0: mov     v13.s[1], v6.s[1]
      +0x6f4: sxtl    v4.4s, v8.4h
      +0x6f8: sxtl    v6.4s, v9.4h
      +0x6fc: mla     v0.4s, v4.4s, v26.4s
      +0x700: mla     v3.4s, v6.4s, v26.4s
      +0x704: movi    v4.4s, #0x8, lsl #24
      +0x708: movi    v6.4s, #0x8, lsl #24
      +0x70c: sxtl    v8.4s, v12.4h
      +0x710: sxtl    v9.4s, v13.4h
      +0x714: mla     v4.4s, v8.4s, v26.4s
      +0x718: mla     v6.4s, v9.4s, v26.4s
      +0x71c: movi    v5.4s, #0x8, lsl #24
      +0x720: sxtl    v1.4s, v1.4h
      +0x724: ushr    v3.4s, v3.4s, #28
      +0x728: ushr    v0.4s, v0.4s, #28
      +0x72c: zip2    v12.4h, v16.4h, v17.4h
      +0x730: mla     v5.4s, v1.4s, v26.4s
      +0x734: ushr    v1.4s, v6.4s, #28
      +0x738: uzp1    v0.8h, v0.8h, v3.8h
      +0x73c: ushr    v3.4s, v4.4s, #28
      +0x740: movi    v4.4s, #0x8, lsl #24
      +0x744: zip2    v13.4h, v14.4h, v15.4h
      +0x748: uzp1    v1.8h, v3.8h, v1.8h
      +0x74c: sxtl    v2.4s, v2.4h
      +0x750: uzp2    v3.4h, v10.4h, v11.4h
      +0x754: mla     v4.4s, v2.4s, v26.4s
      +0x758: uzp2    v2.4h, v30.4h, v31.4h
      +0x75c: uzp1    v0.16b, v1.16b, v0.16b
      +0x760: uzp2    v1.4h, v24.4h, v25.4h
      +0x764: uzp2    v3.4h, v3.4h, v10.4h
      +0x768: zip2    v8.4h, v22.4h, v23.4h
      +0x76c: str     q4, [sp, #48]
      +0x770: uzp2    v2.4h, v2.4h, v30.4h
      +0x774: stp     q0, q5, [sp, #64]
      +0x778: uzp2    v0.4h, v28.4h, v29.4h
      +0x77c: zip2    v4.4h, v20.4h, v21.4h
      +0x780: uzp2    v1.4h, v1.4h, v24.4h
      +0x784: mov     v3.s[1], v8.s[1]
      +0x788: movi    v9.4s, #0x8, lsl #24
      +0x78c: uzp2    v0.4h, v0.4h, v28.4h
      +0x790: mov     v2.s[1], v4.s[1]
      +0x794: movi    v4.4s, #0x8, lsl #24
      +0x798: mov     v1.s[1], v13.s[1]
      +0x79c: mov     v0.s[1], v12.s[1]
      +0x7a0: sxtl    v2.4s, v2.4h
      +0x7a4: movi    v5.4s, #0x8, lsl #24
      +0x7a8: mla     v4.4s, v2.4s, v26.4s
      +0x7ac: movi    v2.4s, #0x8, lsl #24
      +0x7b0: sxtl    v0.4s, v0.4h
      +0x7b4: sxtl    v1.4s, v1.4h
      +0x7b8: sxtl    v3.4s, v3.4h
      +0x7bc: mla     v2.4s, v0.4s, v26.4s
      +0x7c0: mla     v9.4s, v1.4s, v26.4s
      +0x7c4: ldp     q0, q1, [sp, #144]
      +0x7c8: mla     v5.4s, v3.4s, v26.4s
      +0x7cc: str     q2, [sp]
      +0x7d0: zip2    v8.8h, v30.8h, v31.8h
      +0x7d4: tbl     v27.16b, {v30.16b-v31.16b}, v0.16b
      +0x7d8: stp     q5, q4, [sp, #16]
      +0x7dc: ldr     q2, [sp, #208]
      +0x7e0: tbl     v18.16b, {v30.16b-v31.16b}, v1.16b
      +0x7e4: tbl     v5.16b, {v30.16b-v31.16b}, v7.16b
      +0x7e8: zip2    v30.8h, v10.8h, v11.8h
      +0x7ec: tbl     v31.16b, {v10.16b-v11.16b}, v0.16b
      +0x7f0: tbl     v12.16b, {v10.16b-v11.16b}, v1.16b
      +0x7f4: tbl     v10.16b, {v10.16b-v11.16b}, v7.16b
      +0x7f8: zip2    v11.8h, v28.8h, v29.8h
      +0x7fc: tbl     v13.16b, {v28.16b-v29.16b}, v0.16b
      +0x800: tbl     v4.16b, {v28.16b-v29.16b}, v1.16b
      +0x804: tbl     v28.16b, {v28.16b-v29.16b}, v7.16b
      +0x808: tbl     v29.16b, {v24.16b-v25.16b}, v0.16b
      +0x80c: tbl     v0.16b, {v22.16b-v23.16b}, v2.16b
      +0x810: tbl     v3.16b, {v24.16b-v25.16b}, v1.16b
      +0x814: tbl     v7.16b, {v24.16b-v25.16b}, v7.16b
      +0x818: zip2    v24.8h, v24.8h, v25.8h
      +0x81c: tbl     v25.16b, {v20.16b-v21.16b}, v2.16b
      +0x820: tbl     v1.16b, {v16.16b-v17.16b}, v2.16b
      +0x824: tbl     v2.16b, {v14.16b-v15.16b}, v2.16b
      +0x828: mov     v30.s[1], v0.s[1]
      +0x82c: mov     v8.s[1], v25.s[1]
      +0x830: mov     v11.s[1], v1.s[1]
      +0x834: movi    v1.4s, #0x8, lsl #24
      +0x838: mov     v24.s[1], v2.s[1]
      +0x83c: movi    v0.4s, #0x8, lsl #24
      +0x840: sxtl    v25.4s, v30.4h
      +0x844: sxtl    v2.4s, v8.4h
      +0x848: mla     v1.4s, v25.4s, v26.4s
      +0x84c: movi    v25.4s, #0x8, lsl #24
      +0x850: ldp     q19, q6, [sp, #176]
      +0x854: mla     v0.4s, v2.4s, v26.4s
      +0x858: movi    v2.4s, #0x8, lsl #24
      +0x85c: sxtl    v24.4s, v24.4h
      +0x860: sxtl    v30.4s, v11.4h
      +0x864: mla     v25.4s, v24.4s, v26.4s
      +0x868: zip2    v24.8h, v20.8h, v21.8h
      +0x86c: mla     v2.4s, v30.4s, v26.4s
      +0x870: tbl     v30.16b, {v20.16b-v21.16b}, v6.16b
      +0x874: tbl     v20.16b, {v20.16b-v21.16b}, v19.16b
      +0x878: zip2    v21.8h, v22.8h, v23.8h
      +0x87c: tbl     v8.16b, {v22.16b-v23.16b}, v6.16b
      +0x880: tbl     v22.16b, {v22.16b-v23.16b}, v19.16b
      +0x884: zip2    v23.8h, v16.8h, v17.8h
      +0x888: tbl     v11.16b, {v16.16b-v17.16b}, v6.16b
      +0x88c: tbl     v16.16b, {v16.16b-v17.16b}, v19.16b
      +0x890: tbl     v17.16b, {v14.16b-v15.16b}, v6.16b
      +0x894: tbl     v6.16b, {v14.16b-v15.16b}, v19.16b
      +0x898: zip2    v19.8h, v14.8h, v15.8h
      +0x89c: mov     v27.s[1], v24.s[1]
      +0x8a0: mov     v31.s[1], v21.s[1]
      +0x8a4: mov     v13.s[1], v23.s[1]
      +0x8a8: mov     v29.s[1], v19.s[1]
      +0x8ac: movi    v19.4s, #0x8, lsl #24
      +0x8b0: movi    v21.4s, #0x8, lsl #24
      +0x8b4: sxtl    v23.4s, v27.4h
      +0x8b8: sxtl    v24.4s, v31.4h
      +0x8bc: mla     v19.4s, v23.4s, v26.4s
      +0x8c0: movi    v23.4s, #0x8, lsl #24
      +0x8c4: mla     v21.4s, v24.4s, v26.4s
      +0x8c8: movi    v24.4s, #0x8, lsl #24
      +0x8cc: sxtl    v27.4s, v13.4h
      +0x8d0: mov     v12.s[1], v8.s[1]
      +0x8d4: sxtl    v29.4s, v29.4h
      +0x8d8: mla     v23.4s, v27.4s, v26.4s
      +0x8dc: mov     v18.s[1], v30.s[1]
      +0x8e0: ldr     q30, [sp]
      +0x8e4: movi    v27.4s, #0x8, lsl #24
      +0x8e8: mla     v24.4s, v29.4s, v26.4s
      +0x8ec: mov     v3.s[1], v17.s[1]
      +0x8f0: movi    v17.4s, #0x8, lsl #24
      +0x8f4: sxtl    v29.4s, v12.4h
      +0x8f8: mov     v4.s[1], v11.s[1]
      +0x8fc: sxtl    v18.4s, v18.4h
      +0x900: mla     v27.4s, v29.4s, v26.4s
      +0x904: movi    v29.4s, #0x8, lsl #24
      +0x908: mla     v17.4s, v18.4s, v26.4s
      +0x90c: movi    v18.4s, #0x8, lsl #24
      +0x910: sxtl    v3.4s, v3.4h
      +0x914: mov     v5.s[1], v20.s[1]
      +0x918: ldr     q20, [sp, #48]
      +0x91c: sxtl    v4.4s, v4.4h
      +0x920: mla     v29.4s, v3.4s, v26.4s
      +0x924: movi    v3.4s, #0x8, lsl #24
      +0x928: mla     v18.4s, v4.4s, v26.4s
      +0x92c: mov     v10.s[1], v22.s[1]
      +0x930: ldr     q22, [sp, #80]
      +0x934: mov     v28.s[1], v16.s[1]
      +0x938: sxtl    v4.4s, v5.4h
      +0x93c: movi    v5.4s, #0x8, lsl #24
      +0x940: mla     v3.4s, v4.4s, v26.4s
      +0x944: movi    v4.4s, #0x8, lsl #24
      +0x948: mov     v7.s[1], v6.s[1]
      +0x94c: sxtl    v6.4s, v10.4h
      +0x950: sxtl    v16.4s, v28.4h
      +0x954: mla     v4.4s, v6.4s, v26.4s
      +0x958: mla     v5.4s, v16.4s, v26.4s
      +0x95c: ldp     q6, q16, [sp, #96]
      +0x960: ushr    v20.4s, v20.4s, #24
      +0x964: ushr    v22.4s, v22.4s, #24
      +0x968: ushr    v28.4s, v9.4s, #24
      +0x96c: ushr    v30.4s, v30.4s, #24
      +0x970: sxtl    v7.4s, v7.4h
      +0x974: ushr    v1.4s, v1.4s, #28
      +0x978: ushr    v6.4s, v6.4s, #24
      +0x97c: ushr    v0.4s, v0.4s, #28
      +0x980: ushr    v2.4s, v2.4s, #28
      +0x984: ushr    v16.4s, v16.4s, #24
      +0x988: ushr    v19.4s, v19.4s, #24
      +0x98c: uzp1    v0.8h, v0.8h, v1.8h
      +0x990: ushr    v4.4s, v4.4s, #24
      +0x994: uzp1    v6.8h, v16.8h, v6.8h
      +0x998: uzp1    v16.8h, v22.8h, v20.8h
      +0x99c: ldp     q20, q22, [sp, #16]
      +0x9a0: ushr    v3.4s, v3.4s, #24
      +0x9a4: ushr    v5.4s, v5.4s, #24
      +0x9a8: ushr    v18.4s, v18.4s, #28
      +0x9ac: uzp1    v6.16b, v16.16b, v6.16b
      +0x9b0: ushr    v20.4s, v20.4s, #24
      +0x9b4: uzp1    v3.8h, v3.8h, v4.8h
      +0x9b8: ushr    v22.4s, v22.4s, #24
      +0x9bc: uzp1    v20.8h, v22.8h, v20.8h
      +0x9c0: uzp1    v22.8h, v30.8h, v28.8h
      +0x9c4: movi    v28.4s, #0x8, lsl #24
      +0x9c8: uzp1    v16.16b, v22.16b, v20.16b
      +0x9cc: ldr     q22, [sp, #64]
      +0x9d0: movi    v20.16b, #0xf0
      +0x9d4: mla     v28.4s, v7.4s, v26.4s
      +0x9d8: ldr     q7, [sp, #128]
      +0x9dc: and     v6.16b, v6.16b, v20.16b
      +0x9e0: orr     v6.16b, v6.16b, v7.16b
      +0x9e4: and     v16.16b, v16.16b, v20.16b
      +0x9e8: orr     v7.16b, v16.16b, v22.16b
      +0x9ec: ushr    v16.4s, v25.4s, #28
      +0x9f0: ushr    v4.4s, v28.4s, #24
      +0x9f4: uzp1    v1.8h, v2.8h, v16.8h
      +0x9f8: ushr    v2.4s, v27.4s, #28
      +0x9fc: ushr    v16.4s, v17.4s, #28
      +0xa00: ushr    v17.4s, v21.4s, #24
      +0xa04: uzp1    v2.8h, v16.8h, v2.8h
      +0xa08: uzp1    v16.8h, v19.8h, v17.8h
      +0xa0c: ushr    v17.4s, v24.4s, #24
      +0xa10: ushr    v19.4s, v23.4s, #24
      +0xa14: uzp1    v4.8h, v5.8h, v4.8h
      +0xa18: uzp1    v17.8h, v19.8h, v17.8h
      +0xa1c: ushr    v19.4s, v29.4s, #28
      +0xa20: uzp1    v0.16b, v1.16b, v0.16b
      +0xa24: uzp1    v5.8h, v18.8h, v19.8h
      +0xa28: uzp1    v16.16b, v17.16b, v16.16b
      +0xa2c: uzp1    v1.16b, v4.16b, v3.16b
      +0xa30: uzp1    v2.16b, v5.16b, v2.16b
      +0xa34: and     v3.16b, v16.16b, v20.16b
      +0xa38: orr     v8.16b, v3.16b, v0.16b
      +0xa3c: and     v0.16b, v1.16b, v20.16b
      +0xa40: orr     v9.16b, v0.16b, v2.16b
      +0xa44: st4     {v6.16b-v9.16b}, [x0]
      +0xa48: ldp     d9, d8, [sp, #272]
      +0xa4c: ldp     d11, d10, [sp, #256]
      +0xa50: ldp     d13, d12, [sp, #240]
      +0xa54: ldp     d15, d14, [sp, #224]
      +0xa58: ldr     x29, [sp, #288]
      +0xa5c: add     sp, sp, #0x130
      +0xa60: ret
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_compress_d4"];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to 4 bits, as computed in a 32-bit lane  *)
(* (COMPRESS_D4_ARITH is that of gcc12_O2), and the 128 bytes of the result  *)
(* from the pairs of 4-bit values in them.                                   *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D4_ARITH_STMT =
  `!v. v < 3329
       ==> (134217728 + v * 1290160) DIV 268435456 =
           (32 * v + 3329) DIV 6658`;;

let COMPRESS_D4_ARITH = assume_spec COMPRESS_D4_ARITH_STMT;;

let COMPRESS_D4_LANE_STMT =
  `!y:int16.
        val y < 3329
        ==> word_subword (word_add (word 134217728)
                                   (word_mul (word_sx y) (word 1290160)):int32)
                         (28,4):4 word =
            word((32 * val y + 3329) DIV 6658)`;;

let COMPRESS_D4_LANE = assume_spec COMPRESS_D4_LANE_STMT;;

let COMPRESS_D4_PACK_STMT =
  `!r s (c:num->num).
     (!m. m < 128
          ==> read (memory :> bytes8 (word_add r (word m))) s =
              word_join (word(c(2 * m + 1)):4 word) (word(c(2 * m)):4 word))
     ==> read (memory :> bytes(r,128)) s =
         nsum {i | i < 256} (\i. c i MOD 16 * 2 EXP (4 * i))`;;

let COMPRESS_D4_PACK = assume_spec COMPRESS_D4_PACK_STMT;;

(*** The 256 coefficients, merged into the 128-bit parts that the loads
 *** read ***)

let COMPRESS_D4_MERGES = map (fun k ->
  let addr = if k = 0 then `a:int64` else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`a:int64`),
            mk_comb(`word:num->int64`, mk_small_numeral(16 * k))) in
  READ_MEMORY_MERGE_CONV 3
   (vsubst [addr,`x:int64`] `read (memory :> bytes128 x) s0`)) (0--31);;

let COMPRESS_D4_INPUT_TAC =
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_forall(concl th) && free_in `x:num->int16` (concl th))) THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  MAP_EVERY MP_TAC COMPRESS_D4_MERGES THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`];;

(*** The six vectors of byte indices for TBL ***)

let MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O3_CONSTANTS =
  map (fun k ->
    MLKEM_NATIVE_IMAGE_CONST_RULE
     (layout("mlkem_poly_compress_d4_const" ^ string_of_int k)) 128) (1--6);;

let COMPRESS_D4_CONSTANTS_TAC =
  MAP_EVERY (fun th -> FIRST_ASSUM(fun ath ->
      if can (term_match [] `aligned_bytes_loaded s0 (word pc)
                               mlkem_native_libmlkem_clang17_O3_mc`)
             (concl ath)
      then ASSUME_TAC(MATCH_MP th ath) else failwith ""))
    MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O3_CONSTANTS;;

(* ------------------------------------------------------------------------- *)
(* The check for overlap has one branch for each order of the arrays: with   *)
(* the input a (512 bytes) and the output r (128 bytes), the scalar loop is  *)
(* taken unless a + 512 <= r or r + 128 <= a. In either case the vector code *)
(* is entered at the same instruction, after 3 or 6 steps (after the 6 steps *)
(* of the prologue) respectively.                                            *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D4_RESOLVE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_FLAG; VAL_WORD_SUB_EQ_0]) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read PC s = if p then x else y`) c then
      let p = rand(rator(rator(rand c))) in
      let decide q = SUBGOAL_THEN q (fun th' ->
        ASSUME_TAC(REWRITE_RULE[th'] th)) THENL [ASM_ARITH_TAC; ALL_TAC] in
      decide p ORELSE decide (mk_neg p)
    else failwith "COMPRESS_D4_RESOLVE_TAC");;

let COMPRESS_D4_CHECK_TAC (body:int->tactic) =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O3_EXEC (1--6) THEN
  MP_TAC(SPECL [`r:int64`; `a:int64`; `128`; `512`]
                NONOVERLAPPING_ALIAS_CHECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O3_EXEC (7--9) THEN
  ASM_CASES_TAC `val(word_add a (word 512):int64) <= val(r:int64)` THENL
   [COMPRESS_D4_RESOLVE_TAC THEN body 9;
    COMPRESS_D4_RESOLVE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O3_EXEC (10--12) THEN
    COMPRESS_D4_RESOLVE_TAC THEN body 12];;

(*** The vector code from join1 on: 613 steps and the return ***)

let COMPRESS_D4_BODY_TAC (simp:tactic) off =
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O3_EXEC [k + off] THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    simp) (1--614);;

(*** The restored D registers, as zero extensions of the 64 bits saved ***)

let COMPRESS_D4_DREG_STMT =
  `!x:int64. word_zx(word_zx x:int128):int64 = x`;;

let COMPRESS_D4_DREG = assume_spec COMPRESS_D4_DREG_STMT;;

(*** The lanes of the multiply-accumulates in the stores come out of the
 *** simulation with the 16-bit operand of the SXTL as a join of the bytes
 *** of coefficients (EXT works on bytes); find which coefficient x k it is
 *** by bit-blasting and replace it by x k ***)

let COMPRESS_D4_NORMALIZE_LANES lanepat th =
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

let COMPRESS_D4_SIMPLIFY_CONV =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC REWR_CONV WORD_SUBWORD_OR ORELSEC
    WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV;;

let COMPRESS_D4_SIMD_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> match t with
              Const(("word_subdeinterleave"|"word_interleave"),_) -> true
            | _ -> false)) (concl th)
    then CONV_RULE(RAND_CONV COMPRESS_D4_SIMPLIFY_CONV)
          (CONV_RULE(TOP_DEPTH_CONV MLKEM_NATIVE_INTERLEAVE_CONV) th)
    else th) THEN
  SIMD_SIMPLIFY_TAC[];;

(*** After the simulation, the subwords of the stores taken through AND and
 *** OR to the lanes ***)


(*** Each stored byte as the bits 28 to 31 of the two lanes for it, found
 *** by bit-blasting with the lanes, multiply-accumulates, as variables ***)

let compress_d4_lanepat =
  `word_add (word 134217728)
            (word_mul (word_shl (word_sx (y:int16)) 0) (word 1290160)):int32`;;

let COMPRESS_D4_BYTE_RULE th =
  let v = rand(concl th) in
  let ms = setify(find_terms (can (term_match [] compress_d4_lanepat)) v) in
  let idx m = dest_small_numeral(rand(find_term
    (fun t -> is_comb t && rator t = `x:num->int16`) m)) in
  let ims = sort (fun (i,_) (j,_) -> i < j) (map (fun m -> idx m,m) ms) in
  if length ims <> 2 then
    (print_term v; Format.print_newline();
     failwith "COMPRESS_D4_BYTE_RULE") else
  let gs = map (fun _ -> genvar `:int32`) ims in
  let v' = subst (zip gs (map snd ims)) v in
  let nib g = mk_comb(mk_comb(`word_subword:int32->num#num->4 word`,g),
                      `(28,4)`) in
  let tgt = mk_comb(mk_comb(`word_join:4 word->4 word->byte`,
                            nib(el 1 gs)),nib(el 0 gs)) in
  let bth = BITBLAST_RULE(mk_eq(v',tgt)) in
  CONV_RULE(RAND_CONV(REWRITE_CONV[WORD_SHL_ZERO]))
   (TRANS th (INST (zip (map snd ims) gs) bth));;

(*** The stored bytes, from the 8 stores of 16 bytes ***)

let COMPRESS_D4_STORES_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
    check (fun th -> can (term_match []
                     `read (memory :> bytes128 a) s = x`) (concl th) &&
                     free_in `r:int64` (concl th)))) THEN
  REPEAT(DISCH_THEN(fun th ->
    MAP_EVERY (ASSUME_TAC o COMPRESS_D4_BYTE_RULE o
        COMPRESS_D4_NORMALIZE_LANES compress_d4_lanepat o
      CONV_RULE(RAND_CONV COMPRESS_D4_SIMPLIFY_CONV) o
      CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD;
                                       WORD_ADD_0]
                          THENC NUM_REDUCE_CONV)))
     (CONJUNCTS th)));;

(*** The 4-bit value of each coefficient, given the bounds ***)

let COMPRESS_D4_NIBBLES_TAC =
  DISCH_THEN(fun bth ->
    let lths = map (fun k ->
      let kt = mk_small_numeral k in
      MP (SPEC (mk_comb(`x:num->int16`,kt)) COMPRESS_D4_LANE)
         (MP (SPEC kt bth)
             (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool` kt
                                            `256`))))) (0--255) in
    RULE_ASSUM_TAC(REWRITE_RULE lths));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_compress 4 in common/fips203.ml, the      *)
(* result for a coefficient x in [0,3329) is the integer closest to          *)
(* 16 * x / 3329, rounding up on ties, modulo 16, i.e.                       *)
(* ((32 * x + 3329) DIV 6658) MOD 16, and as for mlkem_encode 4 the 4-bit    *)
(* values are put together little-endian. Like the C code, this relies on    *)
(* the coefficients being in [0,3329).                                       *)
(* ------------------------------------------------------------------------- *)


let MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,128); (a,512); (word_sub stackpointer (word 304),304)] /\
        ALLPAIRS nonoverlapping
         [(r,128); (word_sub stackpointer (word 304),304)]
         [(word pc,libmlkem_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_poly_compress_d4) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes16
                                     (word_add a (word(2 * i)))) s =
                           x i))
             (\s. read PC s = returnaddress /\
                  ((!i. i < 256 ==> val(x i) < 3329)
                   ==> read(memory :> bytes(r,128)) s =
                       nsum {i | i < 256}
                            (\i. ((32 * val(x i) + 3329) DIV 6658) MOD 16 *
                                 2 EXP (4 * i))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,128);
                         memory :> bytes(word_sub stackpointer
                                                  (word 304),304)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. This is stated directly rather     *)
(* than by mk_safety_spec, as for gcc12_O2, with the events depending on the *)
(* stack frame. Unlike at -O2, the code reads six vectors of constants and   *)
(* there is no stack guard.                                                  *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e r a pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,128; a,512; word_sub stackpointer (word 304),304] /\
       ALLPAIRS nonoverlapping
        [r,128; word_sub stackpointer (word 304),304]
        [word pc,libmlkem_size]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_clang17_O3_mc /\
                 read PC s = word (pc + mlkem_poly_compress_d4) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [r; a] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a r pc
                           (word_sub stackpointer (word 304)) returnaddress /\
                    memaccess_inbounds e2
                     [a,512; r,128; word_sub stackpointer (word 304),304;
                      word(pc + mlkem_poly_compress_d4_consts),
                      mlkem_poly_compress_d4_consts_size]
                     [r,128; word_sub stackpointer (word 304),304]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,128);
                        memory :> bytes(word_sub stackpointer (word 304),
                                        304)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
