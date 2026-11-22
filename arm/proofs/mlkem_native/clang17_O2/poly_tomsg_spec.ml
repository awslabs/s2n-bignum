(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Conversion of a polynomial to a 32-byte message, one bit per coefficient. *)
(* This is the code for mlkem_poly_tomsg from mlkem-native's portable C      *)
(* implementation compiled by clang 17 with -O2 (see mlkem_native/README.md).*)
(* It is verified in the whole image (see libmlkem.ml).                      *)
(*                                                                           *)
(* The compiler has vectorized the loop, with 32-bit lanes, after a check    *)
(* that the input and the output do not overlap, with one branch for each of *)
(* the two orders of the arrays; if they overlap, the code falls back to a   *)
(* scalar loop (loop1, one byte of the message per iteration). Since the     *)
(* specification requires them not to overlap, only the vector loop (loop2)  *)
(* runs. It has two iterations of 128 coefficients each: it computes one     *)
(* bit per coefficient in 32-bit lanes, gathers the bits for each byte with  *)
(* TBL on a four-register table, masks them into place, and writes 16 bytes  *)
(* of the message (after writing 16 zero bytes to the same place at the      *)
(* start of the iteration). The code saves D8 to D15 and X29 and spills      *)
(* vectors to the stack, all in a frame of 480 bytes, which the              *)
(* specifications therefore have (gcc12_O2 has none). It reads seven vectors *)
(* of byte indices for TBL from the read-only data; they are the same as     *)
(* those of mlkem_poly_compress_d4.                                          *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/overlap.ml";;
needs "arm/proofs/mlkem_native/interleave.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/libmlkem.ml";;

(*** The code in the image (the labels are those of layout.ml):

    mlkem_poly_tomsg:
     +0x0: sub     sp, sp, #0x1e0
     +0x4: stp     d15, d14, [sp, #400]
     +0x8: stp     d13, d12, [sp, #416]
     +0xc: stp     d11, d10, [sp, #432]
    +0x10: stp     d9, d8, [sp, #448]
    +0x14: str     x29, [sp, #464]
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
  loop1:
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
  loop1_test:
    +0xf0: cmp     x8, #0x20
  loop1_back:
    +0xf4: b.ne    loop1
  loop1_exit:
    +0xf8: b       join2
  join1:
    +0xfc: adrp    x9, <page>
   +0x100: adrp    x10, <page>
   +0x104: mov     x8, xzr
   +0x108: ldr     q0, [x9, #3168]
                  // mlkem_poly_compress_d4_const1
   +0x10c: adrp    x9, <page>
   +0x110: str     q0, [sp, #256]
   +0x114: ldr     q0, [x10, #3184]
                  // mlkem_poly_compress_d4_const2
   +0x118: adrp    x10, <page>
   +0x11c: str     q0, [sp, #80]
   +0x120: ldr     q0, [x9, #3200]
                  // mlkem_poly_compress_d4_const3
   +0x124: mov     w9, #0xafb8
   +0x128: movk    w9, #0x13, lsl #16
   +0x12c: str     q0, [sp, #64]
   +0x130: ldr     q0, [x10, #3216]
                  // mlkem_poly_compress_d4_const4
   +0x134: adrp    x10, <page>
   +0x138: dup     v12.4s, w9
   +0x13c: str     q0, [sp, #48]
   +0x140: ldr     q0, [x10, #3232]
                  // mlkem_poly_compress_d4_const5
   +0x144: adrp    x10, <page>
   +0x148: str     q0, [sp, #32]
   +0x14c: ldr     q0, [x10, #3248]
                  // mlkem_poly_compress_d4_const6
   +0x150: adrp    x10, <page>
   +0x154: str     q0, [sp, #16]
   +0x158: ldr     q0, [x10, #3264]
                  // mlkem_poly_compress_d4_const7
   +0x15c: str     q0, [sp]
  loop2:
   +0x160: movi    v0.2d, #0x0
   +0x164: add     x9, sp, #0x130
   +0x168: str     q0, [x0, x8]
   +0x16c: ldp     q0, q1, [x1, #128]
   +0x170: mov     v5.16b, v0.16b
   +0x174: mov     v31.16b, v5.16b
   +0x178: ldp     q16, q17, [x1, #32]
   +0x17c: mov     v6.16b, v1.16b
   +0x180: zip1    v20.4h, v5.4h, v6.4h
   +0x184: mov     v27.16b, v16.16b
   +0x188: ldp     q25, q26, [x1]
   +0x18c: zip1    v4.4h, v16.4h, v17.4h
   +0x190: mov     v28.16b, v17.16b
   +0x194: ext     v2.8b, v16.8b, v4.8b, #4
   +0x198: ldp     q23, q24, [x1, #224]
   +0x19c: st1     {v25.2d-v26.2d}, [x9]
   +0x1a0: add     x9, sp, #0xa0
   +0x1a4: zip1    v3.4h, v25.4h, v26.4h
   +0x1a8: movi    v16.4s, #0x40, lsl #24
   +0x1ac: ldp     q8, q9, [x1, #96]
   +0x1b0: zip1    v17.4h, v23.4h, v24.4h
   +0x1b4: mov     v3.s[1], v2.s[1]
   +0x1b8: ext     v21.8b, v23.8b, v17.8b, #4
   +0x1bc: ldp     q29, q30, [x1, #160]
   +0x1c0: zip1    v15.4h, v8.4h, v9.4h
   +0x1c4: sxtl    v3.4s, v3.4h
   +0x1c8: mla     v16.4s, v3.4s, v12.4s
   +0x1cc: ext     v2.8b, v8.8b, v15.8b, #4
   +0x1d0: ldp     q0, q1, [x1, #64]
   +0x1d4: zip1    v7.4h, v29.4h, v30.4h
   +0x1d8: mov     v13.16b, v0.16b
   +0x1dc: ext     v19.8b, v29.8b, v7.8b, #4
   +0x1e0: ldp     q10, q11, [x1, #192]
   +0x1e4: st1     {v0.2d-v1.2d}, [x9]
   +0x1e8: add     x9, sp, #0x150
   +0x1ec: zip1    v18.4h, v0.4h, v1.4h
   +0x1f0: add     x1, x1, #0x100
   +0x1f4: mov     v20.s[1], v19.s[1]
   +0x1f8: st1     {v5.2d-v6.2d}, [x9]
   +0x1fc: add     x9, sp, #0x170
   +0x200: movi    v19.4s, #0x40, lsl #24
   +0x204: zip1    v5.4h, v10.4h, v11.4h
   +0x208: mov     v18.s[1], v2.s[1]
   +0x20c: st1     {v29.2d-v30.2d}, [x9]
   +0x210: mov     v0.16b, v6.16b
   +0x214: add     x9, sp, #0x130
   +0x218: movi    v6.4s, #0x40, lsl #24
   +0x21c: mov     v5.s[1], v21.s[1]
   +0x220: movi    v21.4s, #0x40, lsl #24
   +0x224: mov     v14.16b, v1.16b
   +0x228: sxtl    v1.4s, v18.4h
   +0x22c: sxtl    v5.4s, v5.4h
   +0x230: trn2    v18.4h, v25.4h, v26.4h
   +0x234: ld1     {v25.2d-v26.2d}, [x9]
   +0x238: sxtl    v2.4s, v20.4h
   +0x23c: trn2    v20.4h, v31.4h, v0.4h
   +0x240: mla     v21.4s, v5.4s, v12.4s
   +0x244: add     x9, sp, #0xa0
   +0x248: mla     v19.4s, v2.4s, v12.4s
   +0x24c: mla     v6.4s, v1.4s, v12.4s
   +0x250: mov     v18.s[1], v4.s[1]
   +0x254: trn2    v4.4h, v10.4h, v11.4h
   +0x258: ushr    v3.4s, v21.4s, #31
   +0x25c: ldr     q21, [sp, #256]
   +0x260: ushr    v2.4s, v19.4s, #31
   +0x264: trn2    v22.4h, v13.4h, v14.4h
   +0x268: ushr    v1.4s, v6.4s, #31
   +0x26c: mov     v4.s[1], v17.s[1]
   +0x270: ushr    v0.4s, v16.4s, #31
   +0x274: mov     v20.s[1], v7.s[1]
   +0x278: tbl     v0.16b, {v0.16b-v3.16b}, v21.16b
   +0x27c: movi    v3.4s, #0x40, lsl #24
   +0x280: sxtl    v1.4s, v4.4h
   +0x284: mov     v22.s[1], v15.s[1]
   +0x288: mov     v13.16b, v27.16b
   +0x28c: str     q0, [sp, #240]
   +0x290: mla     v3.4s, v1.4s, v12.4s
   +0x294: mov     v14.16b, v28.16b
   +0x298: ld1     {v27.2d-v28.2d}, [x9]
   +0x29c: add     x9, sp, #0x150
   +0x2a0: movi    v7.4s, #0x40, lsl #24
   +0x2a4: sxtl    v5.4s, v18.4h
   +0x2a8: movi    v4.4s, #0x40, lsl #24
   +0x2ac: ushr    v19.4s, v3.4s, #30
   +0x2b0: mov     v3.16b, v29.16b
   +0x2b4: sxtl    v0.4s, v20.4h
   +0x2b8: mov     v3.h[3], v30.h[2]
   +0x2bc: ld1     {v29.2d-v30.2d}, [x9]
   +0x2c0: sxtl    v6.4s, v22.4h
   +0x2c4: add     x9, sp, #0x110
   +0x2c8: mla     v7.4s, v0.4s, v12.4s
   +0x2cc: mla     v4.4s, v6.4s, v12.4s
   +0x2d0: movi    v2.4s, #0x40, lsl #24
   +0x2d4: st1     {v8.2d-v9.2d}, [x9]
   +0x2d8: mov     v0.16b, v8.16b
   +0x2dc: add     x9, sp, #0x170
   +0x2e0: mov     v0.h[3], v9.h[2]
   +0x2e4: mov     v6.16b, v23.16b
   +0x2e8: ushr    v18.4s, v7.4s, #30
   +0x2ec: zip2    v7.4h, v27.4h, v28.4h
   +0x2f0: ushr    v17.4s, v4.4s, #30
   +0x2f4: mov     v1.16b, v13.16b
   +0x2f8: zip2    v4.4h, v29.4h, v30.4h
   +0x2fc: mov     v6.h[3], v24.h[2]
   +0x300: zip2    v20.4h, v10.4h, v11.4h
   +0x304: mla     v2.4s, v5.4s, v12.4s
   +0x308: zip2    v5.4h, v25.4h, v26.4h
   +0x30c: mov     v1.h[3], v14.h[2]
   +0x310: mov     v7.s[1], v0.s[1]
   +0x314: mov     v4.s[1], v3.s[1]
   +0x318: mov     v20.s[1], v6.s[1]
   +0x31c: mov     v5.s[1], v1.s[1]
   +0x320: movi    v6.4s, #0x40, lsl #24
   +0x324: sxtl    v1.4s, v7.4h
   +0x328: movi    v7.4s, #0x40, lsl #24
   +0x32c: sxtl    v3.4s, v4.4h
   +0x330: sxtl    v4.4s, v20.4h
   +0x334: movi    v20.4s, #0x40, lsl #24
   +0x338: sxtl    v0.4s, v5.4h
   +0x33c: movi    v5.4s, #0x40, lsl #24
   +0x340: mla     v6.4s, v4.4s, v12.4s
   +0x344: mla     v7.4s, v3.4s, v12.4s
   +0x348: mla     v20.4s, v1.4s, v12.4s
   +0x34c: mla     v5.4s, v0.4s, v12.4s
   +0x350: ushr    v16.4s, v2.4s, #30
   +0x354: ushr    v3.4s, v6.4s, #29
   +0x358: uzp2    v6.4h, v25.4h, v26.4h
   +0x35c: ushr    v2.4s, v7.4s, #29
   +0x360: ushr    v1.4s, v20.4s, #29
   +0x364: ushr    v0.4s, v5.4s, #29
   +0x368: zip2    v5.4h, v13.4h, v14.4h
   +0x36c: tbl     v4.16b, {v16.16b-v19.16b}, v21.16b
   +0x370: uzp2    v7.4h, v6.4h, v25.4h
   +0x374: tbl     v0.16b, {v0.16b-v3.16b}, v21.16b
   +0x378: mov     v18.16b, v27.16b
   +0x37c: mov     v19.16b, v28.16b
   +0x380: mov     v16.16b, v29.16b
   +0x384: stp     q0, q4, [sp, #208]
   +0x388: uzp2    v0.4h, v18.4h, v19.4h
   +0x38c: mov     v17.16b, v30.16b
   +0x390: ld1     {v29.2d-v30.2d}, [x9]
   +0x394: mov     v27.16b, v10.16b
   +0x398: add     x9, sp, #0x80
   +0x39c: mov     v28.16b, v11.16b
   +0x3a0: uzp2    v1.4h, v16.4h, v17.4h
   +0x3a4: uzp2    v2.4h, v27.4h, v28.4h
   +0x3a8: zip2    v3.4h, v8.4h, v9.4h
   +0x3ac: mov     v7.s[1], v5.s[1]
   +0x3b0: uzp2    v0.4h, v0.4h, v18.4h
   +0x3b4: movi    v4.4s, #0x40, lsl #24
   +0x3b8: st1     {v27.2d-v28.2d}, [x9]
   +0x3bc: uzp2    v1.4h, v1.4h, v16.4h
   +0x3c0: add     x9, sp, #0x150
   +0x3c4: zip2    v16.4h, v23.4h, v24.4h
   +0x3c8: uzp2    v2.4h, v2.4h, v27.4h
   +0x3cc: mov     v0.s[1], v3.s[1]
   +0x3d0: zip2    v5.4h, v29.4h, v30.4h
   +0x3d4: sxtl    v3.4s, v7.4h
   +0x3d8: movi    v17.4s, #0x40, lsl #24
   +0x3dc: mla     v4.4s, v3.4s, v12.4s
   +0x3e0: mov     v2.s[1], v16.s[1]
   +0x3e4: mov     v1.s[1], v5.s[1]
   +0x3e8: movi    v5.4s, #0x40, lsl #24
   +0x3ec: str     q4, [sp, #192]
   +0x3f0: ldr     q4, [sp, #80]
   +0x3f4: sxtl    v2.4s, v2.4h
   +0x3f8: movi    v3.4s, #0x40, lsl #24
   +0x3fc: sxtl    v0.4s, v0.4h
   +0x400: sxtl    v1.4s, v1.4h
   +0x404: mla     v5.4s, v2.4s, v12.4s
   +0x408: tbl     v2.16b, {v13.16b-v14.16b}, v4.16b
   +0x40c: zip2    v16.8h, v25.8h, v26.8h
   +0x410: mov     v10.16b, v18.16b
   +0x414: mov     v11.16b, v19.16b
   +0x418: mla     v17.4s, v0.4s, v12.4s
   +0x41c: mla     v3.4s, v1.4s, v12.4s
   +0x420: tbl     v0.16b, {v8.16b-v9.16b}, v4.16b
   +0x424: zip2    v1.8h, v10.8h, v11.8h
   +0x428: mov     v16.s[1], v2.s[1]
   +0x42c: tbl     v2.16b, {v29.16b-v30.16b}, v4.16b
   +0x430: ld1     {v29.2d-v30.2d}, [x9]
   +0x434: add     x9, sp, #0x60
   +0x438: ushr    v21.4s, v5.4s, #28
   +0x43c: mov     v1.s[1], v0.s[1]
   +0x440: ushr    v20.4s, v3.4s, #28
   +0x444: sxtl    v3.4s, v16.4h
   +0x448: tbl     v0.16b, {v23.16b-v24.16b}, v4.16b
   +0x44c: st1     {v23.2d-v24.2d}, [x9]
   +0x450: zip2    v16.8h, v27.8h, v28.8h
   +0x454: add     x9, sp, #0x110
   +0x458: movi    v27.4s, #0x40, lsl #24
   +0x45c: sxtl    v1.4s, v1.4h
   +0x460: mov     v8.16b, v23.16b
   +0x464: mov     v16.s[1], v0.s[1]
   +0x468: mla     v27.4s, v1.4s, v12.4s
   +0x46c: ld1     {v0.2d-v1.2d}, [x9]
   +0x470: add     x9, sp, #0x170
   +0x474: ushr    v19.4s, v17.4s, #28
   +0x478: mov     v9.16b, v24.16b
   +0x47c: movi    v7.4s, #0x40, lsl #24
   +0x480: ld1     {v23.2d-v24.2d}, [x9]
   +0x484: add     x9, sp, #0x80
   +0x488: zip2    v5.8h, v29.8h, v30.8h
   +0x48c: movi    v22.4s, #0x40, lsl #24
   +0x490: mla     v7.4s, v3.4s, v12.4s
   +0x494: ldr     q3, [sp, #64]
   +0x498: mov     v5.s[1], v2.s[1]
   +0x49c: sxtl    v16.4s, v16.4h
   +0x4a0: movi    v2.4s, #0x40, lsl #24
   +0x4a4: mla     v22.4s, v16.4s, v12.4s
   +0x4a8: zip2    v16.8h, v0.8h, v1.8h
   +0x4ac: zip2    v1.8h, v23.8h, v24.8h
   +0x4b0: tbl     v23.16b, {v29.16b-v30.16b}, v3.16b
   +0x4b4: ld1     {v30.2d-v31.2d}, [x9]
   +0x4b8: sxtl    v5.4s, v5.4h
   +0x4bc: add     x9, sp, #0x130
   +0x4c0: tbl     v0.16b, {v10.16b-v11.16b}, v3.16b
   +0x4c4: mla     v2.4s, v5.4s, v12.4s
   +0x4c8: zip2    v6.8h, v13.8h, v14.8h
   +0x4cc: tbl     v5.16b, {v25.16b-v26.16b}, v3.16b
   +0x4d0: ldr     q26, [sp, #256]
   +0x4d4: zip2    v25.8h, v8.8h, v9.8h
   +0x4d8: tbl     v24.16b, {v30.16b-v31.16b}, v3.16b
   +0x4dc: mov     v0.s[1], v16.s[1]
   +0x4e0: mov     v5.s[1], v6.s[1]
   +0x4e4: movi    v6.4s, #0x40, lsl #24
   +0x4e8: movi    v4.4s, #0x40, lsl #24
   +0x4ec: mov     v24.s[1], v25.s[1]
   +0x4f0: sxtl    v0.4s, v0.4h
   +0x4f4: mov     v23.s[1], v1.s[1]
   +0x4f8: ldr     q1, [sp, #192]
   +0x4fc: sxtl    v5.4s, v5.4h
   +0x500: mla     v6.4s, v0.4s, v12.4s
   +0x504: movi    v0.4s, #0x40, lsl #24
   +0x508: mla     v4.4s, v5.4s, v12.4s
   +0x50c: movi    v5.4s, #0x40, lsl #24
   +0x510: sxtl    v16.4s, v24.4h
   +0x514: sxtl    v23.4s, v23.4h
   +0x518: mla     v0.4s, v16.4s, v12.4s
   +0x51c: mla     v5.4s, v23.4s, v12.4s
   +0x520: ushr    v18.4s, v1.4s, #28
   +0x524: ushr    v25.4s, v22.4s, #27
   +0x528: tbl     v9.16b, {v18.16b-v21.16b}, v26.16b
   +0x52c: ld1     {v17.2d-v18.2d}, [x9]
   +0x530: add     x9, sp, #0x110
   +0x534: ushr    v24.4s, v2.4s, #27
   +0x538: ushr    v3.4s, v0.4s, #26
   +0x53c: ushr    v23.4s, v27.4s, #27
   +0x540: ushr    v2.4s, v5.4s, #26
   +0x544: ushr    v22.4s, v7.4s, #27
   +0x548: ushr    v1.4s, v6.4s, #26
   +0x54c: ld1     {v7.2d-v8.2d}, [x9]
   +0x550: add     x9, sp, #0x170
   +0x554: ushr    v0.4s, v4.4s, #26
   +0x558: tbl     v4.16b, {v22.16b-v25.16b}, v26.16b
   +0x55c: tbl     v15.16b, {v0.16b-v3.16b}, v26.16b
   +0x560: ldp     q16, q6, [sp, #32]
   +0x564: mov     v22.16b, v13.16b
   +0x568: mov     v23.16b, v14.16b
   +0x56c: str     q4, [sp, #192]
   +0x570: tbl     v1.16b, {v17.16b-v18.16b}, v16.16b
   +0x574: tbl     v3.16b, {v10.16b-v11.16b}, v16.16b
   +0x578: ld1     {v19.2d-v20.2d}, [x9]
   +0x57c: add     x9, sp, #0x150
   +0x580: tbl     v0.16b, {v13.16b-v14.16b}, v6.16b
   +0x584: tbl     v2.16b, {v7.16b-v8.16b}, v6.16b
   +0x588: ld1     {v13.2d-v14.2d}, [x9]
   +0x58c: add     x9, sp, #0x60
   +0x590: mov     v1.s[1], v0.s[1]
   +0x594: movi    v0.4s, #0x40, lsl #24
   +0x598: tbl     v4.16b, {v19.16b-v20.16b}, v6.16b
   +0x59c: ld1     {v24.2d-v25.2d}, [x9]
   +0x5a0: mov     v3.s[1], v2.s[1]
   +0x5a4: sxtl    v1.4s, v1.4h
   +0x5a8: tbl     v5.16b, {v13.16b-v14.16b}, v16.16b
   +0x5ac: tbl     v16.16b, {v30.16b-v31.16b}, v16.16b
   +0x5b0: ldr     q21, [sp, #16]
   +0x5b4: movi    v2.4s, #0x40, lsl #24
   +0x5b8: mla     v0.4s, v1.4s, v12.4s
   +0x5bc: tbl     v6.16b, {v24.16b-v25.16b}, v6.16b
   +0x5c0: mov     v5.s[1], v4.s[1]
   +0x5c4: movi    v1.4s, #0x40, lsl #24
   +0x5c8: sxtl    v3.4s, v3.4h
   +0x5cc: mov     v16.s[1], v6.s[1]
   +0x5d0: sxtl    v4.4s, v5.4h
   +0x5d4: mla     v2.4s, v3.4s, v12.4s
   +0x5d8: movi    v3.4s, #0x40, lsl #24
   +0x5dc: mla     v1.4s, v4.4s, v12.4s
   +0x5e0: tbl     v4.16b, {v22.16b-v23.16b}, v21.16b
   +0x5e4: ldr     q22, [sp]
   +0x5e8: sxtl    v5.4s, v16.4h
   +0x5ec: tbl     v6.16b, {v7.16b-v8.16b}, v21.16b
   +0x5f0: mla     v3.4s, v5.4s, v12.4s
   +0x5f4: tbl     v5.16b, {v17.16b-v18.16b}, v22.16b
   +0x5f8: tbl     v16.16b, {v10.16b-v11.16b}, v22.16b
   +0x5fc: tbl     v19.16b, {v19.16b-v20.16b}, v21.16b
   +0x600: tbl     v20.16b, {v13.16b-v14.16b}, v22.16b
   +0x604: tbl     v21.16b, {v24.16b-v25.16b}, v21.16b
   +0x608: tbl     v22.16b, {v30.16b-v31.16b}, v22.16b
   +0x60c: mov     v5.s[1], v4.s[1]
   +0x610: mov     v16.s[1], v6.s[1]
   +0x614: mov     v20.s[1], v19.s[1]
   +0x618: mov     v22.s[1], v21.s[1]
   +0x61c: sxtl    v4.4s, v5.4h
   +0x620: sxtl    v5.4s, v16.4h
   +0x624: movi    v19.4s, #0x40, lsl #24
   +0x628: sxtl    v16.4s, v22.4h
   +0x62c: movi    v21.4s, #0x40, lsl #24
   +0x630: movi    v22.4s, #0x40, lsl #24
   +0x634: sxtl    v6.4s, v20.4h
   +0x638: mla     v19.4s, v4.4s, v12.4s
   +0x63c: mla     v21.4s, v6.4s, v12.4s
   +0x640: mla     v22.4s, v5.4s, v12.4s
   +0x644: ushr    v6.4s, v3.4s, #25
   +0x648: ushr    v5.4s, v1.4s, #25
   +0x64c: ushr    v4.4s, v2.4s, #25
   +0x650: ushr    v3.4s, v0.4s, #25
   +0x654: movi    v2.16b, #0x2
   +0x658: tbl     v0.16b, {v3.16b-v6.16b}, v26.16b
   +0x65c: ldp     q4, q3, [sp, #208]
   +0x660: movi    v20.4s, #0x40, lsl #24
   +0x664: mla     v20.4s, v16.4s, v12.4s
   +0x668: and     v2.16b, v3.16b, v2.16b
   +0x66c: movi    v3.16b, #0x4
   +0x670: ushr    v30.4s, v20.4s, #24
   +0x674: ushr    v29.4s, v21.4s, #24
   +0x678: and     v3.16b, v4.16b, v3.16b
   +0x67c: ldr     q4, [sp, #192]
   +0x680: orr     v2.16b, v2.16b, v3.16b
   +0x684: ldr     q3, [sp, #240]
   +0x688: ushr    v28.4s, v22.4s, #24
   +0x68c: ushr    v27.4s, v19.4s, #24
   +0x690: orr     v2.16b, v2.16b, v3.16b
   +0x694: movi    v3.16b, #0x8
   +0x698: tbl     v1.16b, {v27.16b-v30.16b}, v26.16b
   +0x69c: and     v3.16b, v9.16b, v3.16b
   +0x6a0: orr     v2.16b, v2.16b, v3.16b
   +0x6a4: movi    v3.16b, #0x10
   +0x6a8: and     v3.16b, v4.16b, v3.16b
   +0x6ac: movi    v4.16b, #0x20
   +0x6b0: and     v4.16b, v15.16b, v4.16b
   +0x6b4: orr     v3.16b, v3.16b, v4.16b
   +0x6b8: movi    v4.16b, #0x40
   +0x6bc: and     v0.16b, v0.16b, v4.16b
   +0x6c0: orr     v0.16b, v3.16b, v0.16b
   +0x6c4: orr     v0.16b, v2.16b, v0.16b
   +0x6c8: movi    v2.16b, #0x80
   +0x6cc: and     v1.16b, v1.16b, v2.16b
   +0x6d0: orr     v0.16b, v0.16b, v1.16b
   +0x6d4: str     q0, [x0, x8]
   +0x6d8: add     x8, x8, #0x10
  loop2_test:
   +0x6dc: cmp     x8, #0x20
  loop2_back:
   +0x6e0: b.ne    loop2
  join2: loop2_exit:
   +0x6e4: ldp     d9, d8, [sp, #448]
   +0x6e8: ldp     d11, d10, [sp, #432]
   +0x6ec: ldp     d13, d12, [sp, #416]
   +0x6f0: ldp     d15, d14, [sp, #400]
   +0x6f4: ldr     x29, [sp, #464]
   +0x6f8: add     sp, sp, #0x1e0
  ret:
   +0x6fc: ret
 ***)

let MLKEM_NATIVE_POLY_TOMSG_CLANG17_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O2_mc
   [layout_range "mlkem_poly_tomsg"];;

(* ------------------------------------------------------------------------- *)
(* The compression of a coefficient to one bit, as computed in a 32-bit lane *)
(* (COMPRESS_D1_ARITH is that of gcc12_O2), and the 32 bytes of the result   *)
(* from the eight bits in each.                                              *)
(* ------------------------------------------------------------------------- *)

let COMPRESS_D1_ARITH_STMT =
  `!v. v < 3329
       ==> (1073741824 + v * 1290168) DIV 2147483648 =
           (4 * v + 3329) DIV 6658`;;

let COMPRESS_D1_ARITH = assume_spec COMPRESS_D1_ARITH_STMT;;

let TOMSG_LANE_STMT =
  `!y:int16.
        val y < 3329
        ==> word_subword (word_add (word 1073741824)
                                   (word_mul (word_sx y) (word 1290168)):int32)
                         (31,1):1 word =
            word((4 * val y + 3329) DIV 6658)`;;

let TOMSG_LANE = assume_spec TOMSG_LANE_STMT;;

let TOMSG_PACK_STMT =
  `!r s (c:num->num).
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
         nsum {i | i < 256} (\i. c i MOD 2 * 2 EXP i)`;;

let TOMSG_PACK = assume_spec TOMSG_PACK_STMT;;

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

(*** The seven vectors of byte indices for TBL ***)

let MLKEM_NATIVE_POLY_TOMSG_CLANG17_O2_CONSTANTS =
  map (fun k ->
    MLKEM_NATIVE_IMAGE_CONST_RULE
     (layout("mlkem_poly_tomsg_const" ^ string_of_int k)) 128) (1--7);;

let TOMSG_CONSTANTS_TAC =
  MAP_EVERY (fun th -> FIRST_ASSUM(fun ath ->
      if can (term_match [] `aligned_bytes_loaded s0 (word pc)
                               mlkem_native_libmlkem_clang17_O2_mc`)
             (concl ath)
      then ASSUME_TAC(MATCH_MP th ath) else failwith ""))
    MLKEM_NATIVE_POLY_TOMSG_CLANG17_O2_CONSTANTS;;

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
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_CLANG17_O2_EXEC (1--6) THEN
  MP_TAC(SPECL [`r:int64`; `a:int64`; `32`; `512`]
                NONOVERLAPPING_ALIAS_CHECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_CLANG17_O2_EXEC (7--9) THEN
  ASM_CASES_TAC `val(word_add a (word 512):int64) <= val(r:int64)` THENL
   [TOMSG_RESOLVE_TAC THEN body 9;
    TOMSG_RESOLVE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_CLANG17_O2_EXEC (10--12) THEN
    TOMSG_RESOLVE_TAC THEN body 12];;

(*** The vector code from join1 on: 738 steps and the return ***)

let TOMSG_BODY_TAC (simp:tactic) off =
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_TOMSG_CLANG17_O2_EXEC [k + off] THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    simp) (1--738);;

(*** The restored D registers, as zero extensions of the 64 bits saved ***)

let TOMSG_DREG_STMT =
  `!x:int64. word_zx(word_zx x:int128):int64 = x`;;

let TOMSG_DREG = assume_spec TOMSG_DREG_STMT;;

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
(* Correctness proof. As for mlkem_compress 1 in common/fips203/fips203.ml,  *)
(* the bit for a coefficient x in [0,3329) is the integer closest to 2 * x / *)
(* 3329, rounding up on ties, modulo 2, i.e. ((4 * x + 3329) DIV 6658) MOD   *)
(* 2, and as for mlkem_encode 1 the bits are put together little-endian.     *)
(* Like the C code, this relies on the coefficients being in [0,3329).       *)
(* ------------------------------------------------------------------------- *)


let MLKEM_NATIVE_POLY_TOMSG_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (r,32)) [(word pc,libmlkem_size); (a,512)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 480),480))
            [(word pc,libmlkem_size); (a,512); (r,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O2_mc /\
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
                                                 (word 480),480)])`;;

let MLKEM_NATIVE_POLY_TOMSG_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_TOMSG_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_TOMSG_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (r,32)) [word pc,libmlkem_size; a,512] /\
           ALL (nonoverlapping (word_sub stackpointer (word 480),480))
               [word pc,libmlkem_size; a,512; r,32]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O2_mc /\
                    read PC s = word (pc + mlkem_poly_tomsg) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc (word_sub stackpointer (word 480))
                                       returnaddress /\
                         memaccess_inbounds e2
                          [a,512; r,32;
                           word (pc + mlkem_poly_tomsg_consts),
                           mlkem_poly_tomsg_consts_size;
                           word_sub stackpointer (word 480),480]
                          [r,32; word_sub stackpointer (word 480),480]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,32);
                           memory :> bytes(word_sub stackpointer
                                                   (word 480),480)])`;;

let MLKEM_NATIVE_POLY_TOMSG_CLANG17_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_TOMSG_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
