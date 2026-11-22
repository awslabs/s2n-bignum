(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Compression of a polynomial to 4 bits per coefficient. This is the code   *)
(* for mlkem_poly_compress_d4 from mlkem-native's portable C implementation  *)
(* compiled by clang 17 with -O2 (see mlkem_native/README.md). It is         *)
(* verified in the whole image (see libmlkem.ml).                            *)
(*                                                                           *)
(* The compiler has vectorized the loop, with 32-bit lanes, after a check    *)
(* that the input and the output do not overlap, with one branch for each of *)
(* the two orders of the arrays; if they overlap, the code falls back to a   *)
(* scalar loop (loop1, 4 coefficients per iteration). Since the              *)
(* specification requires them not to overlap, only the vector loop (loop2)  *)
(* runs. It has two iterations of 128 coefficients each: it loads them with  *)
(* LDP, computes the 4-bit values in 32-bit lanes, gathers pairs of them     *)
(* into bytes with TBL on a four-register table, and writes 64 bytes with    *)
(* ST4. The code saves D8 to D15 and X29 and spills vectors to the stack,    *)
(* all in a frame of 320 bytes, which the specifications therefore have      *)
(* (unlike those of gcc12_O2, which have a frame of 32 bytes). The code has  *)
(* no stack guard. It reads seven vectors of byte indices for TBL from the   *)
(* read-only data.                                                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/overlap.ml";;
needs "arm/proofs/mlkem_native/interleave.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/libmlkem.ml";;

(*** The code in the image (the labels are those of layout.ml):

    mlkem_poly_compress_d4:
     +0x0: sub     sp, sp, #0x140
     +0x4: stp     d15, d14, [sp, #240]
     +0x8: stp     d13, d12, [sp, #256]
     +0xc: stp     d11, d10, [sp, #272]
    +0x10: stp     d9, d8, [sp, #288]
    +0x14: str     x29, [sp, #304]
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
  loop1:
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
  loop1_test:
    +0xc0: cmp     x8, #0x80
  loop1_back:
    +0xc4: b.ne    loop1
  loop1_exit:
    +0xc8: b       join2
  join1:
    +0xcc: adrp    x9, <page>
    +0xd0: adrp    x10, <page>
    +0xd4: adrp    x11, <page>
    +0xd8: mov     x8, xzr
    +0xdc: ldr     q0, [x9, #3168]
                  // mlkem_poly_compress_d4_const1
    +0xe0: adrp    x9, <page>
    +0xe4: str     q0, [sp, #96]
    +0xe8: ldr     q0, [x10, #3184]
                  // mlkem_poly_compress_d4_const2
    +0xec: adrp    x10, <page>
    +0xf0: str     q0, [sp, #80]
    +0xf4: ldr     q0, [x11, #3200]
                  // mlkem_poly_compress_d4_const3
    +0xf8: adrp    x11, <page>
    +0xfc: str     q0, [sp, #64]
   +0x100: ldr     q0, [x9, #3216]
                  // mlkem_poly_compress_d4_const4
   +0x104: adrp    x9, <page>
   +0x108: str     q0, [sp, #48]
   +0x10c: ldr     q0, [x10, #3232]
                  // mlkem_poly_compress_d4_const5
   +0x110: mov     w10, #0xafb0
   +0x114: movk    w10, #0x13, lsl #16
   +0x118: str     q0, [sp, #32]
   +0x11c: ldr     q0, [x11, #3248]
                  // mlkem_poly_compress_d4_const6
   +0x120: dup     v16.4s, w10
   +0x124: str     q0, [sp, #16]
   +0x128: ldr     q0, [x9, #3264]
                  // mlkem_poly_compress_d4_const7
   +0x12c: str     q0, [sp]
  loop2:
   +0x130: ldp     q21, q22, [x1, #32]
   +0x134: add     x9, sp, #0x70
   +0x138: movi    v7.4s, #0x8, lsl #24
   +0x13c: movi    v15.4s, #0x8, lsl #24
   +0x140: ldp     q23, q24, [x1]
   +0x144: zip1    v18.4h, v21.4h, v22.4h
   +0x148: ext     v31.8b, v21.8b, v18.8b, #4
   +0x14c: ldp     q19, q20, [x1, #96]
   +0x150: zip1    v6.4h, v23.4h, v24.4h
   +0x154: trn2    v4.4h, v23.4h, v24.4h
   +0x158: mov     v6.s[1], v31.s[1]
   +0x15c: ldp     q25, q26, [x1, #224]
   +0x160: zip1    v3.4h, v19.4h, v20.4h
   +0x164: mov     v4.s[1], v18.s[1]
   +0x168: sxtl    v6.4s, v6.4h
   +0x16c: ext     v10.8b, v19.8b, v3.8b, #4
   +0x170: ldp     q0, q1, [x1, #64]
   +0x174: zip1    v31.4h, v25.4h, v26.4h
   +0x178: mla     v15.4s, v6.4s, v16.4s
   +0x17c: sxtl    v4.4s, v4.4h
   +0x180: ext     v13.8b, v25.8b, v31.8b, #4
   +0x184: ldp     q29, q30, [x1, #160]
   +0x188: zip1    v11.4h, v0.4h, v1.4h
   +0x18c: trn2    v5.4h, v0.4h, v1.4h
   +0x190: st1     {v0.2d-v1.2d}, [x9]
   +0x194: mov     v11.s[1], v10.s[1]
   +0x198: ldp     q27, q28, [x1, #192]
   +0x19c: zip1    v17.4h, v29.4h, v30.4h
   +0x1a0: mov     v5.s[1], v3.s[1]
   +0x1a4: sxtl    v11.4s, v11.4h
   +0x1a8: ext     v10.8b, v29.8b, v17.8b, #4
   +0x1ac: ldp     q8, q9, [x1, #128]
   +0x1b0: zip1    v14.4h, v27.4h, v28.4h
   +0x1b4: add     x1, x1, #0x100
   +0x1b8: mov     v14.s[1], v13.s[1]
   +0x1bc: zip1    v12.4h, v8.4h, v9.4h
   +0x1c0: movi    v13.4s, #0x8, lsl #24
   +0x1c4: trn2    v18.4h, v8.4h, v9.4h
   +0x1c8: sxtl    v1.4s, v14.4h
   +0x1cc: mov     v12.s[1], v10.s[1]
   +0x1d0: movi    v10.4s, #0x8, lsl #24
   +0x1d4: mla     v7.4s, v1.4s, v16.4s
   +0x1d8: mov     v18.s[1], v17.s[1]
   +0x1dc: sxtl    v3.4s, v12.4h
   +0x1e0: mla     v10.4s, v11.4s, v16.4s
   +0x1e4: mla     v13.4s, v3.4s, v16.4s
   +0x1e8: ushr    v3.4s, v7.4s, #28
   +0x1ec: trn2    v12.4h, v27.4h, v28.4h
   +0x1f0: movi    v7.4s, #0x8, lsl #24
   +0x1f4: ushr    v2.4s, v13.4s, #28
   +0x1f8: ushr    v1.4s, v10.4s, #28
   +0x1fc: ushr    v0.4s, v15.4s, #28
   +0x200: ldr     q15, [sp, #96]
   +0x204: mov     v12.s[1], v31.s[1]
   +0x208: zip2    v31.8h, v23.8h, v24.8h
   +0x20c: tbl     v6.16b, {v0.16b-v3.16b}, v15.16b
   +0x210: movi    v3.4s, #0x8, lsl #24
   +0x214: sxtl    v1.4s, v18.4h
   +0x218: ld1     {v17.2d-v18.2d}, [x9]
   +0x21c: sxtl    v0.4s, v5.4h
   +0x220: add     x9, x0, x8
   +0x224: movi    v5.4s, #0x8, lsl #24
   +0x228: add     x8, x8, #0x40
   +0x22c: mla     v3.4s, v4.4s, v16.4s
   +0x230: cmp     x8, #0x80
   +0x234: sxtl    v2.4s, v12.4h
   +0x238: mla     v7.4s, v0.4s, v16.4s
   +0x23c: mov     v0.16b, v19.16b
   +0x240: stp     q3, q6, [sp, #208]
   +0x244: zip2    v4.4h, v23.4h, v24.4h
   +0x248: movi    v6.4s, #0x8, lsl #24
   +0x24c: mov     v3.16b, v21.16b
   +0x250: mov     v3.h[3], v22.h[2]
   +0x254: mla     v5.4s, v1.4s, v16.4s
   +0x258: mla     v6.4s, v2.4s, v16.4s
   +0x25c: mov     v0.h[3], v20.h[2]
   +0x260: zip2    v2.4h, v17.4h, v18.4h
   +0x264: mov     v1.16b, v29.16b
   +0x268: stp     q6, q5, [sp, #176]
   +0x26c: zip2    v5.4h, v8.4h, v9.4h
   +0x270: mov     v4.s[1], v3.s[1]
   +0x274: zip2    v6.4h, v27.4h, v28.4h
   +0x278: mov     v3.16b, v25.16b
   +0x27c: mov     v1.h[3], v30.h[2]
   +0x280: mov     v2.s[1], v0.s[1]
   +0x284: mov     v3.h[3], v26.h[2]
   +0x288: sxtl    v0.4s, v4.4h
   +0x28c: mov     v5.s[1], v1.s[1]
   +0x290: sxtl    v1.4s, v2.4h
   +0x294: movi    v2.4s, #0x8, lsl #24
   +0x298: mov     v6.s[1], v3.s[1]
   +0x29c: sxtl    v3.4s, v5.4h
   +0x2a0: movi    v5.4s, #0x8, lsl #24
   +0x2a4: mla     v2.4s, v0.4s, v16.4s
   +0x2a8: movi    v0.4s, #0x8, lsl #24
   +0x2ac: sxtl    v4.4s, v6.4h
   +0x2b0: movi    v6.4s, #0x8, lsl #24
   +0x2b4: mla     v5.4s, v1.4s, v16.4s
   +0x2b8: mla     v0.4s, v4.4s, v16.4s
   +0x2bc: uzp2    v1.4h, v23.4h, v24.4h
   +0x2c0: mla     v6.4s, v3.4s, v16.4s
   +0x2c4: zip2    v3.4h, v21.4h, v22.4h
   +0x2c8: zip2    v4.4h, v29.4h, v30.4h
   +0x2cc: ushr    v13.4s, v0.4s, #28
   +0x2d0: uzp2    v0.4h, v17.4h, v18.4h
   +0x2d4: uzp2    v1.4h, v1.4h, v23.4h
   +0x2d8: ushr    v12.4s, v6.4s, #28
   +0x2dc: ushr    v11.4s, v5.4s, #28
   +0x2e0: ushr    v10.4s, v2.4s, #28
   +0x2e4: uzp2    v6.4h, v0.4h, v17.4h
   +0x2e8: mov     v1.s[1], v3.s[1]
   +0x2ec: zip2    v2.4h, v19.4h, v20.4h
   +0x2f0: tbl     v0.16b, {v10.16b-v13.16b}, v15.16b
   +0x2f4: ldr     q10, [sp, #80]
   +0x2f8: movi    v11.4s, #0x8, lsl #24
   +0x2fc: sxtl    v3.4s, v1.4h
   +0x300: uzp2    v1.4h, v27.4h, v28.4h
   +0x320: str     q0, [sp, #160]
   +0x308: uzp2    v0.4h, v8.4h, v9.4h
   +0x30c: mov     v6.s[1], v2.s[1]
   +0x310: mla     v11.4s, v3.4s, v16.4s
   +0x314: uzp2    v1.4h, v1.4h, v27.4h
   +0x318: uzp2    v2.4h, v0.4h, v8.4h
   +0x31c: zip2    v0.4h, v25.4h, v26.4h
   +0x320: tbl     v5.16b, {v21.16b-v22.16b}, v10.16b
   +0x324: str     q11, [sp, #144]
   +0x328: tbl     v3.16b, {v29.16b-v30.16b}, v10.16b
   +0x32c: mov     v1.s[1], v0.s[1]
   +0x330: tbl     v0.16b, {v19.16b-v20.16b}, v10.16b
   +0x334: tbl     v10.16b, {v25.16b-v26.16b}, v10.16b
   +0x338: zip2    v11.8h, v27.8h, v28.8h
   +0x33c: mov     v2.s[1], v4.s[1]
   +0x340: zip2    v4.8h, v8.8h, v9.8h
   +0x344: mov     v31.s[1], v5.s[1]
   +0x348: zip2    v5.8h, v17.8h, v18.8h
   +0x34c: mov     v11.s[1], v10.s[1]
   +0x350: mov     v4.s[1], v3.s[1]
   +0x354: sxtl    v3.4s, v31.4h
   +0x358: movi    v31.4s, #0x8, lsl #24
   +0x35c: mov     v5.s[1], v0.s[1]
   +0x360: movi    v0.4s, #0x8, lsl #24
   +0x364: sxtl    v10.4s, v11.4h
   +0x368: sxtl    v4.4s, v4.4h
   +0x36c: mla     v31.4s, v10.4s, v16.4s
   +0x370: movi    v10.4s, #0x8, lsl #24
   +0x374: mla     v0.4s, v4.4s, v16.4s
   +0x378: movi    v4.4s, #0x8, lsl #24
   +0x37c: sxtl    v5.4s, v5.4h
   +0x380: ushr    v14.4s, v31.4s, #28
   +0x384: mla     v10.4s, v5.4s, v16.4s
   +0x388: ushr    v13.4s, v0.4s, #28
   +0x38c: mla     v4.4s, v3.4s, v16.4s
   +0x390: sxtl    v3.4s, v6.4h
   +0x394: movi    v31.4s, #0x8, lsl #24
   +0x398: ushr    v12.4s, v10.4s, #28
   +0x39c: ushr    v11.4s, v4.4s, #28
   +0x3a0: movi    v0.4s, #0x8, lsl #24
   +0x3a4: tbl     v6.16b, {v11.16b-v14.16b}, v15.16b
   +0x3a8: ldp     q13, q12, [sp, #32]
   +0x3ac: sxtl    v2.4s, v2.4h
   +0x3b0: mla     v31.4s, v3.4s, v16.4s
   +0x3b4: mla     v0.4s, v2.4s, v16.4s
   +0x3b8: tbl     v3.16b, {v23.16b-v24.16b}, v13.16b
   +0x3bc: tbl     v5.16b, {v17.16b-v18.16b}, v13.16b
   +0x3c0: tbl     v2.16b, {v21.16b-v22.16b}, v12.16b
   +0x3c4: tbl     v4.16b, {v19.16b-v20.16b}, v12.16b
   +0x3c8: tbl     v10.16b, {v29.16b-v30.16b}, v12.16b
   +0x3cc: tbl     v11.16b, {v8.16b-v9.16b}, v13.16b
   +0x3d0: tbl     v12.16b, {v25.16b-v26.16b}, v12.16b
   +0x3d4: tbl     v13.16b, {v27.16b-v28.16b}, v13.16b
   +0x3d8: mov     v3.s[1], v2.s[1]
   +0x3dc: mov     v5.s[1], v4.s[1]
   +0x3e0: movi    v2.4s, #0x8, lsl #24
   +0x3e4: movi    v4.4s, #0x8, lsl #24
   +0x3e8: mov     v13.s[1], v12.s[1]
   +0x3ec: sxtl    v3.4s, v3.4h
   +0x3f0: mov     v11.s[1], v10.s[1]
   +0x3f4: sxtl    v5.4s, v5.4h
   +0x3f8: mla     v2.4s, v3.4s, v16.4s
   +0x3fc: movi    v3.4s, #0x8, lsl #24
   +0x400: mla     v4.4s, v5.4s, v16.4s
   +0x404: movi    v5.4s, #0x8, lsl #24
   +0x408: sxtl    v10.4s, v13.4h
   +0x40c: sxtl    v11.4s, v11.4h
   +0x410: mla     v3.4s, v10.4s, v16.4s
   +0x414: mla     v5.4s, v11.4s, v16.4s
   +0x418: movi    v10.4s, #0x8, lsl #24
   +0x41c: sxtl    v1.4s, v1.4h
   +0x420: ushr    v14.4s, v3.4s, #28
   +0x424: ushr    v13.4s, v5.4s, #28
   +0x428: ushr    v12.4s, v4.4s, #28
   +0x42c: ushr    v11.4s, v2.4s, #28
   +0x430: mla     v10.4s, v1.4s, v16.4s
   +0x434: tbl     v1.16b, {v11.16b-v14.16b}, v15.16b
   +0x438: ldr     q14, [sp, #64]
   +0x43c: zip2    v2.8h, v21.8h, v22.8h
   +0x440: zip2    v11.8h, v29.8h, v30.8h
   +0x444: tbl     v4.16b, {v23.16b-v24.16b}, v14.16b
   +0x448: tbl     v5.16b, {v17.16b-v18.16b}, v14.16b
   +0x44c: tbl     v12.16b, {v8.16b-v9.16b}, v14.16b
   +0x450: zip2    v13.8h, v25.8h, v26.8h
   +0x454: tbl     v14.16b, {v27.16b-v28.16b}, v14.16b
   +0x458: mov     v4.s[1], v2.s[1]
   +0x45c: mov     v12.s[1], v11.s[1]
   +0x460: movi    v2.4s, #0x8, lsl #24
   +0x464: mov     v14.s[1], v13.s[1]
   +0x468: ldp     q13, q11, [sp]
   +0x46c: zip2    v3.8h, v19.8h, v20.8h
   +0x470: sxtl    v4.4s, v4.4h
   +0x474: mla     v2.4s, v4.4s, v16.4s
   +0x478: mov     v5.s[1], v3.s[1]
   +0x47c: tbl     v4.16b, {v21.16b-v22.16b}, v11.16b
   +0x480: tbl     v21.16b, {v23.16b-v24.16b}, v13.16b
   +0x484: movi    v3.4s, #0x8, lsl #24
   +0x488: movi    v22.4s, #0x8, lsl #24
   +0x48c: sxtl    v5.4s, v5.4h
   +0x490: mov     v21.s[1], v4.s[1]
   +0x494: tbl     v4.16b, {v19.16b-v20.16b}, v11.16b
   +0x498: tbl     v19.16b, {v17.16b-v18.16b}, v13.16b
   +0x49c: ldr     q17, [sp, #176]
   +0x4a0: sxtl    v24.4s, v14.4h
   +0x4a4: mla     v3.4s, v5.4s, v16.4s
   +0x4a8: movi    v5.4s, #0x8, lsl #24
   +0x4ac: mla     v22.4s, v24.4s, v16.4s
   +0x4b0: tbl     v20.16b, {v29.16b-v30.16b}, v11.16b
   +0x4b4: tbl     v24.16b, {v25.16b-v26.16b}, v11.16b
   +0x4b8: tbl     v25.16b, {v27.16b-v28.16b}, v13.16b
   +0x4bc: ushr    v29.4s, v17.4s, #24
   +0x4c0: ldr     q17, [sp, #192]
   +0x4c4: sxtl    v23.4s, v12.4h
   +0x4c8: mov     v19.s[1], v4.s[1]
   +0x4cc: ushr    v28.4s, v17.4s, #24
   +0x4d0: mla     v5.4s, v23.4s, v16.4s
   +0x4d4: ushr    v27.4s, v7.4s, #24
   +0x4d8: tbl     v23.16b, {v8.16b-v9.16b}, v13.16b
   +0x4dc: ldr     q7, [sp, #208]
   +0x4e0: movi    v18.4s, #0x8, lsl #24
   +0x4e4: mov     v25.s[1], v24.s[1]
   +0x4e8: ushr    v26.4s, v7.4s, #24
   +0x4ec: sxtl    v7.4s, v19.4h
   +0x4f0: mov     v23.s[1], v20.s[1]
   +0x4f4: movi    v19.4s, #0x8, lsl #24
   +0x4f8: mla     v18.4s, v7.4s, v16.4s
   +0x4fc: tbl     v7.16b, {v26.16b-v29.16b}, v15.16b
   +0x500: ushr    v29.4s, v10.4s, #24
   +0x504: ushr    v28.4s, v0.4s, #24
   +0x508: movi    v0.4s, #0x8, lsl #24
   +0x50c: ushr    v27.4s, v31.4s, #24
   +0x510: sxtl    v20.4s, v25.4h
   +0x514: movi    v4.4s, #0x8, lsl #24
   +0x518: sxtl    v17.4s, v23.4h
   +0x51c: mla     v19.4s, v20.4s, v16.4s
   +0x520: ldr     q20, [sp, #144]
   +0x524: sxtl    v21.4s, v21.4h
   +0x528: mla     v0.4s, v17.4s, v16.4s
   +0x52c: ushr    v26.4s, v20.4s, #24
   +0x530: mla     v4.4s, v21.4s, v16.4s
   +0x534: ushr    v23.4s, v22.4s, #24
   +0x538: tbl     v17.16b, {v26.16b-v29.16b}, v15.16b
   +0x53c: ushr    v27.4s, v19.4s, #24
   +0x540: ushr    v26.4s, v0.4s, #24
   +0x544: ushr    v22.4s, v5.4s, #24
   +0x548: ushr    v25.4s, v18.4s, #24
   +0x54c: ushr    v21.4s, v3.4s, #24
   +0x550: ushr    v24.4s, v4.4s, #24
   +0x554: ushr    v20.4s, v2.4s, #24
   +0x558: movi    v4.16b, #0xf0
   +0x55c: ldr     q5, [sp, #224]
   +0x560: tbl     v0.16b, {v20.16b-v23.16b}, v15.16b
   +0x564: tbl     v2.16b, {v24.16b-v27.16b}, v15.16b
   +0x568: and     v3.16b, v7.16b, v4.16b
   +0x56c: orr     v18.16b, v3.16b, v5.16b
   +0x570: ldr     q5, [sp, #160]
   +0x574: and     v3.16b, v17.16b, v4.16b
   +0x578: and     v0.16b, v0.16b, v4.16b
   +0x57c: orr     v19.16b, v3.16b, v5.16b
   +0x580: orr     v20.16b, v0.16b, v6.16b
   +0x584: and     v0.16b, v2.16b, v4.16b
   +0x588: orr     v21.16b, v0.16b, v1.16b
  loop2_test:
   +0x58c: st4     {v18.16b-v21.16b}, [x9]
  loop2_back:
   +0x590: b.ne    loop2
  join2: loop2_exit:
   +0x594: ldp     d9, d8, [sp, #288]
   +0x598: ldp     d11, d10, [sp, #272]
   +0x59c: ldp     d13, d12, [sp, #256]
   +0x5a0: ldp     d15, d14, [sp, #240]
   +0x5a4: ldr     x29, [sp, #304]
   +0x5a8: add     sp, sp, #0x140
  ret:
   +0x5ac: ret
 ***)

let MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O2_mc
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

(*** The seven vectors of byte indices for TBL ***)

let MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O2_CONSTANTS =
  map (fun k ->
    MLKEM_NATIVE_IMAGE_CONST_RULE
     (layout("mlkem_poly_compress_d4_const" ^ string_of_int k)) 128) (1--7);;

let COMPRESS_D4_CONSTANTS_TAC =
  MAP_EVERY (fun th -> FIRST_ASSUM(fun ath ->
      if can (term_match [] `aligned_bytes_loaded s0 (word pc)
                               mlkem_native_libmlkem_clang17_O2_mc`)
             (concl ath)
      then ASSUME_TAC(MATCH_MP th ath) else failwith ""))
    MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O2_CONSTANTS;;

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
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O2_EXEC (1--6) THEN
  MP_TAC(SPECL [`r:int64`; `a:int64`; `128`; `512`]
                NONOVERLAPPING_ALIAS_CHECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O2_EXEC (7--9) THEN
  ASM_CASES_TAC `val(word_add a (word 512):int64) <= val(r:int64)` THENL
   [COMPRESS_D4_RESOLVE_TAC THEN body 9;
    COMPRESS_D4_RESOLVE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O2_EXEC (10--12) THEN
    COMPRESS_D4_RESOLVE_TAC THEN body 12];;

(*** The vector code from join1 on: 594 steps and the return ***)

let COMPRESS_D4_BODY_TAC (simp:tactic) off =
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O2_EXEC [k + off] THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    simp) (1--594);;

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

(*** The stored bytes, from the 2 stores of 64 bytes ***)

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
(* Correctness proof. As for mlkem_compress 4 in common/fips203/fips203.ml,  *)
(* the result for a coefficient x in [0,3329) is the integer closest to 16 * *)
(* x / 3329, rounding up on ties, modulo 16, i.e. ((32 * x + 3329) DIV 6658) *)
(* MOD 16, and as for mlkem_encode 4 the 4-bit values are put together       *)
(* little-endian. Like the C code, this relies on the coefficients being in  *)
(* [0,3329).                                                                 *)
(* ------------------------------------------------------------------------- *)


let MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,128); (a,512); (word_sub stackpointer (word 320),320)] /\
        ALLPAIRS nonoverlapping
         [(r,128); (word_sub stackpointer (word 320),320)]
         [(word pc,libmlkem_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O2_mc /\
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
                                                  (word 320),320)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. This is stated directly rather     *)
(* than by mk_safety_spec, as for gcc12_O2, with the events depending on the *)
(* stack frame. Unlike gcc12_O2, the code reads seven vectors of constants  *)
(* and there is no stack guard.                                              *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e r a pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [r,128; a,512; word_sub stackpointer (word 320),320] /\
       ALLPAIRS nonoverlapping
        [r,128; word_sub stackpointer (word 320),320]
        [word pc,libmlkem_size]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_clang17_O2_mc /\
                 read PC s = word (pc + mlkem_poly_compress_d4) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [r; a] s /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events a r pc
                           (word_sub stackpointer (word 320)) returnaddress /\
                    memaccess_inbounds e2
                     [a,512; r,128; word_sub stackpointer (word 320),320;
                      word(pc + mlkem_poly_compress_d4_consts),
                      mlkem_poly_compress_d4_consts_size]
                     [r,128; word_sub stackpointer (word 320),320]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
             MAYCHANGE [memory :> bytes(r,128);
                        memory :> bytes(word_sub stackpointer (word 320),
                                        320)])`;;

let MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_COMPRESS_D4_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
