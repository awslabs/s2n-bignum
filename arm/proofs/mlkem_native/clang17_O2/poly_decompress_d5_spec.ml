(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 5 bits per coefficient. This is the    *)
(* code for mlkem_poly_decompress_d5 from mlkem-native's portable C          *)
(* implementation compiled by clang 17 with -O2 (see mlkem_native/README.md).*)
(* It is verified in the whole image (see libmlkem.ml).                      *)
(*                                                                           *)
(* The compiler has vectorized the loop: after a check that the input and    *)
(* the output do not overlap, with one branch for each of the two orders of  *)
(* the arrays (if they overlap, the code falls back to a scalar loop, which  *)
(* cannot run under the specification), it copies 30 vectors of indices      *)
(* from the read-only data to the stack, and then loops twice, each time     *)
(* for 128 coefficients from 80 bytes: it loads the indices from the stack,  *)
(* gathers the bytes of the fields with TBL, extracts the fields with        *)
(* shifts and masks, computes the coefficients with UMULL and RSHRN #5,      *)
(* puts them in order with more TBL and stores them. It saves D8 to D15 and  *)
(* X29 and spills more vectors to the stack, all in a frame of 784 bytes,    *)
(* which the specifications therefore have (unlike those of gcc12_O2, which  *)
(* have none). The two iterations of the loop are simulated one after the    *)
(* other.                                                                    *)
(*                                                                           *)
(* The registers are kept in the bit-level normal form of bitnorm.ml during  *)
(* the simulation, so that each lane before the product with 3329 is a       *)
(* 5-bit field of the 160 bytes, and each stored lane the rounded product.   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/overlap.ml";;
needs "arm/proofs/mlkem_native/bitnorm.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/libmlkem.ml";;

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
      +0x20: b.ls    <mlkem_poly_decompress_d5+0x130>
      +0x24: add     x8, x0, #0x200
      +0x28: cmp     x8, x1
      +0x2c: b.ls    <mlkem_poly_decompress_d5+0x130>
      +0x30: adrp    x9, <page>
      +0x34: adrp    x10, <page>
      +0x38: mov     w11, #0xd01
      +0x3c: movi    d0, #0xff000000ff
      +0x40: mov     x8, xzr
      +0x44: ldr     d1, [x9, #384]
      +0x48: add     x9, x1, #0x2
      +0x4c: ldr     d2, [x10, #392]
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
     +0x128: b.ne    <mlkem_poly_decompress_d5+0x54>
     +0x12c: b       <mlkem_poly_decompress_d5+0x6a8>
     +0x130: adrp    x9, <page>
     +0x134: adrp    x10, <page>
     +0x138: adrp    x11, <page>
     +0x13c: mov     x8, xzr
     +0x140: ldr     q0, [x9, #3376]
     +0x144: adrp    x9, <page>
     +0x148: str     q0, [sp, #400]
     +0x14c: ldr     q0, [x10, #3392]
     +0x150: adrp    x10, <page>
     +0x154: str     q0, [sp, #384]
     +0x158: ldr     q0, [x11, #3408]
     +0x15c: adrp    x11, <page>
     +0x160: str     q0, [sp, #368]
     +0x164: ldr     q0, [x9, #3424]
     +0x168: adrp    x9, <page>
     +0x16c: str     q0, [sp, #352]
     +0x170: ldr     q0, [x10, #3440]
     +0x174: adrp    x10, <page>
     +0x178: str     q0, [sp, #336]
     +0x17c: ldr     q0, [x11, #3456]
     +0x180: adrp    x11, <page>
     +0x184: str     q0, [sp, #320]
     +0x188: ldr     q0, [x9, #3472]
     +0x18c: adrp    x9, <page>
     +0x190: str     q0, [sp, #304]
     +0x194: ldr     q0, [x10, #3488]
     +0x198: adrp    x10, <page>
     +0x19c: str     q0, [sp, #288]
     +0x1a0: ldr     q0, [x11, #3504]
     +0x1a4: adrp    x11, <page>
     +0x1a8: str     q0, [sp, #272]
     +0x1ac: ldr     q0, [x9, #3520]
     +0x1b0: adrp    x9, <page>
     +0x1b4: str     q0, [sp, #256]
     +0x1b8: ldr     q0, [x10, #3536]
     +0x1bc: adrp    x10, <page>
     +0x1c0: str     q0, [sp, #240]
     +0x1c4: ldr     q0, [x11, #3552]
     +0x1c8: adrp    x11, <page>
     +0x1cc: str     q0, [sp, #224]
     +0x1d0: ldr     q0, [x9, #3568]
     +0x1d4: adrp    x9, <page>
     +0x1d8: str     q0, [sp, #208]
     +0x1dc: ldr     q0, [x10, #3584]
     +0x1e0: adrp    x10, <page>
     +0x1e4: str     q0, [sp, #192]
     +0x1e8: ldr     q0, [x11, #3600]
     +0x1ec: adrp    x11, <page>
     +0x1f0: str     q0, [sp, #176]
     +0x1f4: ldr     q0, [x9, #3616]
     +0x1f8: adrp    x9, <page>
     +0x1fc: str     q0, [sp, #160]
     +0x200: ldr     q0, [x10, #3632]
     +0x204: adrp    x10, <page>
     +0x208: str     q0, [sp, #144]
     +0x20c: ldr     q0, [x11, #3648]
     +0x210: adrp    x11, <page>
     +0x214: str     q0, [sp, #128]
     +0x218: ldr     q0, [x9, #3664]
     +0x21c: adrp    x9, <page>
     +0x220: str     q0, [sp, #112]
     +0x224: ldr     q0, [x10, #3680]
     +0x228: adrp    x10, <page>
     +0x22c: str     q0, [sp, #96]
     +0x230: ldr     q0, [x11, #3696]
     +0x234: str     q0, [sp, #80]
     +0x238: ldr     q0, [x9, #3712]
     +0x23c: adrp    x9, <page>
     +0x240: str     q0, [sp, #64]
     +0x244: ldr     q0, [x10, #3728]
     +0x248: adrp    x10, <page>
     +0x24c: str     q0, [sp, #48]
     +0x250: ldr     q0, [x9, #3744]
     +0x254: adrp    x9, <page>
     +0x258: str     q0, [sp, #32]
     +0x25c: ldr     q0, [x10, #3760]
     +0x260: adrp    x10, <page>
     +0x264: str     q0, [sp, #16]
     +0x268: ldr     q0, [x9, #3776]
     +0x26c: adrp    x9, <page>
     +0x270: str     q0, [sp]
     +0x274: ldr     q0, [x10, #3792]
     +0x278: adrp    x10, <page>
     +0x27c: str     q0, [sp, #688]
     +0x280: ldr     q0, [x9, #3808]
     +0x284: mov     w9, #0xd01
     +0x288: str     q0, [sp, #672]
     +0x28c: ldr     q0, [x10, #3824]
     +0x290: adrp    x10, <page>
     +0x294: dup     v13.8h, w9
     +0x298: str     q0, [sp, #656]
     +0x29c: ldr     q0, [x10, #3840]
     +0x2a0: str     q0, [sp, #640]
     +0x2a4: add     x9, x1, x8
     +0x2a8: ldr     q22, [sp, #368]
     +0x2ac: ldp     q16, q6, [sp, #384]
     +0x2b0: movi    v23.16b, #0x1f
     +0x2b4: add     x8, x8, #0x50
     +0x2b8: cmp     x8, #0xa0
     +0x2bc: ldp     q5, q2, [x9, #16]
     +0x2c0: ldp     q3, q1, [x9, #48]
     +0x2c4: tbl     v7.16b, {v2.16b-v3.16b}, v6.16b
     +0x2c8: ldr     q4, [x9]
     +0x2cc: ldr     q18, [sp, #288]
     +0x2d0: ldr     q20, [sp, #176]
     +0x2d4: tbl     v6.16b, {v4.16b-v5.16b}, v16.16b
     +0x2d8: ldr     q16, [sp, #336]
     +0x2dc: tbl     v19.16b, {v2.16b-v3.16b}, v18.16b
     +0x2e0: tbl     v21.16b, {v2.16b-v3.16b}, v20.16b
     +0x2e4: tbl     v17.16b, {v2.16b-v3.16b}, v16.16b
     +0x2e8: tbl     v0.16b, {v6.16b-v7.16b}, v22.16b
     +0x2ec: ldr     q6, [sp, #320]
     +0x2f0: tbl     v16.16b, {v4.16b-v5.16b}, v6.16b
     +0x2f4: ldr     q6, [sp, #224]
     +0x2f8: tbl     v7.16b, {v2.16b-v3.16b}, v6.16b
     +0x2fc: ldr     q2, [sp, #352]
     +0x300: tbl     v2.16b, {v0.16b-v1.16b}, v2.16b
     +0x304: tbl     v0.16b, {v16.16b-v17.16b}, v22.16b
     +0x308: ldp     q22, q3, [sp, #256]
     +0x30c: tbl     v18.16b, {v4.16b-v5.16b}, v3.16b
     +0x310: ldr     q3, [sp, #208]
     +0x314: tbl     v6.16b, {v4.16b-v5.16b}, v3.16b
     +0x318: ldr     q3, [sp, #160]
     +0x31c: tbl     v20.16b, {v4.16b-v5.16b}, v3.16b
     +0x320: ldr     q3, [sp, #304]
     +0x324: tbl     v4.16b, {v0.16b-v1.16b}, v3.16b
     +0x328: and     v3.16b, v2.16b, v23.16b
     +0x32c: uxtl    v5.8h, v3.8b
     +0x330: tbl     v0.16b, {v18.16b-v19.16b}, v22.16b
     +0x334: ldr     q19, [sp, #144]
     +0x338: uxtl2   v16.8h, v3.16b
     +0x33c: umull   v3.4s, v5.4h, v13.4h
     +0x340: umull2  v17.4s, v5.8h, v13.8h
     +0x344: ldr     q5, [sp, #240]
     +0x348: movi    v18.16b, #0x18
     +0x34c: tbl     v5.16b, {v0.16b-v1.16b}, v5.16b
     +0x350: tbl     v0.16b, {v6.16b-v7.16b}, v22.16b
     +0x354: shl     v6.16b, v4.16b, #3
     +0x358: ushr    v7.16b, v4.16b, #2
     +0x35c: and     v6.16b, v6.16b, v18.16b
     +0x360: and     v18.16b, v7.16b, v23.16b
     +0x364: ldr     q7, [sp, #192]
     +0x368: usra    v6.16b, v2.16b, #5
     +0x36c: movi    v2.16b, #0x1e
     +0x370: tbl     v7.16b, {v0.16b-v1.16b}, v7.16b
     +0x374: tbl     v0.16b, {v20.16b-v21.16b}, v19.16b
     +0x378: add     v19.16b, v5.16b, v5.16b
     +0x37c: umull   v22.4s, v16.4h, v13.4h
     +0x380: and     v2.16b, v19.16b, v2.16b
     +0x384: ldr     q19, [sp, #128]
     +0x388: usra    v2.16b, v4.16b, #7
     +0x38c: movi    v4.16b, #0x10
     +0x390: tbl     v19.16b, {v0.16b-v1.16b}, v19.16b
     +0x394: ushr    v1.16b, v7.16b, #1
     +0x398: shl     v0.16b, v7.16b, #4
     +0x39c: and     v20.16b, v1.16b, v23.16b
     +0x3a0: movi    v1.16b, #0x1c
     +0x3a4: and     v4.16b, v0.16b, v4.16b
     +0x3a8: shl     v0.16b, v19.16b, #2
     +0x3ac: usra    v4.16b, v5.16b, #4
     +0x3b0: ushr    v15.16b, v19.16b, #3
     +0x3b4: and     v5.16b, v0.16b, v1.16b
     +0x3b8: uxtl2   v1.8h, v6.16b
     +0x3bc: usra    v5.16b, v7.16b, #6
     +0x3c0: umull2  v7.4s, v1.8h, v13.8h
     +0x3c4: umull   v1.4s, v1.4h, v13.4h
     +0x3c8: uxtl    v6.8h, v6.8b
     +0x3cc: umull2  v0.4s, v16.8h, v13.8h
     +0x3d0: umull2  v25.4s, v6.8h, v13.8h
     +0x3d4: str     q1, [sp, #560]
     +0x3d8: umull   v1.4s, v6.4h, v13.4h
     +0x3dc: uxtl    v6.8h, v18.8b
     +0x3e0: uxtl2   v16.8h, v18.16b
     +0x3e4: umull   v21.4s, v6.4h, v13.4h
     +0x3e8: umull2  v23.4s, v6.8h, v13.8h
     +0x3ec: uxtl2   v6.8h, v2.16b
     +0x3f0: uxtl    v18.8h, v2.8b
     +0x3f4: umull2  v2.4s, v6.8h, v13.8h
     +0x3f8: umull   v24.4s, v16.4h, v13.4h
     +0x3fc: umull2  v26.4s, v16.8h, v13.8h
     +0x400: umull2  v16.4s, v18.8h, v13.8h
     +0x404: stp     q2, q7, [sp, #608]
     +0x408: umull   v2.4s, v6.4h, v13.4h
     +0x40c: uxtl    v6.8h, v4.8b
     +0x410: uxtl2   v4.8h, v4.16b
     +0x414: umull   v28.4s, v18.4h, v13.4h
     +0x418: umull   v18.4s, v4.4h, v13.4h
     +0x41c: str     q2, [sp, #544]
     +0x420: umull2  v8.4s, v4.8h, v13.8h
     +0x424: uxtl2   v4.8h, v20.16b
     +0x428: umull   v30.4s, v6.4h, v13.4h
     +0x42c: umull2  v2.4s, v4.8h, v13.8h
     +0x430: uxtl    v20.8h, v20.8b
     +0x434: rshrn   v18.4h, v18.4s, #5
     +0x438: umull2  v27.4s, v20.8h, v13.8h
     +0x43c: rshrn   v9.4h, v30.4s, #5
     +0x440: str     q2, [sp, #576]
     +0x444: umull   v2.4s, v4.4h, v13.4h
     +0x448: uxtl    v4.8h, v5.8b
     +0x44c: uxtl2   v5.8h, v5.16b
     +0x450: umull   v12.4s, v4.4h, v13.4h
     +0x454: umull   v14.4s, v5.4h, v13.4h
     +0x458: str     q2, [sp, #512]
     +0x45c: umull2  v11.4s, v4.8h, v13.8h
     +0x460: umull2  v31.4s, v6.8h, v13.8h
     +0x464: rshrn   v6.4h, v3.4s, #5
     +0x468: rshrn   v19.4h, v14.4s, #5
     +0x46c: rshrn   v10.4h, v12.4s, #5
     +0x470: umull   v14.4s, v20.4h, v13.4h
     +0x474: rshrn   v7.4h, v21.4s, #5
     +0x478: uxtl2   v20.8h, v15.16b
     +0x47c: uxtl    v2.8h, v15.8b
     +0x480: umull2  v4.4s, v20.8h, v13.8h
     +0x484: str     q2, [sp, #592]
     +0x488: umull2  v30.4s, v2.8h, v13.8h
     +0x48c: rshrn   v2.4h, v17.4s, #5
     +0x490: umull   v15.4s, v20.4h, v13.4h
     +0x494: rshrn2  v6.8h, v1.4s, #5
     +0x498: rshrn   v20.4h, v0.4s, #5
     +0x49c: umull2  v5.4s, v5.8h, v13.8h
     +0x4a0: rshrn   v21.4h, v26.4s, #5
     +0x4a4: rshrn2  v10.8h, v11.4s, #5
     +0x4a8: rshrn   v3.4h, v23.4s, #5
     +0x4ac: rshrn2  v7.8h, v28.4s, #5
     +0x4b0: rshrn   v4.4h, v4.4s, #5
     +0x4b4: ldp     q26, q28, [sp, #96]
     +0x4b8: rshrn2  v9.8h, v14.4s, #5
     +0x4bc: rshrn   v0.4h, v31.4s, #5
     +0x4c0: rshrn2  v2.8h, v25.4s, #5
     +0x4c4: str     q4, [sp, #528]
     +0x4c8: rshrn2  v19.8h, v5.4s, #5
     +0x4cc: tbl     v5.16b, {v9.16b-v10.16b}, v26.16b
     +0x4d0: rshrn2  v0.8h, v27.4s, #5
     +0x4d4: ldr     q25, [sp, #64]
     +0x4d8: rshrn   v30.4h, v30.4s, #5
     +0x4dc: ldr     q31, [sp, #32]
     +0x4e0: rshrn   v17.4h, v15.4s, #5
     +0x4e4: mov     v1.16b, v10.16b
     +0x4e8: ldr     q14, [sp]
     +0x4ec: tbl     v4.16b, {v9.16b-v10.16b}, v25.16b
     +0x4f0: rshrn2  v3.8h, v16.4s, #5
     +0x4f4: rshrn   v11.4h, v22.4s, #5
     +0x4f8: ldr     q22, [sp, #80]
     +0x4fc: rshrn   v12.4h, v24.4s, #5
     +0x500: rshrn   v23.4h, v8.4s, #5
     +0x504: stp     q4, q5, [sp, #480]
     +0x508: ldr     q4, [sp, #688]
     +0x50c: tbl     v8.16b, {v2.16b-v3.16b}, v22.16b
     +0x510: tbl     v5.16b, {v0.16b-v1.16b}, v4.16b
     +0x514: tbl     v4.16b, {v9.16b-v10.16b}, v31.16b
     +0x518: mov     v5.h[7], v30.h[0]
     +0x51c: str     q4, [sp, #464]
     +0x520: tbl     v4.16b, {v9.16b-v10.16b}, v14.16b
     +0x524: str     q4, [sp, #448]
     +0x528: tbl     v4.16b, {v2.16b-v3.16b}, v28.16b
     +0x52c: stp     q5, q4, [sp, #416]
     +0x530: ldr     q4, [sp, #672]
     +0x534: ldr     q5, [sp, #48]
     +0x538: tbl     v15.16b, {v0.16b-v1.16b}, v4.16b
     +0x53c: ldr     q4, [sp, #656]
     +0x540: tbl     v9.16b, {v2.16b-v3.16b}, v5.16b
     +0x544: tbl     v10.16b, {v0.16b-v1.16b}, v4.16b
     +0x548: ldr     q4, [sp, #640]
     +0x54c: mov     v15.h[7], v30.h[1]
     +0x550: tbl     v29.16b, {v0.16b-v1.16b}, v4.16b
     +0x554: ldr     q0, [sp, #560]
     +0x558: ldr     q4, [sp, #16]
     +0x55c: mov     v10.h[7], v30.h[2]
     +0x560: rshrn2  v11.8h, v0.4s, #5
     +0x564: ldr     q0, [sp, #512]
     +0x568: tbl     v27.16b, {v2.16b-v3.16b}, v4.16b
     +0x56c: mov     v29.h[7], v30.h[3]
     +0x570: rshrn2  v18.8h, v0.4s, #5
     +0x574: ldr     q0, [sp, #544]
     +0x578: mov     v8.d[1], v15.d[1]
     +0x57c: mov     v9.d[1], v10.d[1]
     +0x580: rshrn2  v12.8h, v0.4s, #5
     +0x584: ldr     q0, [sp, #624]
     +0x588: tbl     v16.16b, {v18.16b-v19.16b}, v26.16b
     +0x58c: tbl     v2.16b, {v18.16b-v19.16b}, v25.16b
     +0x590: rshrn2  v20.8h, v0.4s, #5
     +0x594: ldr     q0, [sp, #608]
     +0x598: tbl     v25.16b, {v18.16b-v19.16b}, v31.16b
     +0x59c: tbl     v30.16b, {v18.16b-v19.16b}, v14.16b
     +0x5a0: rshrn2  v21.8h, v0.4s, #5
     +0x5a4: ldr     q0, [sp, #576]
     +0x5a8: tbl     v26.16b, {v11.16b-v12.16b}, v28.16b
     +0x5ac: tbl     v3.16b, {v11.16b-v12.16b}, v22.16b
     +0x5b0: rshrn2  v23.8h, v0.4s, #5
     +0x5b4: ldr     q0, [sp, #688]
     +0x5b8: mov     v24.16b, v19.16b
     +0x5bc: tbl     v1.16b, {v11.16b-v12.16b}, v5.16b
     +0x5c0: tbl     v18.16b, {v23.16b-v24.16b}, v0.16b
     +0x5c4: ldr     q0, [sp, #672]
     +0x5c8: tbl     v11.16b, {v11.16b-v12.16b}, v4.16b
     +0x5cc: mov     v25.h[7], v17.h[2]
     +0x5d0: tbl     v19.16b, {v23.16b-v24.16b}, v0.16b
     +0x5d4: ldr     q0, [sp, #656]
     +0x5d8: mov     v30.h[7], v17.h[3]
     +0x5dc: mov     v16.h[7], v17.h[0]
     +0x5e0: tbl     v12.16b, {v23.16b-v24.16b}, v0.16b
     +0x5e4: ldr     q0, [sp, #640]
     +0x5e8: mov     v2.h[7], v17.h[1]
     +0x5ec: tbl     v17.16b, {v20.16b-v21.16b}, v28.16b
     +0x5f0: tbl     v23.16b, {v23.16b-v24.16b}, v0.16b
     +0x5f4: tbl     v24.16b, {v20.16b-v21.16b}, v22.16b
     +0x5f8: tbl     v0.16b, {v20.16b-v21.16b}, v5.16b
     +0x5fc: tbl     v20.16b, {v20.16b-v21.16b}, v4.16b
     +0x600: ldr     q21, [sp, #528]
     +0x604: mov     v11.d[1], v30.d[1]
     +0x608: mov     v1.d[1], v25.d[1]
     +0x60c: mov     v23.h[7], v21.h[3]
     +0x610: mov     v12.h[7], v21.h[2]
     +0x614: mov     v26.d[1], v16.d[1]
     +0x618: stp     q1, q11, [x0, #160]
     +0x61c: ldp     q1, q16, [sp, #416]
     +0x620: mov     v20.d[1], v23.d[1]
     +0x624: mov     v0.d[1], v12.d[1]
     +0x628: mov     v3.d[1], v2.d[1]
     +0x62c: tbl     v2.16b, {v6.16b-v7.16b}, v22.16b
     +0x630: tbl     v4.16b, {v6.16b-v7.16b}, v4.16b
     +0x634: stp     q0, q20, [x0, #224]
     +0x638: ldr     q0, [sp, #592]
     +0x63c: mov     v16.d[1], v1.d[1]
     +0x640: stp     q26, q3, [x0, #128]
     +0x644: tbl     v1.16b, {v6.16b-v7.16b}, v28.16b
     +0x648: umull   v0.4s, v0.4h, v13.4h
     +0x64c: tbl     v3.16b, {v6.16b-v7.16b}, v5.16b
     +0x650: stp     q16, q8, [x0, #64]
     +0x654: ldp     q16, q7, [sp, #448]
     +0x658: rshrn   v0.4h, v0.4s, #5
     +0x65c: mov     v19.h[7], v21.h[1]
     +0x660: mov     v18.h[7], v21.h[0]
     +0x664: mov     v16.h[7], v0.h[3]
     +0x668: mov     v27.d[1], v29.d[1]
     +0x66c: ldp     q6, q5, [sp, #480]
     +0x670: mov     v7.h[7], v0.h[2]
     +0x674: mov     v24.d[1], v19.d[1]
     +0x678: mov     v17.d[1], v18.d[1]
     +0x67c: stp     q9, q27, [x0, #96]
     +0x680: mov     v6.h[7], v0.h[1]
     +0x684: mov     v4.d[1], v16.d[1]
     +0x688: mov     v5.h[7], v0.h[0]
     +0x68c: mov     v3.d[1], v7.d[1]
     +0x690: stp     q17, q24, [x0, #192]
     +0x694: mov     v2.d[1], v6.d[1]
     +0x698: mov     v1.d[1], v5.d[1]
     +0x69c: stp     q3, q4, [x0, #32]
     +0x6a0: stp     q1, q2, [x0], #256
     +0x6a4: b.ne    <mlkem_poly_decompress_d5+0x2a4>
     +0x6a8: add     sp, sp, #0x2c0
     +0x6ac: ldp     d9, d8, [sp, #48]
     +0x6b0: ldp     d11, d10, [sp, #32]
     +0x6b4: ldp     d13, d12, [sp, #16]
     +0x6b8: ldr     x29, [sp, #64]
     +0x6bc: ldp     d15, d14, [sp], #80
     +0x6c0: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O2_mc
   [layout_range "mlkem_poly_decompress_d5"];;

(*** The 30 vectors of constants of the vector code ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O2_CONSTANTS =
  map (fun k ->
    MLKEM_NATIVE_IMAGE_CONST_RULE
     (layout("mlkem_poly_decompress_d5_const" ^ string_of_int k)) 128)
   (1--30);;

let DECOMPRESS_D5_CONSTANTS_TAC =
  MAP_EVERY (fun th -> FIRST_ASSUM(fun ath ->
      if can (term_match [] `aligned_bytes_loaded s0 (word pc)
                               mlkem_native_libmlkem_clang17_O2_mc`)
             (concl ath)
      then ASSUME_TAC(MATCH_MP th ath) else failwith ""))
    MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O2_CONSTANTS;;

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
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O2_EXEC (1--6) THEN
  MP_TAC(SPECL [`r:int64`; `a:int64`; `512`; `160`]
                NONOVERLAPPING_ALIAS_CHECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O2_EXEC (7--9) THEN
  ASM_CASES_TAC `val(word_add a (word 160):int64) <= val(r:int64)` THENL
   [DECOMPRESS_D5_RESOLVE_TAC THEN body 9;
    DECOMPRESS_D5_RESOLVE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O2_EXEC
     (10--12) THEN
    DECOMPRESS_D5_RESOLVE_TAC THEN body 12];;

(*** The vector code from the label at +0x130 to the return, 614 steps (93
 *** of setup, two iterations of 257 and 7 of epilogue), with the page of the
 *** constants computed by ADRP in the steps below ***)

let DECOMPRESS_D5_ADRP_STEPS =
  [1; 2; 3; 6; 9; 12; 15; 18; 21; 24; 27; 30; 33; 36; 39; 42; 45; 48; 51; 54;
   57; 60; 63; 68; 71; 74; 77; 80; 83; 89];;

let DECOMPRESS_D5_BODY_TAC (simp:tactic) off =
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O2_EXEC [k + off] THEN
    (if mem k DECOMPRESS_D5_ADRP_STEPS then MLKEM_NATIVE_ADRP_TAC
     else ALL_TAC) THEN
    simp) (1--614);;

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
(* Correctness proof. As for mlkem_decompress 5 in                           *)
(* common/fips203/fips203.ml, the result for a 5-bit field y is the integer  *)
(* closest to 3329 * y / 32, rounding up on ties, i.e. (3329 * y + 16) DIV   *)
(* 32.                                                                       *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
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
                    mlkem_native_libmlkem_clang17_O2_mc /\
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

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. This is stated directly rather     *)
(* than by mk_safety_spec, with the events depending on the stack frame, as  *)
(* for poly_compress_d4. The safety theorem has the constants of the         *)
(* function among the regions read (unlike at gcc 12 -O2, 30 vectors).       *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT =
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
                   mlkem_native_libmlkem_clang17_O2_mc /\
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

let MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D5_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
