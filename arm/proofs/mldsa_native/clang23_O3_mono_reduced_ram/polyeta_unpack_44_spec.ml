(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 3 bits per coefficient, of 2 - a: the      *)
(* statement. This is the code for mldsa44_polyeta_unpack                    *)
(* (mld_polyeta_unpack in poly_kl.c with MLDSA_ETA = 2, for ML-DSA-44) from  *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3 as *)
(* a monolithic build with MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md).*)
(* If the input (96 bytes) and the output (1024 bytes) do not overlap, clang *)
(* unpacks the first 128 coefficients from 48 bytes with one straight-line   *)
(* block of vector instructions (ld3 and tbl, with 8 vectors of constants    *)
(* that it copies from the image to the stack), and the other 128 with a     *)
(* scalar loop; otherwise the scalar loop does all of them. The function     *)
(* saves d8 to d15 and x29 and has a frame of 560 bytes with x18 cleared (the*)
(* frame has MAYCHANGE [X18] added; the gcc code had no frame and the        *)
(* statements gain the stack pointer). It is verified in the whole image (see*)
(* libmldsa.ml) against mld_polyeta_unpack_2 of common/mldsa_native_packing.ml*)
(* and shown to be constant time and memory safe.                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyeta_unpack:
       +0x0: stp     d15, d14, [sp, #-80]!
       +0x4: stp     d13, d12, [sp, #16]
       +0x8: stp     d11, d10, [sp, #32]
       +0xc: stp     d9, d8, [sp, #48]
      +0x10: str     x29, [sp, #64]
      +0x14: sub     sp, sp, #0x1e0
      +0x18: add     x8, x0, #0x400
      +0x1c: add     x9, x1, #0x60
      +0x20: cmp     x1, x8
      +0x24: ccmp    x0, x9, #0x2, cc
      +0x28: b.cs    <mldsa44_polyeta_unpack+0x34>
      +0x2c: mov     x9, xzr
      +0x30: b       <mldsa44_polyeta_unpack+0x5b0>
      +0x34: adrp    x9, <page>
      +0x38: adrp    x10, <page>
      +0x3c: adrp    x11, <page>
      +0x40: ldr     q0, [x9, #1488]
      +0x44: adrp    x9, <page>
      +0x48: mov     x8, xzr
      +0x4c: str     q0, [sp, #96]
      +0x50: ldr     q0, [x10, #1504]
      +0x54: adrp    x10, <page>
      +0x58: str     q0, [sp, #80]
      +0x5c: ldr     q0, [x9, #1520]
      +0x60: adrp    x9, <page>
      +0x64: str     q0, [sp, #64]
      +0x68: ldr     q0, [x10, #1472]
      +0x6c: adrp    x10, <page>
      +0x70: str     q0, [sp, #400]
      +0x74: ldr     q0, [x11, #1536]
      +0x78: mov     x11, x1
      +0x7c: str     q0, [sp, #48]
      +0x80: ldr     q0, [x9, #1552]
      +0x84: adrp    x9, <page>
      +0x88: str     q0, [sp, #32]
      +0x8c: ldr     q0, [x9, #1568]
      +0x90: mov     w9, #0x10
      +0x94: str     q0, [sp, #16]
      +0x98: ldr     q0, [x10, #1584]
      +0x9c: mov     x10, x1
      +0xa0: str     q0, [sp]
      +0xa4: ld3     {v5.16b-v7.16b}, [x11]
      +0xa8: movi    v4.16b, #0x7
      +0xac: add     x12, x11, #0x29
      +0xb0: ldr     q8, [sp, #400]
      +0xb4: ldur    q19, [x11, #17]
      +0xb8: ldr     q15, [sp, #64]
      +0xbc: ldur    q18, [x11, #1]
      +0xc0: mov     v12.16b, v8.16b
      +0xc4: ldur    d20, [x11, #33]
      +0xc8: add     x11, x11, #0x2d
      +0xcc: ushr    v0.16b, v5.16b, #3
      +0xd0: and     v17.16b, v5.16b, v4.16b
      +0xd4: ld1     {v20.s}[2], [x12]
      +0xd8: ushr    v2.16b, v6.16b, #1
      +0xdc: ushr    v3.16b, v6.16b, #4
      +0xe0: ushr    v5.16b, v7.16b, #2
      +0xe4: tbl     v22.16b, {v7.16b}, v15.16b
      +0xe8: tbl     v26.16b, {v7.16b}, v8.16b
      +0xec: and     v1.16b, v0.16b, v4.16b
      +0xf0: tbl     v16.16b, {v17.16b}, v8.16b
      +0xf4: ld1     {v20.h}[6], [x11]
      +0xf8: tbl     v13.16b, {v17.16b}, v15.16b
      +0xfc: add     x11, x0, x8
     +0x100: and     v30.16b, v2.16b, v4.16b
     +0x104: and     v9.16b, v3.16b, v4.16b
     +0x108: add     x8, x8, #0x200
     +0x10c: tbl     v21.16b, {v1.16b}, v8.16b
     +0x110: add     v3.4s, v26.4s, v26.4s
     +0x114: tbl     v26.16b, {v1.16b}, v15.16b
     +0x118: add     v22.4s, v22.4s, v22.4s
     +0x11c: stp     q30, q9, [sp, #304]
     +0x120: tbl     v30.16b, {v30.16b}, v15.16b
     +0x124: cmp     x8, #0x200
     +0x128: stp     q16, q21, [sp, #368]
     +0x12c: zip1    v23.2s, v16.2s, v21.2s
     +0x130: ldp     q16, q21, [sp, #80]
     +0x134: tbl     v0.16b, {v17.16b}, v16.16b
     +0x138: tbl     v25.16b, {v7.16b}, v21.16b
     +0x13c: tbl     v24.16b, {v7.16b}, v16.16b
     +0x140: tbl     v31.16b, {v17.16b}, v21.16b
     +0x144: and     v17.16b, v5.16b, v4.16b
     +0x148: movi    v5.2d, #0x0
     +0x14c: str     d23, [x11]
     +0x150: ldr     q4, [sp, #48]
     +0x154: ld3     {v27.16b-v29.16b}, [x10], #48
     +0x158: str     q0, [sp, #416]
     +0x15c: ldp     q6, q0, [sp, #16]
     +0x160: add     v23.4s, v25.4s, v25.4s
     +0x164: add     v24.4s, v24.4s, v24.4s
     +0x168: tbl     v2.16b, {v18.16b-v19.16b}, v6.16b
     +0x16c: tbl     v7.16b, {v19.16b-v20.16b}, v0.16b
     +0x170: ldr     q0, [sp]
     +0x174: movi    v6.2d, #0xff000000ff
     +0x178: tbl     v25.16b, {v18.16b}, v0.16b
     +0x17c: tbl     v0.16b, {v1.16b}, v16.16b
     +0x180: tbl     v18.16b, {v20.16b}, v4.16b
     +0x184: tbl     v4.16b, {v1.16b}, v21.16b
     +0x188: ushr    v1.16b, v27.16b, #6
     +0x18c: movi    v20.4s, #0x6
     +0x190: bif     v2.16b, v5.16b, v6.16b
     +0x194: bif     v7.16b, v5.16b, v6.16b
     +0x198: movi    v6.4s, #0x4
     +0x19c: str     q0, [sp, #240]
     +0x1a0: tbl     v0.16b, {v9.16b}, v16.16b
     +0x1a4: shl     v19.4s, v25.4s, #2
     +0x1a8: ushr    v25.16b, v28.16b, #7
     +0x1ac: tbl     v8.16b, {v1.16b}, v8.16b
     +0x1b0: shl     v18.4s, v18.4s, #2
     +0x1b4: and     v24.16b, v24.16b, v20.16b
     +0x1b8: and     v3.16b, v3.16b, v20.16b
     +0x1bc: tbl     v10.16b, {v1.16b}, v16.16b
     +0x1c0: shl     v2.4s, v2.4s, #2
     +0x1c4: shl     v7.4s, v7.4s, #2
     +0x1c8: and     v19.16b, v19.16b, v6.16b
     +0x1cc: str     q0, [sp, #288]
     +0x1d0: tbl     v0.16b, {v1.16b}, v21.16b
     +0x1d4: tbl     v14.16b, {v25.16b}, v16.16b
     +0x1d8: and     v23.16b, v23.16b, v20.16b
     +0x1dc: and     v22.16b, v22.16b, v20.16b
     +0x1e0: movi    v20.4s, #0x2
     +0x1e4: and     v2.16b, v2.16b, v6.16b
     +0x1e8: and     v18.16b, v18.16b, v6.16b
     +0x1ec: and     v7.16b, v7.16b, v6.16b
     +0x1f0: tbl     v11.16b, {v1.16b}, v15.16b
     +0x1f4: tbl     v12.16b, {v25.16b}, v12.16b
     +0x1f8: orr     v6.16b, v19.16b, v8.16b
     +0x1fc: tbl     v19.16b, {v25.16b}, v21.16b
     +0x200: tbl     v25.16b, {v25.16b}, v15.16b
     +0x204: tbl     v1.16b, {v9.16b}, v15.16b
     +0x208: orr     v2.16b, v2.16b, v0.16b
     +0x20c: tbl     v0.16b, {v17.16b}, v16.16b
     +0x210: orr     v8.16b, v7.16b, v10.16b
     +0x214: orr     v7.16b, v24.16b, v14.16b
     +0x218: sub     v24.4s, v20.4s, v13.4s
     +0x21c: sub     v26.4s, v20.4s, v26.4s
     +0x220: orr     v10.16b, v18.16b, v11.16b
     +0x224: sub     v18.4s, v20.4s, v4.4s
     +0x228: tbl     v5.16b, {v9.16b}, v21.16b
     +0x22c: orr     v19.16b, v23.16b, v19.16b
     +0x230: orr     v23.16b, v22.16b, v25.16b
     +0x234: sub     v22.4s, v20.4s, v31.4s
     +0x238: stp     q24, q0, [sp, #256]
     +0x23c: orr     v0.16b, v3.16b, v12.16b
     +0x240: sub     v31.4s, v20.4s, v1.4s
     +0x244: zip1    v1.4s, v24.4s, v26.4s
     +0x248: ushr    v9.16b, v29.16b, #5
     +0x24c: sub     v4.4s, v20.4s, v10.4s
     +0x250: sub     v28.4s, v20.4s, v23.4s
     +0x254: ldr     q23, [sp, #416]
     +0x258: stp     q0, q6, [sp, #336]
     +0x25c: tbl     v6.16b, {v17.16b}, v15.16b
     +0x260: sub     v0.4s, v20.4s, v2.4s
     +0x264: uzp2    v2.4s, v22.4s, v18.4s
     +0x268: tbl     v3.16b, {v9.16b}, v15.16b
     +0x26c: stp     q4, q26, [sp, #448]
     +0x270: sub     v26.4s, v20.4s, v23.4s
     +0x274: zip1    v23.4s, v22.4s, v18.4s
     +0x278: zip1    v11.4s, v31.4s, v28.4s
     +0x27c: mov     v1.s[2], v4.s[0]
     +0x280: sub     v25.4s, v20.4s, v30.4s
     +0x284: str     q28, [sp, #432]
     +0x288: sub     v15.4s, v20.4s, v19.4s
     +0x28c: sub     v24.4s, v20.4s, v5.4s
     +0x290: sub     v28.4s, v20.4s, v6.4s
     +0x294: trn2    v19.4s, v22.4s, v18.4s
     +0x298: zip2    v18.4s, v22.4s, v18.4s
     +0x29c: ldr     q5, [sp, #240]
     +0x2a0: uzp2    v29.4s, v2.4s, v22.4s
     +0x2a4: sub     v22.4s, v20.4s, v3.4s
     +0x2a8: mov     v23.s[2], v0.s[0]
     +0x2ac: sub     v5.4s, v20.4s, v5.4s
     +0x2b0: uzp2    v2.4s, v24.4s, v15.4s
     +0x2b4: mov     v11.s[2], v28.s[0]
     +0x2b8: ldp     q4, q3, [sp, #272]
     +0x2bc: mov     v1.s[3], v25.s[0]
     +0x2c0: mov     v27.16b, v17.16b
     +0x2c4: sub     v17.4s, v20.4s, v8.4s
     +0x2c8: mov     v19.s[2], v0.s[1]
     +0x2cc: mov     v18.s[2], v0.s[2]
     +0x2d0: mov     v29.s[2], v0.s[3]
     +0x2d4: ldr     q0, [sp, #304]
     +0x2d8: str     q25, [sp, #208]
     +0x2dc: sub     v6.4s, v20.4s, v7.4s
     +0x2e0: sub     v14.4s, v20.4s, v3.4s
     +0x2e4: zip2    v3.4s, v26.4s, v5.4s
     +0x2e8: tbl     v25.16b, {v9.16b}, v16.16b
     +0x2ec: stp     q22, q23, [sp, #128]
     +0x2f0: uzp2    v7.4s, v2.4s, v24.4s
     +0x2f4: tbl     v2.16b, {v0.16b}, v16.16b
     +0x2f8: sub     v23.4s, v20.4s, v4.4s
     +0x2fc: trn2    v4.4s, v26.4s, v5.4s
     +0x300: stp     q17, q5, [sp, #224]
     +0x304: mov     v11.s[3], v22.s[0]
     +0x308: str     q1, [x11, #384]
     +0x30c: zip1    v16.4s, v26.4s, v5.4s
     +0x310: tbl     v5.16b, {v0.16b}, v21.16b
     +0x314: mov     v22.16b, v0.16b
     +0x318: ldr     q0, [sp, #400]
     +0x31c: ldr     q1, [sp, #320]
     +0x320: stp     q19, q26, [sp, #176]
     +0x324: zip2    v10.4s, v14.4s, v6.4s
     +0x328: tbl     v30.16b, {v27.16b}, v21.16b
     +0x32c: trn2    v26.4s, v14.4s, v6.4s
     +0x330: tbl     v19.16b, {v1.16b}, v0.16b
     +0x334: str     q28, [sp, #416]
     +0x338: mov     v3.s[2], v17.s[2]
     +0x33c: str     q6, [sp, #160]
     +0x340: sub     v28.4s, v20.4s, v25.4s
     +0x344: zip1    v25.4s, v14.4s, v6.4s
     +0x348: ldp     q6, q1, [sp, #368]
     +0x34c: zip1    v13.4s, v24.4s, v15.4s
     +0x350: trn2    v12.4s, v24.4s, v15.4s
     +0x354: zip2    v15.4s, v24.4s, v15.4s
     +0x358: sub     v24.4s, v20.4s, v2.4s
     +0x35c: mov     v4.s[2], v17.s[1]
     +0x360: str     q18, [sp, #112]
     +0x364: mov     v2.16b, v27.16b
     +0x368: mov     v10.s[2], v23.s[2]
     +0x36c: sub     v27.4s, v20.4s, v6.4s
     +0x370: sub     v6.4s, v20.4s, v5.4s
     +0x374: sub     v18.4s, v20.4s, v30.4s
     +0x378: mov     v26.s[2], v23.s[1]
     +0x37c: tbl     v5.16b, {v9.16b}, v21.16b
     +0x380: sub     v30.4s, v20.4s, v19.4s
     +0x384: mov     v19.16b, v7.16b
     +0x388: mov     v3.s[3], v24.s[2]
     +0x38c: mov     v16.s[2], v17.s[0]
     +0x390: mov     v17.16b, v28.16b
     +0x394: sub     v8.4s, v20.4s, v1.4s
     +0x398: ldr     q1, [sp, #336]
     +0x39c: mov     v4.s[3], v24.s[1]
     +0x3a0: mov     v19.s[2], v18.s[3]
     +0x3a4: mov     v10.s[3], v28.s[2]
     +0x3a8: mov     v29.s[3], v6.s[3]
     +0x3ac: sub     v28.4s, v20.4s, v1.4s
     +0x3b0: mov     v26.s[3], v17.s[1]
     +0x3b4: mov     v21.16b, v17.16b
     +0x3b8: str     q17, [sp, #320]
     +0x3bc: sub     v17.4s, v20.4s, v5.4s
     +0x3c0: ldr     q1, [sp, #352]
     +0x3c4: str     q3, [x11, #320]
     +0x3c8: uzp2    v3.4s, v27.4s, v8.4s
     +0x3cc: mov     v25.s[2], v23.s[0]
     +0x3d0: stp     q23, q24, [sp, #272]
     +0x3d4: mov     v16.s[3], v24.s[0]
     +0x3d8: sub     v24.4s, v20.4s, v1.4s
     +0x3dc: str     q4, [x11, #288]
     +0x3e0: tbl     v4.16b, {v22.16b}, v0.16b
     +0x3e4: uzp2    v1.4s, v30.4s, v28.4s
     +0x3e8: mov     v19.s[3], v17.s[3]
     +0x3ec: tbl     v23.16b, {v2.16b}, v0.16b
     +0x3f0: tbl     v22.16b, {v9.16b}, v0.16b
     +0x3f4: ldp     q2, q0, [sp, #432]
     +0x3f8: uzp2    v7.4s, v3.4s, v27.4s
     +0x3fc: str     q29, [x11, #224]
     +0x400: ldr     q29, [sp, #256]
     +0x404: ldr     q3, [sp, #464]
     +0x408: mov     v25.s[3], v21.s[0]
     +0x40c: str     q16, [x11, #256]
     +0x410: str     q19, [sp, #384]
     +0x414: sub     v9.4s, v20.4s, v4.4s
     +0x418: zip2    v5.4s, v31.4s, v2.4s
     +0x41c: zip2    v19.4s, v29.4s, v3.4s
     +0x420: trn2    v4.4s, v29.4s, v3.4s
     +0x424: uzp2    v21.4s, v1.4s, v30.4s
     +0x428: trn2    v2.4s, v31.4s, v2.4s
     +0x42c: ldr     q16, [sp, #144]
     +0x430: ldr     q1, [sp, #112]
     +0x434: ldr     q3, [sp, #176]
     +0x438: mov     v7.s[2], v24.s[3]
     +0x43c: sub     v23.4s, v20.4s, v23.4s
     +0x440: mov     v16.s[3], v6.s[0]
     +0x444: mov     v1.s[3], v6.s[2]
     +0x448: sub     v22.4s, v20.4s, v22.4s
     +0x44c: mov     v3.s[3], v6.s[1]
     +0x450: ldr     q6, [sp, #416]
     +0x454: mov     v4.s[2], v0.s[1]
     +0x458: mov     v19.s[2], v0.s[2]
     +0x45c: ldr     q0, [sp, #128]
     +0x460: mov     v15.s[2], v18.s[2]
     +0x464: mov     v2.s[2], v6.s[1]
     +0x468: mov     v5.s[2], v6.s[2]
     +0x46c: mov     v7.s[3], v9.s[3]
     +0x470: str     q16, [x11, #128]
     +0x474: ldp     q16, q6, [sp, #192]
     +0x478: mov     v4.s[3], v6.s[1]
     +0x47c: str     q3, [x11, #160]
     +0x480: mov     v12.s[2], v18.s[1]
     +0x484: mov     v19.s[3], v6.s[2]
     +0x488: str     q1, [x11, #192]
     +0x48c: zip2    v1.4s, v30.4s, v28.4s
     +0x490: mov     v2.s[3], v0.s[1]
     +0x494: mov     v5.s[3], v0.s[2]
     +0x498: mov     v13.s[2], v18.s[0]
     +0x49c: str     q7, [x11, #96]
     +0x4a0: mov     v7.16b, v0.16b
     +0x4a4: zip2    v0.4s, v27.4s, v8.4s
     +0x4a8: mov     v15.s[3], v17.s[2]
     +0x4ac: mov     v12.s[3], v17.s[1]
     +0x4b0: zip1    v18.4s, v30.4s, v28.4s
     +0x4b4: mov     v1.s[2], v23.s[2]
     +0x4b8: mov     v21.s[2], v23.s[3]
     +0x4bc: str     q11, [x11, #400]
     +0x4c0: stp     q4, q2, [x11, #416]
     +0x4c4: ldr     q2, [sp, #464]
     +0x4c8: mov     v13.s[3], v17.s[0]
     +0x4cc: stp     q19, q5, [x11, #448]
     +0x4d0: mov     v0.s[2], v24.s[2]
     +0x4d4: mov     v17.16b, v6.16b
     +0x4d8: uzp2    v3.4s, v29.4s, v2.4s
     +0x4dc: ldr     q2, [sp, #432]
     +0x4e0: trn2    v4.4s, v27.4s, v8.4s
     +0x4e4: mov     v1.s[3], v22.s[2]
     +0x4e8: trn2    v6.4s, v30.4s, v28.4s
     +0x4ec: zip1    v19.4s, v27.4s, v8.4s
     +0x4f0: uzp2    v5.4s, v31.4s, v2.4s
     +0x4f4: ldr     q2, [sp, #240]
     +0x4f8: mov     v18.s[2], v23.s[0]
     +0x4fc: mov     v0.s[3], v9.s[2]
     +0x500: mov     v21.s[3], v22.s[3]
     +0x504: str     q10, [x11, #336]
     +0x508: uzp2    v20.4s, v16.4s, v2.4s
     +0x50c: ldr     q2, [sp, #160]
     +0x510: uzp2    v3.4s, v3.4s, v29.4s
     +0x514: mov     v4.s[2], v24.s[1]
     +0x518: mov     v6.s[2], v23.s[1]
     +0x51c: mov     v19.s[2], v24.s[0]
     +0x520: uzp2    v2.4s, v14.4s, v2.4s
     +0x524: uzp2    v5.4s, v5.4s, v31.4s
     +0x528: mov     v18.s[3], v22.s[0]
     +0x52c: stp     q0, q1, [x11, #64]
     +0x530: ldp     q1, q0, [sp, #272]
     +0x534: uzp2    v16.4s, v20.4s, v16.4s
     +0x538: str     q26, [x11, #304]
     +0x53c: mov     v4.s[3], v9.s[1]
     +0x540: mov     v6.s[3], v22.s[1]
     +0x544: mov     v19.s[3], v9.s[0]
     +0x548: uzp2    v20.4s, v2.4s, v14.4s
     +0x54c: ldr     q2, [sp, #448]
     +0x550: str     q25, [x11, #272]
     +0x554: str     q15, [x11, #208]
     +0x558: mov     v3.s[2], v2.s[3]
     +0x55c: ldr     q2, [sp, #416]
     +0x560: str     q12, [x11, #176]
     +0x564: str     q13, [x11, #144]
     +0x568: mov     v5.s[2], v2.s[3]
     +0x56c: ldr     q2, [sp, #224]
     +0x570: mov     v20.s[2], v1.s[3]
     +0x574: stp     q19, q18, [x11]
     +0x578: mov     v16.s[2], v2.s[3]
     +0x57c: mov     v3.s[3], v17.s[3]
     +0x580: stp     q4, q6, [x11, #32]
     +0x584: str     q21, [x11, #112]
     +0x588: mov     v5.s[3], v7.s[3]
     +0x58c: mov     v16.s[3], v0.s[3]
     +0x590: ldr     q0, [sp, #320]
     +0x594: mov     v20.s[3], v0.s[3]
     +0x598: ldr     q0, [sp, #384]
     +0x59c: stp     q3, q5, [x11, #480]
     +0x5a0: str     q0, [x11, #240]
     +0x5a4: stp     q16, q20, [x11, #352]
     +0x5a8: mov     x11, x10
     +0x5ac: b.ne    <mldsa44_polyeta_unpack+0xa4>
     +0x5b0: add     x10, x9, x9, lsl #1
     +0x5b4: add     x11, x0, x9, lsl #5
     +0x5b8: orr     x8, x9, #0xffffffffffffffe0
     +0x5bc: add     x9, x10, x1
     +0x5c0: add     x10, x11, #0x10
     +0x5c4: mov     w11, #0x2
     +0x5c8: add     x9, x9, #0x1
     +0x5cc: ldurb   w12, [x9, #-1]
     +0x5d0: adds    x8, x8, #0x1
     +0x5d4: and     w12, w12, #0x7
     +0x5d8: stur    w12, [x10, #-16]
     +0x5dc: sub     w12, w11, w12
     +0x5e0: ldurb   w13, [x9, #-1]
     +0x5e4: ubfx    w13, w13, #3, #3
     +0x5e8: stur    w13, [x10, #-12]
     +0x5ec: sub     w13, w11, w13
     +0x5f0: ldurb   w14, [x9, #-1]
     +0x5f4: ldrb    w15, [x9]
     +0x5f8: lsr     w14, w14, #6
     +0x5fc: bfi     w14, w15, #2, #1
     +0x600: stur    w14, [x10, #-8]
     +0x604: ldrb    w15, [x9]
     +0x608: ubfx    w15, w15, #1, #3
     +0x60c: stur    w15, [x10, #-4]
     +0x610: ldrb    w16, [x9]
     +0x614: ubfx    w16, w16, #4, #3
     +0x618: str     w16, [x10]
     +0x61c: ldrb    w17, [x9]
     +0x620: ldrb    w18, [x9, #1]
     +0x624: lsr     w17, w17, #7
     +0x628: bfi     w17, w18, #1, #2
     +0x62c: str     w17, [x10, #4]
     +0x630: ldrb    w18, [x9, #1]
     +0x634: ubfx    w18, w18, #2, #3
     +0x638: str     w18, [x10, #8]
     +0x63c: ldrb    w0, [x9, #1]
     +0x640: stp     w12, w13, [x10, #-16]
     +0x644: sub     w12, w11, w14
     +0x648: sub     w13, w11, w15
     +0x64c: add     x9, x9, #0x3
     +0x650: stp     w12, w13, [x10, #-8]
     +0x654: sub     w12, w11, w16
     +0x658: sub     w13, w11, w17
     +0x65c: stp     w12, w13, [x10]
     +0x660: sub     w13, w11, w0, lsr #5
     +0x664: sub     w12, w11, w18
     +0x668: stp     w12, w13, [x10, #8]
     +0x66c: add     x10, x10, #0x20
     +0x670: b.cc    <mldsa44_polyeta_unpack+0x5cc>
     +0x674: add     sp, sp, #0x1e0
     +0x678: ldp     d9, d8, [sp, #48]
     +0x67c: ldr     x29, [sp, #64]
     +0x680: ldp     d11, d10, [sp, #32]
     +0x684: ldp     d13, d12, [sp, #16]
     +0x688: ldp     d15, d14, [sp], #80
     +0x68c: mov     x0, #0x0
     +0x690: mov     x1, #0x0
     +0x694: mov     x8, #0x0
     +0x698: mov     x9, #0x0
     +0x69c: mov     x10, #0x0
     +0x6a0: mov     x11, #0x0
     +0x6a4: mov     x12, #0x0
     +0x6a8: mov     x13, #0x0
     +0x6ac: mov     x14, #0x0
     +0x6b0: mov     x15, #0x0
     +0x6b4: mov     x16, #0x0
     +0x6b8: mov     x17, #0x0
     +0x6bc: mov     x18, #0x0
     +0x6c0: ret     
 ***)

let MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa44_polyeta_unpack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,1024); (a,96); (word_sub stackpointer (word 560),560)] /\
        ALLPAIRS nonoverlapping
         [(r,1024); (word_sub stackpointer (word 560),560)]
         [(word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mldsa44_polyeta_unpack) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 96
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add r (word(4 * i))))
                            s = mld_polyeta_unpack_2 b i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18] ,,
              MAYCHANGE [memory :> bytes(r,1024);
                         memory :> bytes(word_sub stackpointer (word 560),560)])`;;

let MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the writes within the outputs.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,1024); (a,96); (word_sub stackpointer (word 560),560)] /\
        ALLPAIRS nonoverlapping
         [(r,1024); (word_sub stackpointer (word 560),560)]
         [(word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mldsa44_polyeta_unpack) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 96
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i))))
                             s = mld_polyeta_unpack_2 b i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc (word_sub stackpointer (word 560))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [a,96; r,1024; word(pc + mldsa44_polyeta_unpack_consts),128;
                       word_sub stackpointer (word 560),560]
                      [r,1024; word_sub stackpointer (word 560),560]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18] ,,
              MAYCHANGE [memory :> bytes(r,1024);
                         memory :> bytes(word_sub stackpointer (word 560),560)])`;;

let MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,1024); (a,96); (word_sub stackpointer (word 560),560)] /\
        ALLPAIRS nonoverlapping
         [(r,1024); (word_sub stackpointer (word 560),560)]
         [(word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mldsa44_polyeta_unpack) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc (word_sub stackpointer (word 560))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [a,96; r,1024; word(pc + mldsa44_polyeta_unpack_consts),128;
                       word_sub stackpointer (word 560),560]
                      [r,1024; word_sub stackpointer (word 560),560]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18] ,,
              MAYCHANGE [memory :> bytes(r,1024);
                         memory :> bytes(word_sub stackpointer (word 560),560)])`;;

let MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYETA_UNPACK_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
