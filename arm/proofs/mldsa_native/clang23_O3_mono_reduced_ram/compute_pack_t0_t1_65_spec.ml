(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The vector t of key generation, split and packed: the statement. This is  *)
(* the code for mld_compute_pack_t0_t165 (mld_compute_pack_t0_t1 in sign.c)  *)
(* from mldsa-native's portable C implementation compiled by clang 23 with   *)
(* -O3 as a monolithic build with MLD_CONFIG_REDUCE_RAM (see                 *)
(* mldsa_native/README.md). It copies rho into the matrix structure on its   *)
(* stack, spills 17 vector constants of the image to the stack, and for each *)
(* of the 6 rows computes polynomial k of t = A * s1 + s2 by calls of        *)
(* mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy,                     *)
(* mldsa_poly_invntt_tomont and an inlined unpacking of s2 (eta 4), adds s2  *)
(* with an unrolled loop of 128-bit additions, and reduces and normalizes    *)
(* the sum (poly_reduce and poly_caddq, inlined loops), splits it with an    *)
(* inlined loop that computes power2round and packs t1 (with ld4, uzp and    *)
(* tbl instructions), and packs t0 with mldsa_polyt0_pack, before zeroing    *)
(* the buffers with three calls of memset. It is verified in the whole image *)
(* (see libmldsa.ml) against mld_compute_t of common/mldsa_native_sign.ml,   *)
(* the specification of the code without MLD_CONFIG_REDUCE_RAM, for s1hat    *)
(* within the bound MLD_NTT_BOUND of the C contract (see lazy_eq_spec.ml),   *)
(* using the theorems for the callees and the contracts memset_full_contract *)
(* and memcpy_full_contract of utils/mlkem_native_libc_full.ml (for the      *)
(* calls of memset and of memcpy in the callee row_lazy), assuming that the  *)
(* sampling of the matrix terminates (mld_matrix_terminates), and shown to   *)
(* be constant time and memory safe, with the events depending on rho, which *)
(* is public.                                                                *)
(*                                                                           *)
(* The stack is the 5312 bytes below the stack pointer of the caller: 160    *)
(* bytes of saved registers, 3456 bytes (0xd80) of frame, up to 32 bytes for *)
(* the realignment to 32 bytes, and the 1664 bytes of the callee row_lazy    *)
(* (the N of ~/scratch/c23/arm.stack2); the events depend on whether the     *)
(* stack pointer is a multiple of 32.                                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_65_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyt0_pack_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mld_compute_pack_t0_t165:
       +0x0: stp     d15, d14, [sp, #-160]!
       +0x4: stp     d13, d12, [sp, #16]
       +0x8: stp     d11, d10, [sp, #32]
       +0xc: stp     d9, d8, [sp, #48]
      +0x10: stp     x29, x30, [sp, #64]
      +0x14: stp     x28, x27, [sp, #80]
      +0x18: stp     x26, x25, [sp, #96]
      +0x1c: stp     x24, x23, [sp, #112]
      +0x20: stp     x22, x21, [sp, #128]
      +0x24: stp     x20, x19, [sp, #144]
      +0x28: add     x29, sp, #0x40
      +0x2c: sub     x9, sp, #0xd80
      +0x30: and     sp, x9, #0xffffffffffffffe0
      +0x34: ldr     xzr, [sp]
      +0x38: stp     x2, x3, [sp, #96]
      +0x3c: adrp    x8, <page>
      +0x40: str     x1, [sp, #88]
      +0x44: adrp    x9, <page>
      +0x48: adrp    x10, <page>
      +0x4c: ldr     x8, [x8, #4088]
      +0x50: add     x24, sp, #0x140
      +0x54: mov     w21, #0xe001
      +0x58: mov     x22, x0
      +0x5c: mov     x23, xzr
      +0x60: add     x25, sp, #0x540
      +0x64: ldr     x8, [x8]
      +0x68: add     x26, x24, #0x200
      +0x6c: add     x19, x24, #0x280
      +0x70: add     x27, x24, #0x300
      +0x74: add     x20, x24, #0x380
      +0x78: mov     w28, #0xff801fff
      +0x7c: str     x8, [sp, #3448]
      +0x80: adrp    x8, <page>
      +0x84: movk    w21, #0x7f, lsl #16
      +0x88: ldp     q0, q1, [x4]
      +0x8c: str     q0, [sp, #3392]
      +0x90: ldr     q0, [x8, #1200]
      +0x94: adrp    x8, <page>
      +0x98: str     q1, [sp, #3408]
      +0x9c: str     q0, [sp, #64]
      +0xa0: ldr     q0, [x9, #1216]
      +0xa4: adrp    x9, <page>
      +0xa8: str     q0, [sp, #48]
      +0xac: ldr     q0, [x8, #1232]
      +0xb0: adrp    x8, <page>
      +0xb4: str     q0, [sp, #32]
      +0xb8: ldr     q0, [x9, #1248]
      +0xbc: adrp    x9, <page>
      +0xc0: str     q0, [sp, #16]
      +0xc4: ldr     q0, [x10, #1264]
      +0xc8: adrp    x10, <page>
      +0xcc: str     q0, [sp, #304]
      +0xd0: ldr     q0, [x8, #1280]
      +0xd4: adrp    x8, <page>
      +0xd8: str     q0, [sp, #288]
      +0xdc: ldr     q0, [x9, #1296]
      +0xe0: adrp    x9, <page>
      +0xe4: str     q0, [sp, #272]
      +0xe8: ldr     q0, [x10, #1312]
      +0xec: adrp    x10, <page>
      +0xf0: str     q0, [sp, #256]
      +0xf4: ldr     q0, [x8, #1328]
      +0xf8: adrp    x8, <page>
      +0xfc: str     q0, [sp, #240]
     +0x100: ldr     q0, [x9, #1344]
     +0x104: adrp    x9, <page>
     +0x108: str     q0, [sp, #224]
     +0x10c: ldr     q0, [x10, #1360]
     +0x110: adrp    x10, <page>
     +0x114: str     q0, [sp, #208]
     +0x118: ldr     q0, [x8, #1376]
     +0x11c: adrp    x8, <page>
     +0x120: str     q0, [sp, #192]
     +0x124: ldr     q0, [x9, #1392]
     +0x128: adrp    x9, <page>
     +0x12c: str     q0, [sp, #176]
     +0x130: ldr     q0, [x10, #1408]
     +0x134: adrp    x10, <page>
     +0x138: str     q0, [sp, #160]
     +0x13c: ldr     q0, [x8, #1424]
     +0x140: str     q0, [sp, #144]
     +0x144: ldr     q0, [x9, #1440]
     +0x148: str     q0, [sp, #128]
     +0x14c: ldr     q0, [x10, #1456]
     +0x150: str     q0, [sp, #112]
     +0x154: ldr     x2, [sp, #96]
     +0x158: add     x0, sp, #0x540
     +0x15c: add     x1, sp, #0x940
     +0x160: mov     w3, w23
     +0x164: bl      <mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy>
     +0x168: add     x0, sp, #0x540
     +0x16c: bl      <mldsa_poly_invntt_tomont>
     +0x170: ldr     x9, [sp, #104]
     +0x174: movi    v19.16b, #0xf
     +0x178: movi    v20.4s, #0x4
     +0x17c: add     x10, x24, #0x40
     +0x180: add     x11, x24, #0x80
     +0x184: mov     x8, xzr
     +0x188: add     x9, x9, x23, lsl #7
     +0x18c: ldp     q0, q2, [x9]
     +0x190: and     v1.16b, v0.16b, v19.16b
     +0x194: ushr    v0.16b, v0.16b, #4
     +0x198: and     v7.16b, v2.16b, v19.16b
     +0x19c: ushr    v2.16b, v2.16b, #4
     +0x1a0: uxtl2   v3.8h, v1.16b
     +0x1a4: uxtl2   v4.8h, v0.16b
     +0x1a8: uxtl    v1.8h, v1.8b
     +0x1ac: uxtl    v0.8h, v0.8b
     +0x1b0: usubw   v5.4s, v20.4s, v3.4h
     +0x1b4: usubw2  v16.4s, v20.4s, v3.8h
     +0x1b8: uxtl    v3.8h, v7.8b
     +0x1bc: usubw   v6.4s, v20.4s, v4.4h
     +0x1c0: usubw2  v17.4s, v20.4s, v4.8h
     +0x1c4: uxtl    v4.8h, v2.8b
     +0x1c8: uxtl2   v2.8h, v2.16b
     +0x1cc: st2     {v5.4s-v6.4s}, [x10]
     +0x1d0: usubw   v5.4s, v20.4s, v3.4h
     +0x1d4: add     x10, x24, #0x60
     +0x1d8: usubw   v6.4s, v20.4s, v4.4h
     +0x1dc: st2     {v16.4s-v17.4s}, [x10]
     +0x1e0: add     x10, x24, #0x80
     +0x1e4: usubw2  v16.4s, v20.4s, v3.8h
     +0x1e8: uxtl2   v3.8h, v7.16b
     +0x1ec: usubw2  v17.4s, v20.4s, v4.8h
     +0x1f0: st2     {v5.4s-v6.4s}, [x10], #32
     +0x1f4: usubw   v4.4s, v20.4s, v3.4h
     +0x1f8: ldp     q6, q7, [x9, #32]
     +0x1fc: usubw   v5.4s, v20.4s, v2.4h
     +0x200: st2     {v16.4s-v17.4s}, [x10]
     +0x204: and     v16.16b, v6.16b, v19.16b
     +0x208: ushr    v6.16b, v6.16b, #4
     +0x20c: usubw2  v17.4s, v20.4s, v3.8h
     +0x210: add     x10, x11, #0x40
     +0x214: usubw2  v18.4s, v20.4s, v2.8h
     +0x218: uxtl    v2.8h, v16.8b
     +0x21c: uxtl    v3.8h, v6.8b
     +0x220: st2     {v4.4s-v5.4s}, [x10]
     +0x224: add     x10, x11, #0x60
     +0x228: add     x11, x24, #0x100
     +0x22c: usubw   v4.4s, v20.4s, v2.4h
     +0x230: usubw   v5.4s, v20.4s, v3.4h
     +0x234: st2     {v17.4s-v18.4s}, [x10]
     +0x238: usubw2  v17.4s, v20.4s, v2.8h
     +0x23c: uxtl2   v2.8h, v16.16b
     +0x240: usubw2  v18.4s, v20.4s, v3.8h
     +0x244: uxtl2   v3.8h, v6.16b
     +0x248: add     x10, x24, #0x100
     +0x24c: and     v6.16b, v7.16b, v19.16b
     +0x250: ushr    v7.16b, v7.16b, #4
     +0x254: st2     {v4.4s-v5.4s}, [x10], #32
     +0x258: usubw   v4.4s, v20.4s, v2.4h
     +0x25c: usubw   v5.4s, v20.4s, v3.4h
     +0x260: st2     {v17.4s-v18.4s}, [x10]
     +0x264: usubw2  v16.4s, v20.4s, v2.8h
     +0x268: uxtl    v2.8h, v6.8b
     +0x26c: usubw2  v17.4s, v20.4s, v3.8h
     +0x270: add     x10, x11, #0x40
     +0x274: uxtl    v3.8h, v7.8b
     +0x278: st2     {v4.4s-v5.4s}, [x10]
     +0x27c: add     x10, x11, #0x60
     +0x280: usubw   v4.4s, v20.4s, v2.4h
     +0x284: usubw   v5.4s, v20.4s, v3.4h
     +0x288: add     x11, x24, #0x180
     +0x28c: st2     {v16.4s-v17.4s}, [x10]
     +0x290: usubw2  v16.4s, v20.4s, v2.8h
     +0x294: uxtl2   v2.8h, v6.16b
     +0x298: usubw2  v17.4s, v20.4s, v3.8h
     +0x29c: uxtl2   v3.8h, v7.16b
     +0x2a0: add     x10, x24, #0x180
     +0x2a4: ldp     q6, q7, [x9, #64]
     +0x2a8: st2     {v4.4s-v5.4s}, [x10], #32
     +0x2ac: usubw   v4.4s, v20.4s, v2.4h
     +0x2b0: usubw   v5.4s, v20.4s, v3.4h
     +0x2b4: st2     {v16.4s-v17.4s}, [x10]
     +0x2b8: and     v16.16b, v6.16b, v19.16b
     +0x2bc: ushr    v6.16b, v6.16b, #4
     +0x2c0: usubw2  v17.4s, v20.4s, v2.8h
     +0x2c4: add     x10, x11, #0x40
     +0x2c8: usubw2  v18.4s, v20.4s, v3.8h
     +0x2cc: uxtl    v2.8h, v16.8b
     +0x2d0: uxtl    v3.8h, v6.8b
     +0x2d4: st2     {v4.4s-v5.4s}, [x10]
     +0x2d8: add     x10, x11, #0x60
     +0x2dc: usubw   v4.4s, v20.4s, v2.4h
     +0x2e0: usubw   v5.4s, v20.4s, v3.4h
     +0x2e4: st2     {v17.4s-v18.4s}, [x10]
     +0x2e8: usubw2  v17.4s, v20.4s, v2.8h
     +0x2ec: uxtl2   v2.8h, v16.16b
     +0x2f0: usubw2  v18.4s, v20.4s, v3.8h
     +0x2f4: uxtl2   v3.8h, v6.16b
     +0x2f8: and     v6.16b, v7.16b, v19.16b
     +0x2fc: add     x10, x24, #0x200
     +0x300: ushr    v7.16b, v7.16b, #4
     +0x304: st2     {v4.4s-v5.4s}, [x10], #32
     +0x308: usubw   v4.4s, v20.4s, v2.4h
     +0x30c: usubw   v5.4s, v20.4s, v3.4h
     +0x310: st2     {v17.4s-v18.4s}, [x10]
     +0x314: usubw2  v16.4s, v20.4s, v2.8h
     +0x318: uxtl    v2.8h, v6.8b
     +0x31c: usubw2  v17.4s, v20.4s, v3.8h
     +0x320: uxtl    v3.8h, v7.8b
     +0x324: add     x10, x26, #0x40
     +0x328: st2     {v4.4s-v5.4s}, [x10]
     +0x32c: usubw   v4.4s, v20.4s, v2.4h
     +0x330: add     x10, x26, #0x60
     +0x334: usubw   v5.4s, v20.4s, v3.4h
     +0x338: st2     {v16.4s-v17.4s}, [x10]
     +0x33c: add     x10, x24, #0x280
     +0x340: usubw2  v16.4s, v20.4s, v2.8h
     +0x344: usubw2  v17.4s, v20.4s, v3.8h
     +0x348: usubw   v2.4s, v20.4s, v1.4h
     +0x34c: usubw   v3.4s, v20.4s, v0.4h
     +0x350: st2     {v4.4s-v5.4s}, [x10], #32
     +0x354: usubw2  v4.4s, v20.4s, v1.8h
     +0x358: usubw2  v5.4s, v20.4s, v0.8h
     +0x35c: uxtl2   v0.8h, v6.16b
     +0x360: uxtl2   v1.8h, v7.16b
     +0x364: st2     {v16.4s-v17.4s}, [x10]
     +0x368: add     x10, sp, #0x140
     +0x36c: usubw2  v16.4s, v20.4s, v0.8h
     +0x370: usubw2  v17.4s, v20.4s, v1.8h
     +0x374: st2     {v2.4s-v3.4s}, [x10], #32
     +0x378: usubw   v2.4s, v20.4s, v0.4h
     +0x37c: usubw   v3.4s, v20.4s, v1.4h
     +0x380: st2     {v4.4s-v5.4s}, [x10]
     +0x384: ldp     q6, q4, [x9, #96]
     +0x388: add     x9, x19, #0x40
     +0x38c: and     v5.16b, v6.16b, v19.16b
     +0x390: ushr    v6.16b, v6.16b, #4
     +0x394: st2     {v2.4s-v3.4s}, [x9]
     +0x398: add     x9, x19, #0x60
     +0x39c: uxtl    v0.8h, v5.8b
     +0x3a0: uxtl    v1.8h, v6.8b
     +0x3a4: st2     {v16.4s-v17.4s}, [x9]
     +0x3a8: add     x9, x24, #0x300
     +0x3ac: usubw   v2.4s, v20.4s, v0.4h
     +0x3b0: usubw2  v16.4s, v20.4s, v0.8h
     +0x3b4: uxtl2   v0.8h, v5.16b
     +0x3b8: usubw   v3.4s, v20.4s, v1.4h
     +0x3bc: usubw2  v17.4s, v20.4s, v1.8h
     +0x3c0: uxtl2   v1.8h, v6.16b
     +0x3c4: and     v5.16b, v4.16b, v19.16b
     +0x3c8: ushr    v4.16b, v4.16b, #4
     +0x3cc: ldr     q19, [sp, #1456]
     +0x3d0: usubw2  v6.4s, v20.4s, v0.8h
     +0x3d4: st2     {v2.4s-v3.4s}, [x9], #32
     +0x3d8: usubw   v2.4s, v20.4s, v0.4h
     +0x3dc: usubw   v3.4s, v20.4s, v1.4h
     +0x3e0: uxtl    v0.8h, v5.8b
     +0x3e4: usubw2  v7.4s, v20.4s, v1.8h
     +0x3e8: uxtl    v1.8h, v4.8b
     +0x3ec: st2     {v16.4s-v17.4s}, [x9]
     +0x3f0: add     x9, x27, #0x40
     +0x3f4: ldr     q16, [sp, #1424]
     +0x3f8: ldp     q17, q18, [sp, #368]
     +0x3fc: st2     {v2.4s-v3.4s}, [x9]
     +0x400: usubw   v2.4s, v20.4s, v0.4h
     +0x404: add     x9, x27, #0x60
     +0x408: usubw   v3.4s, v20.4s, v1.4h
     +0x40c: st2     {v6.4s-v7.4s}, [x9]
     +0x410: add     x9, x24, #0x380
     +0x414: ldr     q6, [x10]
     +0x418: ldr     q7, [sp, #1408]
     +0x41c: st2     {v2.4s-v3.4s}, [x9], #32
     +0x420: usubw2  v2.4s, v20.4s, v0.8h
     +0x424: uxtl2   v0.8h, v5.16b
     +0x428: usubw2  v3.4s, v20.4s, v1.8h
     +0x42c: uxtl2   v1.8h, v4.16b
     +0x430: ldr     q4, [sp, #1376]
     +0x434: ldr     q5, [sp, #1392]
     +0x438: st2     {v2.4s-v3.4s}, [x9]
     +0x43c: usubw   v2.4s, v20.4s, v0.4h
     +0x440: add     x9, x20, #0x40
     +0x444: usubw   v3.4s, v20.4s, v1.4h
     +0x448: st2     {v2.4s-v3.4s}, [x9]
     +0x44c: usubw2  v2.4s, v20.4s, v0.8h
     +0x450: add     x9, x20, #0x60
     +0x454: usubw2  v3.4s, v20.4s, v1.8h
     +0x458: ldr     q1, [sp, #1360]
     +0x45c: ldr     q0, [sp, #1344]
     +0x460: st2     {v2.4s-v3.4s}, [x9]
     +0x464: ldp     q2, q3, [sp, #320]
     +0x468: add     v1.4s, v3.4s, v1.4s
     +0x46c: add     v3.4s, v6.4s, v4.4s
     +0x470: add     v0.4s, v2.4s, v0.4s
     +0x474: ldp     q4, q6, [sp, #400]
     +0x478: ldr     q2, [sp, #1440]
     +0x47c: str     q1, [sp, #1360]
     +0x480: add     v1.4s, v18.4s, v7.4s
     +0x484: str     q3, [sp, #1376]
     +0x488: add     v3.4s, v4.4s, v16.4s
     +0x48c: ldr     q16, [sp, #1520]
     +0x490: ldp     q4, q7, [sp, #432]
     +0x494: str     q0, [sp, #1344]
     +0x498: add     v0.4s, v17.4s, v5.4s
     +0x49c: ldr     q5, [sp, #1472]
     +0x4a0: str     q1, [sp, #1408]
     +0x4a4: ldp     q1, q18, [sp, #464]
     +0x4a8: add     v2.4s, v6.4s, v2.4s
     +0x4ac: add     v4.4s, v4.4s, v19.4s
     +0x4b0: add     v5.4s, v7.4s, v5.4s
     +0x4b4: ldr     q17, [sp, #1488]
     +0x4b8: ldp     q7, q19, [sp, #496]
     +0x4bc: str     q0, [sp, #1392]
     +0x4c0: ldr     q0, [sp, #1504]
     +0x4c4: ldr     q6, [sp, #1552]
     +0x4c8: str     q2, [sp, #1440]
     +0x4cc: str     q4, [sp, #1456]
     +0x4d0: add     v1.4s, v1.4s, v17.4s
     +0x4d4: ldr     q2, [sp, #1568]
     +0x4d8: add     v0.4s, v18.4s, v0.4s
     +0x4dc: str     q5, [sp, #1472]
     +0x4e0: add     v4.4s, v7.4s, v16.4s
     +0x4e4: ldp     q5, q7, [sp, #528]
     +0x4e8: str     q3, [sp, #1424]
     +0x4ec: ldr     q3, [sp, #1536]
     +0x4f0: str     q1, [sp, #1488]
     +0x4f4: ldr     q1, [sp, #1600]
     +0x4f8: str     q0, [sp, #1504]
     +0x4fc: ldp     q0, q18, [sp, #560]
     +0x500: add     v5.4s, v5.4s, v6.4s
     +0x504: add     v2.4s, v7.4s, v2.4s
     +0x508: ldr     q16, [sp, #1616]
     +0x50c: ldp     q6, q7, [sp, #592]
     +0x510: add     v3.4s, v19.4s, v3.4s
     +0x514: ldr     q17, [sp, #1584]
     +0x518: add     v1.4s, v18.4s, v1.4s
     +0x51c: ldr     q19, [sp, #1648]
     +0x520: str     q5, [sp, #1552]
     +0x524: str     q2, [sp, #1568]
     +0x528: add     v2.4s, v6.4s, v16.4s
     +0x52c: add     v0.4s, v0.4s, v17.4s
     +0x530: ldp     q5, q6, [sp, #624]
     +0x534: str     q3, [sp, #1536]
     +0x538: ldr     q3, [sp, #1664]
     +0x53c: str     q4, [sp, #1520]
     +0x540: ldr     q4, [sp, #1632]
     +0x544: str     q1, [sp, #1600]
     +0x548: ldp     q1, q18, [sp, #656]
     +0x54c: add     v5.4s, v5.4s, v19.4s
     +0x550: add     v3.4s, v6.4s, v3.4s
     +0x554: str     q0, [sp, #1584]
     +0x558: ldp     q6, q19, [sp, #688]
     +0x55c: ldr     q0, [sp, #1696]
     +0x560: ldr     q16, [sp, #1712]
     +0x564: str     q2, [sp, #1616]
     +0x568: add     v2.4s, v7.4s, v4.4s
     +0x56c: ldr     q17, [sp, #1680]
     +0x570: str     q5, [sp, #1648]
     +0x574: add     v0.4s, v18.4s, v0.4s
     +0x578: str     q3, [sp, #1664]
     +0x57c: add     v3.4s, v6.4s, v16.4s
     +0x580: ldr     q7, [sp, #1744]
     +0x584: ldp     q5, q6, [sp, #720]
     +0x588: str     q2, [sp, #1632]
     +0x58c: add     v1.4s, v1.4s, v17.4s
     +0x590: ldr     q2, [sp, #1760]
     +0x594: ldr     q4, [sp, #1728]
     +0x598: str     q0, [sp, #1696]
     +0x59c: ldp     q0, q18, [sp, #752]
     +0x5a0: add     v5.4s, v5.4s, v7.4s
     +0x5a4: add     v2.4s, v6.4s, v2.4s
     +0x5a8: ldr     q16, [sp, #1808]
     +0x5ac: ldp     q6, q7, [sp, #784]
     +0x5b0: str     q1, [sp, #1680]
     +0x5b4: ldr     q1, [sp, #1792]
     +0x5b8: ldr     q17, [sp, #1776]
     +0x5bc: str     q3, [sp, #1712]
     +0x5c0: add     v3.4s, v19.4s, v4.4s
     +0x5c4: str     q5, [sp, #1744]
     +0x5c8: ldr     q19, [sp, #1840]
     +0x5cc: add     v1.4s, v18.4s, v1.4s
     +0x5d0: str     q2, [sp, #1760]
     +0x5d4: add     v2.4s, v6.4s, v16.4s
     +0x5d8: ldp     q5, q6, [sp, #816]
     +0x5dc: add     v0.4s, v0.4s, v17.4s
     +0x5e0: ldr     q4, [sp, #1824]
     +0x5e4: str     q3, [sp, #1728]
     +0x5e8: ldr     q3, [sp, #1856]
     +0x5ec: str     q1, [sp, #1792]
     +0x5f0: ldp     q1, q18, [sp, #848]
     +0x5f4: add     v5.4s, v5.4s, v19.4s
     +0x5f8: ldr     q17, [sp, #1872]
     +0x5fc: str     q0, [sp, #1776]
     +0x600: ldr     q0, [sp, #1888]
     +0x604: str     q2, [sp, #1808]
     +0x608: add     v2.4s, v7.4s, v4.4s
     +0x60c: add     v3.4s, v6.4s, v3.4s
     +0x610: ldp     q6, q19, [sp, #880]
     +0x614: ldr     q4, [sp, #1920]
     +0x618: add     v1.4s, v1.4s, v17.4s
     +0x61c: str     q5, [sp, #1840]
     +0x620: add     v0.4s, v18.4s, v0.4s
     +0x624: ldp     q5, q18, [sp, #912]
     +0x628: ldr     q16, [sp, #1904]
     +0x62c: ldr     q7, [sp, #1936]
     +0x630: str     q2, [sp, #1824]
     +0x634: ldr     q2, [sp, #1952]
     +0x638: add     v4.4s, v19.4s, v4.4s
     +0x63c: str     q1, [sp, #1872]
     +0x640: add     v1.4s, v6.4s, v16.4s
     +0x644: add     v5.4s, v5.4s, v7.4s
     +0x648: str     q0, [sp, #1888]
     +0x64c: ldp     q7, q16, [sp, #944]
     +0x650: add     v0.4s, v18.4s, v2.4s
     +0x654: ldr     q17, [sp, #1968]
     +0x658: str     q3, [sp, #1856]
     +0x65c: ldr     q3, [sp, #1984]
     +0x660: str     q4, [sp, #1920]
     +0x664: ldp     q4, q18, [sp, #976]
     +0x668: ldr     q6, [sp, #2000]
     +0x66c: add     v7.4s, v7.4s, v17.4s
     +0x670: str     q0, [sp, #1952]
     +0x674: add     v0.4s, v16.4s, v3.4s
     +0x678: ldp     q3, q16, [sp, #1008]
     +0x67c: str     q1, [sp, #1904]
     +0x680: ldr     q1, [sp, #2016]
     +0x684: ldr     q2, [sp, #2032]
     +0x688: add     v4.4s, v4.4s, v6.4s
     +0x68c: str     q5, [sp, #1936]
     +0x690: ldr     q5, [sp, #2048]
     +0x694: ldr     q17, [sp, #2064]
     +0x698: add     v1.4s, v18.4s, v1.4s
     +0x69c: ldr     q6, [sp, #2080]
     +0x6a0: add     v2.4s, v3.4s, v2.4s
     +0x6a4: str     q7, [sp, #1968]
     +0x6a8: ldr     q3, [sp, #1040]
     +0x6ac: ldr     q7, [sp, #1056]
     +0x6b0: str     q0, [sp, #1984]
     +0x6b4: add     v0.4s, v16.4s, v5.4s
     +0x6b8: ldr     q16, [sp, #2128]
     +0x6bc: str     q4, [sp, #2000]
     +0x6c0: ldr     q4, [sp, #1104]
     +0x6c4: ldr     q18, [sp, #2096]
     +0x6c8: ldr     q5, [sp, #2112]
     +0x6cc: add     v3.4s, v3.4s, v17.4s
     +0x6d0: add     v6.4s, v7.4s, v6.4s
     +0x6d4: ldr     q7, [sp, #1072]
     +0x6d8: ldr     q17, [sp, #1088]
     +0x6dc: str     q1, [sp, #2016]
     +0x6e0: ldr     q1, [sp, #1120]
     +0x6e4: add     v4.4s, v4.4s, v16.4s
     +0x6e8: ldr     q16, [sp, #2144]
     +0x6ec: add     v7.4s, v7.4s, v18.4s
     +0x6f0: add     v5.4s, v17.4s, v5.4s
     +0x6f4: ldr     q17, [sp, #2160]
     +0x6f8: str     q2, [sp, #2032]
     +0x6fc: ldr     q2, [sp, #1136]
     +0x700: add     v1.4s, v1.4s, v16.4s
     +0x704: str     q0, [sp, #2048]
     +0x708: ldr     q0, [sp, #1152]
     +0x70c: str     q3, [sp, #2064]
     +0x710: ldr     q3, [sp, #2176]
     +0x714: ldr     q16, [sp, #2192]
     +0x718: str     q6, [sp, #2080]
     +0x71c: ldr     q6, [sp, #1168]
     +0x720: add     v2.4s, v2.4s, v17.4s
     +0x724: add     v0.4s, v0.4s, v3.4s
     +0x728: ldr     q3, [sp, #1184]
     +0x72c: str     q7, [sp, #2096]
     +0x730: add     v6.4s, v6.4s, v16.4s
     +0x734: str     q5, [sp, #2112]
     +0x738: ldr     q5, [sp, #2208]
     +0x73c: ldr     q7, [sp, #2224]
     +0x740: ldr     q16, [sp, #1200]
     +0x744: str     q4, [sp, #2128]
     +0x748: add     v3.4s, v3.4s, v5.4s
     +0x74c: ldr     q4, [sp, #1216]
     +0x750: str     q1, [sp, #2144]
     +0x754: add     v1.4s, v16.4s, v7.4s
     +0x758: str     q2, [sp, #2160]
     +0x75c: ldr     q2, [sp, #2240]
     +0x760: ldr     q5, [sp, #2256]
     +0x764: ldr     q7, [sp, #1232]
     +0x768: str     q0, [sp, #2176]
     +0x76c: ldr     q0, [sp, #2272]
     +0x770: ldr     q16, [sp, #1248]
     +0x774: add     v2.4s, v4.4s, v2.4s
     +0x778: str     q6, [sp, #2192]
     +0x77c: add     v4.4s, v7.4s, v5.4s
     +0x780: ldr     q5, [sp, #1280]
     +0x784: str     q3, [sp, #2208]
     +0x788: ldr     q3, [sp, #2288]
     +0x78c: ldr     q6, [sp, #2304]
     +0x790: str     q1, [sp, #2224]
     +0x794: ldr     q1, [sp, #1264]
     +0x798: add     v0.4s, v16.4s, v0.4s
     +0x79c: ldr     q7, [sp, #2320]
     +0x7a0: ldr     q16, [sp, #1296]
     +0x7a4: str     q2, [sp, #2240]
     +0x7a8: add     v1.4s, v1.4s, v3.4s
     +0x7ac: add     v2.4s, v5.4s, v6.4s
     +0x7b0: ldr     q3, [sp, #1312]
     +0x7b4: ldr     q5, [sp, #2336]
     +0x7b8: str     q4, [sp, #2256]
     +0x7bc: add     v4.4s, v16.4s, v7.4s
     +0x7c0: ldr     q6, [sp, #2352]
     +0x7c4: ldr     q7, [sp, #1328]
     +0x7c8: str     q0, [sp, #2272]
     +0x7cc: add     v0.4s, v3.4s, v5.4s
     +0x7d0: movi    v5.4s, #0x40, lsl #16
     +0x7d4: str     q1, [sp, #2288]
     +0x7d8: add     v1.4s, v7.4s, v6.4s
     +0x7dc: str     q2, [sp, #2304]
     +0x7e0: str     q4, [sp, #2320]
     +0x7e4: str     q0, [sp, #2336]
     +0x7e8: str     q1, [sp, #2352]
     +0x7ec: add     x9, x25, x8
     +0x7f0: dup     v4.4s, w28
     +0x7f4: add     x8, x8, #0x20
     +0x7f8: ldp     q0, q1, [x9]
     +0x7fc: cmp     x8, #0x400
     +0x800: add     v2.4s, v0.4s, v5.4s
     +0x804: add     v3.4s, v1.4s, v5.4s
     +0x808: sshr    v2.4s, v2.4s, #23
     +0x80c: sshr    v3.4s, v3.4s, #23
     +0x810: mla     v0.4s, v2.4s, v4.4s
     +0x814: mla     v1.4s, v3.4s, v4.4s
     +0x818: stp     q0, q1, [x9]
     +0x81c: b.ne    <mld_compute_pack_t0_t165+0x7ec>
     +0x820: mov     x8, xzr
     +0x824: ldrsw   x9, [x25, x8]
     +0x828: mov     w10, w9
     +0x82c: lsr     x9, x9, #31
     +0x830: add     w11, w10, w21
     +0x834: bic     w10, w10, w9
     +0x838: and     w9, w11, w9
     +0x83c: orr     w9, w9, w10
     +0x840: str     w9, [x25, x8]
     +0x844: add     x8, x8, #0x4
     +0x848: cmp     x8, #0x400
     +0x84c: b.ne    <mld_compute_pack_t0_t165+0x824>
     +0x850: movi    v6.4s, #0xf, msl #8
     +0x854: mvni    v7.4s, #0x1f, msl #8
     +0x858: mov     x8, xzr
     +0x85c: ldp     q14, q13, [sp, #48]
     +0x860: ldp     q12, q15, [sp, #16]
     +0x864: add     x9, x25, x8
     +0x868: add     x10, x24, x8
     +0x86c: add     x8, x8, #0x20
     +0x870: ldp     q0, q1, [x9]
     +0x874: cmp     x8, #0x400
     +0x878: add     v2.4s, v0.4s, v6.4s
     +0x87c: add     v3.4s, v1.4s, v6.4s
     +0x880: and     v4.16b, v2.16b, v7.16b
     +0x884: and     v5.16b, v3.16b, v7.16b
     +0x888: sshr    v2.4s, v2.4s, #13
     +0x88c: sshr    v3.4s, v3.4s, #13
     +0x890: sub     v0.4s, v0.4s, v4.4s
     +0x894: sub     v1.4s, v1.4s, v5.4s
     +0x898: stp     q2, q3, [x10]
     +0x89c: stp     q0, q1, [x9]
     +0x8a0: b.ne    <mld_compute_pack_t0_t165+0x864>
     +0x8a4: mov     x8, xzr
     +0x8a8: mov     x9, x22
     +0x8ac: add     x11, x24, x8
     +0x8b0: add     x10, x24, x8
     +0x8b4: add     x8, x8, #0x100
     +0x8b8: ld4     {v4.4s-v7.4s}, [x11], #64
     +0x8bc: cmp     x8, #0x400
     +0x8c0: ld4     {v0.4s-v3.4s}, [x11]
     +0x8c4: add     x11, x10, #0x80
     +0x8c8: add     x10, x10, #0xc0
     +0x8cc: ld4     {v20.4s-v23.4s}, [x11]
     +0x8d0: ld4     {v16.4s-v19.4s}, [x10]
     +0x8d4: ushr    v25.4s, v4.4s, #8
     +0x8d8: shl     v27.4s, v5.4s, #2
     +0x8dc: shl     v11.4s, v6.4s, #4
     +0x8e0: ushr    v24.4s, v0.4s, #8
     +0x8e4: shl     v26.4s, v1.4s, #2
     +0x8e8: shl     v8.4s, v3.4s, #6
     +0x8ec: ushr    v28.4s, v20.4s, #8
     +0x8f0: ushr    v29.4s, v16.4s, #8
     +0x8f4: shl     v30.4s, v21.4s, #2
     +0x8f8: shl     v31.4s, v17.4s, #2
     +0x8fc: orr     v25.16b, v27.16b, v25.16b
     +0x900: ushr    v27.4s, v6.4s, #4
     +0x904: orr     v24.16b, v26.16b, v24.16b
     +0x908: ushr    v26.4s, v2.4s, #4
     +0x90c: shl     v9.4s, v7.4s, #6
     +0x910: orr     v28.16b, v30.16b, v28.16b
     +0x914: ushr    v30.4s, v1.4s, #6
     +0x918: shl     v10.4s, v2.4s, #4
     +0x91c: orr     v29.16b, v31.16b, v29.16b
     +0x920: ushr    v31.4s, v5.4s, #6
     +0x924: uzp1    v24.8h, v25.8h, v24.8h
     +0x928: orr     v27.16b, v9.16b, v27.16b
     +0x92c: orr     v26.16b, v8.16b, v26.16b
     +0x930: orr     v30.16b, v10.16b, v30.16b
     +0x934: ushr    v8.4s, v21.4s, #6
     +0x938: uzp1    v25.8h, v28.8h, v29.8h
     +0x93c: uzp1    v28.8h, v4.8h, v0.8h
     +0x940: orr     v29.16b, v11.16b, v31.16b
     +0x944: uzp1    v31.8h, v20.8h, v16.8h
     +0x948: ushr    v4.4s, v7.4s, #2
     +0x94c: uzp1    v26.8h, v27.8h, v26.8h
     +0x950: ushr    v27.4s, v17.4s, #6
     +0x954: ushr    v7.4s, v19.4s, #2
     +0x958: shl     v20.4s, v23.4s, #6
     +0x95c: uzp1    v29.8h, v29.8h, v30.8h
     +0x960: shl     v30.4s, v22.4s, #4
     +0x964: ushr    v6.4s, v23.4s, #2
     +0x968: uzp1    v25.16b, v24.16b, v25.16b
     +0x96c: ushr    v5.4s, v3.4s, #2
     +0x970: ushr    v21.4s, v18.4s, #4
     +0x974: uzp1    v24.16b, v28.16b, v31.16b
     +0x978: shl     v28.4s, v18.4s, #4
     +0x97c: ushr    v31.4s, v22.4s, #4
     +0x980: orr     v1.16b, v30.16b, v8.16b
     +0x984: shl     v16.4s, v19.4s, #6
     +0x988: uzp1    v3.16b, v29.16b, v26.16b
     +0x98c: tbl     v5.16b, {v4.16b-v7.16b}, v13.16b
     +0x990: orr     v0.16b, v28.16b, v27.16b
     +0x994: orr     v17.16b, v20.16b, v31.16b
     +0x998: tbl     v2.16b, {v24.16b-v25.16b}, v14.16b
     +0x99c: orr     v16.16b, v16.16b, v21.16b
     +0x9a0: uzp1    v0.8h, v1.8h, v0.8h
     +0x9a4: ldp     q7, q1, [sp, #288]
     +0x9a8: uzp1    v6.8h, v17.8h, v16.8h
     +0x9ac: tbl     v4.16b, {v2.16b-v3.16b}, v15.16b
     +0x9b0: tbl     v2.16b, {v24.16b-v25.16b}, v1.16b
     +0x9b4: uzp1    v17.16b, v0.16b, v6.16b
     +0x9b8: tbl     v1.16b, {v4.16b-v5.16b}, v12.16b
     +0x9bc: tbl     v4.16b, {v2.16b-v3.16b}, v7.16b
     +0x9c0: ldp     q7, q2, [sp, #240]
     +0x9c4: tbl     v16.16b, {v24.16b-v25.16b}, v2.16b
     +0x9c8: uzp1    v3.16b, v26.16b, v6.16b
     +0x9cc: ldr     q6, [sp, #272]
     +0x9d0: uzp1    v2.16b, v29.16b, v0.16b
     +0x9d4: tbl     v6.16b, {v4.16b-v5.16b}, v6.16b
     +0x9d8: tbl     v4.16b, {v16.16b-v17.16b}, v7.16b
     +0x9dc: ldp     q7, q0, [sp, #208]
     +0x9e0: tbl     v16.16b, {v24.16b-v25.16b}, v7.16b
     +0x9e4: ldr     q7, [sp, #192]
     +0x9e8: tbl     v0.16b, {v4.16b-v5.16b}, v0.16b
     +0x9ec: tbl     v4.16b, {v16.16b-v17.16b}, v7.16b
     +0x9f0: ldr     q7, [sp, #160]
     +0x9f4: tbl     v2.16b, {v2.16b-v3.16b}, v7.16b
     +0x9f8: ldp     q16, q3, [sp, #128]
     +0x9fc: ldr     q7, [sp, #176]
     +0xa00: tbl     v3.16b, {v24.16b-v25.16b}, v3.16b
     +0xa04: tbl     v7.16b, {v4.16b-v5.16b}, v7.16b
     +0xa08: mov     v4.16b, v16.16b
     +0xa0c: bsl     v4.16b, v3.16b, v2.16b
     +0xa10: ldr     q2, [sp, #112]
     +0xa14: stp     q0, q7, [x9, #48]
     +0xa18: tbl     v2.16b, {v4.16b-v5.16b}, v2.16b
     +0xa1c: stp     q6, q2, [x9, #16]
     +0xa20: str     q1, [x9], #80
     +0xa24: b.ne    <mld_compute_pack_t0_t165+0x8ac>
     +0xa28: mov     w9, #0x1a0
     +0xa2c: ldr     x8, [sp, #88]
     +0xa30: add     x1, sp, #0x540
     +0xa34: madd    x0, x23, x9, x8
     +0xa38: bl      <mldsa_polyt0_pack>
     +0xa3c: add     x23, x23, #0x1
     +0xa40: add     x22, x22, #0x140
     +0xa44: cmp     x23, #0x6
     +0xa48: b.ne    <mld_compute_pack_t0_t165+0x154>
     +0xa4c: add     x0, sp, #0x140
     +0xa50: mov     w1, wzr
     +0xa54: mov     w2, #0x400
     +0xa58: add     x19, sp, #0x140
     +0xa5c: bl      <memset>
     +0xa60: add     x0, sp, #0x540
     +0xa64: mov     w1, wzr
     +0xa68: mov     w2, #0x400
     +0xa6c: add     x19, sp, #0x540
     +0xa70: bl      <memset>
     +0xa74: add     x0, sp, #0x940
     +0xa78: mov     w1, wzr
     +0xa7c: mov     w2, #0x420
     +0xa80: add     x19, sp, #0x940
     +0xa84: bl      <memset>
     +0xa88: adrp    x8, <page>
     +0xa8c: ldr     x8, [x8, #4088]
     +0xa90: ldr     x9, [sp, #3448]
     +0xa94: ldr     x8, [x8]
     +0xa98: cmp     x8, x9
     +0xa9c: b.ne    <mld_compute_pack_t0_t165+0xaf4>
     +0xaa0: sub     sp, x29, #0x40
     +0xaa4: ldp     x20, x19, [sp, #144]
     +0xaa8: ldp     x22, x21, [sp, #128]
     +0xaac: ldp     x24, x23, [sp, #112]
     +0xab0: ldp     x26, x25, [sp, #96]
     +0xab4: ldp     x28, x27, [sp, #80]
     +0xab8: ldp     x29, x30, [sp, #64]
     +0xabc: ldp     d9, d8, [sp, #48]
     +0xac0: ldp     d11, d10, [sp, #32]
     +0xac4: ldp     d13, d12, [sp, #16]
     +0xac8: ldp     d15, d14, [sp], #160
     +0xacc: mov     x0, #0x0
     +0xad0: mov     x1, #0x0
     +0xad4: mov     x2, #0x0
     +0xad8: mov     x3, #0x0
     +0xadc: mov     x4, #0x0
     +0xae0: mov     x8, #0x0
     +0xae4: mov     x9, #0x0
     +0xae8: mov     x10, #0x0
     +0xaec: mov     x11, #0x0
     +0xaf0: ret     
     +0xaf4: bl      <__stack_chk_fail>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mld_compute_pack_t0_t165";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for memset and memcpy. The vector     *)
(* s1hat (s1 in the NTT domain) of 5 polynomials sh at s1hat, with           *)
(* coefficients below MLD_NTT_BOUND = 94279689 in absolute value, the 6      *)
(* polynomials of s2 packed in 128 bytes each, s2b at s2, and rho, the 32    *)
(* bytes r at rho: the 6 polynomials of t1 packed in 320 bytes each are      *)
(* written at pkt1 and the 6 of t0 packed in 416 bytes each at t0, with t =  *)
(* mld_compute_t, if the sampling of the matrix terminates, and the result   *)
(* is 0. The stack is the 5312 bytes below the stack pointer (see above).    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\ memcpy_full_contract mc ea el ev
     ==> !pkt1 t0 s1hat s2 rho sh s2b r guard pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 r /\
          (!j. j < 1280 ==> abs(ival((sh:num->int32) j)) < &94279689) /\
          PAIRWISE nonoverlapping
           [(pkt1,1920); (t0,2496);
            (word_sub stackpointer (word 5312),5312)] /\
          ALLPAIRS nonoverlapping
           [(pkt1,1920); (t0,2496);
            (word_sub stackpointer (word 5312),5312)]
           [(s1hat,5120); (s2,768); (rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mld_compute_pack_t0_t165) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 1280
                         ==> read(memory :> bytes32
                                   (word_add s1hat (word(4 * j)))) s =
                             sh j) /\
                    (!j. j < 768
                         ==> read(memory :> bytes8(word_add s2 (word j))) s =
                             s2b j) /\
                    read (memory :> bytes(rho,32)) s = r)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    (!j. j < 1920
                         ==> read(memory :> bytes8(word_add pkt1 (word j))) s =
                             mld_polyvec_pack 320 mld_polyt1_pack
                              (mld_polyvec_map mld_poly_power2round_hi
                                (mld_compute_t 5 mld_polyeta_unpack_4 128 r
                                   sh s2b)) j) /\
                    (!j. j < 2496
                         ==> read(memory :> bytes8(word_add t0 (word j))) s =
                             mld_polyvec_pack 416 mld_polyt0_pack
                              (mld_polyvec_map mld_poly_power2round_lo
                                (mld_compute_t 5 mld_polyeta_unpack_4 128 r
                                   sh s2b)) j))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pkt1,1920); memory :> bytes(t0,2496);
                  memory :> bytes(word_sub stackpointer (word 5312),5312)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the address of memset and    *)
(* the stack, with all accesses within the arguments, the stack, the GOT     *)
(* entries and the stack guard, the region (ea,el) that memset may read and  *)
(* the constants of the callees, and the writes within the outputs and the   *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e pkt1 t0 s1hat s2 rho sh s2b r guard pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 r /\
          (!j. j < 1280 ==> abs(ival((sh:num->int32) j)) < &94279689) /\
          PAIRWISE nonoverlapping
           [(pkt1,1920); (t0,2496);
            (word_sub stackpointer (word 5312),5312)] /\
          ALLPAIRS nonoverlapping
           [(pkt1,1920); (t0,2496);
            (word_sub stackpointer (word 5312),5312)]
           [(s1hat,5120); (s2,768); (rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mld_compute_pack_t0_t165) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 1280
                         ==> read(memory :> bytes32
                                   (word_add s1hat (word(4 * j)))) s =
                             sh j) /\
                    (!j. j < 768
                         ==> read(memory :> bytes8(word_add s2 (word j))) s =
                             s2b j) /\
                    read (memory :> bytes(rho,32)) s = r /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    (!j. j < 1920
                         ==> read(memory :> bytes8(word_add pkt1 (word j))) s =
                             mld_polyvec_pack 320 mld_polyt1_pack
                              (mld_polyvec_map mld_poly_power2round_hi
                                (mld_compute_t 5 mld_polyeta_unpack_4 128 r
                                   sh s2b)) j) /\
                    (!j. j < 2496
                         ==> read(memory :> bytes8(word_add t0 (word j))) s =
                             mld_polyvec_pack 416 mld_polyt0_pack
                              (mld_polyvec_map mld_poly_power2round_lo
                                (mld_compute_t 5 mld_polyeta_unpack_4 128 r
                                   sh s2b)) j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pkt1 t0 s1hat s2 rho r guard mf mc pc
                              (word_sub stackpointer (word 5312))
                              returnaddress /\
                       memaccess_inbounds e2
                        [s1hat,5120; s2,768; rho,32; pkt1,1920; t0,2496;
                         word_sub stackpointer (word 5312),5312;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mld_compute_pack_t0_t165_consts),272]
                        [pkt1,1920; t0,2496;
                         word_sub stackpointer (word 5312),5312]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pkt1,1920); memory :> bytes(t0,2496);
                  memory :> bytes(word_sub stackpointer (word 5312),5312)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e pkt1 t0 s1hat s2 rho sh s2b r guard pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 r /\
          PAIRWISE nonoverlapping
           [(pkt1,1920); (t0,2496);
            (word_sub stackpointer (word 5312),5312)] /\
          ALLPAIRS nonoverlapping
           [(pkt1,1920); (t0,2496);
            (word_sub stackpointer (word 5312),5312)]
           [(s1hat,5120); (s2,768); (rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mld_compute_pack_t0_t165) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 1280
                         ==> read(memory :> bytes32
                                   (word_add s1hat (word(4 * j)))) s =
                             sh j) /\
                    (!j. j < 768
                         ==> read(memory :> bytes8(word_add s2 (word j))) s =
                             s2b j) /\
                    read (memory :> bytes(rho,32)) s = r /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pkt1 t0 s1hat s2 rho r guard mf mc pc
                              (word_sub stackpointer (word 5312))
                              returnaddress /\
                       memaccess_inbounds e2
                        [s1hat,5120; s2,768; rho,32; pkt1,1920; t0,2496;
                         word_sub stackpointer (word 5312),5312;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mld_compute_pack_t0_t165_consts),272]
                        [pkt1,1920; t0,2496;
                         word_sub stackpointer (word 5312),5312]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pkt1,1920); memory :> bytes(t0,2496);
                  memory :> bytes(word_sub stackpointer (word 5312),5312)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_COMPUTE_PACK_T0_T1_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
