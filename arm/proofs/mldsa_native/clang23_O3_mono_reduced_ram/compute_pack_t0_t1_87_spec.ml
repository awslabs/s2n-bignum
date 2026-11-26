(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The vector t of key generation, split and packed: the statement. This is  *)
(* the code for mld_compute_pack_t0_t187 (mld_compute_pack_t0_t1 in sign.c)  *)
(* from mldsa-native's portable C implementation compiled by clang 23 with   *)
(* -O3 as a monolithic build with MLD_CONFIG_REDUCE_RAM (see                 *)
(* mldsa_native/README.md). It copies rho into the matrix structure on its   *)
(* stack, spills 17 vector constants of the image to the stack, and for each *)
(* of the 8 rows computes polynomial k of t = A * s1 + s2 by calls of        *)
(* mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy,                     *)
(* mldsa_poly_invntt_tomont and mldsa87_polyeta_unpack (for s2), adds s2     *)
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
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_87_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyeta_unpack_87_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyt0_pack_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mld_compute_pack_t0_t187:
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
      +0x34: adrp    x8, <page>
      +0x38: ldr     xzr, [sp]
      +0x3c: adrp    x9, <page>
      +0x40: ldr     x8, [x8, #4088]
      +0x44: adrp    x10, <page>
      +0x48: mov     w27, #0xe001
      +0x4c: mov     x19, x3
      +0x50: mov     x20, x2
      +0x54: mov     x21, x1
      +0x58: ldr     x8, [x8]
      +0x5c: mov     x22, x0
      +0x60: mov     x23, xzr
      +0x64: add     x24, sp, #0x540
      +0x68: mov     w25, #0x60
      +0x6c: add     x26, sp, #0x140
      +0x70: str     x8, [sp, #3448]
      +0x74: mov     w8, #0xff801fff
      +0x78: movk    w27, #0x7f, lsl #16
      +0x7c: ldp     q0, q1, [x4]
      +0x80: dup     v2.4s, w8
      +0x84: adrp    x8, <page>
      +0x88: mov     w28, #0x1a0
      +0x8c: str     q0, [sp, #3392]
      +0x90: ldr     q0, [x9, #1200]
      +0x94: adrp    x9, <page>
      +0x98: stp     q0, q2, [sp, #80]
      +0x9c: ldr     q0, [x10, #1216]
      +0xa0: adrp    x10, <page>
      +0xa4: str     q1, [sp, #3408]
      +0xa8: str     q0, [sp, #64]
      +0xac: ldr     q0, [x8, #1232]
      +0xb0: adrp    x8, <page>
      +0xb4: str     q0, [sp, #48]
      +0xb8: ldr     q0, [x9, #1248]
      +0xbc: adrp    x9, <page>
      +0xc0: str     q0, [sp, #32]
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
     +0x154: add     x0, sp, #0x540
     +0x158: add     x1, sp, #0x940
     +0x15c: mov     x2, x20
     +0x160: mov     w3, w23
     +0x164: bl      <mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy>
     +0x168: add     x0, sp, #0x540
     +0x16c: bl      <mldsa_poly_invntt_tomont>
     +0x170: madd    x1, x23, x25, x19
     +0x174: add     x0, sp, #0x140
     +0x178: bl      <mldsa87_polyeta_unpack>
     +0x17c: ldp     q0, q3, [sp, #320]
     +0x180: mov     x8, xzr
     +0x184: ldr     q1, [sp, #1344]
     +0x188: ldr     q2, [sp, #1360]
     +0x18c: ldr     q4, [sp, #1392]
     +0x190: ldr     q6, [sp, #1408]
     +0x194: ldr     q16, [sp, #2320]
     +0x198: ldr     q18, [sp, #1296]
     +0x19c: add     v0.4s, v0.4s, v1.4s
     +0x1a0: add     v2.4s, v3.4s, v2.4s
     +0x1a4: ldr     q3, [sp, #1376]
     +0x1a8: ldp     q1, q5, [sp, #352]
     +0x1ac: ldr     q17, [sp, #1280]
     +0x1b0: str     q0, [sp, #1344]
     +0x1b4: add     v1.4s, v1.4s, v3.4s
     +0x1b8: add     v0.4s, v5.4s, v4.4s
     +0x1bc: str     q2, [sp, #1360]
     +0x1c0: ldp     q7, q3, [sp, #384]
     +0x1c4: ldr     q2, [sp, #1424]
     +0x1c8: ldr     q5, [sp, #1440]
     +0x1cc: str     q0, [sp, #1392]
     +0x1d0: add     v4.4s, v7.4s, v6.4s
     +0x1d4: add     v0.4s, v3.4s, v2.4s
     +0x1d8: str     q1, [sp, #1376]
     +0x1dc: ldp     q6, q2, [sp, #416]
     +0x1e0: ldr     q1, [sp, #1456]
     +0x1e4: ldr     q7, [sp, #2304]
     +0x1e8: str     q0, [sp, #1424]
     +0x1ec: add     v3.4s, v6.4s, v5.4s
     +0x1f0: add     v0.4s, v2.4s, v1.4s
     +0x1f4: ldr     q5, [sp, #1472]
     +0x1f8: ldp     q6, q2, [sp, #448]
     +0x1fc: ldr     q1, [sp, #1488]
     +0x200: str     q4, [sp, #1408]
     +0x204: str     q0, [sp, #1456]
     +0x208: add     v4.4s, v6.4s, v5.4s
     +0x20c: add     v0.4s, v2.4s, v1.4s
     +0x210: ldr     q5, [sp, #1504]
     +0x214: ldp     q6, q2, [sp, #480]
     +0x218: ldr     q1, [sp, #1520]
     +0x21c: str     q3, [sp, #1440]
     +0x220: str     q0, [sp, #1488]
     +0x224: add     v3.4s, v6.4s, v5.4s
     +0x228: add     v0.4s, v2.4s, v1.4s
     +0x22c: ldr     q5, [sp, #1536]
     +0x230: ldp     q6, q2, [sp, #512]
     +0x234: ldr     q1, [sp, #1552]
     +0x238: str     q4, [sp, #1472]
     +0x23c: str     q0, [sp, #1520]
     +0x240: add     v4.4s, v6.4s, v5.4s
     +0x244: add     v0.4s, v2.4s, v1.4s
     +0x248: ldr     q5, [sp, #1568]
     +0x24c: ldp     q6, q2, [sp, #544]
     +0x250: ldr     q1, [sp, #1584]
     +0x254: str     q3, [sp, #1504]
     +0x258: str     q0, [sp, #1552]
     +0x25c: add     v3.4s, v6.4s, v5.4s
     +0x260: add     v0.4s, v2.4s, v1.4s
     +0x264: ldr     q5, [sp, #1600]
     +0x268: ldp     q6, q2, [sp, #576]
     +0x26c: ldr     q1, [sp, #1616]
     +0x270: str     q4, [sp, #1536]
     +0x274: str     q0, [sp, #1584]
     +0x278: add     v4.4s, v6.4s, v5.4s
     +0x27c: add     v0.4s, v2.4s, v1.4s
     +0x280: ldr     q5, [sp, #1632]
     +0x284: ldp     q6, q2, [sp, #608]
     +0x288: ldr     q1, [sp, #1648]
     +0x28c: str     q3, [sp, #1568]
     +0x290: str     q0, [sp, #1616]
     +0x294: add     v3.4s, v6.4s, v5.4s
     +0x298: add     v0.4s, v2.4s, v1.4s
     +0x29c: ldr     q5, [sp, #1664]
     +0x2a0: ldp     q6, q2, [sp, #640]
     +0x2a4: ldr     q1, [sp, #1680]
     +0x2a8: str     q4, [sp, #1600]
     +0x2ac: str     q0, [sp, #1648]
     +0x2b0: add     v4.4s, v6.4s, v5.4s
     +0x2b4: add     v0.4s, v2.4s, v1.4s
     +0x2b8: ldr     q5, [sp, #1696]
     +0x2bc: ldp     q6, q2, [sp, #672]
     +0x2c0: ldr     q1, [sp, #1712]
     +0x2c4: str     q3, [sp, #1632]
     +0x2c8: str     q0, [sp, #1680]
     +0x2cc: add     v3.4s, v6.4s, v5.4s
     +0x2d0: add     v0.4s, v2.4s, v1.4s
     +0x2d4: ldr     q5, [sp, #1728]
     +0x2d8: ldp     q6, q2, [sp, #704]
     +0x2dc: ldr     q1, [sp, #1744]
     +0x2e0: str     q4, [sp, #1664]
     +0x2e4: str     q0, [sp, #1712]
     +0x2e8: add     v4.4s, v6.4s, v5.4s
     +0x2ec: add     v0.4s, v2.4s, v1.4s
     +0x2f0: ldr     q5, [sp, #1760]
     +0x2f4: ldp     q6, q2, [sp, #736]
     +0x2f8: ldr     q1, [sp, #1776]
     +0x2fc: str     q3, [sp, #1696]
     +0x300: str     q0, [sp, #1744]
     +0x304: add     v3.4s, v6.4s, v5.4s
     +0x308: add     v0.4s, v2.4s, v1.4s
     +0x30c: ldr     q5, [sp, #1792]
     +0x310: ldp     q6, q2, [sp, #768]
     +0x314: ldr     q1, [sp, #1808]
     +0x318: str     q4, [sp, #1728]
     +0x31c: str     q0, [sp, #1776]
     +0x320: add     v4.4s, v6.4s, v5.4s
     +0x324: add     v0.4s, v2.4s, v1.4s
     +0x328: ldr     q5, [sp, #1824]
     +0x32c: ldp     q6, q2, [sp, #800]
     +0x330: ldr     q1, [sp, #1840]
     +0x334: str     q3, [sp, #1760]
     +0x338: str     q0, [sp, #1808]
     +0x33c: add     v3.4s, v6.4s, v5.4s
     +0x340: add     v0.4s, v2.4s, v1.4s
     +0x344: ldr     q5, [sp, #1856]
     +0x348: ldp     q6, q2, [sp, #832]
     +0x34c: ldr     q1, [sp, #1872]
     +0x350: str     q4, [sp, #1792]
     +0x354: str     q0, [sp, #1840]
     +0x358: add     v4.4s, v6.4s, v5.4s
     +0x35c: add     v0.4s, v2.4s, v1.4s
     +0x360: ldr     q5, [sp, #1888]
     +0x364: ldp     q6, q2, [sp, #864]
     +0x368: ldr     q1, [sp, #1904]
     +0x36c: str     q3, [sp, #1824]
     +0x370: str     q0, [sp, #1872]
     +0x374: add     v3.4s, v6.4s, v5.4s
     +0x378: add     v0.4s, v2.4s, v1.4s
     +0x37c: ldr     q5, [sp, #1920]
     +0x380: ldp     q6, q2, [sp, #896]
     +0x384: ldr     q1, [sp, #1936]
     +0x388: str     q4, [sp, #1856]
     +0x38c: str     q0, [sp, #1904]
     +0x390: add     v4.4s, v6.4s, v5.4s
     +0x394: add     v0.4s, v2.4s, v1.4s
     +0x398: ldr     q5, [sp, #1952]
     +0x39c: ldp     q6, q2, [sp, #928]
     +0x3a0: ldr     q1, [sp, #1968]
     +0x3a4: str     q3, [sp, #1888]
     +0x3a8: str     q0, [sp, #1936]
     +0x3ac: add     v3.4s, v6.4s, v5.4s
     +0x3b0: add     v0.4s, v2.4s, v1.4s
     +0x3b4: ldr     q5, [sp, #1984]
     +0x3b8: ldp     q6, q2, [sp, #960]
     +0x3bc: ldr     q1, [sp, #2000]
     +0x3c0: str     q4, [sp, #1920]
     +0x3c4: str     q0, [sp, #1968]
     +0x3c8: add     v4.4s, v6.4s, v5.4s
     +0x3cc: add     v0.4s, v2.4s, v1.4s
     +0x3d0: ldr     q1, [sp, #2032]
     +0x3d4: ldp     q6, q2, [sp, #992]
     +0x3d8: ldr     q5, [sp, #2016]
     +0x3dc: str     q3, [sp, #1952]
     +0x3e0: str     q0, [sp, #2000]
     +0x3e4: add     v0.4s, v2.4s, v1.4s
     +0x3e8: ldr     q1, [sp, #2064]
     +0x3ec: ldr     q2, [sp, #1040]
     +0x3f0: add     v3.4s, v6.4s, v5.4s
     +0x3f4: ldr     q5, [sp, #2048]
     +0x3f8: ldr     q6, [sp, #1024]
     +0x3fc: str     q4, [sp, #1984]
     +0x400: str     q0, [sp, #2032]
     +0x404: add     v0.4s, v2.4s, v1.4s
     +0x408: ldr     q1, [sp, #2096]
     +0x40c: ldr     q2, [sp, #1072]
     +0x410: add     v4.4s, v6.4s, v5.4s
     +0x414: ldr     q5, [sp, #2080]
     +0x418: ldr     q6, [sp, #1056]
     +0x41c: str     q3, [sp, #2016]
     +0x420: str     q0, [sp, #2064]
     +0x424: add     v0.4s, v2.4s, v1.4s
     +0x428: ldr     q1, [sp, #2128]
     +0x42c: ldr     q2, [sp, #1104]
     +0x430: add     v3.4s, v6.4s, v5.4s
     +0x434: ldr     q5, [sp, #2112]
     +0x438: ldr     q6, [sp, #1088]
     +0x43c: str     q4, [sp, #2048]
     +0x440: str     q0, [sp, #2096]
     +0x444: add     v0.4s, v2.4s, v1.4s
     +0x448: ldr     q1, [sp, #2160]
     +0x44c: add     v4.4s, v6.4s, v5.4s
     +0x450: ldr     q5, [sp, #2144]
     +0x454: ldr     q6, [sp, #1120]
     +0x458: ldr     q2, [sp, #1136]
     +0x45c: str     q3, [sp, #2080]
     +0x460: add     v3.4s, v6.4s, v5.4s
     +0x464: ldr     q5, [sp, #2176]
     +0x468: ldr     q6, [sp, #1152]
     +0x46c: str     q0, [sp, #2128]
     +0x470: add     v0.4s, v2.4s, v1.4s
     +0x474: ldr     q1, [sp, #2192]
     +0x478: ldr     q2, [sp, #1168]
     +0x47c: str     q4, [sp, #2112]
     +0x480: add     v4.4s, v6.4s, v5.4s
     +0x484: ldr     q5, [sp, #2208]
     +0x488: ldr     q6, [sp, #1184]
     +0x48c: str     q3, [sp, #2144]
     +0x490: str     q0, [sp, #2160]
     +0x494: add     v0.4s, v2.4s, v1.4s
     +0x498: ldr     q1, [sp, #2224]
     +0x49c: add     v3.4s, v6.4s, v5.4s
     +0x4a0: ldr     q2, [sp, #1200]
     +0x4a4: ldr     q5, [sp, #2240]
     +0x4a8: ldr     q6, [sp, #1216]
     +0x4ac: str     q4, [sp, #2176]
     +0x4b0: ldr     q4, [sp, #1232]
     +0x4b4: str     q0, [sp, #2192]
     +0x4b8: ldr     q0, [sp, #2256]
     +0x4bc: add     v1.4s, v2.4s, v1.4s
     +0x4c0: str     q3, [sp, #2208]
     +0x4c4: add     v2.4s, v6.4s, v5.4s
     +0x4c8: ldr     q3, [sp, #2272]
     +0x4cc: ldr     q5, [sp, #1248]
     +0x4d0: add     v0.4s, v4.4s, v0.4s
     +0x4d4: ldr     q4, [sp, #2288]
     +0x4d8: ldr     q6, [sp, #1264]
     +0x4dc: str     q1, [sp, #2224]
     +0x4e0: add     v1.4s, v17.4s, v7.4s
     +0x4e4: add     v3.4s, v5.4s, v3.4s
     +0x4e8: add     v5.4s, v18.4s, v16.4s
     +0x4ec: str     q2, [sp, #2240]
     +0x4f0: add     v4.4s, v6.4s, v4.4s
     +0x4f4: str     q0, [sp, #2256]
     +0x4f8: ldr     q0, [sp, #2336]
     +0x4fc: ldr     q2, [sp, #1312]
     +0x500: ldr     q6, [sp, #1328]
     +0x504: str     q1, [sp, #2304]
     +0x508: str     q3, [sp, #2272]
     +0x50c: ldr     q3, [sp, #2352]
     +0x510: str     q4, [sp, #2288]
     +0x514: movi    v4.4s, #0x40, lsl #16
     +0x518: add     v0.4s, v2.4s, v0.4s
     +0x51c: add     v2.4s, v6.4s, v3.4s
     +0x520: str     q5, [sp, #2320]
     +0x524: ldr     q5, [sp, #96]
     +0x528: str     q0, [sp, #2336]
     +0x52c: str     q2, [sp, #2352]
     +0x530: add     x9, x24, x8
     +0x534: add     x8, x8, #0x20
     +0x538: ldp     q0, q1, [x9]
     +0x53c: cmp     x8, #0x400
     +0x540: add     v2.4s, v0.4s, v4.4s
     +0x544: add     v3.4s, v1.4s, v4.4s
     +0x548: sshr    v2.4s, v2.4s, #23
     +0x54c: sshr    v3.4s, v3.4s, #23
     +0x550: mla     v0.4s, v2.4s, v5.4s
     +0x554: mla     v1.4s, v3.4s, v5.4s
     +0x558: stp     q0, q1, [x9]
     +0x55c: b.ne    <mld_compute_pack_t0_t187+0x530>
     +0x560: mov     x8, xzr
     +0x564: ldrsw   x9, [x24, x8]
     +0x568: mov     w10, w9
     +0x56c: lsr     x9, x9, #31
     +0x570: add     w11, w10, w27
     +0x574: bic     w10, w10, w9
     +0x578: and     w9, w11, w9
     +0x57c: orr     w9, w9, w10
     +0x580: str     w9, [x24, x8]
     +0x584: add     x8, x8, #0x4
     +0x588: cmp     x8, #0x400
     +0x58c: b.ne    <mld_compute_pack_t0_t187+0x564>
     +0x590: movi    v6.4s, #0xf, msl #8
     +0x594: mvni    v7.4s, #0x1f, msl #8
     +0x598: mov     x8, xzr
     +0x59c: ldp     q14, q13, [sp, #64]
     +0x5a0: ldp     q12, q15, [sp, #32]
     +0x5a4: add     x9, x24, x8
     +0x5a8: add     x10, x26, x8
     +0x5ac: add     x8, x8, #0x20
     +0x5b0: ldp     q0, q1, [x9]
     +0x5b4: cmp     x8, #0x400
     +0x5b8: add     v2.4s, v0.4s, v6.4s
     +0x5bc: add     v3.4s, v1.4s, v6.4s
     +0x5c0: and     v4.16b, v2.16b, v7.16b
     +0x5c4: and     v5.16b, v3.16b, v7.16b
     +0x5c8: sshr    v2.4s, v2.4s, #13
     +0x5cc: sshr    v3.4s, v3.4s, #13
     +0x5d0: sub     v0.4s, v0.4s, v4.4s
     +0x5d4: sub     v1.4s, v1.4s, v5.4s
     +0x5d8: stp     q2, q3, [x10]
     +0x5dc: stp     q0, q1, [x9]
     +0x5e0: b.ne    <mld_compute_pack_t0_t187+0x5a4>
     +0x5e4: mov     x8, xzr
     +0x5e8: mov     x9, x22
     +0x5ec: add     x11, x26, x8
     +0x5f0: add     x10, x26, x8
     +0x5f4: add     x8, x8, #0x100
     +0x5f8: ld4     {v4.4s-v7.4s}, [x11], #64
     +0x5fc: cmp     x8, #0x400
     +0x600: ld4     {v0.4s-v3.4s}, [x11]
     +0x604: add     x11, x10, #0x80
     +0x608: add     x10, x10, #0xc0
     +0x60c: ld4     {v20.4s-v23.4s}, [x11]
     +0x610: ld4     {v16.4s-v19.4s}, [x10]
     +0x614: ushr    v25.4s, v4.4s, #8
     +0x618: shl     v27.4s, v5.4s, #2
     +0x61c: shl     v11.4s, v6.4s, #4
     +0x620: ushr    v24.4s, v0.4s, #8
     +0x624: shl     v26.4s, v1.4s, #2
     +0x628: shl     v8.4s, v3.4s, #6
     +0x62c: ushr    v28.4s, v20.4s, #8
     +0x630: ushr    v29.4s, v16.4s, #8
     +0x634: shl     v30.4s, v21.4s, #2
     +0x638: shl     v31.4s, v17.4s, #2
     +0x63c: orr     v25.16b, v27.16b, v25.16b
     +0x640: ushr    v27.4s, v6.4s, #4
     +0x644: orr     v24.16b, v26.16b, v24.16b
     +0x648: ushr    v26.4s, v2.4s, #4
     +0x64c: shl     v9.4s, v7.4s, #6
     +0x650: orr     v28.16b, v30.16b, v28.16b
     +0x654: ushr    v30.4s, v1.4s, #6
     +0x658: shl     v10.4s, v2.4s, #4
     +0x65c: orr     v29.16b, v31.16b, v29.16b
     +0x660: ushr    v31.4s, v5.4s, #6
     +0x664: uzp1    v24.8h, v25.8h, v24.8h
     +0x668: orr     v27.16b, v9.16b, v27.16b
     +0x66c: orr     v26.16b, v8.16b, v26.16b
     +0x670: orr     v30.16b, v10.16b, v30.16b
     +0x674: ushr    v8.4s, v21.4s, #6
     +0x678: uzp1    v25.8h, v28.8h, v29.8h
     +0x67c: uzp1    v28.8h, v4.8h, v0.8h
     +0x680: orr     v29.16b, v11.16b, v31.16b
     +0x684: uzp1    v31.8h, v20.8h, v16.8h
     +0x688: ushr    v4.4s, v7.4s, #2
     +0x68c: uzp1    v26.8h, v27.8h, v26.8h
     +0x690: ushr    v27.4s, v17.4s, #6
     +0x694: ushr    v7.4s, v19.4s, #2
     +0x698: shl     v20.4s, v23.4s, #6
     +0x69c: uzp1    v29.8h, v29.8h, v30.8h
     +0x6a0: shl     v30.4s, v22.4s, #4
     +0x6a4: ushr    v6.4s, v23.4s, #2
     +0x6a8: uzp1    v25.16b, v24.16b, v25.16b
     +0x6ac: ushr    v5.4s, v3.4s, #2
     +0x6b0: ushr    v21.4s, v18.4s, #4
     +0x6b4: uzp1    v24.16b, v28.16b, v31.16b
     +0x6b8: shl     v28.4s, v18.4s, #4
     +0x6bc: ushr    v31.4s, v22.4s, #4
     +0x6c0: orr     v1.16b, v30.16b, v8.16b
     +0x6c4: shl     v16.4s, v19.4s, #6
     +0x6c8: uzp1    v3.16b, v29.16b, v26.16b
     +0x6cc: tbl     v5.16b, {v4.16b-v7.16b}, v13.16b
     +0x6d0: orr     v0.16b, v28.16b, v27.16b
     +0x6d4: orr     v17.16b, v20.16b, v31.16b
     +0x6d8: tbl     v2.16b, {v24.16b-v25.16b}, v14.16b
     +0x6dc: orr     v16.16b, v16.16b, v21.16b
     +0x6e0: uzp1    v0.8h, v1.8h, v0.8h
     +0x6e4: ldp     q7, q1, [sp, #288]
     +0x6e8: uzp1    v6.8h, v17.8h, v16.8h
     +0x6ec: tbl     v4.16b, {v2.16b-v3.16b}, v15.16b
     +0x6f0: tbl     v2.16b, {v24.16b-v25.16b}, v1.16b
     +0x6f4: uzp1    v17.16b, v0.16b, v6.16b
     +0x6f8: tbl     v1.16b, {v4.16b-v5.16b}, v12.16b
     +0x6fc: tbl     v4.16b, {v2.16b-v3.16b}, v7.16b
     +0x700: ldp     q7, q2, [sp, #240]
     +0x704: tbl     v16.16b, {v24.16b-v25.16b}, v2.16b
     +0x708: uzp1    v3.16b, v26.16b, v6.16b
     +0x70c: ldr     q6, [sp, #272]
     +0x710: uzp1    v2.16b, v29.16b, v0.16b
     +0x714: tbl     v6.16b, {v4.16b-v5.16b}, v6.16b
     +0x718: tbl     v4.16b, {v16.16b-v17.16b}, v7.16b
     +0x71c: ldp     q7, q0, [sp, #208]
     +0x720: tbl     v16.16b, {v24.16b-v25.16b}, v7.16b
     +0x724: ldr     q7, [sp, #192]
     +0x728: tbl     v0.16b, {v4.16b-v5.16b}, v0.16b
     +0x72c: tbl     v4.16b, {v16.16b-v17.16b}, v7.16b
     +0x730: ldr     q7, [sp, #160]
     +0x734: tbl     v2.16b, {v2.16b-v3.16b}, v7.16b
     +0x738: ldp     q16, q3, [sp, #128]
     +0x73c: ldr     q7, [sp, #176]
     +0x740: tbl     v3.16b, {v24.16b-v25.16b}, v3.16b
     +0x744: tbl     v7.16b, {v4.16b-v5.16b}, v7.16b
     +0x748: mov     v4.16b, v16.16b
     +0x74c: bsl     v4.16b, v3.16b, v2.16b
     +0x750: ldr     q2, [sp, #112]
     +0x754: stp     q0, q7, [x9, #48]
     +0x758: tbl     v2.16b, {v4.16b-v5.16b}, v2.16b
     +0x75c: stp     q6, q2, [x9, #16]
     +0x760: str     q1, [x9], #80
     +0x764: b.ne    <mld_compute_pack_t0_t187+0x5ec>
     +0x768: madd    x0, x23, x28, x21
     +0x76c: add     x1, sp, #0x540
     +0x770: bl      <mldsa_polyt0_pack>
     +0x774: add     x23, x23, #0x1
     +0x778: add     x22, x22, #0x140
     +0x77c: cmp     x23, #0x8
     +0x780: b.ne    <mld_compute_pack_t0_t187+0x154>
     +0x784: add     x0, sp, #0x140
     +0x788: mov     w1, wzr
     +0x78c: mov     w2, #0x400
     +0x790: add     x19, sp, #0x140
     +0x794: bl      <memset>
     +0x798: add     x0, sp, #0x540
     +0x79c: mov     w1, wzr
     +0x7a0: mov     w2, #0x400
     +0x7a4: add     x19, sp, #0x540
     +0x7a8: bl      <memset>
     +0x7ac: add     x0, sp, #0x940
     +0x7b0: mov     w1, wzr
     +0x7b4: mov     w2, #0x420
     +0x7b8: add     x19, sp, #0x940
     +0x7bc: bl      <memset>
     +0x7c0: adrp    x8, <page>
     +0x7c4: ldr     x8, [x8, #4088]
     +0x7c8: ldr     x9, [sp, #3448]
     +0x7cc: ldr     x8, [x8]
     +0x7d0: cmp     x8, x9
     +0x7d4: b.ne    <mld_compute_pack_t0_t187+0x82c>
     +0x7d8: sub     sp, x29, #0x40
     +0x7dc: ldp     x20, x19, [sp, #144]
     +0x7e0: ldp     x22, x21, [sp, #128]
     +0x7e4: ldp     x24, x23, [sp, #112]
     +0x7e8: ldp     x26, x25, [sp, #96]
     +0x7ec: ldp     x28, x27, [sp, #80]
     +0x7f0: ldp     x29, x30, [sp, #64]
     +0x7f4: ldp     d9, d8, [sp, #48]
     +0x7f8: ldp     d11, d10, [sp, #32]
     +0x7fc: ldp     d13, d12, [sp, #16]
     +0x800: ldp     d15, d14, [sp], #160
     +0x804: mov     x0, #0x0
     +0x808: mov     x1, #0x0
     +0x80c: mov     x2, #0x0
     +0x810: mov     x3, #0x0
     +0x814: mov     x4, #0x0
     +0x818: mov     x8, #0x0
     +0x81c: mov     x9, #0x0
     +0x820: mov     x10, #0x0
     +0x824: mov     x11, #0x0
     +0x828: ret     
     +0x82c: bl      <__stack_chk_fail>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mld_compute_pack_t0_t187";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for memset and memcpy. The vector     *)
(* s1hat (s1 in the NTT domain) of 7 polynomials sh at s1hat, with           *)
(* coefficients below MLD_NTT_BOUND = 94279689 in absolute value, the 8      *)
(* polynomials of s2 packed in 96 bytes each, s2b at s2, and rho, the 32     *)
(* bytes r at rho: the 8 polynomials of t1 packed in 320 bytes each are      *)
(* written at pkt1 and the 8 of t0 packed in 416 bytes each at t0, with t =  *)
(* mld_compute_t, if the sampling of the matrix terminates, and the result   *)
(* is 0. The stack is the 5312 bytes below the stack pointer (see above).    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\ memcpy_full_contract mc ea el ev
     ==> !pkt1 t0 s1hat s2 rho sh s2b r guard pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 r /\
          (!j. j < 1792 ==> abs(ival((sh:num->int32) j)) < &94279689) /\
          PAIRWISE nonoverlapping
           [(pkt1,2560); (t0,3328);
            (word_sub stackpointer (word 5312),5312)] /\
          ALLPAIRS nonoverlapping
           [(pkt1,2560); (t0,3328);
            (word_sub stackpointer (word 5312),5312)]
           [(s1hat,7168); (s2,768); (rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mld_compute_pack_t0_t187) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 1792
                         ==> read(memory :> bytes32
                                   (word_add s1hat (word(4 * j)))) s =
                             sh j) /\
                    (!j. j < 768
                         ==> read(memory :> bytes8(word_add s2 (word j))) s =
                             s2b j) /\
                    read (memory :> bytes(rho,32)) s = r)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add pkt1 (word j))) s =
                             mld_polyvec_pack 320 mld_polyt1_pack
                              (mld_polyvec_map mld_poly_power2round_hi
                                (mld_compute_t 7 mld_polyeta_unpack_2 96 r
                                   sh s2b)) j) /\
                    (!j. j < 3328
                         ==> read(memory :> bytes8(word_add t0 (word j))) s =
                             mld_polyvec_pack 416 mld_polyt0_pack
                              (mld_polyvec_map mld_poly_power2round_lo
                                (mld_compute_t 7 mld_polyeta_unpack_2 96 r
                                   sh s2b)) j))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pkt1,2560); memory :> bytes(t0,3328);
                  memory :> bytes(word_sub stackpointer (word 5312),5312)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the address of memset and    *)
(* the stack, with all accesses within the arguments, the stack, the GOT     *)
(* entries and the stack guard, the region (ea,el) that memset may read and  *)
(* the constants of the callees, and the writes within the outputs and the   *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e pkt1 t0 s1hat s2 rho sh s2b r guard pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 r /\
          (!j. j < 1792 ==> abs(ival((sh:num->int32) j)) < &94279689) /\
          PAIRWISE nonoverlapping
           [(pkt1,2560); (t0,3328);
            (word_sub stackpointer (word 5312),5312)] /\
          ALLPAIRS nonoverlapping
           [(pkt1,2560); (t0,3328);
            (word_sub stackpointer (word 5312),5312)]
           [(s1hat,7168); (s2,768); (rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mld_compute_pack_t0_t187) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 1792
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
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add pkt1 (word j))) s =
                             mld_polyvec_pack 320 mld_polyt1_pack
                              (mld_polyvec_map mld_poly_power2round_hi
                                (mld_compute_t 7 mld_polyeta_unpack_2 96 r
                                   sh s2b)) j) /\
                    (!j. j < 3328
                         ==> read(memory :> bytes8(word_add t0 (word j))) s =
                             mld_polyvec_pack 416 mld_polyt0_pack
                              (mld_polyvec_map mld_poly_power2round_lo
                                (mld_compute_t 7 mld_polyeta_unpack_2 96 r
                                   sh s2b)) j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pkt1 t0 s1hat s2 rho r guard mf mc pc
                              (word_sub stackpointer (word 5312))
                              returnaddress /\
                       memaccess_inbounds e2
                        [s1hat,7168; s2,768; rho,32; pkt1,2560; t0,3328;
                         word_sub stackpointer (word 5312),5312;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mld_compute_pack_t0_t187_consts),272;
                         word(pc + mldsa87_polyeta_unpack_consts),128]
                        [pkt1,2560; t0,3328;
                         word_sub stackpointer (word 5312),5312]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pkt1,2560); memory :> bytes(t0,3328);
                  memory :> bytes(word_sub stackpointer (word 5312),5312)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e pkt1 t0 s1hat s2 rho sh s2b r guard pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 r /\
          PAIRWISE nonoverlapping
           [(pkt1,2560); (t0,3328);
            (word_sub stackpointer (word 5312),5312)] /\
          ALLPAIRS nonoverlapping
           [(pkt1,2560); (t0,3328);
            (word_sub stackpointer (word 5312),5312)]
           [(s1hat,7168); (s2,768); (rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mld_compute_pack_t0_t187) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 1792
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
                        [s1hat,7168; s2,768; rho,32; pkt1,2560; t0,3328;
                         word_sub stackpointer (word 5312),5312;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mld_compute_pack_t0_t187_consts),272;
                         word(pc + mldsa87_polyeta_unpack_consts),128]
                        [pkt1,2560; t0,3328;
                         word_sub stackpointer (word 5312),5312]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pkt1,2560); memory :> bytes(t0,3328);
                  memory :> bytes(word_sub stackpointer (word 5312),5312)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
