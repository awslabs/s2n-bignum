(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Row i of the product of the matrix A with a vector in the NTT domain,     *)
(* with A sampled on demand: the statement. This is the code for             *)
(* mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy                      *)
(* (mld_polyvec_matrix_pointwise_montgomery_row_lazy in polyvec_lazy.c) from *)
(* mldsa-native's portable C implementation compiled by clang 23 with -O3 as *)
(* a monolithic build with MLD_CONFIG_REDUCE_RAM (see                        *)
(* mldsa_native/README.md). The structure mld_polymat_lazy at mat has a      *)
(* polynomial cur (1024 bytes) and then the 32 bytes of rho, which           *)
(* mld_polyvec_matrix_expand_lazy, inlined into the callers, copies there.   *)
(* The code copies rho to a buffer of 64 bytes on the stack, aligned to 32   *)
(* bytes with an and of the stack pointer, with the indices j and i of an    *)
(* entry after it, and for each of the 4 entries of row i calls              *)
(* mldsa_poly_uniform to sample it and multiplies it with the polynomial of  *)
(* the vector in NTT domain (inlined, with the sum and the reduction),       *)
(* before zeroing the buffer. The stack is the 1664 bytes of the frame and   *)
(* of mldsa_poly_uniform. It is verified in the whole image (see             *)
(* libmldsa.ml) against mld_polyvec_matrix_row_lazy of                       *)
(* common/mldsa_native_lazy.ml, using the theorem for mldsa_poly_uniform and *)
(* the contracts memset_full_contract and memcpy_full_contract of            *)
(* utils/mldsa_native_libc.ml for the memset and memcpy of that function,    *)
(* assuming that the sampling of the entries terminates                      *)
(* (mld_matrix_terminates), and shown to be constant time and memory safe,   *)
(* with the events depending on rho, which is public.                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_lazy.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/poly_uniform_spec.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy:
       +0x0: stp     x29, x30, [sp, #-64]!
       +0x4: stp     x24, x23, [sp, #16]
       +0x8: stp     x22, x21, [sp, #32]
       +0xc: stp     x20, x19, [sp, #48]
      +0x10: mov     x29, sp
      +0x14: sub     x9, sp, #0x60
      +0x18: and     sp, x9, #0xffffffffffffffe0
      +0x1c: adrp    x8, <page>
      +0x20: mov     x20, x1
      +0x24: mov     x24, #0x200100000000
      +0x28: ldr     x8, [x8, #4088]
      +0x2c: add     x23, x1, #0x400
      +0x30: mov     w22, w3
      +0x34: mov     x21, x2
      +0x38: mov     x19, x0
      +0x3c: movk    x24, #0x380, lsl #48
      +0x40: ldr     x8, [x8]
      +0x44: str     x8, [sp, #88]
      +0x48: ldr     q0, [x1, #1024]
      +0x4c: ldr     q1, [x1, #1040]
      +0x50: mov     x1, sp
      +0x54: strb    wzr, [sp, #32]
      +0x58: stp     q0, q1, [sp]
      +0x5c: strb    w3, [sp, #33]
      +0x60: bl      <mldsa_poly_uniform>
      +0x64: mov     x8, xzr
      +0x68: mov     x9, #0xffffffffff801fff
      +0x6c: ldrsw   x10, [x19, x8]
      +0x70: ldrsw   x11, [x21, x8]
      +0x74: smull   x10, w11, w10
      +0x78: mul     x11, x10, x24
      +0x7c: asr     x11, x11, #32
      +0x80: smaddl  x10, w11, w9, x10
      +0x84: lsr     x10, x10, #32
      +0x88: str     w10, [x19, x8]
      +0x8c: add     x8, x8, #0x4
      +0x90: cmp     x8, #0x400
      +0x94: b.ne    <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x6c>
      +0x98: mov     w8, #0x1
      +0x9c: mov     x1, sp
      +0xa0: mov     x0, x20
      +0xa4: strb    w8, [sp, #32]
      +0xa8: strb    w22, [sp, #33]
      +0xac: bl      <mldsa_poly_uniform>
      +0xb0: mov     x8, xzr
      +0xb4: add     x9, x21, #0x400
      +0xb8: mov     x10, #0xffffffffff801fff
      +0xbc: ldrsw   x11, [x20, x8]
      +0xc0: ldrsw   x12, [x9, x8]
      +0xc4: smull   x11, w12, w11
      +0xc8: mul     x12, x11, x24
      +0xcc: asr     x12, x12, #32
      +0xd0: smaddl  x11, w12, w10, x11
      +0xd4: lsr     x11, x11, #32
      +0xd8: str     w11, [x20, x8]
      +0xdc: add     x8, x8, #0x4
      +0xe0: cmp     x8, #0x400
      +0xe4: b.ne    <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0xbc>
      +0xe8: add     x8, x19, #0x400
      +0xec: cmp     x20, x8
      +0xf0: ccmp    x19, x23, #0x2, cc
      +0xf4: b.cs    <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x11c>
      +0xf8: mov     x8, xzr
      +0xfc: ldr     w9, [x19, x8]
     +0x100: ldr     w10, [x20, x8]
     +0x104: add     w9, w10, w9
     +0x108: str     w9, [x19, x8]
     +0x10c: add     x8, x8, #0x4
     +0x110: cmp     x8, #0x400
     +0x114: b.ne    <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0xfc>
     +0x118: b       <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x3a8>
     +0x11c: ldp     q0, q3, [x20]
     +0x120: ldr     q7, [x20, #64]
     +0x124: ldp     q1, q2, [x19]
     +0x128: ldp     q17, q18, [x20, #960]
     +0x12c: add     v0.4s, v0.4s, v1.4s
     +0x130: ldp     q1, q5, [x20, #32]
     +0x134: add     v2.4s, v3.4s, v2.4s
     +0x138: ldp     q3, q4, [x19, #32]
     +0x13c: add     v1.4s, v1.4s, v3.4s
     +0x140: stp     q0, q2, [x19]
     +0x144: add     v0.4s, v5.4s, v4.4s
     +0x148: ldp     q6, q2, [x19, #64]
     +0x14c: stp     q1, q0, [x19, #32]
     +0x150: ldp     q5, q1, [x19, #96]
     +0x154: add     v4.4s, v7.4s, v6.4s
     +0x158: ldp     q3, q6, [x20, #80]
     +0x15c: ldp     q7, q16, [x19, #960]
     +0x160: add     v0.4s, v3.4s, v2.4s
     +0x164: add     v3.4s, v6.4s, v5.4s
     +0x168: ldp     q2, q6, [x20, #112]
     +0x16c: stp     q4, q0, [x19, #64]
     +0x170: add     v0.4s, v2.4s, v1.4s
     +0x174: ldp     q5, q1, [x19, #128]
     +0x178: add     v4.4s, v6.4s, v5.4s
     +0x17c: ldp     q2, q6, [x20, #144]
     +0x180: stp     q3, q0, [x19, #96]
     +0x184: add     v0.4s, v2.4s, v1.4s
     +0x188: ldp     q5, q1, [x19, #160]
     +0x18c: add     v3.4s, v6.4s, v5.4s
     +0x190: ldp     q2, q6, [x20, #176]
     +0x194: stp     q4, q0, [x19, #128]
     +0x198: add     v0.4s, v2.4s, v1.4s
     +0x19c: ldp     q5, q1, [x19, #192]
     +0x1a0: add     v4.4s, v6.4s, v5.4s
     +0x1a4: ldp     q2, q6, [x20, #208]
     +0x1a8: stp     q3, q0, [x19, #160]
     +0x1ac: add     v0.4s, v2.4s, v1.4s
     +0x1b0: ldp     q5, q1, [x19, #224]
     +0x1b4: add     v3.4s, v6.4s, v5.4s
     +0x1b8: ldp     q2, q6, [x20, #240]
     +0x1bc: stp     q4, q0, [x19, #192]
     +0x1c0: add     v0.4s, v2.4s, v1.4s
     +0x1c4: ldp     q5, q1, [x19, #256]
     +0x1c8: add     v4.4s, v6.4s, v5.4s
     +0x1cc: ldp     q2, q6, [x20, #272]
     +0x1d0: stp     q3, q0, [x19, #224]
     +0x1d4: add     v0.4s, v2.4s, v1.4s
     +0x1d8: ldp     q5, q1, [x19, #288]
     +0x1dc: add     v3.4s, v6.4s, v5.4s
     +0x1e0: ldp     q2, q6, [x20, #304]
     +0x1e4: stp     q4, q0, [x19, #256]
     +0x1e8: add     v0.4s, v2.4s, v1.4s
     +0x1ec: ldp     q5, q1, [x19, #320]
     +0x1f0: add     v4.4s, v6.4s, v5.4s
     +0x1f4: ldp     q2, q6, [x20, #336]
     +0x1f8: stp     q3, q0, [x19, #288]
     +0x1fc: add     v0.4s, v2.4s, v1.4s
     +0x200: ldp     q5, q1, [x19, #352]
     +0x204: add     v3.4s, v6.4s, v5.4s
     +0x208: ldp     q2, q6, [x20, #368]
     +0x20c: stp     q4, q0, [x19, #320]
     +0x210: add     v0.4s, v2.4s, v1.4s
     +0x214: ldp     q5, q1, [x19, #384]
     +0x218: add     v4.4s, v6.4s, v5.4s
     +0x21c: ldp     q2, q6, [x20, #400]
     +0x220: stp     q3, q0, [x19, #352]
     +0x224: add     v0.4s, v2.4s, v1.4s
     +0x228: ldp     q5, q1, [x19, #416]
     +0x22c: add     v3.4s, v6.4s, v5.4s
     +0x230: ldp     q2, q6, [x20, #432]
     +0x234: stp     q4, q0, [x19, #384]
     +0x238: add     v0.4s, v2.4s, v1.4s
     +0x23c: ldp     q5, q1, [x19, #448]
     +0x240: add     v4.4s, v6.4s, v5.4s
     +0x244: ldp     q2, q6, [x20, #464]
     +0x248: stp     q3, q0, [x19, #416]
     +0x24c: add     v0.4s, v2.4s, v1.4s
     +0x250: ldp     q5, q1, [x19, #480]
     +0x254: add     v3.4s, v6.4s, v5.4s
     +0x258: ldp     q2, q6, [x20, #496]
     +0x25c: stp     q4, q0, [x19, #448]
     +0x260: add     v0.4s, v2.4s, v1.4s
     +0x264: ldp     q5, q1, [x19, #512]
     +0x268: add     v4.4s, v6.4s, v5.4s
     +0x26c: ldp     q2, q6, [x20, #528]
     +0x270: stp     q3, q0, [x19, #480]
     +0x274: add     v0.4s, v2.4s, v1.4s
     +0x278: ldp     q5, q1, [x19, #544]
     +0x27c: add     v3.4s, v6.4s, v5.4s
     +0x280: ldp     q2, q6, [x20, #560]
     +0x284: stp     q4, q0, [x19, #512]
     +0x288: add     v0.4s, v2.4s, v1.4s
     +0x28c: ldp     q5, q1, [x19, #576]
     +0x290: add     v4.4s, v6.4s, v5.4s
     +0x294: ldp     q2, q6, [x20, #592]
     +0x298: stp     q3, q0, [x19, #544]
     +0x29c: add     v0.4s, v2.4s, v1.4s
     +0x2a0: ldp     q5, q1, [x19, #608]
     +0x2a4: add     v3.4s, v6.4s, v5.4s
     +0x2a8: ldp     q2, q6, [x20, #624]
     +0x2ac: stp     q4, q0, [x19, #576]
     +0x2b0: add     v0.4s, v2.4s, v1.4s
     +0x2b4: ldp     q5, q1, [x19, #640]
     +0x2b8: add     v4.4s, v6.4s, v5.4s
     +0x2bc: ldp     q2, q6, [x20, #656]
     +0x2c0: stp     q3, q0, [x19, #608]
     +0x2c4: add     v0.4s, v2.4s, v1.4s
     +0x2c8: ldp     q5, q1, [x19, #672]
     +0x2cc: add     v3.4s, v6.4s, v5.4s
     +0x2d0: ldp     q2, q6, [x20, #688]
     +0x2d4: stp     q4, q0, [x19, #640]
     +0x2d8: add     v0.4s, v2.4s, v1.4s
     +0x2dc: ldp     q5, q1, [x19, #704]
     +0x2e0: add     v4.4s, v6.4s, v5.4s
     +0x2e4: ldp     q2, q6, [x20, #720]
     +0x2e8: stp     q3, q0, [x19, #672]
     +0x2ec: add     v0.4s, v2.4s, v1.4s
     +0x2f0: ldp     q5, q1, [x19, #736]
     +0x2f4: add     v3.4s, v6.4s, v5.4s
     +0x2f8: ldp     q2, q6, [x20, #752]
     +0x2fc: stp     q4, q0, [x19, #704]
     +0x300: add     v0.4s, v2.4s, v1.4s
     +0x304: ldp     q5, q1, [x19, #768]
     +0x308: add     v4.4s, v6.4s, v5.4s
     +0x30c: ldp     q2, q6, [x20, #784]
     +0x310: stp     q3, q0, [x19, #736]
     +0x314: add     v0.4s, v2.4s, v1.4s
     +0x318: ldp     q5, q1, [x19, #800]
     +0x31c: add     v3.4s, v6.4s, v5.4s
     +0x320: ldp     q2, q6, [x20, #816]
     +0x324: stp     q4, q0, [x19, #768]
     +0x328: add     v0.4s, v2.4s, v1.4s
     +0x32c: ldp     q5, q1, [x19, #832]
     +0x330: add     v4.4s, v6.4s, v5.4s
     +0x334: ldp     q2, q6, [x20, #848]
     +0x338: stp     q3, q0, [x19, #800]
     +0x33c: add     v0.4s, v2.4s, v1.4s
     +0x340: ldp     q5, q1, [x19, #864]
     +0x344: add     v3.4s, v6.4s, v5.4s
     +0x348: ldp     q2, q6, [x20, #880]
     +0x34c: stp     q4, q0, [x19, #832]
     +0x350: ldp     q5, q0, [x19, #896]
     +0x354: ldr     q4, [x20, #912]
     +0x358: add     v1.4s, v2.4s, v1.4s
     +0x35c: str     q3, [x19, #864]
     +0x360: add     v2.4s, v6.4s, v5.4s
     +0x364: add     v0.4s, v4.4s, v0.4s
     +0x368: ldp     q3, q4, [x19, #928]
     +0x36c: ldp     q5, q6, [x20, #928]
     +0x370: str     q0, [x19, #912]
     +0x374: stp     q1, q2, [x19, #880]
     +0x378: add     v1.4s, v17.4s, v7.4s
     +0x37c: add     v3.4s, v5.4s, v3.4s
     +0x380: add     v4.4s, v6.4s, v4.4s
     +0x384: ldp     q2, q6, [x20, #992]
     +0x388: add     v5.4s, v18.4s, v16.4s
     +0x38c: str     q3, [x19, #928]
     +0x390: ldp     q0, q3, [x19, #992]
     +0x394: stp     q4, q1, [x19, #944]
     +0x398: add     v0.4s, v2.4s, v0.4s
     +0x39c: add     v2.4s, v6.4s, v3.4s
     +0x3a0: stp     q5, q0, [x19, #976]
     +0x3a4: str     q2, [x19, #1008]
     +0x3a8: mov     w8, #0x2
     +0x3ac: mov     x1, sp
     +0x3b0: mov     x0, x20
     +0x3b4: strb    w8, [sp, #32]
     +0x3b8: strb    w22, [sp, #33]
     +0x3bc: bl      <mldsa_poly_uniform>
     +0x3c0: mov     x8, xzr
     +0x3c4: add     x9, x21, #0x800
     +0x3c8: mov     x10, #0xffffffffff801fff
     +0x3cc: ldrsw   x11, [x20, x8]
     +0x3d0: ldrsw   x12, [x9, x8]
     +0x3d4: smull   x11, w12, w11
     +0x3d8: mul     x12, x11, x24
     +0x3dc: asr     x12, x12, #32
     +0x3e0: smaddl  x11, w12, w10, x11
     +0x3e4: lsr     x11, x11, #32
     +0x3e8: str     w11, [x20, x8]
     +0x3ec: add     x8, x8, #0x4
     +0x3f0: cmp     x8, #0x400
     +0x3f4: b.ne    <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x3cc>
     +0x3f8: add     x8, x19, #0x400
     +0x3fc: cmp     x20, x8
     +0x400: ccmp    x19, x23, #0x2, cc
     +0x404: b.cs    <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x42c>
     +0x408: mov     x8, xzr
     +0x40c: ldr     w9, [x19, x8]
     +0x410: ldr     w10, [x20, x8]
     +0x414: add     w9, w10, w9
     +0x418: str     w9, [x19, x8]
     +0x41c: add     x8, x8, #0x4
     +0x420: cmp     x8, #0x400
     +0x424: b.ne    <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x40c>
     +0x428: b       <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x6b8>
     +0x42c: ldp     q0, q3, [x20]
     +0x430: ldr     q7, [x20, #64]
     +0x434: ldp     q1, q2, [x19]
     +0x438: ldp     q17, q18, [x20, #960]
     +0x43c: add     v0.4s, v0.4s, v1.4s
     +0x440: ldp     q1, q5, [x20, #32]
     +0x444: add     v2.4s, v3.4s, v2.4s
     +0x448: ldp     q3, q4, [x19, #32]
     +0x44c: add     v1.4s, v1.4s, v3.4s
     +0x450: stp     q0, q2, [x19]
     +0x454: add     v0.4s, v5.4s, v4.4s
     +0x458: ldp     q6, q2, [x19, #64]
     +0x45c: stp     q1, q0, [x19, #32]
     +0x460: ldp     q5, q1, [x19, #96]
     +0x464: add     v4.4s, v7.4s, v6.4s
     +0x468: ldp     q3, q6, [x20, #80]
     +0x46c: ldp     q7, q16, [x19, #960]
     +0x470: add     v0.4s, v3.4s, v2.4s
     +0x474: add     v3.4s, v6.4s, v5.4s
     +0x478: ldp     q2, q6, [x20, #112]
     +0x47c: stp     q4, q0, [x19, #64]
     +0x480: add     v0.4s, v2.4s, v1.4s
     +0x484: ldp     q5, q1, [x19, #128]
     +0x488: add     v4.4s, v6.4s, v5.4s
     +0x48c: ldp     q2, q6, [x20, #144]
     +0x490: stp     q3, q0, [x19, #96]
     +0x494: add     v0.4s, v2.4s, v1.4s
     +0x498: ldp     q5, q1, [x19, #160]
     +0x49c: add     v3.4s, v6.4s, v5.4s
     +0x4a0: ldp     q2, q6, [x20, #176]
     +0x4a4: stp     q4, q0, [x19, #128]
     +0x4a8: add     v0.4s, v2.4s, v1.4s
     +0x4ac: ldp     q5, q1, [x19, #192]
     +0x4b0: add     v4.4s, v6.4s, v5.4s
     +0x4b4: ldp     q2, q6, [x20, #208]
     +0x4b8: stp     q3, q0, [x19, #160]
     +0x4bc: add     v0.4s, v2.4s, v1.4s
     +0x4c0: ldp     q5, q1, [x19, #224]
     +0x4c4: add     v3.4s, v6.4s, v5.4s
     +0x4c8: ldp     q2, q6, [x20, #240]
     +0x4cc: stp     q4, q0, [x19, #192]
     +0x4d0: add     v0.4s, v2.4s, v1.4s
     +0x4d4: ldp     q5, q1, [x19, #256]
     +0x4d8: add     v4.4s, v6.4s, v5.4s
     +0x4dc: ldp     q2, q6, [x20, #272]
     +0x4e0: stp     q3, q0, [x19, #224]
     +0x4e4: add     v0.4s, v2.4s, v1.4s
     +0x4e8: ldp     q5, q1, [x19, #288]
     +0x4ec: add     v3.4s, v6.4s, v5.4s
     +0x4f0: ldp     q2, q6, [x20, #304]
     +0x4f4: stp     q4, q0, [x19, #256]
     +0x4f8: add     v0.4s, v2.4s, v1.4s
     +0x4fc: ldp     q5, q1, [x19, #320]
     +0x500: add     v4.4s, v6.4s, v5.4s
     +0x504: ldp     q2, q6, [x20, #336]
     +0x508: stp     q3, q0, [x19, #288]
     +0x50c: add     v0.4s, v2.4s, v1.4s
     +0x510: ldp     q5, q1, [x19, #352]
     +0x514: add     v3.4s, v6.4s, v5.4s
     +0x518: ldp     q2, q6, [x20, #368]
     +0x51c: stp     q4, q0, [x19, #320]
     +0x520: add     v0.4s, v2.4s, v1.4s
     +0x524: ldp     q5, q1, [x19, #384]
     +0x528: add     v4.4s, v6.4s, v5.4s
     +0x52c: ldp     q2, q6, [x20, #400]
     +0x530: stp     q3, q0, [x19, #352]
     +0x534: add     v0.4s, v2.4s, v1.4s
     +0x538: ldp     q5, q1, [x19, #416]
     +0x53c: add     v3.4s, v6.4s, v5.4s
     +0x540: ldp     q2, q6, [x20, #432]
     +0x544: stp     q4, q0, [x19, #384]
     +0x548: add     v0.4s, v2.4s, v1.4s
     +0x54c: ldp     q5, q1, [x19, #448]
     +0x550: add     v4.4s, v6.4s, v5.4s
     +0x554: ldp     q2, q6, [x20, #464]
     +0x558: stp     q3, q0, [x19, #416]
     +0x55c: add     v0.4s, v2.4s, v1.4s
     +0x560: ldp     q5, q1, [x19, #480]
     +0x564: add     v3.4s, v6.4s, v5.4s
     +0x568: ldp     q2, q6, [x20, #496]
     +0x56c: stp     q4, q0, [x19, #448]
     +0x570: add     v0.4s, v2.4s, v1.4s
     +0x574: ldp     q5, q1, [x19, #512]
     +0x578: add     v4.4s, v6.4s, v5.4s
     +0x57c: ldp     q2, q6, [x20, #528]
     +0x580: stp     q3, q0, [x19, #480]
     +0x584: add     v0.4s, v2.4s, v1.4s
     +0x588: ldp     q5, q1, [x19, #544]
     +0x58c: add     v3.4s, v6.4s, v5.4s
     +0x590: ldp     q2, q6, [x20, #560]
     +0x594: stp     q4, q0, [x19, #512]
     +0x598: add     v0.4s, v2.4s, v1.4s
     +0x59c: ldp     q5, q1, [x19, #576]
     +0x5a0: add     v4.4s, v6.4s, v5.4s
     +0x5a4: ldp     q2, q6, [x20, #592]
     +0x5a8: stp     q3, q0, [x19, #544]
     +0x5ac: add     v0.4s, v2.4s, v1.4s
     +0x5b0: ldp     q5, q1, [x19, #608]
     +0x5b4: add     v3.4s, v6.4s, v5.4s
     +0x5b8: ldp     q2, q6, [x20, #624]
     +0x5bc: stp     q4, q0, [x19, #576]
     +0x5c0: add     v0.4s, v2.4s, v1.4s
     +0x5c4: ldp     q5, q1, [x19, #640]
     +0x5c8: add     v4.4s, v6.4s, v5.4s
     +0x5cc: ldp     q2, q6, [x20, #656]
     +0x5d0: stp     q3, q0, [x19, #608]
     +0x5d4: add     v0.4s, v2.4s, v1.4s
     +0x5d8: ldp     q5, q1, [x19, #672]
     +0x5dc: add     v3.4s, v6.4s, v5.4s
     +0x5e0: ldp     q2, q6, [x20, #688]
     +0x5e4: stp     q4, q0, [x19, #640]
     +0x5e8: add     v0.4s, v2.4s, v1.4s
     +0x5ec: ldp     q5, q1, [x19, #704]
     +0x5f0: add     v4.4s, v6.4s, v5.4s
     +0x5f4: ldp     q2, q6, [x20, #720]
     +0x5f8: stp     q3, q0, [x19, #672]
     +0x5fc: add     v0.4s, v2.4s, v1.4s
     +0x600: ldp     q5, q1, [x19, #736]
     +0x604: add     v3.4s, v6.4s, v5.4s
     +0x608: ldp     q2, q6, [x20, #752]
     +0x60c: stp     q4, q0, [x19, #704]
     +0x610: add     v0.4s, v2.4s, v1.4s
     +0x614: ldp     q5, q1, [x19, #768]
     +0x618: add     v4.4s, v6.4s, v5.4s
     +0x61c: ldp     q2, q6, [x20, #784]
     +0x620: stp     q3, q0, [x19, #736]
     +0x624: add     v0.4s, v2.4s, v1.4s
     +0x628: ldp     q5, q1, [x19, #800]
     +0x62c: add     v3.4s, v6.4s, v5.4s
     +0x630: ldp     q2, q6, [x20, #816]
     +0x634: stp     q4, q0, [x19, #768]
     +0x638: add     v0.4s, v2.4s, v1.4s
     +0x63c: ldp     q5, q1, [x19, #832]
     +0x640: add     v4.4s, v6.4s, v5.4s
     +0x644: ldp     q2, q6, [x20, #848]
     +0x648: stp     q3, q0, [x19, #800]
     +0x64c: add     v0.4s, v2.4s, v1.4s
     +0x650: ldp     q5, q1, [x19, #864]
     +0x654: add     v3.4s, v6.4s, v5.4s
     +0x658: ldp     q2, q6, [x20, #880]
     +0x65c: stp     q4, q0, [x19, #832]
     +0x660: ldp     q5, q0, [x19, #896]
     +0x664: ldr     q4, [x20, #912]
     +0x668: add     v1.4s, v2.4s, v1.4s
     +0x66c: str     q3, [x19, #864]
     +0x670: add     v2.4s, v6.4s, v5.4s
     +0x674: add     v0.4s, v4.4s, v0.4s
     +0x678: ldp     q3, q4, [x19, #928]
     +0x67c: ldp     q5, q6, [x20, #928]
     +0x680: str     q0, [x19, #912]
     +0x684: stp     q1, q2, [x19, #880]
     +0x688: add     v1.4s, v17.4s, v7.4s
     +0x68c: add     v3.4s, v5.4s, v3.4s
     +0x690: add     v4.4s, v6.4s, v4.4s
     +0x694: ldp     q2, q6, [x20, #992]
     +0x698: add     v5.4s, v18.4s, v16.4s
     +0x69c: str     q3, [x19, #928]
     +0x6a0: ldp     q0, q3, [x19, #992]
     +0x6a4: stp     q4, q1, [x19, #944]
     +0x6a8: add     v0.4s, v2.4s, v0.4s
     +0x6ac: add     v2.4s, v6.4s, v3.4s
     +0x6b0: stp     q5, q0, [x19, #976]
     +0x6b4: str     q2, [x19, #1008]
     +0x6b8: mov     w8, #0x3
     +0x6bc: mov     x1, sp
     +0x6c0: mov     x0, x20
     +0x6c4: strb    w8, [sp, #32]
     +0x6c8: strb    w22, [sp, #33]
     +0x6cc: bl      <mldsa_poly_uniform>
     +0x6d0: mov     x8, xzr
     +0x6d4: add     x9, x21, #0xc00
     +0x6d8: mov     x10, #0xffffffffff801fff
     +0x6dc: ldrsw   x11, [x20, x8]
     +0x6e0: ldrsw   x12, [x9, x8]
     +0x6e4: smull   x11, w12, w11
     +0x6e8: mul     x12, x11, x24
     +0x6ec: asr     x12, x12, #32
     +0x6f0: smaddl  x11, w12, w10, x11
     +0x6f4: lsr     x11, x11, #32
     +0x6f8: str     w11, [x20, x8]
     +0x6fc: add     x8, x8, #0x4
     +0x700: cmp     x8, #0x400
     +0x704: b.ne    <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x6dc>
     +0x708: add     x8, x19, #0x400
     +0x70c: cmp     x20, x8
     +0x710: ccmp    x19, x23, #0x2, cc
     +0x714: b.cs    <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x73c>
     +0x718: mov     x8, xzr
     +0x71c: ldr     w9, [x19, x8]
     +0x720: ldr     w10, [x20, x8]
     +0x724: add     w9, w10, w9
     +0x728: str     w9, [x19, x8]
     +0x72c: add     x8, x8, #0x4
     +0x730: cmp     x8, #0x400
     +0x734: b.ne    <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x71c>
     +0x738: b       <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x9c8>
     +0x73c: ldp     q0, q3, [x20]
     +0x740: ldr     q7, [x20, #64]
     +0x744: ldp     q1, q2, [x19]
     +0x748: ldp     q17, q18, [x20, #960]
     +0x74c: add     v0.4s, v0.4s, v1.4s
     +0x750: ldp     q1, q5, [x20, #32]
     +0x754: add     v2.4s, v3.4s, v2.4s
     +0x758: ldp     q3, q4, [x19, #32]
     +0x75c: add     v1.4s, v1.4s, v3.4s
     +0x760: stp     q0, q2, [x19]
     +0x764: add     v0.4s, v5.4s, v4.4s
     +0x768: ldp     q6, q2, [x19, #64]
     +0x76c: stp     q1, q0, [x19, #32]
     +0x770: ldp     q5, q1, [x19, #96]
     +0x774: add     v4.4s, v7.4s, v6.4s
     +0x778: ldp     q3, q6, [x20, #80]
     +0x77c: ldp     q7, q16, [x19, #960]
     +0x780: add     v0.4s, v3.4s, v2.4s
     +0x784: add     v3.4s, v6.4s, v5.4s
     +0x788: ldp     q2, q6, [x20, #112]
     +0x78c: stp     q4, q0, [x19, #64]
     +0x790: add     v0.4s, v2.4s, v1.4s
     +0x794: ldp     q5, q1, [x19, #128]
     +0x798: add     v4.4s, v6.4s, v5.4s
     +0x79c: ldp     q2, q6, [x20, #144]
     +0x7a0: stp     q3, q0, [x19, #96]
     +0x7a4: add     v0.4s, v2.4s, v1.4s
     +0x7a8: ldp     q5, q1, [x19, #160]
     +0x7ac: add     v3.4s, v6.4s, v5.4s
     +0x7b0: ldp     q2, q6, [x20, #176]
     +0x7b4: stp     q4, q0, [x19, #128]
     +0x7b8: add     v0.4s, v2.4s, v1.4s
     +0x7bc: ldp     q5, q1, [x19, #192]
     +0x7c0: add     v4.4s, v6.4s, v5.4s
     +0x7c4: ldp     q2, q6, [x20, #208]
     +0x7c8: stp     q3, q0, [x19, #160]
     +0x7cc: add     v0.4s, v2.4s, v1.4s
     +0x7d0: ldp     q5, q1, [x19, #224]
     +0x7d4: add     v3.4s, v6.4s, v5.4s
     +0x7d8: ldp     q2, q6, [x20, #240]
     +0x7dc: stp     q4, q0, [x19, #192]
     +0x7e0: add     v0.4s, v2.4s, v1.4s
     +0x7e4: ldp     q5, q1, [x19, #256]
     +0x7e8: add     v4.4s, v6.4s, v5.4s
     +0x7ec: ldp     q2, q6, [x20, #272]
     +0x7f0: stp     q3, q0, [x19, #224]
     +0x7f4: add     v0.4s, v2.4s, v1.4s
     +0x7f8: ldp     q5, q1, [x19, #288]
     +0x7fc: add     v3.4s, v6.4s, v5.4s
     +0x800: ldp     q2, q6, [x20, #304]
     +0x804: stp     q4, q0, [x19, #256]
     +0x808: add     v0.4s, v2.4s, v1.4s
     +0x80c: ldp     q5, q1, [x19, #320]
     +0x810: add     v4.4s, v6.4s, v5.4s
     +0x814: ldp     q2, q6, [x20, #336]
     +0x818: stp     q3, q0, [x19, #288]
     +0x81c: add     v0.4s, v2.4s, v1.4s
     +0x820: ldp     q5, q1, [x19, #352]
     +0x824: add     v3.4s, v6.4s, v5.4s
     +0x828: ldp     q2, q6, [x20, #368]
     +0x82c: stp     q4, q0, [x19, #320]
     +0x830: add     v0.4s, v2.4s, v1.4s
     +0x834: ldp     q5, q1, [x19, #384]
     +0x838: add     v4.4s, v6.4s, v5.4s
     +0x83c: ldp     q2, q6, [x20, #400]
     +0x840: stp     q3, q0, [x19, #352]
     +0x844: add     v0.4s, v2.4s, v1.4s
     +0x848: ldp     q5, q1, [x19, #416]
     +0x84c: add     v3.4s, v6.4s, v5.4s
     +0x850: ldp     q2, q6, [x20, #432]
     +0x854: stp     q4, q0, [x19, #384]
     +0x858: add     v0.4s, v2.4s, v1.4s
     +0x85c: ldp     q5, q1, [x19, #448]
     +0x860: add     v4.4s, v6.4s, v5.4s
     +0x864: ldp     q2, q6, [x20, #464]
     +0x868: stp     q3, q0, [x19, #416]
     +0x86c: add     v0.4s, v2.4s, v1.4s
     +0x870: ldp     q5, q1, [x19, #480]
     +0x874: add     v3.4s, v6.4s, v5.4s
     +0x878: ldp     q2, q6, [x20, #496]
     +0x87c: stp     q4, q0, [x19, #448]
     +0x880: add     v0.4s, v2.4s, v1.4s
     +0x884: ldp     q5, q1, [x19, #512]
     +0x888: add     v4.4s, v6.4s, v5.4s
     +0x88c: ldp     q2, q6, [x20, #528]
     +0x890: stp     q3, q0, [x19, #480]
     +0x894: add     v0.4s, v2.4s, v1.4s
     +0x898: ldp     q5, q1, [x19, #544]
     +0x89c: add     v3.4s, v6.4s, v5.4s
     +0x8a0: ldp     q2, q6, [x20, #560]
     +0x8a4: stp     q4, q0, [x19, #512]
     +0x8a8: add     v0.4s, v2.4s, v1.4s
     +0x8ac: ldp     q5, q1, [x19, #576]
     +0x8b0: add     v4.4s, v6.4s, v5.4s
     +0x8b4: ldp     q2, q6, [x20, #592]
     +0x8b8: stp     q3, q0, [x19, #544]
     +0x8bc: add     v0.4s, v2.4s, v1.4s
     +0x8c0: ldp     q5, q1, [x19, #608]
     +0x8c4: add     v3.4s, v6.4s, v5.4s
     +0x8c8: ldp     q2, q6, [x20, #624]
     +0x8cc: stp     q4, q0, [x19, #576]
     +0x8d0: add     v0.4s, v2.4s, v1.4s
     +0x8d4: ldp     q5, q1, [x19, #640]
     +0x8d8: add     v4.4s, v6.4s, v5.4s
     +0x8dc: ldp     q2, q6, [x20, #656]
     +0x8e0: stp     q3, q0, [x19, #608]
     +0x8e4: add     v0.4s, v2.4s, v1.4s
     +0x8e8: ldp     q5, q1, [x19, #672]
     +0x8ec: add     v3.4s, v6.4s, v5.4s
     +0x8f0: ldp     q2, q6, [x20, #688]
     +0x8f4: stp     q4, q0, [x19, #640]
     +0x8f8: add     v0.4s, v2.4s, v1.4s
     +0x8fc: ldp     q5, q1, [x19, #704]
     +0x900: add     v4.4s, v6.4s, v5.4s
     +0x904: ldp     q2, q6, [x20, #720]
     +0x908: stp     q3, q0, [x19, #672]
     +0x90c: add     v0.4s, v2.4s, v1.4s
     +0x910: ldp     q5, q1, [x19, #736]
     +0x914: add     v3.4s, v6.4s, v5.4s
     +0x918: ldp     q2, q6, [x20, #752]
     +0x91c: stp     q4, q0, [x19, #704]
     +0x920: add     v0.4s, v2.4s, v1.4s
     +0x924: ldp     q5, q1, [x19, #768]
     +0x928: add     v4.4s, v6.4s, v5.4s
     +0x92c: ldp     q2, q6, [x20, #784]
     +0x930: stp     q3, q0, [x19, #736]
     +0x934: add     v0.4s, v2.4s, v1.4s
     +0x938: ldp     q5, q1, [x19, #800]
     +0x93c: add     v3.4s, v6.4s, v5.4s
     +0x940: ldp     q2, q6, [x20, #816]
     +0x944: stp     q4, q0, [x19, #768]
     +0x948: add     v0.4s, v2.4s, v1.4s
     +0x94c: ldp     q5, q1, [x19, #832]
     +0x950: add     v4.4s, v6.4s, v5.4s
     +0x954: ldp     q2, q6, [x20, #848]
     +0x958: stp     q3, q0, [x19, #800]
     +0x95c: add     v0.4s, v2.4s, v1.4s
     +0x960: ldp     q5, q1, [x19, #864]
     +0x964: add     v3.4s, v6.4s, v5.4s
     +0x968: ldp     q2, q6, [x20, #880]
     +0x96c: stp     q4, q0, [x19, #832]
     +0x970: ldp     q5, q0, [x19, #896]
     +0x974: ldr     q4, [x20, #912]
     +0x978: add     v1.4s, v2.4s, v1.4s
     +0x97c: str     q3, [x19, #864]
     +0x980: add     v2.4s, v6.4s, v5.4s
     +0x984: add     v0.4s, v4.4s, v0.4s
     +0x988: ldp     q3, q4, [x19, #928]
     +0x98c: ldp     q5, q6, [x20, #928]
     +0x990: str     q0, [x19, #912]
     +0x994: stp     q1, q2, [x19, #880]
     +0x998: add     v1.4s, v17.4s, v7.4s
     +0x99c: add     v3.4s, v5.4s, v3.4s
     +0x9a0: add     v4.4s, v6.4s, v4.4s
     +0x9a4: ldp     q2, q6, [x20, #992]
     +0x9a8: add     v5.4s, v18.4s, v16.4s
     +0x9ac: str     q3, [x19, #928]
     +0x9b0: ldp     q0, q3, [x19, #992]
     +0x9b4: stp     q4, q1, [x19, #944]
     +0x9b8: add     v0.4s, v2.4s, v0.4s
     +0x9bc: add     v2.4s, v6.4s, v3.4s
     +0x9c0: stp     q5, q0, [x19, #976]
     +0x9c4: str     q2, [x19, #1008]
     +0x9c8: movi    v0.4s, #0x40, lsl #16
     +0x9cc: mov     w8, #0xff801fff
     +0x9d0: mov     w9, #0x100
     +0x9d4: dup     v1.4s, w8
     +0x9d8: add     x8, x19, #0x10
     +0x9dc: ldp     q2, q3, [x8, #-16]
     +0x9e0: subs    x9, x9, #0x8
     +0x9e4: add     v4.4s, v2.4s, v0.4s
     +0x9e8: add     v5.4s, v3.4s, v0.4s
     +0x9ec: sshr    v4.4s, v4.4s, #23
     +0x9f0: sshr    v5.4s, v5.4s, #23
     +0x9f4: mla     v2.4s, v4.4s, v1.4s
     +0x9f8: mla     v3.4s, v5.4s, v1.4s
     +0x9fc: stp     q2, q3, [x8, #-16]
     +0xa00: add     x8, x8, #0x20
     +0xa04: b.ne    <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0x9dc>
     +0xa08: movi    v0.2d, #0x0
     +0xa0c: mov     x8, sp
     +0xa10: stp     q0, q0, [sp]
     +0xa14: stp     q0, q0, [sp, #32]
     +0xa18: adrp    x8, <page>
     +0xa1c: ldr     x8, [x8, #4088]
     +0xa20: ldr     x9, [sp, #88]
     +0xa24: ldr     x8, [x8]
     +0xa28: cmp     x8, x9
     +0xa2c: b.ne    <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy+0xa6c>
     +0xa30: mov     sp, x29
     +0xa34: ldp     x20, x19, [sp, #48]
     +0xa38: ldp     x22, x21, [sp, #32]
     +0xa3c: ldp     x24, x23, [sp, #16]
     +0xa40: ldp     x29, x30, [sp], #64
     +0xa44: mov     x0, #0x0
     +0xa48: mov     x1, #0x0
     +0xa4c: mov     x2, #0x0
     +0xa50: mov     x3, #0x0
     +0xa54: mov     x8, #0x0
     +0xa58: mov     x9, #0x0
     +0xa5c: mov     x10, #0x0
     +0xa60: mov     x11, #0x0
     +0xa64: mov     x12, #0x0
     +0xa68: ret     
     +0xa6c: bl      <__stack_chk_fail>
 ***)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for memset and memcpy. The structure *)
(* at mat has                                                                *)
(* the 32 bytes of rho, as the number r, at offset 1024, and the vector x at *)
(* v is 4 polynomials of 256 coefficients of 32 bits each (see               *)
(* common/mldsa_native_polyvec.ml): the polynomial at t becomes              *)
(* mld_polyvec_matrix_row_lazy 4 r x i. The polynomial cur at mat and the    *)
(* stack are scratch space.                                                  *)
(* ------------------------------------------------------------------------- *)
let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\ memcpy_full_contract mc ea el ev
     ==> !t mat v r x i guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 4 4 r /\ i < 4 /\
          PAIRWISE nonoverlapping
           [(t,1024); (mat,1024); (word_sub stackpointer (word 1664),1664)] /\
          ALLPAIRS nonoverlapping
           [(t,1024); (mat,1024); (word_sub stackpointer (word 1664),1664)]
           [(word_add mat (word 1024),32); (v,4096); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [t; mat; v; word i] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(word_add mat (word 1024),32)) s = r /\
                    (!j. j < 1024
                         ==> read(memory :> bytes32(word_add v (word(4 * j))))
                               s = x j))
               (\s. read PC s = returnaddress /\
                    (!m. m < 256
                         ==> read(memory :> bytes32(word_add t (word(4 * m)))) s =
                             mld_polyvec_matrix_row_lazy 4 r x i m))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(t,1024); memory :> bytes(mat,1024);
                  memory :> bytes(word_sub stackpointer (word 1664),1664)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;


(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, i, rho and the addresses of the   *)
(* stack guard and memset, with all accesses within the arguments, the       *)
(* stack, the GOT entries and the stack guard, the region (ea,el) that       *)
(* memset may read and the constants of the callees, and the writes within   *)
(* t, cur and the stack.                                                     *)
(* ------------------------------------------------------------------------- *)
let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e t mat v r x i guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 4 4 r /\ i < 4 /\
          PAIRWISE nonoverlapping
           [(t,1024); (mat,1024); (word_sub stackpointer (word 1664),1664)] /\
          ALLPAIRS nonoverlapping
           [(t,1024); (mat,1024); (word_sub stackpointer (word 1664),1664)]
           [(word_add mat (word 1024),32); (v,4096); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [t; mat; v; word i] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(word_add mat (word 1024),32)) s = r /\
                    (!j. j < 1024
                         ==> read(memory :> bytes32(word_add v (word(4 * j))))
                               s = x j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!m. m < 256
                         ==> read(memory :> bytes32(word_add t (word(4 * m)))) s =
                             mld_polyvec_matrix_row_lazy 4 r x i m) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events t mat v i r guard mf mc pc
                              (word_sub stackpointer (word 1664))
                              returnaddress /\
                       memaccess_inbounds e2
                        [word_add mat (word 1024),32; v,4096; t,1024; mat,1024;
                         word_sub stackpointer (word 1664),1664;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [t,1024; mat,1024;
                         word_sub stackpointer (word 1664),1664]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(t,1024); memory :> bytes(mat,1024);
                  memory :> bytes(word_sub stackpointer (word 1664),1664)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;


(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)
let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e t mat v r i guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 4 4 r /\ i < 4 /\
          PAIRWISE nonoverlapping
           [(t,1024); (mat,1024); (word_sub stackpointer (word 1664),1664)] /\
          ALLPAIRS nonoverlapping
           [(t,1024); (mat,1024); (word_sub stackpointer (word 1664),1664)]
           [(word_add mat (word 1024),32); (v,4096); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [t; mat; v; word i] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(word_add mat (word 1024),32)) s = r /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events t mat v i r guard mf mc pc
                              (word_sub stackpointer (word 1664))
                              returnaddress /\
                       memaccess_inbounds e2
                        [word_add mat (word 1024),32; v,4096; t,1024; mat,1024;
                         word_sub stackpointer (word 1664),1664;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [t,1024; mat,1024;
                         word_sub stackpointer (word 1664),1664]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(t,1024); memory :> bytes(mat,1024);
                  memory :> bytes(word_sub stackpointer (word 1664),1664)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
