(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 of up to three inputs: the statement. This is the code for       *)
(* mld_H87 (mld_H in sign.c, for ML-DSA-87) from mldsa-native's portable C   *)
(* implementation compiled by clang 23 with -O3 as a monolithic build with   *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), where the output      *)
(* length is fixed at 64 bytes: all the calls in ML-DSA-87 have outlen = 64  *)
(* (the lengths of tr, mu, rhoprime and the challenge), so the compiler has  *)
(* dropped the argument. Clang inlined the SHAKE256 functions: the function  *)
(* zeroes a Keccak state on its stack, absorbs in1, and in2 and in3 unless   *)
(* their lengths are zero, with loops over blocks of 136, 32 and 8 bytes and *)
(* over single bytes and calls of mldsa_keccakf1600_permute, finalizes,      *)
(* permutes once, copies the first 64 bytes of the state to the output with  *)
(* vector loads and stores, and zeroes the state. It is verified in the      *)
(* whole image (see libmldsa.ml) against mld_shake256_byte of                *)
(* common/mldsa_native_fips202.ml for the concatenation of the three inputs; *)
(* the inputs and the output may overlap, and a pointer with a zero length   *)
(* may be anything (NULL), except that in1len must not be zero: when in1 is  *)
(* shorter than a block, the code goes from its test of in1len < 136         *)
(* straight to the XOR of the rest of in1, past the test of an empty rest,   *)
(* and for in1len = 0 its byte loop runs on until its index wraps around,    *)
(* XORing far past the state (all callers pass a nonzero constant in1len,    *)
(* presumably why clang dropped the test). The code uses the 304 bytes of    *)
(* the function and the 240 of mldsa_keccakf1600_permute below them; the     *)
(* statement allows the 560 bytes below the stack pointer, as for the gcc    *)
(* build. The address of the stack guard is read from the GOT. It is also    *)
(* shown to be constant time and memory safe.                                *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_absorb.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mld_H87:
       +0x0: sub     sp, sp, #0x130
       +0x4: str     x29, [sp, #224]
       +0x8: stp     x30, x25, [sp, #240]
       +0xc: stp     x24, x23, [sp, #256]
      +0x10: stp     x22, x21, [sp, #272]
      +0x14: stp     x20, x19, [sp, #288]
      +0x18: adrp    x8, <page>
      +0x1c: movi    v0.2d, #0x0
      +0x20: mov     x20, x6
      +0x24: ldr     x8, [x8, #4088]
      +0x28: mov     x21, x5
      +0x2c: mov     x23, x4
      +0x30: mov     x24, x3
      +0x34: mov     x22, x2
      +0x38: mov     x25, x1
      +0x3c: ldr     x8, [x8]
      +0x40: mov     x19, x0
      +0x44: cmp     x2, #0x88
      +0x48: str     x8, [sp, #216]
      +0x4c: stur    q0, [sp, #188]
      +0x50: stp     q0, q0, [sp]
      +0x54: stp     q0, q0, [sp, #32]
      +0x58: stp     q0, q0, [sp, #64]
      +0x5c: stp     q0, q0, [sp, #96]
      +0x60: stp     q0, q0, [sp, #128]
      +0x64: stp     q0, q0, [sp, #160]
      +0x68: b.cc    <mld_H87+0x138>
      +0x6c: ldp     d0, d3, [sp]
      +0x70: mov     x0, sp
      +0x74: ldp     d1, d2, [x25]
      +0x78: sub     x22, x22, #0x88
      +0x7c: ldp     d6, d7, [sp, #32]
      +0x80: ldp     d16, d17, [sp, #48]
      +0x84: eor     v0.8b, v0.8b, v1.8b
      +0x88: eor     v1.8b, v3.8b, v2.8b
      +0x8c: ldp     d4, d2, [x25, #16]
      +0x90: ldp     d5, d3, [sp, #16]
      +0x94: stp     d0, d1, [sp]
      +0x98: eor     v4.8b, v5.8b, v4.8b
      +0x9c: eor     v2.8b, v3.8b, v2.8b
      +0xa0: ldp     d5, d3, [x25, #32]
      +0xa4: stp     d4, d2, [sp, #16]
      +0xa8: ldp     d1, d2, [x25, #80]
      +0xac: eor     v5.8b, v6.8b, v5.8b
      +0xb0: eor     v3.8b, v7.8b, v3.8b
      +0xb4: ldp     d6, d7, [x25, #48]
      +0xb8: stp     d5, d3, [sp, #32]
      +0xbc: ldp     d3, d5, [x25, #96]
      +0xc0: eor     v6.8b, v16.8b, v6.8b
      +0xc4: eor     v7.8b, v17.8b, v7.8b
      +0xc8: ldp     d16, d0, [x25, #64]
      +0xcc: ldp     d18, d17, [sp, #64]
      +0xd0: stp     d6, d7, [sp, #48]
      +0xd4: eor     v0.8b, v17.8b, v0.8b
      +0xd8: ldp     d4, d17, [sp, #80]
      +0xdc: eor     v16.8b, v18.8b, v16.8b
      +0xe0: eor     v1.8b, v4.8b, v1.8b
      +0xe4: ldp     d4, d6, [sp, #96]
      +0xe8: eor     v2.8b, v17.8b, v2.8b
      +0xec: stp     d16, d0, [sp, #64]
      +0xf0: eor     v3.8b, v4.8b, v3.8b
      +0xf4: ldp     d4, d0, [x25, #112]
      +0xf8: eor     v5.8b, v6.8b, v5.8b
      +0xfc: ldp     d7, d6, [sp, #112]
     +0x100: stp     d1, d2, [sp, #80]
     +0x104: ldr     d1, [x25, #128]
     +0x108: ldr     d2, [sp, #128]
     +0x10c: add     x25, x25, #0x88
     +0x110: eor     v4.8b, v7.8b, v4.8b
     +0x114: eor     v0.8b, v6.8b, v0.8b
     +0x118: eor     v1.8b, v2.8b, v1.8b
     +0x11c: stp     d3, d5, [sp, #96]
     +0x120: stp     d4, d0, [sp, #112]
     +0x124: str     d1, [sp, #128]
     +0x128: bl      <mldsa_keccakf1600_permute>
     +0x12c: cmp     x22, #0x87
     +0x130: b.hi    <mld_H87+0x6c>
     +0x134: cbz     x22, <mld_H87+0x17c>
     +0x138: cmp     x22, #0x8
     +0x13c: b.cc    <mld_H87+0x158>
     +0x140: mov     x8, sp
     +0x144: add     x10, x25, x22
     +0x148: add     x9, x8, x22
     +0x14c: cmp     x25, x9
     +0x150: ccmp    x8, x10, #0x2, cc
     +0x154: b.cs    <mld_H87+0x5e8>
     +0x158: mov     x8, xzr
     +0x15c: mov     x9, sp
     +0x160: ldrb    w10, [x25, x8]
     +0x164: ldrb    w11, [x9, x8]
     +0x168: eor     w10, w11, w10
     +0x16c: strb    w10, [x9, x8]
     +0x170: add     x8, x8, #0x1
     +0x174: cmp     x22, x8
     +0x178: b.ne    <mld_H87+0x160>
     +0x17c: str     w22, [sp, #200]
     +0x180: cbz     x23, <mld_H87+0x380>
     +0x184: mov     w8, #0x88
     +0x188: sub     x8, x8, x22
     +0x18c: cmp     x23, x8
     +0x190: b.cs    <mld_H87+0x1a8>
     +0x194: mov     x8, sp
     +0x198: add     x8, x8, x22
     +0x19c: cmp     x23, #0x8
     +0x1a0: b.cs    <mld_H87+0x33c>
     +0x1a4: b       <mld_H87+0x350>
     +0x1a8: mov     x25, sp
     +0x1ac: b       <mld_H87+0x1d0>
     +0x1b0: mov     x0, sp
     +0x1b4: sub     x23, x23, x8
     +0x1b8: add     x24, x24, x8
     +0x1bc: bl      <mldsa_keccakf1600_permute>
     +0x1c0: mov     x22, xzr
     +0x1c4: cmp     x23, #0x87
     +0x1c8: mov     w8, #0x88
     +0x1cc: b.ls    <mld_H87+0x328>
     +0x1d0: cmp     x8, #0x8
     +0x1d4: b.cs    <mld_H87+0x1e0>
     +0x1d8: mov     x9, xzr
     +0x1dc: b       <mld_H87+0x2fc>
     +0x1e0: cmp     x8, #0x20
     +0x1e4: b.cs    <mld_H87+0x1f0>
     +0x1e8: mov     x9, xzr
     +0x1ec: b       <mld_H87+0x2c4>
     +0x1f0: add     x10, x25, x22
     +0x1f4: ldp     q1, q2, [x24]
     +0x1f8: ldp     q0, q3, [x10]
     +0x1fc: and     x9, x8, #0xe0
     +0x200: cmp     x9, #0x20
     +0x204: eor     v0.16b, v0.16b, v1.16b
     +0x208: eor     v1.16b, v3.16b, v2.16b
     +0x20c: stp     q0, q1, [x10]
     +0x210: b.eq    <mld_H87+0x2b4>
     +0x214: ldp     q0, q3, [x10, #32]
     +0x218: cmp     x9, #0x40
     +0x21c: ldp     q1, q2, [x24, #32]
     +0x220: eor     v0.16b, v0.16b, v1.16b
     +0x224: eor     v1.16b, v3.16b, v2.16b
     +0x228: stp     q0, q1, [x10, #32]
     +0x22c: b.eq    <mld_H87+0x2b4>
     +0x230: ldp     q0, q3, [x10, #64]
     +0x234: cmp     x9, #0x60
     +0x238: ldp     q1, q2, [x24, #64]
     +0x23c: eor     v0.16b, v0.16b, v1.16b
     +0x240: eor     v1.16b, v3.16b, v2.16b
     +0x244: stp     q0, q1, [x10, #64]
     +0x248: b.eq    <mld_H87+0x2b4>
     +0x24c: ldp     q0, q3, [x10, #96]
     +0x250: cmp     x9, #0x80
     +0x254: ldp     q1, q2, [x24, #96]
     +0x258: eor     v0.16b, v0.16b, v1.16b
     +0x25c: eor     v1.16b, v3.16b, v2.16b
     +0x260: stp     q0, q1, [x10, #96]
     +0x264: b.eq    <mld_H87+0x2b4>
     +0x268: ldp     q0, q3, [x10, #128]
     +0x26c: cmp     x9, #0xa0
     +0x270: ldp     q1, q2, [x24, #128]
     +0x274: eor     v0.16b, v0.16b, v1.16b
     +0x278: eor     v1.16b, v3.16b, v2.16b
     +0x27c: stp     q0, q1, [x10, #128]
     +0x280: b.eq    <mld_H87+0x2b4>
     +0x284: ldp     q0, q3, [x10, #160]
     +0x288: cmp     x9, #0xc0
     +0x28c: ldp     q1, q2, [x24, #160]
     +0x290: eor     v0.16b, v0.16b, v1.16b
     +0x294: eor     v1.16b, v3.16b, v2.16b
     +0x298: stp     q0, q1, [x10, #160]
     +0x29c: b.eq    <mld_H87+0x2b4>
     +0x2a0: ldp     q0, q3, [x10, #192]
     +0x2a4: ldp     q1, q2, [x24, #192]
     +0x2a8: eor     v0.16b, v0.16b, v1.16b
     +0x2ac: eor     v1.16b, v3.16b, v2.16b
     +0x2b0: stp     q0, q1, [x10, #192]
     +0x2b4: cmp     x8, x9
     +0x2b8: b.eq    <mld_H87+0x1b0>
     +0x2bc: and     x10, x8, #0x18
     +0x2c0: cbz     x10, <mld_H87+0x2fc>
     +0x2c4: mov     x12, x9
     +0x2c8: and     x9, x8, #0xf8
     +0x2cc: add     x11, x12, x22
     +0x2d0: sub     x10, x12, x9
     +0x2d4: add     x12, x24, x12
     +0x2d8: add     x11, x25, x11
     +0x2dc: ldr     d0, [x12], #8
     +0x2e0: ldr     d1, [x11]
     +0x2e4: adds    x10, x10, #0x8
     +0x2e8: eor     v0.8b, v1.8b, v0.8b
     +0x2ec: str     d0, [x11], #8
     +0x2f0: b.ne    <mld_H87+0x2dc>
     +0x2f4: cmp     x8, x9
     +0x2f8: b.eq    <mld_H87+0x1b0>
     +0x2fc: add     x11, x9, x22
     +0x300: sub     x10, x8, x9
     +0x304: add     x9, x24, x9
     +0x308: add     x11, x25, x11
     +0x30c: ldrb    w12, [x9], #1
     +0x310: ldrb    w13, [x11]
     +0x314: subs    x10, x10, #0x1
     +0x318: eor     w12, w13, w12
     +0x31c: strb    w12, [x11], #1
     +0x320: b.ne    <mld_H87+0x30c>
     +0x324: b       <mld_H87+0x1b0>
     +0x328: mov     w22, wzr
     +0x32c: cbz     x23, <mld_H87+0x37c>
     +0x330: mov     x8, sp
     +0x334: cmp     x23, #0x8
     +0x338: b.cc    <mld_H87+0x350>
     +0x33c: add     x9, x8, x23
     +0x340: add     x10, x24, x23
     +0x344: cmp     x24, x9
     +0x348: ccmp    x8, x10, #0x2, cc
     +0x34c: b.cs    <mld_H87+0x608>
     +0x350: mov     x9, xzr
     +0x354: sub     x10, x23, x9
     +0x358: add     x8, x8, x9
     +0x35c: add     x9, x24, x9
     +0x360: ldrb    w11, [x9], #1
     +0x364: ldrb    w12, [x8]
     +0x368: subs    x10, x10, #0x1
     +0x36c: eor     w11, w12, w11
     +0x370: strb    w11, [x8], #1
     +0x374: b.ne    <mld_H87+0x360>
     +0x378: add     w22, w22, w23
     +0x37c: str     w22, [sp, #200]
     +0x380: cbz     x20, <mld_H87+0x504>
     +0x384: mov     w8, #0x88
     +0x388: sub     w8, w8, w22
     +0x38c: cmp     x20, x8
     +0x390: b.cs    <mld_H87+0x3a8>
     +0x394: mov     x8, sp
     +0x398: add     x8, x8, w22, uxtw
     +0x39c: cmp     x20, #0x8
     +0x3a0: b.cs    <mld_H87+0x4bc>
     +0x3a4: b       <mld_H87+0x4d4>
     +0x3a8: mov     x23, sp
     +0x3ac: add     x24, x23, #0x10
     +0x3b0: b       <mld_H87+0x3d4>
     +0x3b4: mov     x0, sp
     +0x3b8: sub     x20, x20, x8
     +0x3bc: add     x21, x21, x8
     +0x3c0: bl      <mldsa_keccakf1600_permute>
     +0x3c4: mov     w22, wzr
     +0x3c8: cmp     x20, #0x87
     +0x3cc: mov     w8, #0x88
     +0x3d0: b.ls    <mld_H87+0x4a8>
     +0x3d4: cmp     w22, #0x88
     +0x3d8: b.eq    <mld_H87+0x3b4>
     +0x3dc: cmp     x8, #0x8
     +0x3e0: mov     w9, w22
     +0x3e4: b.cs    <mld_H87+0x3f0>
     +0x3e8: mov     x10, xzr
     +0x3ec: b       <mld_H87+0x47c>
     +0x3f0: cmp     x8, #0x20
     +0x3f4: b.cs    <mld_H87+0x400>
     +0x3f8: mov     x10, xzr
     +0x3fc: b       <mld_H87+0x444>
     +0x400: and     x11, x8, #0x18
     +0x404: and     x10, x8, #0xffffffe0
     +0x408: add     x12, x24, x9
     +0x40c: add     x13, x21, #0x10
     +0x410: and     x14, x8, #0xffffffe0
     +0x414: ldp     q0, q3, [x12, #-16]
     +0x418: subs    x14, x14, #0x20
     +0x41c: ldp     q1, q2, [x13, #-16]
     +0x420: add     x13, x13, #0x20
     +0x424: eor     v0.16b, v0.16b, v1.16b
     +0x428: eor     v1.16b, v3.16b, v2.16b
     +0x42c: stp     q0, q1, [x12, #-16]
     +0x430: add     x12, x12, #0x20
     +0x434: b.ne    <mld_H87+0x414>
     +0x438: cmp     x8, x10
     +0x43c: b.eq    <mld_H87+0x3b4>
     +0x440: cbz     x11, <mld_H87+0x47c>
     +0x444: mov     x13, x10
     +0x448: and     x10, x8, #0xfffffff8
     +0x44c: add     x12, x13, x9
     +0x450: sub     x11, x13, x10
     +0x454: add     x13, x21, x13
     +0x458: add     x12, x23, x12
     +0x45c: ldr     d0, [x13], #8
     +0x460: ldr     d1, [x12]
     +0x464: adds    x11, x11, #0x8
     +0x468: eor     v0.8b, v1.8b, v0.8b
     +0x46c: str     d0, [x12], #8
     +0x470: b.ne    <mld_H87+0x45c>
     +0x474: cmp     x8, x10
     +0x478: b.eq    <mld_H87+0x3b4>
     +0x47c: add     x11, x10, x9
     +0x480: sub     x9, x8, x10
     +0x484: add     x10, x21, x10
     +0x488: add     x11, x23, x11
     +0x48c: ldrb    w12, [x10], #1
     +0x490: ldrb    w13, [x11]
     +0x494: subs    x9, x9, #0x1
     +0x498: eor     w12, w13, w12
     +0x49c: strb    w12, [x11], #1
     +0x4a0: b.ne    <mld_H87+0x48c>
     +0x4a4: b       <mld_H87+0x3b4>
     +0x4a8: mov     w22, wzr
     +0x4ac: cbz     x20, <mld_H87+0x500>
     +0x4b0: mov     x8, sp
     +0x4b4: cmp     x20, #0x8
     +0x4b8: b.cc    <mld_H87+0x4d4>
     +0x4bc: add     x9, x21, x20
     +0x4c0: cmp     x8, x9
     +0x4c4: b.cs    <mld_H87+0x5f8>
     +0x4c8: add     x9, x8, x20
     +0x4cc: cmp     x21, x9
     +0x4d0: b.cs    <mld_H87+0x5f8>
     +0x4d4: mov     x9, xzr
     +0x4d8: sub     x10, x20, x9
     +0x4dc: add     x8, x8, x9
     +0x4e0: add     x9, x21, x9
     +0x4e4: ldrb    w11, [x9], #1
     +0x4e8: ldrb    w12, [x8]
     +0x4ec: subs    x10, x10, #0x1
     +0x4f0: eor     w11, w12, w11
     +0x4f4: strb    w11, [x8], #1
     +0x4f8: b.ne    <mld_H87+0x4e4>
     +0x4fc: add     w22, w22, w20
     +0x500: str     w22, [sp, #200]
     +0x504: mov     x20, sp
     +0x508: mov     w9, #0x88
     +0x50c: mov     x0, sp
     +0x510: ldrb    w8, [x20, w22, uxtw]
     +0x514: eor     w8, w8, #0x1f
     +0x518: strb    w8, [x20, w22, uxtw]
     +0x51c: ldrb    w8, [sp, #135]
     +0x520: str     w9, [sp, #200]
     +0x524: eor     w8, w8, #0x80
     +0x528: strb    w8, [sp, #135]
     +0x52c: bl      <mldsa_keccakf1600_permute>
     +0x530: ldp     q0, q1, [sp]
     +0x534: movi    v3.2d, #0x0
     +0x538: adrp    x8, <page>
     +0x53c: stp     q0, q1, [x19]
     +0x540: ldp     q2, q0, [sp, #32]
     +0x544: str     q3, [sp, #192]
     +0x548: stp     q3, q3, [sp]
     +0x54c: stp     q2, q0, [x19, #32]
     +0x550: stp     q3, q3, [sp, #32]
     +0x554: stp     q3, q3, [sp, #64]
     +0x558: stp     q3, q3, [sp, #96]
     +0x55c: stp     q3, q3, [sp, #128]
     +0x560: stp     q3, q3, [sp, #160]
     +0x564: stp     q3, q3, [sp, #16]
     +0x568: stp     q3, q3, [sp, #48]
     +0x56c: stp     q3, q3, [sp, #80]
     +0x570: stp     q3, q3, [sp, #112]
     +0x574: stp     q3, q3, [sp, #144]
     +0x578: stp     q3, q3, [sp, #176]
     +0x57c: str     q3, [sp]
     +0x580: ldr     x8, [x8, #4088]
     +0x584: ldr     x9, [sp, #216]
     +0x588: ldr     x8, [x8]
     +0x58c: cmp     x8, x9
     +0x590: b.ne    <mld_H87+0x794>
     +0x594: ldp     x20, x19, [sp, #288]
     +0x598: ldr     x29, [sp, #224]
     +0x59c: ldp     x22, x21, [sp, #272]
     +0x5a0: ldp     x24, x23, [sp, #256]
     +0x5a4: ldp     x30, x25, [sp, #240]
     +0x5a8: add     sp, sp, #0x130
     +0x5ac: mov     x0, #0x0
     +0x5b0: mov     x1, #0x0
     +0x5b4: mov     x2, #0x0
     +0x5b8: mov     x3, #0x0
     +0x5bc: mov     x4, #0x0
     +0x5c0: mov     x5, #0x0
     +0x5c4: mov     x6, #0x0
     +0x5c8: mov     x8, #0x0
     +0x5cc: mov     x9, #0x0
     +0x5d0: mov     x10, #0x0
     +0x5d4: mov     x11, #0x0
     +0x5d8: mov     x12, #0x0
     +0x5dc: mov     x13, #0x0
     +0x5e0: mov     x14, #0x0
     +0x5e4: ret     
     +0x5e8: cmp     x22, #0x20
     +0x5ec: b.cs    <mld_H87+0x618>
     +0x5f0: mov     x8, xzr
     +0x5f4: b       <mld_H87+0x660>
     +0x5f8: cmp     x20, #0x20
     +0x5fc: b.cs    <mld_H87+0x69c>
     +0x600: mov     x9, xzr
     +0x604: b       <mld_H87+0x6e0>
     +0x608: cmp     x23, #0x20
     +0x60c: b.cs    <mld_H87+0x718>
     +0x610: mov     x9, xzr
     +0x614: b       <mld_H87+0x75c>
     +0x618: mov     x10, sp
     +0x61c: and     x9, x22, #0x18
     +0x620: and     x8, x22, #0xe0
     +0x624: add     x10, x10, #0x10
     +0x628: add     x11, x25, #0x10
     +0x62c: and     x12, x22, #0xe0
     +0x630: ldp     q0, q3, [x10, #-16]
     +0x634: subs    x12, x12, #0x20
     +0x638: ldp     q1, q2, [x11, #-16]
     +0x63c: add     x11, x11, #0x20
     +0x640: eor     v0.16b, v0.16b, v1.16b
     +0x644: eor     v1.16b, v3.16b, v2.16b
     +0x648: stp     q0, q1, [x10, #-16]
     +0x64c: add     x10, x10, #0x20
     +0x650: b.ne    <mld_H87+0x630>
     +0x654: cmp     x22, x8
     +0x658: b.eq    <mld_H87+0x17c>
     +0x65c: cbz     x9, <mld_H87+0x15c>
     +0x660: mov     x11, x8
     +0x664: and     x8, x22, #0xf8
     +0x668: mov     x10, sp
     +0x66c: sub     x9, x11, x8
     +0x670: add     x10, x10, x11
     +0x674: add     x11, x25, x11
     +0x678: ldr     d0, [x11], #8
     +0x67c: ldr     d1, [x10]
     +0x680: adds    x9, x9, #0x8
     +0x684: eor     v0.8b, v1.8b, v0.8b
     +0x688: str     d0, [x10], #8
     +0x68c: b.ne    <mld_H87+0x678>
     +0x690: cmp     x22, x8
     +0x694: b.eq    <mld_H87+0x17c>
     +0x698: b       <mld_H87+0x15c>
     +0x69c: and     x10, x20, #0x18
     +0x6a0: and     x9, x20, #0xffffffffffffffe0
     +0x6a4: add     x11, x8, #0x10
     +0x6a8: add     x12, x21, #0x10
     +0x6ac: and     x13, x20, #0xffffffffffffffe0
     +0x6b0: ldp     q0, q3, [x11, #-16]
     +0x6b4: subs    x13, x13, #0x20
     +0x6b8: ldp     q1, q2, [x12, #-16]
     +0x6bc: add     x12, x12, #0x20
     +0x6c0: eor     v0.16b, v0.16b, v1.16b
     +0x6c4: eor     v1.16b, v3.16b, v2.16b
     +0x6c8: stp     q0, q1, [x11, #-16]
     +0x6cc: add     x11, x11, #0x20
     +0x6d0: b.ne    <mld_H87+0x6b0>
     +0x6d4: cmp     x20, x9
     +0x6d8: b.eq    <mld_H87+0x4fc>
     +0x6dc: cbz     x10, <mld_H87+0x4d8>
     +0x6e0: mov     x12, x9
     +0x6e4: and     x9, x20, #0xfffffffffffffff8
     +0x6e8: sub     x10, x12, x9
     +0x6ec: add     x11, x8, x12
     +0x6f0: add     x12, x21, x12
     +0x6f4: ldr     d0, [x12], #8
     +0x6f8: ldr     d1, [x11]
     +0x6fc: adds    x10, x10, #0x8
     +0x700: eor     v0.8b, v1.8b, v0.8b
     +0x704: str     d0, [x11], #8
     +0x708: b.ne    <mld_H87+0x6f4>
     +0x70c: cmp     x20, x9
     +0x710: b.eq    <mld_H87+0x4fc>
     +0x714: b       <mld_H87+0x4d8>
     +0x718: and     x10, x23, #0x18
     +0x71c: and     x9, x23, #0xffffffffffffffe0
     +0x720: add     x11, x8, #0x10
     +0x724: add     x12, x24, #0x10
     +0x728: and     x13, x23, #0xffffffffffffffe0
     +0x72c: ldp     q0, q3, [x11, #-16]
     +0x730: subs    x13, x13, #0x20
     +0x734: ldp     q1, q2, [x12, #-16]
     +0x738: add     x12, x12, #0x20
     +0x73c: eor     v0.16b, v0.16b, v1.16b
     +0x740: eor     v1.16b, v3.16b, v2.16b
     +0x744: stp     q0, q1, [x11, #-16]
     +0x748: add     x11, x11, #0x20
     +0x74c: b.ne    <mld_H87+0x72c>
     +0x750: cmp     x23, x9
     +0x754: b.eq    <mld_H87+0x378>
     +0x758: cbz     x10, <mld_H87+0x354>
     +0x75c: mov     x12, x9
     +0x760: and     x9, x23, #0xfffffffffffffff8
     +0x764: sub     x10, x12, x9
     +0x768: add     x11, x8, x12
     +0x76c: add     x12, x24, x12
     +0x770: ldr     d0, [x12], #8
     +0x774: ldr     d1, [x11]
     +0x778: adds    x10, x10, #0x8
     +0x77c: eor     v0.8b, v1.8b, v0.8b
     +0x780: str     d0, [x11], #8
     +0x784: b.ne    <mld_H87+0x770>
     +0x788: cmp     x23, x9
     +0x78c: b.eq    <mld_H87+0x378>
     +0x790: b       <mld_H87+0x354>
     +0x794: bl      <__stack_chk_fail>
 ***)

let MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mld_H87"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The output is SHAKE256 of in1 || in2 || in3, the bytes M1,   *)
(* M2 and M3 as numbers.                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!out in1 in1len in2 in2len in3 in3len M1 M2 M3 guard pc stackpointer
   returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ~(in1len = 0) /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 560),560))
         [(out,64); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        ALLPAIRS nonoverlapping
         [(out,64); (word_sub stackpointer (word 560),560)]
         [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mld_H87) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; in1; word in1len; in2; word in2len; in3;
                               word in3len] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(in1,in1len)) s = M1 /\
                  read (memory :> bytes(in2,in2len)) s = M2 /\
                  read (memory :> bytes(in3,in3len)) s = M3)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,64)) s =
                  num_of_bytelist
                   (list_of_seq
                     (mld_shake256_byte (in1len + in2len + in3len)
                       (M1 + 2 EXP (8 * in1len) *
                             (M2 + 2 EXP (8 * in2len) * M3)))
                     64))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,64);
                memory :> bytes(word_sub stackpointer (word 560),560)])`;;

let MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the lengths only (which give   *)
(* the calls and their arguments), with all accesses within the output, the  *)
(* inputs, the stack, the GOT entry of the stack guard, the guard and the    *)
(* round constants of the permutation, and the writes within the output and  *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e out in1 in1len in2 in2len in3 in3len M1 M2 M3 guard pc
            stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ~(in1len = 0) /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 560),560))
         [(out,64); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        ALLPAIRS nonoverlapping
         [(out,64); (word_sub stackpointer (word 560),560)]
         [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mld_H87) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; in1; word in1len; in2; word in2len; in3;
                               word in3len] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(in1,in1len)) s = M1 /\
                  read (memory :> bytes(in2,in2len)) s = M2 /\
                  read (memory :> bytes(in3,in3len)) s = M3 /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,64)) s =
                  num_of_bytelist
                   (list_of_seq
                     (mld_shake256_byte (in1len + in2len + in3len)
                       (M1 + 2 EXP (8 * in1len) *
                             (M2 + 2 EXP (8 * in2len) * M3)))
                     64) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out in1 in1len in2 in2len in3 in3len
                                 guard pc (word_sub stackpointer (word 560))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,64; in1,in1len; in2,in2len; in3,in3len;
                       word_sub stackpointer (word 560),560;
                       word(pc + got_stack_chk_guard),8; guard,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [out,64; word_sub stackpointer (word 560),560]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,64);
                memory :> bytes(word_sub stackpointer (word 560),560)])`;;

let MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e out in1 in1len in2 in2len in3 in3len guard pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ~(in1len = 0) /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 560),560))
         [(out,64); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        ALLPAIRS nonoverlapping
         [(out,64); (word_sub stackpointer (word 560),560)]
         [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mld_H87) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; in1; word in1len; in2; word in2len; in3;
                               word in3len] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out in1 in1len in2 in2len in3 in3len
                                 guard pc (word_sub stackpointer (word 560))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,64; in1,in1len; in2,in2len; in3,in3len;
                       word_sub stackpointer (word 560),560;
                       word(pc + got_stack_chk_guard),8; guard,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [out,64; word_sub stackpointer (word 560),560]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,64);
                memory :> bytes(word_sub stackpointer (word 560),560)])`;;

let MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_H_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
