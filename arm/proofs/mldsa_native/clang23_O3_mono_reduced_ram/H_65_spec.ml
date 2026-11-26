(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 of up to three inputs: the statement. This is the code for       *)
(* mld_H65 (mld_H in sign.c, for ML-DSA-65) from mldsa-native's portable C   *)
(* implementation compiled by clang 23 with -O3 as a monolithic build with   *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md). Clang inlined the     *)
(* SHAKE256 functions: the function zeroes a Keccak state on its stack,      *)
(* absorbs in1, and in2 and in3 unless their lengths are zero, with loops    *)
(* over blocks of 136, 32 and 8 bytes and over single bytes and calls of     *)
(* mldsa_keccakf1600_permute, finalizes, squeezes the output block by block  *)
(* with calls of mldsa_keccakf1600_permute and memcpy (through its PLT stub  *)
(* and the GOT), and zeroes the state. It is verified in the whole image     *)
(* (see libmldsa.ml) against mld_shake256_byte of                            *)
(* common/mldsa_native_fips202.ml for the concatenation of the three inputs; *)
(* the inputs and the output may overlap, and a pointer with a zero length   *)
(* may be anything (NULL), except that in1len must not be zero: when in1 is  *)
(* shorter than a block, the code goes from its test of in1len < 136         *)
(* straight to the XOR of the rest of in1, past the test of an empty rest,   *)
(* and for in1len = 0 its byte loop runs on until its index wraps around,    *)
(* XORing far past the state (all callers pass a nonzero constant in1len,    *)
(* presumably why clang dropped the test). The stack is the 304 bytes of the *)
(* function and the 240 of mldsa_keccakf1600_permute below them; the address *)
(* of the stack guard is read from the GOT. It is also shown to be constant  *)
(* time and memory safe.                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_absorb.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mld_H65:
       +0x0: sub     sp, sp, #0x130
       +0x4: stp     x29, x30, [sp, #224]
       +0x8: stp     x26, x25, [sp, #240]
       +0xc: stp     x24, x23, [sp, #256]
      +0x10: stp     x22, x21, [sp, #272]
      +0x14: stp     x20, x19, [sp, #288]
      +0x18: adrp    x8, <page>
      +0x1c: movi    v0.2d, #0x0
      +0x20: mov     x21, x7
      +0x24: ldr     x8, [x8, #4088]
      +0x28: mov     x22, x6
      +0x2c: mov     x24, x5
      +0x30: mov     x25, x4
      +0x34: mov     x23, x3
      +0x38: mov     x26, x2
      +0x3c: ldr     x8, [x8]
      +0x40: mov     x19, x1
      +0x44: mov     x20, x0
      +0x48: cmp     x3, #0x88
      +0x4c: str     x8, [sp, #216]
      +0x50: stur    q0, [sp, #188]
      +0x54: stp     q0, q0, [sp]
      +0x58: stp     q0, q0, [sp, #32]
      +0x5c: stp     q0, q0, [sp, #64]
      +0x60: stp     q0, q0, [sp, #96]
      +0x64: stp     q0, q0, [sp, #128]
      +0x68: stp     q0, q0, [sp, #160]
      +0x6c: b.cc    <mld_H65+0x13c>
      +0x70: ldp     d0, d3, [sp]
      +0x74: mov     x0, sp
      +0x78: ldp     d1, d2, [x26]
      +0x7c: sub     x23, x23, #0x88
      +0x80: ldp     d6, d7, [sp, #32]
      +0x84: ldp     d16, d17, [sp, #48]
      +0x88: eor     v0.8b, v0.8b, v1.8b
      +0x8c: eor     v1.8b, v3.8b, v2.8b
      +0x90: ldp     d4, d2, [x26, #16]
      +0x94: ldp     d5, d3, [sp, #16]
      +0x98: stp     d0, d1, [sp]
      +0x9c: eor     v4.8b, v5.8b, v4.8b
      +0xa0: eor     v2.8b, v3.8b, v2.8b
      +0xa4: ldp     d5, d3, [x26, #32]
      +0xa8: stp     d4, d2, [sp, #16]
      +0xac: ldp     d1, d2, [x26, #80]
      +0xb0: eor     v5.8b, v6.8b, v5.8b
      +0xb4: eor     v3.8b, v7.8b, v3.8b
      +0xb8: ldp     d6, d7, [x26, #48]
      +0xbc: stp     d5, d3, [sp, #32]
      +0xc0: ldp     d3, d5, [x26, #96]
      +0xc4: eor     v6.8b, v16.8b, v6.8b
      +0xc8: eor     v7.8b, v17.8b, v7.8b
      +0xcc: ldp     d16, d0, [x26, #64]
      +0xd0: ldp     d18, d17, [sp, #64]
      +0xd4: stp     d6, d7, [sp, #48]
      +0xd8: eor     v0.8b, v17.8b, v0.8b
      +0xdc: ldp     d4, d17, [sp, #80]
      +0xe0: eor     v16.8b, v18.8b, v16.8b
      +0xe4: eor     v1.8b, v4.8b, v1.8b
      +0xe8: ldp     d4, d6, [sp, #96]
      +0xec: eor     v2.8b, v17.8b, v2.8b
      +0xf0: stp     d16, d0, [sp, #64]
      +0xf4: eor     v3.8b, v4.8b, v3.8b
      +0xf8: ldp     d4, d0, [x26, #112]
      +0xfc: eor     v5.8b, v6.8b, v5.8b
     +0x100: ldp     d7, d6, [sp, #112]
     +0x104: stp     d1, d2, [sp, #80]
     +0x108: ldr     d1, [x26, #128]
     +0x10c: ldr     d2, [sp, #128]
     +0x110: add     x26, x26, #0x88
     +0x114: eor     v4.8b, v7.8b, v4.8b
     +0x118: eor     v0.8b, v6.8b, v0.8b
     +0x11c: eor     v1.8b, v2.8b, v1.8b
     +0x120: stp     d3, d5, [sp, #96]
     +0x124: stp     d4, d0, [sp, #112]
     +0x128: str     d1, [sp, #128]
     +0x12c: bl      <mldsa_keccakf1600_permute>
     +0x130: cmp     x23, #0x87
     +0x134: b.hi    <mld_H65+0x70>
     +0x138: cbz     x23, <mld_H65+0x180>
     +0x13c: cmp     x23, #0x8
     +0x140: b.cc    <mld_H65+0x15c>
     +0x144: mov     x8, sp
     +0x148: add     x10, x26, x23
     +0x14c: add     x9, x8, x23
     +0x150: cmp     x26, x9
     +0x154: ccmp    x8, x10, #0x2, cc
     +0x158: b.cs    <mld_H65+0x63c>
     +0x15c: mov     x8, xzr
     +0x160: mov     x9, sp
     +0x164: ldrb    w10, [x26, x8]
     +0x168: ldrb    w11, [x9, x8]
     +0x16c: eor     w10, w11, w10
     +0x170: strb    w10, [x9, x8]
     +0x174: add     x8, x8, #0x1
     +0x178: cmp     x23, x8
     +0x17c: b.ne    <mld_H65+0x164>
     +0x180: str     w23, [sp, #200]
     +0x184: cbz     x24, <mld_H65+0x384>
     +0x188: mov     w8, #0x88
     +0x18c: sub     x8, x8, x23
     +0x190: cmp     x24, x8
     +0x194: b.cs    <mld_H65+0x1ac>
     +0x198: mov     x8, sp
     +0x19c: add     x8, x8, x23
     +0x1a0: cmp     x24, #0x8
     +0x1a4: b.cs    <mld_H65+0x340>
     +0x1a8: b       <mld_H65+0x354>
     +0x1ac: mov     x26, sp
     +0x1b0: b       <mld_H65+0x1d4>
     +0x1b4: mov     x0, sp
     +0x1b8: sub     x24, x24, x8
     +0x1bc: add     x25, x25, x8
     +0x1c0: bl      <mldsa_keccakf1600_permute>
     +0x1c4: mov     x23, xzr
     +0x1c8: cmp     x24, #0x87
     +0x1cc: mov     w8, #0x88
     +0x1d0: b.ls    <mld_H65+0x32c>
     +0x1d4: cmp     x8, #0x8
     +0x1d8: b.cs    <mld_H65+0x1e4>
     +0x1dc: mov     x9, xzr
     +0x1e0: b       <mld_H65+0x300>
     +0x1e4: cmp     x8, #0x20
     +0x1e8: b.cs    <mld_H65+0x1f4>
     +0x1ec: mov     x9, xzr
     +0x1f0: b       <mld_H65+0x2c8>
     +0x1f4: add     x10, x26, x23
     +0x1f8: ldp     q1, q2, [x25]
     +0x1fc: ldp     q0, q3, [x10]
     +0x200: and     x9, x8, #0xe0
     +0x204: cmp     x9, #0x20
     +0x208: eor     v0.16b, v0.16b, v1.16b
     +0x20c: eor     v1.16b, v3.16b, v2.16b
     +0x210: stp     q0, q1, [x10]
     +0x214: b.eq    <mld_H65+0x2b8>
     +0x218: ldp     q0, q3, [x10, #32]
     +0x21c: cmp     x9, #0x40
     +0x220: ldp     q1, q2, [x25, #32]
     +0x224: eor     v0.16b, v0.16b, v1.16b
     +0x228: eor     v1.16b, v3.16b, v2.16b
     +0x22c: stp     q0, q1, [x10, #32]
     +0x230: b.eq    <mld_H65+0x2b8>
     +0x234: ldp     q0, q3, [x10, #64]
     +0x238: cmp     x9, #0x60
     +0x23c: ldp     q1, q2, [x25, #64]
     +0x240: eor     v0.16b, v0.16b, v1.16b
     +0x244: eor     v1.16b, v3.16b, v2.16b
     +0x248: stp     q0, q1, [x10, #64]
     +0x24c: b.eq    <mld_H65+0x2b8>
     +0x250: ldp     q0, q3, [x10, #96]
     +0x254: cmp     x9, #0x80
     +0x258: ldp     q1, q2, [x25, #96]
     +0x25c: eor     v0.16b, v0.16b, v1.16b
     +0x260: eor     v1.16b, v3.16b, v2.16b
     +0x264: stp     q0, q1, [x10, #96]
     +0x268: b.eq    <mld_H65+0x2b8>
     +0x26c: ldp     q0, q3, [x10, #128]
     +0x270: cmp     x9, #0xa0
     +0x274: ldp     q1, q2, [x25, #128]
     +0x278: eor     v0.16b, v0.16b, v1.16b
     +0x27c: eor     v1.16b, v3.16b, v2.16b
     +0x280: stp     q0, q1, [x10, #128]
     +0x284: b.eq    <mld_H65+0x2b8>
     +0x288: ldp     q0, q3, [x10, #160]
     +0x28c: cmp     x9, #0xc0
     +0x290: ldp     q1, q2, [x25, #160]
     +0x294: eor     v0.16b, v0.16b, v1.16b
     +0x298: eor     v1.16b, v3.16b, v2.16b
     +0x29c: stp     q0, q1, [x10, #160]
     +0x2a0: b.eq    <mld_H65+0x2b8>
     +0x2a4: ldp     q0, q3, [x10, #192]
     +0x2a8: ldp     q1, q2, [x25, #192]
     +0x2ac: eor     v0.16b, v0.16b, v1.16b
     +0x2b0: eor     v1.16b, v3.16b, v2.16b
     +0x2b4: stp     q0, q1, [x10, #192]
     +0x2b8: cmp     x8, x9
     +0x2bc: b.eq    <mld_H65+0x1b4>
     +0x2c0: and     x10, x8, #0x18
     +0x2c4: cbz     x10, <mld_H65+0x300>
     +0x2c8: mov     x12, x9
     +0x2cc: and     x9, x8, #0xf8
     +0x2d0: add     x11, x12, x23
     +0x2d4: sub     x10, x12, x9
     +0x2d8: add     x12, x25, x12
     +0x2dc: add     x11, x26, x11
     +0x2e0: ldr     d0, [x12], #8
     +0x2e4: ldr     d1, [x11]
     +0x2e8: adds    x10, x10, #0x8
     +0x2ec: eor     v0.8b, v1.8b, v0.8b
     +0x2f0: str     d0, [x11], #8
     +0x2f4: b.ne    <mld_H65+0x2e0>
     +0x2f8: cmp     x8, x9
     +0x2fc: b.eq    <mld_H65+0x1b4>
     +0x300: add     x11, x9, x23
     +0x304: sub     x10, x8, x9
     +0x308: add     x9, x25, x9
     +0x30c: add     x11, x26, x11
     +0x310: ldrb    w12, [x9], #1
     +0x314: ldrb    w13, [x11]
     +0x318: subs    x10, x10, #0x1
     +0x31c: eor     w12, w13, w12
     +0x320: strb    w12, [x11], #1
     +0x324: b.ne    <mld_H65+0x310>
     +0x328: b       <mld_H65+0x1b4>
     +0x32c: mov     w23, wzr
     +0x330: cbz     x24, <mld_H65+0x380>
     +0x334: mov     x8, sp
     +0x338: cmp     x24, #0x8
     +0x33c: b.cc    <mld_H65+0x354>
     +0x340: add     x9, x8, x24
     +0x344: add     x10, x25, x24
     +0x348: cmp     x25, x9
     +0x34c: ccmp    x8, x10, #0x2, cc
     +0x350: b.cs    <mld_H65+0x65c>
     +0x354: mov     x9, xzr
     +0x358: sub     x10, x24, x9
     +0x35c: add     x8, x8, x9
     +0x360: add     x9, x25, x9
     +0x364: ldrb    w11, [x9], #1
     +0x368: ldrb    w12, [x8]
     +0x36c: subs    x10, x10, #0x1
     +0x370: eor     w11, w12, w11
     +0x374: strb    w11, [x8], #1
     +0x378: b.ne    <mld_H65+0x364>
     +0x37c: add     w23, w23, w24
     +0x380: str     w23, [sp, #200]
     +0x384: cbz     x21, <mld_H65+0x508>
     +0x388: mov     w8, #0x88
     +0x38c: sub     w8, w8, w23
     +0x390: cmp     x21, x8
     +0x394: b.cs    <mld_H65+0x3ac>
     +0x398: mov     x8, sp
     +0x39c: add     x8, x8, w23, uxtw
     +0x3a0: cmp     x21, #0x8
     +0x3a4: b.cs    <mld_H65+0x4c0>
     +0x3a8: b       <mld_H65+0x4d8>
     +0x3ac: mov     x24, sp
     +0x3b0: add     x25, x24, #0x10
     +0x3b4: b       <mld_H65+0x3d8>
     +0x3b8: mov     x0, sp
     +0x3bc: sub     x21, x21, x8
     +0x3c0: add     x22, x22, x8
     +0x3c4: bl      <mldsa_keccakf1600_permute>
     +0x3c8: mov     w23, wzr
     +0x3cc: cmp     x21, #0x87
     +0x3d0: mov     w8, #0x88
     +0x3d4: b.ls    <mld_H65+0x4ac>
     +0x3d8: cmp     w23, #0x88
     +0x3dc: b.eq    <mld_H65+0x3b8>
     +0x3e0: cmp     x8, #0x8
     +0x3e4: mov     w9, w23
     +0x3e8: b.cs    <mld_H65+0x3f4>
     +0x3ec: mov     x10, xzr
     +0x3f0: b       <mld_H65+0x480>
     +0x3f4: cmp     x8, #0x20
     +0x3f8: b.cs    <mld_H65+0x404>
     +0x3fc: mov     x10, xzr
     +0x400: b       <mld_H65+0x448>
     +0x404: and     x11, x8, #0x18
     +0x408: and     x10, x8, #0xffffffe0
     +0x40c: add     x12, x25, x9
     +0x410: add     x13, x22, #0x10
     +0x414: and     x14, x8, #0xffffffe0
     +0x418: ldp     q0, q3, [x12, #-16]
     +0x41c: subs    x14, x14, #0x20
     +0x420: ldp     q1, q2, [x13, #-16]
     +0x424: add     x13, x13, #0x20
     +0x428: eor     v0.16b, v0.16b, v1.16b
     +0x42c: eor     v1.16b, v3.16b, v2.16b
     +0x430: stp     q0, q1, [x12, #-16]
     +0x434: add     x12, x12, #0x20
     +0x438: b.ne    <mld_H65+0x418>
     +0x43c: cmp     x8, x10
     +0x440: b.eq    <mld_H65+0x3b8>
     +0x444: cbz     x11, <mld_H65+0x480>
     +0x448: mov     x13, x10
     +0x44c: and     x10, x8, #0xfffffff8
     +0x450: add     x12, x13, x9
     +0x454: sub     x11, x13, x10
     +0x458: add     x13, x22, x13
     +0x45c: add     x12, x24, x12
     +0x460: ldr     d0, [x13], #8
     +0x464: ldr     d1, [x12]
     +0x468: adds    x11, x11, #0x8
     +0x46c: eor     v0.8b, v1.8b, v0.8b
     +0x470: str     d0, [x12], #8
     +0x474: b.ne    <mld_H65+0x460>
     +0x478: cmp     x8, x10
     +0x47c: b.eq    <mld_H65+0x3b8>
     +0x480: add     x11, x10, x9
     +0x484: sub     x9, x8, x10
     +0x488: add     x10, x22, x10
     +0x48c: add     x11, x24, x11
     +0x490: ldrb    w12, [x10], #1
     +0x494: ldrb    w13, [x11]
     +0x498: subs    x9, x9, #0x1
     +0x49c: eor     w12, w13, w12
     +0x4a0: strb    w12, [x11], #1
     +0x4a4: b.ne    <mld_H65+0x490>
     +0x4a8: b       <mld_H65+0x3b8>
     +0x4ac: mov     w23, wzr
     +0x4b0: cbz     x21, <mld_H65+0x504>
     +0x4b4: mov     x8, sp
     +0x4b8: cmp     x21, #0x8
     +0x4bc: b.cc    <mld_H65+0x4d8>
     +0x4c0: add     x9, x22, x21
     +0x4c4: cmp     x8, x9
     +0x4c8: b.cs    <mld_H65+0x64c>
     +0x4cc: add     x9, x8, x21
     +0x4d0: cmp     x22, x9
     +0x4d4: b.cs    <mld_H65+0x64c>
     +0x4d8: mov     x9, xzr
     +0x4dc: sub     x10, x21, x9
     +0x4e0: add     x8, x8, x9
     +0x4e4: add     x9, x22, x9
     +0x4e8: ldrb    w11, [x9], #1
     +0x4ec: ldrb    w12, [x8]
     +0x4f0: subs    x10, x10, #0x1
     +0x4f4: eor     w11, w12, w11
     +0x4f8: strb    w11, [x8], #1
     +0x4fc: b.ne    <mld_H65+0x4e8>
     +0x500: add     w23, w23, w21
     +0x504: str     w23, [sp, #200]
     +0x508: mov     x25, sp
     +0x50c: mov     x24, xzr
     +0x510: mov     w26, #0x88
     +0x514: ldrb    w8, [x25, w23, uxtw]
     +0x518: eor     w8, w8, #0x1f
     +0x51c: strb    w8, [x25, w23, uxtw]
     +0x520: mov     w23, #0x88
     +0x524: ldrb    w8, [sp, #135]
     +0x528: str     w23, [sp, #200]
     +0x52c: eor     w8, w8, #0x80
     +0x530: strb    w8, [sp, #135]
     +0x534: b       <mld_H65+0x568>
     +0x538: sub     w8, w23, w26
     +0x53c: add     x22, x25, w26, uxtw
     +0x540: cmp     x19, x8
     +0x544: csel    x21, x19, x8, cc
     +0x548: add     x0, x20, x24
     +0x54c: mov     x1, x22
     +0x550: mov     x2, x21
     +0x554: bl      <memcpy>
     +0x558: subs    x19, x19, x21
     +0x55c: add     w26, w26, w21
     +0x560: add     x24, x21, x24
     +0x564: b.eq    <mld_H65+0x58c>
     +0x568: cmp     w26, #0x88
     +0x56c: b.ne    <mld_H65+0x538>
     +0x570: mov     x0, sp
     +0x574: mov     x22, sp
     +0x578: bl      <mldsa_keccakf1600_permute>
     +0x57c: cmp     x19, #0x88
     +0x580: mov     w26, wzr
     +0x584: csel    x21, x19, x23, cc
     +0x588: b       <mld_H65+0x548>
     +0x58c: movi    v0.2d, #0x0
     +0x590: mov     x8, sp
     +0x594: stp     q0, q0, [sp, #16]
     +0x598: stp     q0, q0, [sp, #48]
     +0x59c: stp     q0, q0, [sp, #80]
     +0x5a0: stp     q0, q0, [sp, #112]
     +0x5a4: stp     q0, q0, [sp, #144]
     +0x5a8: stp     q0, q0, [sp, #176]
     +0x5ac: str     q0, [sp]
     +0x5b0: stp     q0, q0, [sp, #16]
     +0x5b4: stp     q0, q0, [sp, #48]
     +0x5b8: stp     q0, q0, [sp, #80]
     +0x5bc: stp     q0, q0, [sp, #112]
     +0x5c0: stp     q0, q0, [sp, #144]
     +0x5c4: stp     q0, q0, [sp, #176]
     +0x5c8: str     q0, [sp]
     +0x5cc: adrp    x8, <page>
     +0x5d0: ldr     x8, [x8, #4088]
     +0x5d4: ldr     x9, [sp, #216]
     +0x5d8: ldr     x8, [x8]
     +0x5dc: cmp     x8, x9
     +0x5e0: b.ne    <mld_H65+0x7e8>
     +0x5e4: ldp     x20, x19, [sp, #288]
     +0x5e8: ldp     x22, x21, [sp, #272]
     +0x5ec: ldp     x24, x23, [sp, #256]
     +0x5f0: ldp     x26, x25, [sp, #240]
     +0x5f4: ldp     x29, x30, [sp, #224]
     +0x5f8: add     sp, sp, #0x130
     +0x5fc: mov     x0, #0x0
     +0x600: mov     x1, #0x0
     +0x604: mov     x2, #0x0
     +0x608: mov     x3, #0x0
     +0x60c: mov     x4, #0x0
     +0x610: mov     x5, #0x0
     +0x614: mov     x6, #0x0
     +0x618: mov     x7, #0x0
     +0x61c: mov     x8, #0x0
     +0x620: mov     x9, #0x0
     +0x624: mov     x10, #0x0
     +0x628: mov     x11, #0x0
     +0x62c: mov     x12, #0x0
     +0x630: mov     x13, #0x0
     +0x634: mov     x14, #0x0
     +0x638: ret     
     +0x63c: cmp     x23, #0x20
     +0x640: b.cs    <mld_H65+0x66c>
     +0x644: mov     x8, xzr
     +0x648: b       <mld_H65+0x6b4>
     +0x64c: cmp     x21, #0x20
     +0x650: b.cs    <mld_H65+0x6f0>
     +0x654: mov     x9, xzr
     +0x658: b       <mld_H65+0x734>
     +0x65c: cmp     x24, #0x20
     +0x660: b.cs    <mld_H65+0x76c>
     +0x664: mov     x9, xzr
     +0x668: b       <mld_H65+0x7b0>
     +0x66c: mov     x10, sp
     +0x670: and     x9, x23, #0x18
     +0x674: and     x8, x23, #0xe0
     +0x678: add     x10, x10, #0x10
     +0x67c: add     x11, x26, #0x10
     +0x680: and     x12, x23, #0xe0
     +0x684: ldp     q0, q3, [x10, #-16]
     +0x688: subs    x12, x12, #0x20
     +0x68c: ldp     q1, q2, [x11, #-16]
     +0x690: add     x11, x11, #0x20
     +0x694: eor     v0.16b, v0.16b, v1.16b
     +0x698: eor     v1.16b, v3.16b, v2.16b
     +0x69c: stp     q0, q1, [x10, #-16]
     +0x6a0: add     x10, x10, #0x20
     +0x6a4: b.ne    <mld_H65+0x684>
     +0x6a8: cmp     x23, x8
     +0x6ac: b.eq    <mld_H65+0x180>
     +0x6b0: cbz     x9, <mld_H65+0x160>
     +0x6b4: mov     x11, x8
     +0x6b8: and     x8, x23, #0xf8
     +0x6bc: mov     x10, sp
     +0x6c0: sub     x9, x11, x8
     +0x6c4: add     x10, x10, x11
     +0x6c8: add     x11, x26, x11
     +0x6cc: ldr     d0, [x11], #8
     +0x6d0: ldr     d1, [x10]
     +0x6d4: adds    x9, x9, #0x8
     +0x6d8: eor     v0.8b, v1.8b, v0.8b
     +0x6dc: str     d0, [x10], #8
     +0x6e0: b.ne    <mld_H65+0x6cc>
     +0x6e4: cmp     x23, x8
     +0x6e8: b.eq    <mld_H65+0x180>
     +0x6ec: b       <mld_H65+0x160>
     +0x6f0: and     x10, x21, #0x18
     +0x6f4: and     x9, x21, #0xffffffffffffffe0
     +0x6f8: add     x11, x8, #0x10
     +0x6fc: add     x12, x22, #0x10
     +0x700: and     x13, x21, #0xffffffffffffffe0
     +0x704: ldp     q0, q3, [x11, #-16]
     +0x708: subs    x13, x13, #0x20
     +0x70c: ldp     q1, q2, [x12, #-16]
     +0x710: add     x12, x12, #0x20
     +0x714: eor     v0.16b, v0.16b, v1.16b
     +0x718: eor     v1.16b, v3.16b, v2.16b
     +0x71c: stp     q0, q1, [x11, #-16]
     +0x720: add     x11, x11, #0x20
     +0x724: b.ne    <mld_H65+0x704>
     +0x728: cmp     x21, x9
     +0x72c: b.eq    <mld_H65+0x500>
     +0x730: cbz     x10, <mld_H65+0x4dc>
     +0x734: mov     x12, x9
     +0x738: and     x9, x21, #0xfffffffffffffff8
     +0x73c: sub     x10, x12, x9
     +0x740: add     x11, x8, x12
     +0x744: add     x12, x22, x12
     +0x748: ldr     d0, [x12], #8
     +0x74c: ldr     d1, [x11]
     +0x750: adds    x10, x10, #0x8
     +0x754: eor     v0.8b, v1.8b, v0.8b
     +0x758: str     d0, [x11], #8
     +0x75c: b.ne    <mld_H65+0x748>
     +0x760: cmp     x21, x9
     +0x764: b.eq    <mld_H65+0x500>
     +0x768: b       <mld_H65+0x4dc>
     +0x76c: and     x10, x24, #0x18
     +0x770: and     x9, x24, #0xffffffffffffffe0
     +0x774: add     x11, x8, #0x10
     +0x778: add     x12, x25, #0x10
     +0x77c: and     x13, x24, #0xffffffffffffffe0
     +0x780: ldp     q0, q3, [x11, #-16]
     +0x784: subs    x13, x13, #0x20
     +0x788: ldp     q1, q2, [x12, #-16]
     +0x78c: add     x12, x12, #0x20
     +0x790: eor     v0.16b, v0.16b, v1.16b
     +0x794: eor     v1.16b, v3.16b, v2.16b
     +0x798: stp     q0, q1, [x11, #-16]
     +0x79c: add     x11, x11, #0x20
     +0x7a0: b.ne    <mld_H65+0x780>
     +0x7a4: cmp     x24, x9
     +0x7a8: b.eq    <mld_H65+0x37c>
     +0x7ac: cbz     x10, <mld_H65+0x358>
     +0x7b0: mov     x12, x9
     +0x7b4: and     x9, x24, #0xfffffffffffffff8
     +0x7b8: sub     x10, x12, x9
     +0x7bc: add     x11, x8, x12
     +0x7c0: add     x12, x25, x12
     +0x7c4: ldr     d0, [x12], #8
     +0x7c8: ldr     d1, [x11]
     +0x7cc: adds    x10, x10, #0x8
     +0x7d0: eor     v0.8b, v1.8b, v0.8b
     +0x7d4: str     d0, [x11], #8
     +0x7d8: b.ne    <mld_H65+0x7c4>
     +0x7dc: cmp     x24, x9
     +0x7e0: b.eq    <mld_H65+0x37c>
     +0x7e4: b       <mld_H65+0x358>
     +0x7e8: bl      <__stack_chk_fail>
 ***)

let MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mld_H65";
    layout_range "plt_memcpy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The output is SHAKE256 of in1 || in2 || in3, the bytes M1,   *)
(* M2 and M3 as numbers.                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mc ea el ev.
   memcpy_full_contract mc ea el ev
   ==> !out outlen in1 in1len in2 in2len in3 in3len M1 M2 M3 guard pc
       stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ~(in1len = 0) /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 544),544))
         [(out,outlen); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 544),544)]
         [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mld_H65) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; in1; word in1len; in2;
                               word in2len; in3; word in3len] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(in1,in1len)) s = M1 /\
                  read (memory :> bytes(in2,in2len)) s = M2 /\
                  read (memory :> bytes(in3,in3len)) s = M3)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist
                   (list_of_seq
                     (mld_shake256_byte (in1len + in2len + in3len)
                       (M1 + 2 EXP (8 * in1len) *
                             (M2 + 2 EXP (8 * in2len) * M3)))
                     outlen))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 544),544)])`;;

let MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the lengths only (which give   *)
(* the calls and their arguments), with all accesses within the output, the  *)
(* inputs, the stack, the GOT entry of the stack guard, the guard and the    *)
(* round constants of the permutation, and the writes within the output and  *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `!mc ea el ev.
   memcpy_full_contract mc ea el ev
   ==> exists f_events.
     forall e out outlen in1 in1len in2 in2len in3 in3len M1 M2 M3 guard pc
            stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ~(in1len = 0) /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 544),544))
         [(out,outlen); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 544),544)]
         [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mld_H65) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; in1; word in1len; in2;
                               word in2len; in3; word in3len] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(in1,in1len)) s = M1 /\
                  read (memory :> bytes(in2,in2len)) s = M2 /\
                  read (memory :> bytes(in3,in3len)) s = M3 /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist
                   (list_of_seq
                     (mld_shake256_byte (in1len + in2len + in3len)
                       (M1 + 2 EXP (8 * in1len) *
                             (M2 + 2 EXP (8 * in2len) * M3)))
                     outlen) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out outlen in1 in1len in2 in2len in3 in3len
                                 guard mc pc (word_sub stackpointer (word 544))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,outlen; in1,in1len; in2,in2len; in3,in3len;
                       word_sub stackpointer (word 544),544;
                       word(pc + got_stack_chk_guard),8; guard,8;
                       word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [out,outlen; word_sub stackpointer (word 544),544]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 544),544)])`;;

let MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mc ea el ev.
   memcpy_full_contract mc ea el ev
   ==> exists f_events.
     forall e out outlen in1 in1len in2 in2len in3 in3len guard pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ~(in1len = 0) /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 544),544))
         [(out,outlen); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 544),544)]
         [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mld_H65) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; in1; word in1len; in2;
                               word in2len; in3; word in3len] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out outlen in1 in1len in2 in2len in3 in3len
                                 guard mc pc (word_sub stackpointer (word 544))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,outlen; in1,in1len; in2,in2len; in3,in3len;
                       word_sub stackpointer (word 544),544;
                       word(pc + got_stack_chk_guard),8; guard,8;
                       word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [out,outlen; word_sub stackpointer (word 544),544]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 544),544)])`;;

let MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_H_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
