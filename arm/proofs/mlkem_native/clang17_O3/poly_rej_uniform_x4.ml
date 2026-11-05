(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of four polynomials from four seeds by rejection. This   *)
(* is the code for mlkem_poly_rej_uniform_x4 from mlkem-native's portable C  *)
(* implementation compiled by clang 17 with -O3 (see                         *)
(* mlkem_native/README.md), which absorbs the four seeds of 34 bytes, 64     *)
(* bytes apart, into a fourfold SHAKE128 state, squeezes three blocks of 168 *)
(* bytes of each and samples the coefficients below 3329 from them, and then *)
(* squeezes one more block of each and samples from those polynomials that   *)
(* have fewer than 256 coefficients until each has 256, before zeroing the   *)
(* state and the buffers. As at gcc -O3, the sampling of mlk_rej_uniform_c   *)
(* is inlined, as eight copies of its loop: loop1 to loop4 for the first     *)
(* three blocks of each polynomial, and loop6 to loop9 for each further      *)
(* block, inside the loop loop5 that squeezes the blocks. The code is in the *)
(* whole image (see libmlkem.ml), and the eight copies of the loop are       *)
(* verified there with the tool in rej_uniform.ml.                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/clang17_O3/rej_uniform.ml";;

(*** The code in the image:

    mlkem_poly_rej_uniform_x4:
       +0x0: stp     x29, x30, [sp, #-96]!
       +0x4: stp     x28, x27, [sp, #16]
       +0x8: stp     x26, x25, [sp, #32]
       +0xc: stp     x24, x23, [sp, #48]
      +0x10: stp     x22, x21, [sp, #64]
      +0x14: stp     x20, x19, [sp, #80]
      +0x18: mov     x29, sp
      +0x1c: sub     x9, sp, #0xb80
      +0x20: and     sp, x9, #0xffffffffffffffe0
      +0x24: adrp    x8, <page>
      +0x28: mov     x22, x0
      +0x2c: add     x0, sp, #0x40
      +0x30: mov     x23, x4
      +0x34: mov     x19, x3
      +0x38: mov     x20, x2
      +0x3c: ldr     x8, [x8, #4088]  // got_stack_chk_guard
      +0x40: mov     x21, x1
      +0x44: ldr     x8, [x8]
      +0x48: str     x8, [sp, #2936]
      +0x4c: bl      <mlkem_shake128x4_init>
      +0x50: add     x2, x23, #0x40
      +0x54: add     x3, x23, #0x80
      +0x58: add     x4, x23, #0xc0
      +0x5c: add     x0, sp, #0x40
      +0x60: mov     x1, x23
      +0x64: mov     w5, #0x22
      +0x68: bl      <mlkem_shake128x4_absorb_once>
      +0x6c: add     x23, sp, #0x360
      +0x70: add     x0, sp, #0x360
      +0x74: add     x1, x23, #0x200
      +0x78: add     x2, x23, #0x400
      +0x7c: add     x3, x23, #0x600
      +0x80: add     x5, sp, #0x40
      +0x84: mov     w4, #0x3
      +0x88: stp     x2, x1, [sp, #40]
      +0x8c: str     x3, [sp, #32]
      +0x90: bl      <mlkem_shake128x4_squeezeblocks>
      +0x94: mov     x8, xzr
      +0x98: mov     x26, xzr
      +0x9c: add     x9, x23, x8
      +0xa0: ldrb    w11, [x9]
      +0xa4: ldrb    w10, [x9, #1]
      +0xa8: bfi     w11, w10, #8, #4
      +0xac: cmp     w11, #0xd00
      +0xb0: b.hi    <mlkem_poly_rej_uniform_x4+0xc0>
      +0xb4: add     x12, x26, #0x1
      +0xb8: strh    w11, [x22, x26, lsl #1]
      +0xbc: mov     x26, x12
      +0xc0: cmp     x26, #0xff
      +0xc4: b.hi    <mlkem_poly_rej_uniform_x4+0xe8>
      +0xc8: ldrb    w9, [x9, #2]
      +0xcc: lsr     w10, w10, #4
      +0xd0: orr     w9, w10, w9, lsl #4
      +0xd4: cmp     w9, #0xd00
      +0xd8: b.hi    <mlkem_poly_rej_uniform_x4+0xe8>
      +0xdc: add     x10, x26, #0x1
      +0xe0: strh    w9, [x22, x26, lsl #1]
      +0xe4: mov     x26, x10
      +0xe8: cmp     x26, #0x100
      +0xec: cset    w16, cc
      +0xf0: cmp     x26, #0xff
      +0xf4: b.hi    <mlkem_poly_rej_uniform_x4+0x108>
      +0xf8: add     x9, x8, #0x3
      +0xfc: add     x8, x8, #0x3
     +0x100: cmp     x9, #0x1f6
     +0x104: b.cc    <mlkem_poly_rej_uniform_x4+0x9c>
     +0x108: mov     x8, xzr
     +0x10c: mov     x27, xzr
     +0x110: add     x9, sp, #0x360
     +0x114: add     x10, x9, x8
     +0x118: ldrb    w12, [x10, #512]
     +0x11c: ldrb    w11, [x10, #513]
     +0x120: bfi     w12, w11, #8, #4
     +0x124: cmp     w12, #0xd00
     +0x128: b.hi    <mlkem_poly_rej_uniform_x4+0x138>
     +0x12c: add     x13, x27, #0x1
     +0x130: strh    w12, [x21, x27, lsl #1]
     +0x134: mov     x27, x13
     +0x138: cmp     x27, #0xff
     +0x13c: b.hi    <mlkem_poly_rej_uniform_x4+0x160>
     +0x140: ldrb    w10, [x10, #514]
     +0x144: lsr     w11, w11, #4
     +0x148: orr     w10, w11, w10, lsl #4
     +0x14c: cmp     w10, #0xd00
     +0x150: b.hi    <mlkem_poly_rej_uniform_x4+0x160>
     +0x154: add     x11, x27, #0x1
     +0x158: strh    w10, [x21, x27, lsl #1]
     +0x15c: mov     x27, x11
     +0x160: cmp     x27, #0x100
     +0x164: cset    w15, cc
     +0x168: cmp     x27, #0xff
     +0x16c: b.hi    <mlkem_poly_rej_uniform_x4+0x180>
     +0x170: add     x10, x8, #0x3
     +0x174: add     x8, x8, #0x3
     +0x178: cmp     x10, #0x1f6
     +0x17c: b.cc    <mlkem_poly_rej_uniform_x4+0x114>
     +0x180: mov     x8, xzr
     +0x184: mov     x28, xzr
     +0x188: add     x9, sp, #0x360
     +0x18c: add     x10, x9, x8
     +0x190: ldrb    w12, [x10, #1024]
     +0x194: ldrb    w11, [x10, #1025]
     +0x198: bfi     w12, w11, #8, #4
     +0x19c: cmp     w12, #0xd00
     +0x1a0: b.hi    <mlkem_poly_rej_uniform_x4+0x1b0>
     +0x1a4: add     x13, x28, #0x1
     +0x1a8: strh    w12, [x20, x28, lsl #1]
     +0x1ac: mov     x28, x13
     +0x1b0: cmp     x28, #0xff
     +0x1b4: b.hi    <mlkem_poly_rej_uniform_x4+0x1d8>
     +0x1b8: ldrb    w10, [x10, #1026]
     +0x1bc: lsr     w11, w11, #4
     +0x1c0: orr     w10, w11, w10, lsl #4
     +0x1c4: cmp     w10, #0xd00
     +0x1c8: b.hi    <mlkem_poly_rej_uniform_x4+0x1d8>
     +0x1cc: add     x11, x28, #0x1
     +0x1d0: strh    w10, [x20, x28, lsl #1]
     +0x1d4: mov     x28, x11
     +0x1d8: cmp     x28, #0x100
     +0x1dc: cset    w14, cc
     +0x1e0: cmp     x28, #0xff
     +0x1e4: b.hi    <mlkem_poly_rej_uniform_x4+0x1f8>
     +0x1e8: add     x10, x8, #0x3
     +0x1ec: add     x8, x8, #0x3
     +0x1f0: cmp     x10, #0x1f6
     +0x1f4: b.cc    <mlkem_poly_rej_uniform_x4+0x18c>
     +0x1f8: mov     x8, xzr
     +0x1fc: mov     x23, xzr
     +0x200: add     x9, sp, #0x360
     +0x204: add     x10, x9, x8
     +0x208: ldrb    w12, [x10, #1536]
     +0x20c: ldrb    w11, [x10, #1537]
     +0x210: bfi     w12, w11, #8, #4
     +0x214: cmp     w12, #0xd00
     +0x218: b.hi    <mlkem_poly_rej_uniform_x4+0x228>
     +0x21c: add     x13, x23, #0x1
     +0x220: strh    w12, [x19, x23, lsl #1]
     +0x224: mov     x23, x13
     +0x228: cmp     x23, #0xff
     +0x22c: b.hi    <mlkem_poly_rej_uniform_x4+0x250>
     +0x230: ldrb    w10, [x10, #1538]
     +0x234: lsr     w11, w11, #4
     +0x238: orr     w10, w11, w10, lsl #4
     +0x23c: cmp     w10, #0xd00
     +0x240: b.hi    <mlkem_poly_rej_uniform_x4+0x250>
     +0x244: add     x11, x23, #0x1
     +0x248: strh    w10, [x19, x23, lsl #1]
     +0x24c: mov     x23, x11
     +0x250: cmp     x23, #0x100
     +0x254: cset    w25, cc
     +0x258: cmp     x23, #0xff
     +0x25c: b.hi    <mlkem_poly_rej_uniform_x4+0x270>
     +0x260: add     x10, x8, #0x3
     +0x264: add     x8, x8, #0x3
     +0x268: cmp     x10, #0x1f6
     +0x26c: b.cc    <mlkem_poly_rej_uniform_x4+0x204>
     +0x270: cmp     x26, #0x100
     +0x274: str     x21, [sp, #24]
     +0x278: b.cc    <mlkem_poly_rej_uniform_x4+0x294>
     +0x27c: cmp     x27, #0x100
     +0x280: b.cc    <mlkem_poly_rej_uniform_x4+0x294>
     +0x284: cmp     x28, #0x100
     +0x288: b.cc    <mlkem_poly_rej_uniform_x4+0x294>
     +0x28c: cmp     x23, #0xff
     +0x290: b.hi    <mlkem_poly_rej_uniform_x4+0x4dc>
     +0x294: add     x24, sp, #0x360
     +0x298: str     x22, [sp, #16]
     +0x29c: ldp     x2, x1, [sp, #40]
     +0x2a0: add     x0, sp, #0x360
     +0x2a4: add     x5, sp, #0x40
     +0x2a8: ldr     x3, [sp, #32]
     +0x2ac: mov     w4, #0x1
     +0x2b0: str     w15, [sp, #60]
     +0x2b4: mov     x21, x20
     +0x2b8: mov     x20, x19
     +0x2bc: mov     w19, w14
     +0x2c0: mov     w22, w16
     +0x2c4: bl      <mlkem_shake128x4_squeezeblocks>
     +0x2c8: tbz     w22, #0, <mlkem_poly_rej_uniform_x4+0x348>
     +0x2cc: ldp     x22, x15, [sp, #16]
     +0x2d0: mov     x8, xzr
     +0x2d4: mov     w14, w19
     +0x2d8: mov     x19, x20
     +0x2dc: mov     x20, x21
     +0x2e0: add     x9, x24, x8
     +0x2e4: ldrb    w11, [x9]
     +0x2e8: ldrb    w10, [x9, #1]
     +0x2ec: bfi     w11, w10, #8, #4
     +0x2f0: cmp     w11, #0xd00
     +0x2f4: b.hi    <mlkem_poly_rej_uniform_x4+0x304>
     +0x2f8: add     x12, x26, #0x1
     +0x2fc: strh    w11, [x22, x26, lsl #1]
     +0x300: mov     x26, x12
     +0x304: cmp     x26, #0xff
     +0x308: b.hi    <mlkem_poly_rej_uniform_x4+0x32c>
     +0x30c: ldrb    w9, [x9, #2]
     +0x310: lsr     w10, w10, #4
     +0x314: orr     w9, w10, w9, lsl #4
     +0x318: cmp     w9, #0xd00
     +0x31c: b.hi    <mlkem_poly_rej_uniform_x4+0x32c>
     +0x320: add     x10, x26, #0x1
     +0x324: strh    w9, [x22, x26, lsl #1]
     +0x328: mov     x26, x10
     +0x32c: cmp     x26, #0xff
     +0x330: b.hi    <mlkem_poly_rej_uniform_x4+0x358>
     +0x334: add     x9, x8, #0x3
     +0x338: add     x8, x8, #0x3
     +0x33c: cmp     x9, #0xa6
     +0x340: b.cc    <mlkem_poly_rej_uniform_x4+0x2e0>
     +0x344: b       <mlkem_poly_rej_uniform_x4+0x358>
     +0x348: ldr     x15, [sp, #24]
     +0x34c: mov     w14, w19
     +0x350: mov     x19, x20
     +0x354: mov     x20, x21
     +0x358: ldr     w8, [sp, #60]
     +0x35c: tbz     w8, #0, <mlkem_poly_rej_uniform_x4+0x3c8>
     +0x360: mov     x8, xzr
     +0x364: add     x9, x24, x8
     +0x368: ldrb    w11, [x9, #512]
     +0x36c: ldrb    w10, [x9, #513]
     +0x370: bfi     w11, w10, #8, #4
     +0x374: cmp     w11, #0xd00
     +0x378: b.hi    <mlkem_poly_rej_uniform_x4+0x388>
     +0x37c: add     x12, x27, #0x1
     +0x380: strh    w11, [x15, x27, lsl #1]
     +0x384: mov     x27, x12
     +0x388: cmp     x27, #0xff
     +0x38c: b.hi    <mlkem_poly_rej_uniform_x4+0x3b0>
     +0x390: ldrb    w9, [x9, #514]
     +0x394: lsr     w10, w10, #4
     +0x398: orr     w9, w10, w9, lsl #4
     +0x39c: cmp     w9, #0xd00
     +0x3a0: b.hi    <mlkem_poly_rej_uniform_x4+0x3b0>
     +0x3a4: add     x10, x27, #0x1
     +0x3a8: strh    w9, [x15, x27, lsl #1]
     +0x3ac: mov     x27, x10
     +0x3b0: cmp     x27, #0xff
     +0x3b4: b.hi    <mlkem_poly_rej_uniform_x4+0x3c8>
     +0x3b8: add     x9, x8, #0x3
     +0x3bc: add     x8, x8, #0x3
     +0x3c0: cmp     x9, #0xa6
     +0x3c4: b.cc    <mlkem_poly_rej_uniform_x4+0x364>
     +0x3c8: tbz     w14, #0, <mlkem_poly_rej_uniform_x4+0x434>
     +0x3cc: mov     x8, xzr
     +0x3d0: add     x9, x24, x8
     +0x3d4: ldrb    w11, [x9, #1024]
     +0x3d8: ldrb    w10, [x9, #1025]
     +0x3dc: bfi     w11, w10, #8, #4
     +0x3e0: cmp     w11, #0xd00
     +0x3e4: b.hi    <mlkem_poly_rej_uniform_x4+0x3f4>
     +0x3e8: add     x12, x28, #0x1
     +0x3ec: strh    w11, [x20, x28, lsl #1]
     +0x3f0: mov     x28, x12
     +0x3f4: cmp     x28, #0xff
     +0x3f8: b.hi    <mlkem_poly_rej_uniform_x4+0x41c>
     +0x3fc: ldrb    w9, [x9, #1026]
     +0x400: lsr     w10, w10, #4
     +0x404: orr     w9, w10, w9, lsl #4
     +0x408: cmp     w9, #0xd00
     +0x40c: b.hi    <mlkem_poly_rej_uniform_x4+0x41c>
     +0x410: add     x10, x28, #0x1
     +0x414: strh    w9, [x20, x28, lsl #1]
     +0x418: mov     x28, x10
     +0x41c: cmp     x28, #0xff
     +0x420: b.hi    <mlkem_poly_rej_uniform_x4+0x434>
     +0x424: add     x9, x8, #0x3
     +0x428: add     x8, x8, #0x3
     +0x42c: cmp     x9, #0xa6
     +0x430: b.cc    <mlkem_poly_rej_uniform_x4+0x3d0>
     +0x434: tbz     w25, #0, <mlkem_poly_rej_uniform_x4+0x4a0>
     +0x438: mov     x8, xzr
     +0x43c: add     x9, x24, x8
     +0x440: ldrb    w11, [x9, #1536]
     +0x444: ldrb    w10, [x9, #1537]
     +0x448: bfi     w11, w10, #8, #4
     +0x44c: cmp     w11, #0xd00
     +0x450: b.hi    <mlkem_poly_rej_uniform_x4+0x460>
     +0x454: add     x12, x23, #0x1
     +0x458: strh    w11, [x19, x23, lsl #1]
     +0x45c: mov     x23, x12
     +0x460: cmp     x23, #0xff
     +0x464: b.hi    <mlkem_poly_rej_uniform_x4+0x488>
     +0x468: ldrb    w9, [x9, #1538]
     +0x46c: lsr     w10, w10, #4
     +0x470: orr     w9, w10, w9, lsl #4
     +0x474: cmp     w9, #0xd00
     +0x478: b.hi    <mlkem_poly_rej_uniform_x4+0x488>
     +0x47c: add     x10, x23, #0x1
     +0x480: strh    w9, [x19, x23, lsl #1]
     +0x484: mov     x23, x10
     +0x488: cmp     x23, #0xff
     +0x48c: b.hi    <mlkem_poly_rej_uniform_x4+0x4a0>
     +0x490: add     x9, x8, #0x3
     +0x494: add     x8, x8, #0x3
     +0x498: cmp     x9, #0xa6
     +0x49c: b.cc    <mlkem_poly_rej_uniform_x4+0x43c>
     +0x4a0: cmp     x27, #0x100
     +0x4a4: cset    w15, cc
     +0x4a8: cmp     x28, #0x100
     +0x4ac: cset    w14, cc
     +0x4b0: cmp     x23, #0x100
     +0x4b4: cset    w25, cc
     +0x4b8: cmp     x26, #0x100
     +0x4bc: cset    w16, cc
     +0x4c0: b.cc    <mlkem_poly_rej_uniform_x4+0x29c>
     +0x4c4: cmp     x27, #0x100
     +0x4c8: b.cc    <mlkem_poly_rej_uniform_x4+0x29c>
     +0x4cc: cmp     x28, #0x100
     +0x4d0: b.cc    <mlkem_poly_rej_uniform_x4+0x29c>
     +0x4d4: cmp     x23, #0x100
     +0x4d8: b.cc    <mlkem_poly_rej_uniform_x4+0x29c>
     +0x4dc: add     x0, sp, #0x40
     +0x4e0: bl      <mlkem_shake128x4_release>
     +0x4e4: add     x0, sp, #0x360
     +0x4e8: mov     w1, wzr
     +0x4ec: mov     w2, #0x800
     +0x4f0: add     x19, sp, #0x360
     +0x4f4: bl      <memset@plt>
     +0x4f8: adrp    x8, <page>
     +0x4fc: ldr     x8, [x8, #4088]  // got_stack_chk_guard
     +0x500: ldr     x9, [sp, #2936]
     +0x504: ldr     x8, [x8]
     +0x508: cmp     x8, x9
     +0x50c: b.ne    <mlkem_poly_rej_uniform_x4+0x530>
     +0x510: mov     sp, x29
     +0x514: ldp     x20, x19, [sp, #80]
     +0x518: ldp     x22, x21, [sp, #64]
     +0x51c: ldp     x24, x23, [sp, #48]
     +0x520: ldp     x26, x25, [sp, #32]
     +0x524: ldp     x28, x27, [sp, #16]
     +0x528: ldp     x29, x30, [sp], #96
     +0x52c: ret     
     +0x530: bl      <__stack_chk_fail@plt>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]  // got_memset
       +0x8: add     x16, x16, #0xfe8  // got_memset
       +0xc: br      x17
 ***)

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_rej_uniform_x4"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* The eight copies of the sampling loop. The four buffers of three blocks   *)
(* are 512 bytes apart from the address in X23 (loop1) or X9 (loop2 to       *)
(* loop4), and the buffers of one block likewise from the address in X24.    *)
(* Each copy of polynomial k uses X8 as the index and the same counter for   *)
(* both kinds of loop. The first four also set a register to 1 or 0          *)
(* according as the counter is below 256 or not, which loop5 uses to decide  *)
(* whether to sample polynomial k from its first further block. Only loop6   *)
(* has two exits.                                                            *)
(* ------------------------------------------------------------------------- *)

let rejx4_loop k base ofs out ctr fields flag regs full en buflen =
  { rej_exec = MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O3_EXEC;
    rej_header = "mlkem_poly_rej_uniform_x4_loop" ^ string_of_int k;
    rej_full = "mlkem_poly_rej_uniform_x4_loop" ^ string_of_int k ^ full;
    rej_end = "mlkem_poly_rej_uniform_x4_loop" ^ string_of_int k ^ en;
    rej_base = base; rej_ofs = ofs; rej_idx = "X8"; rej_buflen = buflen;
    rej_ctr = ctr; rej_out = out; rej_fields = fields; rej_flag = flag;
    rej_regs = regs };;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O3_LOOPS =
  [rejx4_loop 1 "X23" 0 "X22" "X26" ("X11","X9") (Some "X16")
    ["X8"; "X9"; "X10"; "X11"; "X12"; "X16"; "X26"] "_exit" "_exit" 504;
   rejx4_loop 2 "X9" 512 "X21" "X27" ("X12","X10") (Some "X15")
    ["X8"; "X10"; "X11"; "X12"; "X13"; "X15"; "X27"] "_exit" "_exit" 504;
   rejx4_loop 3 "X9" 1024 "X20" "X28" ("X12","X10") (Some "X14")
    ["X8"; "X10"; "X11"; "X12"; "X13"; "X14"; "X28"] "_exit" "_exit" 504;
   rejx4_loop 4 "X9" 1536 "X19" "X23" ("X12","X10") (Some "X25")
    ["X8"; "X10"; "X11"; "X12"; "X13"; "X23"; "X25"] "_exit" "_exit" 504;
   rejx4_loop 6 "X24" 0 "X22" "X26" ("X11","X9") None
    ["X8"; "X9"; "X10"; "X11"; "X12"; "X26"] "_exit2" "_exit1" 168;
   rejx4_loop 7 "X24" 512 "X15" "X27" ("X11","X9") None
    ["X8"; "X9"; "X10"; "X11"; "X12"; "X27"] "_exit" "_exit" 168;
   rejx4_loop 8 "X24" 1024 "X20" "X28" ("X11","X9") None
    ["X8"; "X9"; "X10"; "X11"; "X12"; "X28"] "_exit" "_exit" 168;
   rejx4_loop 9 "X24" 1536 "X19" "X23" ("X11","X9") None
    ["X8"; "X9"; "X10"; "X11"; "X12"; "X23"] "_exit" "_exit" 168];;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O3_LOOPS_FULL =
  map REJ_LOOP_FULL MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O3_LOOPS;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O3_LOOPS_CORRECT =
  map2 REJ_LOOP_CORRECT MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O3_LOOPS
   MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_CLANG17_O3_LOOPS_FULL;;
