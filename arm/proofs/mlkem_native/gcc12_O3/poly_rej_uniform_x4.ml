(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of four polynomials from four seeds by rejection. This   *)
(* is the code for mlkem_poly_rej_uniform_x4 from mlkem-native's portable C  *)
(* implementation compiled by gcc 12 with -O3 (see mlkem_native/README.md),  *)
(* which absorbs the four seeds of 34 bytes, 64 bytes apart, into a fourfold *)
(* SHAKE128 state, squeezes three blocks of 168 bytes of each and samples    *)
(* the coefficients below 3329 from them, and then squeezes one more block   *)
(* of each and samples from those polynomials that have fewer than 256       *)
(* coefficients until each has 256, before zeroing the state and the         *)
(* buffers. Unlike at -O2, the sampling of mlk_rej_uniform_c is inlined, as  *)
(* eight copies of its loop: loop1 to loop4 for the first three blocks of    *)
(* each polynomial, and loop6 to loop9 for each further block, inside the    *)
(* loop loop5 that squeezes the blocks. The code is in the whole image (see  *)
(* libmlkem.ml), and the eight copies of the loop are verified there with    *)
(* the tool in rej_uniform.ml.                                               *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O3/rej_uniform.ml";;

(*** The code in the image:

    mlkem_poly_rej_uniform_x4:
       +0x0: sub     sp, sp, #0xbd0
       +0x4: add     x6, sp, #0xaf
       +0x8: adrp    x5, <page>
       +0xc: ldr     x5, [x5, #4088]  // got_stack_chk_guard
      +0x10: stp     x21, x22, [sp, #16]
      +0x14: and     x22, x6, #0xffffffffffffffe0
      +0x18: add     x6, x22, #0x800
      +0x1c: stp     x19, x20, [sp]
      +0x20: mov     x20, x1
      +0x24: stp     x23, x24, [sp, #32]
      +0x28: mov     x19, x4
      +0x2c: mov     x23, x6
      +0x30: stp     x25, x26, [sp, #48]
      +0x34: mov     x21, x2
      +0x38: add     x24, x22, #0x600
      +0x3c: stp     x27, x28, [sp, #64]
      +0x40: mov     x28, x0
      +0x44: mov     x0, x6
      +0x48: str     x30, [sp, #80]
      +0x4c: mov     w25, #0x0
      +0x50: str     x3, [sp, #104]
      +0x54: str     x6, [sp, #136]
      +0x58: ldr     x1, [x5]
      +0x5c: str     x1, [sp, #3016]
      +0x60: mov     x1, #0x0
      +0x64: bl      mlkem_shake128x4_init
      +0x68: add     x4, x19, #0xc0
      +0x6c: add     x3, x19, #0x80
      +0x70: add     x2, x19, #0x40
      +0x74: mov     x1, x19
      +0x78: mov     x0, x23
      +0x7c: add     x19, x22, #0x400
      +0x80: mov     x5, #0x22
      +0x84: stp     x19, x24, [sp, #112]
      +0x88: bl      mlkem_shake128x4_absorb_once
      +0x8c: add     x0, x22, #0x200
      +0x90: mov     x5, x23
      +0x94: mov     x1, x0
      +0x98: mov     x3, x24
      +0x9c: mov     x2, x19
      +0xa0: mov     x4, #0x3
      +0xa4: str     x0, [sp, #128]
      +0xa8: mov     x0, x22
      +0xac: bl      mlkem_shake128x4_squeezeblocks
      +0xb0: ldr     x8, [sp, #104]
      +0xb4: add     x10, x22, #0x1f8
      +0xb8: mov     x1, x22
      +0xbc: mov     w5, #0xd00
      +0xc0: b       loop1
      +0xc4: cmp     w25, #0xff
      +0xc8: ccmp    w2, w5, #0x0, ls
      +0xcc: b.gt    join2
      +0xd0: mov     w3, w25
      +0xd4: add     w25, w3, #0x1
      +0xd8: strh    w2, [x28, w3, uxtw #1]
      +0xdc: cmp     w25, #0x100
      +0xe0: b.eq    join3
      +0xe4: add     x1, x1, #0x3
      +0xe8: cmp     x1, x10
      +0xec: b.eq    join3
      +0xf0: ldrb    w0, [x1, #1]
      +0xf4: ldrb    w4, [x1]
      +0xf8: ldrb    w2, [x1, #2]
      +0xfc: lsr     w3, w0, #4
     +0x100: orr     w0, w4, w0, lsl #8
     +0x104: and     w0, w0, #0xfff
     +0x108: orr     w2, w3, w2, lsl #4
     +0x10c: cmp     w0, #0xd00
     +0x110: b.gt    +0xc4
     +0x114: add     w3, w25, #0x1
     +0x118: strh    w0, [x28, w25, uxtw #1]
     +0x11c: cmp     w3, #0xff
     +0x120: mov     w25, w3
     +0x124: ccmp    w2, w5, #0x0, ls
     +0x128: b.le    join1
     +0x12c: cmp     w25, #0x100
     +0x130: b.ne    join2
     +0x134: ldr     x1, [sp, #128]
     +0x138: add     x10, x22, #0x3f8
     +0x13c: mov     w26, #0x0
     +0x140: mov     w5, #0xd00
     +0x144: b       loop2
     +0x148: cmp     w26, #0xff
     +0x14c: ccmp    w2, w5, #0x0, ls
     +0x150: b.gt    join5
     +0x154: mov     w3, w26
     +0x158: add     w26, w3, #0x1
     +0x15c: strh    w2, [x20, w3, uxtw #1]
     +0x160: cmp     w26, #0x100
     +0x164: b.eq    join6
     +0x168: add     x1, x1, #0x3
     +0x16c: cmp     x1, x10
     +0x170: b.eq    join6
     +0x174: ldrb    w0, [x1, #1]
     +0x178: ldrb    w4, [x1]
     +0x17c: ldrb    w2, [x1, #2]
     +0x180: lsr     w3, w0, #4
     +0x184: orr     w0, w4, w0, lsl #8
     +0x188: and     w0, w0, #0xfff
     +0x18c: orr     w2, w3, w2, lsl #4
     +0x190: cmp     w0, #0xd00
     +0x194: b.gt    +0x148
     +0x198: add     w3, w26, #0x1
     +0x19c: strh    w0, [x20, w26, uxtw #1]
     +0x1a0: cmp     w3, #0xff
     +0x1a4: mov     w26, w3
     +0x1a8: ccmp    w2, w5, #0x0, ls
     +0x1ac: b.le    join4
     +0x1b0: cmp     w26, #0x100
     +0x1b4: b.ne    join5
     +0x1b8: ldr     x1, [sp, #112]
     +0x1bc: add     x10, x22, #0x5f8
     +0x1c0: mov     w24, #0x0
     +0x1c4: mov     w5, #0xd00
     +0x1c8: b       loop3
     +0x1cc: cmp     w24, #0xff
     +0x1d0: ccmp    w2, w5, #0x0, ls
     +0x1d4: b.gt    join8
     +0x1d8: mov     w3, w24
     +0x1dc: add     w24, w3, #0x1
     +0x1e0: strh    w2, [x21, w3, uxtw #1]
     +0x1e4: cmp     w24, #0x100
     +0x1e8: b.eq    join9
     +0x1ec: add     x1, x1, #0x3
     +0x1f0: cmp     x1, x10
     +0x1f4: b.eq    join9
     +0x1f8: ldrb    w0, [x1, #1]
     +0x1fc: ldrb    w4, [x1]
     +0x200: ldrb    w2, [x1, #2]
     +0x204: lsr     w3, w0, #4
     +0x208: orr     w0, w4, w0, lsl #8
     +0x20c: and     w0, w0, #0xfff
     +0x210: orr     w2, w3, w2, lsl #4
     +0x214: cmp     w0, #0xd00
     +0x218: b.gt    +0x1cc
     +0x21c: add     w3, w24, #0x1
     +0x220: strh    w0, [x21, w24, uxtw #1]
     +0x224: cmp     w3, #0xff
     +0x228: mov     w24, w3
     +0x22c: ccmp    w2, w5, #0x0, ls
     +0x230: b.le    join7
     +0x234: cmp     w24, #0x100
     +0x238: b.ne    join8
     +0x23c: ldr     x1, [sp, #120]
     +0x240: add     x10, x22, #0x7f8
     +0x244: mov     w23, #0x0
     +0x248: mov     w5, #0xd00
     +0x24c: b       loop4
     +0x250: cmp     w23, #0xff
     +0x254: ccmp    w2, w5, #0x0, ls
     +0x258: b.gt    join11
     +0x25c: mov     w3, w23
     +0x260: add     w23, w3, #0x1
     +0x264: strh    w2, [x8, w3, uxtw #1]
     +0x268: cmp     w23, #0x100
     +0x26c: b.eq    join12
     +0x270: add     x1, x1, #0x3
     +0x274: cmp     x1, x10
     +0x278: b.eq    join13
     +0x27c: ldrb    w0, [x1, #1]
     +0x280: ldrb    w4, [x1]
     +0x284: ldrb    w2, [x1, #2]
     +0x288: lsr     w3, w0, #4
     +0x28c: orr     w0, w4, w0, lsl #8
     +0x290: and     w0, w0, #0xfff
     +0x294: orr     w2, w3, w2, lsl #4
     +0x298: cmp     w0, #0xd00
     +0x29c: b.gt    +0x250
     +0x2a0: add     w3, w23, #0x1
     +0x2a4: strh    w0, [x8, w23, uxtw #1]
     +0x2a8: cmp     w3, #0xff
     +0x2ac: mov     w23, w3
     +0x2b0: ccmp    w2, w5, #0x0, ls
     +0x2b4: b.le    join10
     +0x2b8: cmp     w23, #0x100
     +0x2bc: b.ne    join11
     +0x2c0: cmp     w25, #0xff
     +0x2c4: mov     w0, #0xff
     +0x2c8: ccmp    w26, w0, #0x0, hi
     +0x2cc: ccmp    w24, w0, #0x0, hi
     +0x2d0: b.hi    join27
     +0x2d4: mov     w27, #0xd00
     +0x2d8: mov     w19, #0xff
     +0x2dc: nop
     +0x2e0: ldp     x2, x3, [sp, #112]
     +0x2e4: mov     x0, x22
     +0x2e8: ldp     x1, x5, [sp, #128]
     +0x2ec: mov     x4, #0x1
     +0x2f0: str     x8, [sp, #104]
     +0x2f4: bl      mlkem_shake128x4_squeezeblocks
     +0x2f8: ldr     x8, [sp, #104]
     +0x2fc: cmp     w25, #0xff
     +0x300: b.hi    join16
     +0x304: add     x5, x22, #0xa8
     +0x308: mov     x1, x22
     +0x30c: b       loop6
     +0x310: cmp     w2, #0xd00
     +0x314: ccmp    w25, w19, #0x2, le
     +0x318: b.hi    join15
     +0x31c: mov     w3, w25
     +0x320: add     w25, w3, #0x1
     +0x324: strh    w2, [x28, w3, uxtw #1]
     +0x328: cmp     w25, #0x100
     +0x32c: b.eq    join16
     +0x330: add     x1, x1, #0x3
     +0x334: cmp     x1, x5
     +0x338: b.eq    join16
     +0x33c: ldrb    w0, [x1, #1]
     +0x340: ldrb    w4, [x1]
     +0x344: ldrb    w2, [x1, #2]
     +0x348: lsr     w3, w0, #4
     +0x34c: orr     w0, w4, w0, lsl #8
     +0x350: and     w0, w0, #0xfff
     +0x354: orr     w2, w3, w2, lsl #4
     +0x358: cmp     w0, #0xd00
     +0x35c: b.gt    +0x310
     +0x360: add     w3, w25, #0x1
     +0x364: strh    w0, [x28, w25, uxtw #1]
     +0x368: cmp     w3, #0xff
     +0x36c: mov     w25, w3
     +0x370: ccmp    w2, w27, #0x0, ls
     +0x374: b.le    join14
     +0x378: cmp     w25, #0x100
     +0x37c: b.ne    join15
     +0x380: cmp     w26, #0xff
     +0x384: b.hi    join19
     +0x388: ldr     x1, [sp, #128]
     +0x38c: add     x5, x22, #0x2a8
     +0x390: b       loop7
     +0x394: cmp     w26, #0xff
     +0x398: ccmp    w2, w27, #0x0, ls
     +0x39c: b.gt    join18
     +0x3a0: mov     w3, w26
     +0x3a4: add     w26, w3, #0x1
     +0x3a8: strh    w2, [x20, w3, uxtw #1]
     +0x3ac: cmp     w26, #0x100
     +0x3b0: b.eq    join19
     +0x3b4: add     x1, x1, #0x3
     +0x3b8: cmp     x1, x5
     +0x3bc: b.eq    join19
     +0x3c0: ldrb    w0, [x1, #1]
     +0x3c4: ldrb    w4, [x1]
     +0x3c8: ldrb    w2, [x1, #2]
     +0x3cc: lsr     w3, w0, #4
     +0x3d0: orr     w0, w4, w0, lsl #8
     +0x3d4: and     w0, w0, #0xfff
     +0x3d8: orr     w2, w3, w2, lsl #4
     +0x3dc: cmp     w0, #0xd00
     +0x3e0: b.gt    +0x394
     +0x3e4: add     w3, w26, #0x1
     +0x3e8: strh    w0, [x20, w26, uxtw #1]
     +0x3ec: cmp     w3, #0xff
     +0x3f0: mov     w26, w3
     +0x3f4: ccmp    w2, w27, #0x0, ls
     +0x3f8: b.le    join17
     +0x3fc: cmp     w26, #0x100
     +0x400: b.ne    join18
     +0x404: nop
     +0x408: cmp     w24, #0xff
     +0x40c: b.hi    join22
     +0x410: ldr     x1, [sp, #112]
     +0x414: add     x5, x22, #0x4a8
     +0x418: b       loop8
     +0x41c: cmp     w24, #0xff
     +0x420: ccmp    w2, w27, #0x0, ls
     +0x424: b.gt    join21
     +0x428: mov     w3, w24
     +0x42c: add     w24, w3, #0x1
     +0x430: strh    w2, [x21, w3, uxtw #1]
     +0x434: cmp     w24, #0x100
     +0x438: b.eq    join22
     +0x43c: add     x1, x1, #0x3
     +0x440: cmp     x1, x5
     +0x444: b.eq    loop8_exit2
     +0x448: ldrb    w0, [x1, #1]
     +0x44c: ldrb    w4, [x1]
     +0x450: ldrb    w2, [x1, #2]
     +0x454: lsr     w3, w0, #4
     +0x458: orr     w0, w4, w0, lsl #8
     +0x45c: and     w0, w0, #0xfff
     +0x460: orr     w2, w3, w2, lsl #4
     +0x464: cmp     w0, #0xd00
     +0x468: b.gt    +0x41c
     +0x46c: add     w3, w24, #0x1
     +0x470: strh    w0, [x21, w24, uxtw #1]
     +0x474: cmp     w3, #0xff
     +0x478: mov     w24, w3
     +0x47c: ccmp    w2, w27, #0x0, ls
     +0x480: b.le    join20
     +0x484: cmp     w24, #0x100
     +0x488: b.ne    join21
     +0x48c: cmp     w23, #0xff
     +0x490: b.hi    join26
     +0x494: ldr     x1, [sp, #120]
     +0x498: add     x5, x22, #0x6a8
     +0x49c: b       loop9
     +0x4a0: add     x1, x1, #0x3
     +0x4a4: cmp     x1, x5
     +0x4a8: b.eq    loop5
     +0x4ac: ldrb    w0, [x1, #1]
     +0x4b0: ldrb    w4, [x1]
     +0x4b4: ldrb    w2, [x1, #2]
     +0x4b8: lsr     w3, w0, #4
     +0x4bc: orr     w0, w4, w0, lsl #8
     +0x4c0: and     w0, w0, #0xfff
     +0x4c4: orr     w2, w3, w2, lsl #4
     +0x4c8: cmp     w0, #0xd00
     +0x4cc: b.gt    join24
     +0x4d0: strh    w0, [x8, w23, uxtw #1]
     +0x4d4: add     w23, w23, #0x1
     +0x4d8: cmp     w23, #0xff
     +0x4dc: ccmp    w2, w27, #0x0, ls
     +0x4e0: b.gt    join25
     +0x4e4: strh    w2, [x8, w23, uxtw #1]
     +0x4e8: add     w23, w23, #0x1
     +0x4ec: cmp     w23, #0x100
     +0x4f0: b.ne    +0x4a0
     +0x4f4: cmp     w26, #0xff
     +0x4f8: ccmp    w25, w19, #0x0, hi
     +0x4fc: ccmp    w24, w19, #0x0, hi
     +0x500: b.ls    loop5
     +0x504: ldr     x0, [sp, #136]
     +0x508: bl      mlkem_shake128x4_release
     +0x50c: mov     x0, x22
     +0x510: mov     x2, #0x800
     +0x514: mov     w1, #0x0
     +0x518: bl      memset
     +0x51c: adrp    x0, <page>
     +0x520: ldr     x0, [x0, #4088]  // got_stack_chk_guard
     +0x524: ldr     x2, [sp, #3016]
     +0x528: ldr     x1, [x0]
     +0x52c: subs    x2, x2, x1
     +0x530: mov     x1, #0x0
     +0x534: b.ne    +0x564
     +0x538: ldp     x19, x20, [sp]
     +0x53c: ldp     x21, x22, [sp, #16]
     +0x540: ldp     x23, x24, [sp, #32]
     +0x544: ldp     x25, x26, [sp, #48]
     +0x548: ldp     x27, x28, [sp, #64]
     +0x54c: ldr     x30, [sp, #80]
     +0x550: add     sp, sp, #0xbd0
     +0x554: ret
     +0x558: cmp     w23, #0xff
     +0x55c: b.ls    join23
     +0x560: b       loop5
     +0x564: bl      stack_chk_fail
 ***)

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_poly_rej_uniform_x4"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* The eight copies of the sampling loop, with X1 as the pointer, the        *)
(* fields in X0 and X2, and the counter in X25, X26, X24 and X23 and the     *)
(* output in X28, X20, X21 and X8 for the four polynomials. The copies for   *)
(* the first three blocks have the end of the buffer in X10 and 3328 in X5,  *)
(* those for further blocks the end in X5 and 3328 in X27, and loop6 has     *)
(* 255 in X19. Each exit is given by its label in the function, the first    *)
(* when there are 256 coefficients and the second at the end of the buffer.  *)
(* ------------------------------------------------------------------------- *)

let rejx4_loop k ctr out endreg consts full en =
  let f s = "mlkem_poly_rej_uniform_x4_" ^ s in
  { rej_exec = MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC;
    rej_header = f ("loop" ^ string_of_int k);
    rej_full = f full;
    rej_end = f en;
    rej_ptr = "X1"; rej_endreg = endreg; rej_ctr = ctr; rej_out = out;
    rej_consts = consts;
    rej_fields = "X0","X2";
    rej_regs = ["X0"; "X1"; "X2"; "X3"; "X4"; ctr] };;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_LOOPS =
  [rejx4_loop 1 "X25" "X28" "X10" ["X5",3328] "loop1_exit" "loop1_exit";
   rejx4_loop 2 "X26" "X20" "X10" ["X5",3328] "loop2_exit" "loop2_exit";
   rejx4_loop 3 "X24" "X21" "X10" ["X5",3328] "loop3_exit" "loop3_exit";
   rejx4_loop 4 "X23" "X8" "X10" ["X5",3328] "loop4_exit1" "loop4_exit2";
   rejx4_loop 6 "X25" "X28" "X5" ["X19",255; "X27",3328]
     "loop6_exit" "loop6_exit";
   rejx4_loop 7 "X26" "X20" "X5" ["X27",3328] "loop7_exit2" "loop7_exit2";
   rejx4_loop 8 "X24" "X21" "X5" ["X27",3328] "loop8_exit1" "loop8_exit2";
   rejx4_loop 9 "X23" "X8" "X5" ["X27",3328] "loop9_exit2" "loop9_exit1"];;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_LOOPS_FULL =
  map REJ_LOOP_FULL MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_LOOPS;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_LOOPS_CORRECT =
  map2 REJ_LOOP_CORRECT MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_LOOPS
   MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_LOOPS_FULL;;
