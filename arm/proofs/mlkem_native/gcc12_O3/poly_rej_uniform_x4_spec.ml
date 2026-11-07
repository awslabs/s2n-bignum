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
(* loop loop5 that squeezes the blocks. It is verified in the whole image    *)
(* (see libmlkem.ml), using the theorems for mlkem_shake128x4_init,          *)
(* mlkem_shake128x4_absorb_once, mlkem_shake128x4_squeezeblocks and          *)
(* mlkem_shake128x4_release in the image, the theorems for the eight copies  *)
(* of the loop proved here with the tool in rej_uniform.ml, and assuming the *)
(* contracts for memset in utils/mlkem_native_libc.ml.                       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/poly_rej_uniform_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/shake128x4_init_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/shake128x4_absorb_once_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/shake128x4_squeezeblocks_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/shake128x4_release_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/rej_uniform_spec.ml";;

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
  assuming_proofs (fun () ->
  map REJ_LOOP_FULL MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_LOOPS);;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_LOOPS_CORRECT =
  assuming_proofs (fun () ->
  map2 REJ_LOOP_CORRECT MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_LOOPS
   MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_LOOPS_FULL);;

(* ------------------------------------------------------------------------- *)
(* The samples from one more block, whatever the number of samples so far:   *)
(* if there are already 256, they are the same. The tests of whether there   *)
(* are 256 samples compare the numbers of samples with 255 as 32-bit words,  *)
(* using conditional comparisons (ccmp) to combine the tests for three       *)
(* polynomials.                                                              *)
(* ------------------------------------------------------------------------- *)

let REJX4_SAMPLE_SUC_STMT =
  `!(f:num->byte) j.
        SUB_LIST(0,256)
         (REJ_SAMPLE(wordlist_of_num (336 + 112 * (j + 1))
            (num_of_bytelist(list_of_seq f (504 + 168 * (j + 1)))))) =
        APPEND
         (SUB_LIST(0,256)
           (REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
              (num_of_bytelist(list_of_seq f (504 + 168 * j))))))
         (SUB_LIST(0,256 -
                   MIN 256 (LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                     (num_of_bytelist(list_of_seq f (504 + 168 * j)))))))
           (REJ_SAMPLE(wordlist_of_num 112
              (num_of_bytelist
                (list_of_seq (\i. f((504 + 168 * j) + i)) 168)))))`;;

let REJX4_SAMPLE_SUC = assume_spec REJX4_SAMPLE_SUC_STMT;;

let REJX4_CMP_STMT =
  `!c. c < 2 EXP 32
       ==> val(word_zx(word c:int64):int32) = c /\
           (&c - &255:int =
            &(val(word_sub (word_zx (word c:int64):int32) (word 255))) <=>
            255 <= c) /\
           (val(word_sub (word_zx (word c:int64):int32) (word 255)) = 0 <=>
            c = 255)`;;

let REJX4_CMP = assume_spec REJX4_CMP_STMT;;

(*** A test of the numbers of samples ns, at most 256, against 255 ***)

let REJX4_TEST_PROVE_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  W(fun (asl,w) ->
    let vs = filter (fun v -> fst(dest_var v) <> "" &&
                              String.sub (fst(dest_var v)) 0 1 = "n")
                    (frees w) in
    SUBGOAL_THEN (list_mk_conj
       (map (fun v -> mk_binop `(<):num->num->bool` v `2 EXP 32`) vs))
     STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ALL_TAC]) THEN
  ASM_SIMP_TAC[REJX4_CMP] THEN
  REWRITE_TAC[TAUT `(if a then b else F) <=> a /\ b`;
              ARITH_RULE `255 <= n /\ ~(n = 255) <=> 255 < n`] THEN
  REPEAT COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV THEN ASM_ARITH_TAC;;

let REJX4_TEST_TAC cs =
  let vs = map (fun i -> mk_var("n"^string_of_int i,`:num`))
               (0--(length cs - 1)) in
  let ant = list_mk_conj
             (map (fun v -> mk_binop `(<=):num->num->bool` v `256`) vs)
  and res = list_mk_conj
             (map (fun v -> mk_binop `(<):num->num->bool` `255` v) vs) in
  let bth = end_itlist CONJ
             (map (fun c -> if is_comb c && rator c = `MIN 256`
                            then SPECL [`256`; rand c]
                                   (ARITH_RULE `!a b. MIN a b <= a`)
                            else ARITH_RULE(mk_binop `(<=):num->num->bool`
                                              c `256`)) cs) in
  FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),_)),
           Comb(Comb(Comb(Const("COND",_),c),_),_)) when free_in (hd cs) c ->
        let res' = if is_neg c then mk_neg res else res in
        let lth = prove(list_mk_forall(vs,mk_imp(ant,mk_eq(subst(zip vs cs) c,
                                                          res'))),
                        REJX4_TEST_PROVE_TAC) in
        ASSUME_TAC(REWRITE_RULE[MP (SPECL cs lth) bth;
                                ARITH_RULE `255 < MIN 256 x <=> 256 <= x`;
                                ARITH_RULE `255 < 256`] th)
    | _ -> NO_TAC);;

(*** The counts in the registers given, for the tests ***)

let REJX4_COUNTS_IN regs (asl,w) =
  let s = rand w in
  map (fun r ->
    let th = snd(find (fun (_,th) ->
      try lhs(concl th) = list_mk_comb(`read:(armstate,int64)component->
                                              armstate->int64`,[r;s])
      with Failure _ -> false) asl) in
    rand(rhs(concl th))) regs;;

let REJX4_TESTREGS_TAC regs =
  W(fun g ->
    (*** The tests of numerals (256 for a polynomial skipped) are done ***)
    (*** by the simulation                                            ***)
    match filter (not o is_numeral) (REJX4_COUNTS_IN regs g) with
      [] -> ALL_TAC
    | cs -> REJX4_TEST_TAC cs);;

(* ------------------------------------------------------------------------- *)
(* The four buffers of 512 bytes for three blocks each, followed by the four *)
(* states, are aligned to 32 bytes within the stack frame, so their          *)
(* addresses depend on whether the stack pointer is a multiple of 32 or just *)
(* of 16. The frame is 3024 bytes, 16 more than at -O2, the stack used by    *)
(* mlkem_shake128x4_absorb_once 288 rather than 304, and the buffers are 175 *)
(* bytes up from the stack pointer rounded down rather than 159, so they are *)
(* where they are at -O2. They are in the form given by                      *)
(* NORMALIZE_RELATIVE_ADDRESS_CONV, as in the preconditions of the calls.    *)
(* ------------------------------------------------------------------------- *)

let REJX4_BUFFER_ADDRESS_STMT =
  `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 463)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 448 else 432))`;;

let REJX4_BUFFER_ADDRESS = assume_spec REJX4_BUFFER_ADDRESS_STMT;;

let REJX4_BUFFER_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 463))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 448 else 432))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC REJX4_BUFFER_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let REJX4_NORMALIZE_TAC =
  RULE_ASSUM_TAC(fun th ->
    if free_in `stackpointer:int64` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th
    else th);;

let REJX4_SP n =
  let b = `if aligned 32 (stackpointer:int64) then 448 else 432` in
  let off = if n = 0 then b
            else mk_binop `(+):num->num->num` b (mk_small_numeral n) in
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
          mk_comb(`word:num->int64`,off));;

let REJX4_BUF m = REJX4_SP(512 * m);;

let REJX4_ST m =
  let st = REJX4_SP 2048 in
  if m = 0 then st
  else rhs(concl(NORMALIZE_RELATIVE_ADDRESS_CONV
    (mk_comb(mk_comb(`word_add:int64->int64->int64`,st),
             mk_comb(`word:num->int64`,mk_small_numeral(200 * m))))));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, assuming the contract for memset as for                *)
(* mlkem_poly_rej_uniform. The seeds are 34 bytes at seed, seed + 64, seed + *)
(* 128 and seed + 192, given as lists of bytes inp0, ..., inp3. As for       *)
(* mlkem_poly_rej_uniform, the theorem has the hypothesis that for some k    *)
(* there are at least 256 samples among the 12-bit fields of the first 504 + *)
(* 168 * k bytes of shake128 of each seed, and the results are the first 256 *)
(* samples for each. loop5, squeezing one more block of each and sampling    *)
(* from it for those polynomials with fewer than 256 samples, stops when     *)
(* there are 256 samples for all four, so the proof uses the minimal such k, *)
(* k0, as the number of its iterations, and the numbers of samples in the    *)
(* invariant are at most 256. The stack is the 3024 bytes of the function    *)
(* and the 288 used by mlkem_shake128x4_absorb_once below them, 3312 bytes   *)
(* as at -O2.                                                                *)
(* ------------------------------------------------------------------------- *)

(*** The end of a buffer, given to a copy of the loop as buf + buflen, may ***)
(*** be computed by the code as an offset from the first buffer          ***)

let REJX4_ADDRESS_TAC =
  TRY(REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD; GSYM ADD_ASSOC] THEN
      CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REWRITE_TAC[] THEN NO_TAC);;

let REJX4_SIM_TAC th ilist n =
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,th) ilist n THEN
  REJX4_ADDRESS_TAC;;

let LOCAL_INIT_X4_TAC =
  REJX4_SIM_TAC MLKEM_NATIVE_SHAKE128X4_INIT_GCC12_O3_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_ABSORB_X4_TAC =
  REJX4_SIM_TAC
   MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_SQUEEZE_X4_TAC =
  REJX4_SIM_TAC
   MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O3_IMAGE_SUBROUTINE_CORRECT;;

let LOCAL_RELEASE_X4_TAC =
  REJX4_SIM_TAC
   MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT;;

(*** The copies of the loop, loop1 to loop4 and loop6 to loop9 ***)

let REJX4_LOOP_CORRECT k =
  el (if k <= 4 then k - 1 else k - 2)
     MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_LOOPS_CORRECT;;

let REJX4_LOOP_DATA k =
  el (if k <= 4 then k - 1 else k - 2)
     MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_LOOPS;;

(*** The setup, with bounds on the offset of the buffers ***)

let REJX4_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 3312):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `432 <= (if aligned 32 (stackpointer:int64) then 448 else 432) /\
    (if aligned 32 (stackpointer:int64) then 448 else 432) <= 448`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD;
                              SPECL [`pc:num`;
                                     `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun n ->
    let r = "X"^string_of_int n in
    ENSURES_PRESERVED_TAC ("x"^string_of_int n^"_init")
     (mk_const(r,[]))) (19--28);;

(*** The GOT entries in the form in the preconditions of the callees ***)

let REJX4_GOT_TAC =
  MAP_EVERY (fun n ->
    FIRST_ASSUM(fun th ->
      if can (term_match []
               (vsubst [mk_small_numeral n,`n:num`]
                 `read (memory :> bytes64
                         (word_add (word (pc:num)) (word n):int64)) s =
                  (g:int64)`)) (concl th)
      then ASSUME_TAC(REWRITE_RULE[GSYM WORD_ADD] th) else NO_TAC))
   [layout "got_stack_chk_guard"; layout "got_memset"];;

(*** The fields, samples and blocks for each seed ***)

let REJX4_INPS =
  [`inp0:byte list`; `inp1:byte list`; `inp2:byte list`; `inp3:byte list`]
and REJX4_VECS = [`vec0:int64`; `vec1:int64`; `vec2:int64`; `vec3:int64`]
and REJX4_SVS =
  [`S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`]
and REJX4_CTRS = [`X25`; `X26`; `X24`; `X23`]
and REJX4_OUTS = [`X28`; `X20`; `X21`; `X8`];;

let rejx4_fields inp j =
  vsubst [inp,`inp:byte list`; j,`j:num`]
   `wordlist_of_num (336 + 112 * j)
     (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * j))):
    (12 word)list`;;

let rejx4_fields0 inp =
  vsubst [inp,`inp:byte list`]
   `wordlist_of_num 336
     (num_of_bytelist(list_of_seq (shake128 inp) 504)):(12 word)list`;;

let rejx4_count inp j =
  mk_comb(`LENGTH:(16 word)list->num`,
          mk_comb(`REJ_SAMPLE`,rejx4_fields inp j));;

let rejx4_count0 inp =
  rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES] (rejx4_count inp `0`)));;

let rejx4_block inp i =
  vsubst [inp,`inp:byte list`; i,`i:num`]
   `wordlist_of_num 112
     (num_of_bytelist
       (list_of_seq (\j. shake128 inp ((504 + 168 * i) + j)) 168)):
    (12 word)list`;;

let rejx4_done m j =
  mk_binop `(<=):num->num->bool` `256` (rejx4_count (el m REJX4_INPS) j);;

let rejx4_done0 m =
  mk_binop `(<=):num->num->bool` `256` (rejx4_count0 (el m REJX4_INPS));;

(*** The absorbed states as S0, ..., S3, and the minimal number of blocks ***)

let REJX4_ABSORBED_TAC =
  MAP_EVERY (fun (inp,sv) ->
    let t = vsubst [inp,`inp:byte list`] REJ_ABSORBED in
    let len = ASSUME(mk_eq(mk_comb(`LENGTH:byte list->num`,inp),`34`)) in
    ABBREV_TAC(mk_eq(sv,t)) THEN
    ASSUME_TAC(REWRITE_RULE[len; ASSUME(mk_eq(t,sv))]
                (SPEC inp REJ_SPONGE)) THEN
    ASSUME_TAC(REWRITE_RULE[len; ASSUME(mk_eq(t,sv))]
                (SPEC inp REJ_SHAKE128_BLOCKS)))
   (zip REJX4_INPS REJX4_SVS);;

let REJX4_DONE n =
  list_mk_conj
   (map (fun inp -> mk_binop `(<=):num->num->bool` `256` (rejx4_count inp n))
        REJX4_INPS);;

let REJX4_MINIMAL_TAC =
  let p = mk_abs(`n:num`,REJX4_DONE `n:num`) in
  MP_TAC(BETA_RULE(fst(EQ_IMP_RULE(ISPEC p MINIMAL)))) THEN
  ANTS_TAC THENL [EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC(mk_eq(`k0:num`,mk_comb(`(minimal):(num->bool)->num`,p))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `k0 <= k` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(*** The minimality of k0, at j, without rewriting with it, which turns ***)
(*** its own instances into T                                           ***)

let REJX4_MINIMALITY_TAC j =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Const("!",_),Abs(v,Comb(Comb(Const("==>",_),
        Comb(Comb(Const("<",_),v'),Var("k0",_))),_))) when v' = v ->
        MP_TAC(SPEC j th)
    | _ -> NO_TAC);;

(*** The facts at the intermediate points, with the saved registers ***)

let REJX4_FRAME =
 `read SP s = word_add stackpointer (word 288) /\
  read (memory :> bytes64 (word_add stackpointer (word 288))) s = x19_init /\
  read (memory :> bytes64 (word_add stackpointer (word 296))) s = x20_init /\
  read (memory :> bytes64 (word_add stackpointer (word 304))) s = x21_init /\
  read (memory :> bytes64 (word_add stackpointer (word 312))) s = x22_init /\
  read (memory :> bytes64 (word_add stackpointer (word 320))) s = x23_init /\
  read (memory :> bytes64 (word_add stackpointer (word 328))) s = x24_init /\
  read (memory :> bytes64 (word_add stackpointer (word 336))) s = x25_init /\
  read (memory :> bytes64 (word_add stackpointer (word 344))) s = x26_init /\
  read (memory :> bytes64 (word_add stackpointer (word 352))) s = x27_init /\
  read (memory :> bytes64 (word_add stackpointer (word 360))) s = x28_init /\
  read (memory :> bytes64 (word_add stackpointer (word 368))) s =
  returnaddress /\
  read (memory :> bytes64 (word_add stackpointer (word 392))) s = vec3 /\
  read (memory :> bytes64 (word_add stackpointer (word 400))) s =
  word_add stackpointer
   (word((if aligned 32 stackpointer then 448 else 432) + 1024)) /\
  read (memory :> bytes64 (word_add stackpointer (word 408))) s =
  word_add stackpointer
   (word((if aligned 32 stackpointer then 448 else 432) + 1536)) /\
  read (memory :> bytes64 (word_add stackpointer (word 416))) s =
  word_add stackpointer
   (word((if aligned 32 stackpointer then 448 else 432) + 512)) /\
  read (memory :> bytes64 (word_add stackpointer (word 424))) s =
  word_add stackpointer
   (word((if aligned 32 stackpointer then 448 else 432) + 2048)) /\
  read (memory :> bytes64 (word_add stackpointer (word 3304))) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s =
  guard /\
  read (memory :> bytes64 guard) s = canary /\
  read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
  read (memory :> bytes(ea,el)) s = ev /\
  read X22 s =
  word_add stackpointer (word(if aligned 32 stackpointer then 448 else 432)) /\
  read X28 s = vec0 /\ read X20 s = vec1 /\ read X21 s = vec2`;;

let REJX4_POLY =
 `read (R:(armstate,int64)component) s =
  word(MIN 256 (LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * i)
    (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i))))))) /\
  read (memory :> bytes(vec,2 * MIN 256 (LENGTH(REJ_SAMPLE
    (wordlist_of_num (336 + 112 * i)
      (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i)))))))) s =
  num_of_wordlist(SUB_LIST(0,256) (REJ_SAMPLE(wordlist_of_num
    (336 + 112 * i)
    (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i)))))) /\
  read (memory :> bytes(st,200)) s =
  val(keccak_squeeze (3 + i) (S:1600 word))`;;

let REJX4_POLYS regs ms =
  flat
   (map (fun m ->
          let r = el m regs and vec = el m REJX4_VECS
          and inp = el m REJX4_INPS and st = REJX4_ST m
          and sv = el m REJX4_SVS in
          conjuncts
           (vsubst [r,`R:(armstate,int64)component`; vec,`vec:int64`;
                    inp,`inp:byte list`; st,`st:int64`; sv,`S:1600 word`]
                   REJX4_POLY)) ms);;

let REJX4_AT0 t =
  rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES] (vsubst [`0`,`i:num`] t)));;

(*** At the header of loop4, after sampling the first three polynomials ***)

let REJX4_A3 =
  let t = REJX4_AT0 (list_mk_conj(REJX4_POLYS REJX4_CTRS [0;1;2])) in
  let p3 = REJX4_AT0
   (mk_conj(`read (memory :> bytes(st,200)) s = val(keccak_squeeze (3 + i)
                                                    (S3:1600 word))`,
            mk_eq(list_mk_comb(`wordlist_from_memory:int64#num->armstate->
                                  (12 word)list`,
                               [mk_pair(REJX4_BUF 3,`336`); `s:armstate`]),
                  rejx4_fields0 `inp3:byte list`))) in
  let p3 = vsubst [REJX4_ST 3,`st:int64`] p3 in
  mk_abs(`s:armstate`,
    list_mk_conj(conjuncts t @ conjuncts p3 @
     [`read X23 s = word 0`;
      mk_eq(`read X1 s`,REJX4_BUF 3);
      mk_eq(`read X10 s`,REJX4_SP 2040);
      `read X5 s = word 3328`; `read X8 s = vec3`] @
     conjuncts REJX4_FRAME));;

(*** At the header of loop5, after 3 + i blocks of each ***)

let REJX4_INV =
  list_mk_abs([`i:num`; `s:armstate`],
    list_mk_conj(REJX4_POLYS REJX4_CTRS (0--3) @
                 [`read X27 s = word 3328`; `read X19 s = word 255`;
                  `read X8 s = vec3`] @ conjuncts REJX4_FRAME));;

(*** At the exit of loop5, with all the samples ***)

let REJX4_A2 =
  let res inp vec =
    vsubst [inp,`inp:byte list`; vec,`vec:int64`]
     `read (memory :> bytes(vec,512)) s =
      num_of_wordlist(SUB_LIST(0,256) (REJ_SAMPLE(wordlist_of_num
        (336 + 112 * k)
        (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * k))))))` in
  mk_abs(`s:armstate`,
    list_mk_conj(map2 res REJX4_INPS REJX4_VECS @ conjuncts REJX4_FRAME));;

(*** The fields of the first three blocks of each, before its loop ***)

let REJX4_INPUT0_TAC m s =
  let inp = el m REJX4_INPS in
  SUBGOAL_THEN
   (mk_eq(list_mk_comb(`wordlist_from_memory:int64#num->armstate->
                         (12 word)list`,
                       [mk_pair(REJX4_BUF m,`336`); s]),
          rejx4_fields0 inp))
  ASSUME_TAC THENL
   [MATCH_MP_TAC REJ_WORDLIST_FROM_BYTES THEN EXISTS_TAC `504` THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `504 = 168 * 3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

let REJX4_LENGTH0_TAC m =
  ASSUME_TAC(INST_TYPE [`:12`,`:N`]
   (ISPECL [`336`; rand(rejx4_fields0 (el m REJX4_INPS))]
    LENGTH_WORDLIST_OF_NUM));;

(*** A copy of the loop on the first three blocks ***)

(*** The call of copy k of the loop, for correctness (the safety proof ***)
(*** uses another one)                                                  ***)

let REJX4_LOOP_CALL k ilist n =
  REJX4_SIM_TAC (REJX4_LOOP_CORRECT k) ilist n;;

let REJX4_LOOP0_GEN_TAC call m n =
  let inp = el m REJX4_INPS in
  REJX4_LENGTH0_TAC m THEN
  call (m + 1)
   [list_mk_comb(`read:(armstate,int64)component->armstate->int64`,
            [el m REJX4_OUTS; `s:armstate`]); `0`; `read X1 s`; `504`;
    rejx4_fields0 inp; `pc:num`] n THEN
  REJ_POST_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES; MULT_CLAUSES; SUB_0; WORD_ADD_0;
                              LENGTH_SUB_LIST]) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REJ_BYTES16_OF_WORDLIST o check
   (can (term_match [] `wordlist_from_memory(a,n) s = l:int16 list`) o
    concl));;

let REJX4_LOOP0_TAC = REJX4_LOOP0_GEN_TAC REJX4_LOOP_CALL;;

(*** The numbers of samples so far in the loop body as ci0, ..., ci3, and ***)
(*** their definitions packed into a conjunction, which keeps them from   ***)
(*** the arithmetic of NONOVERLAPPING_TAC, much slower with them          ***)

let REJX4_IS_ABBREV tm =
  match tm with
    Comb(Comb(Const("=",_),Comb(Comb(Const("MIN",_),_),_)),Var(n,_)) ->
      String.length n = 3 && String.sub n 0 2 = "ci"
  | _ -> false;;

let REJX4_ABBREV_TAC =
  MAP_EVERY (fun m ->
    let t = mk_comb(`MIN 256`,rejx4_count (el m REJX4_INPS) `i:num`) in
    ASSUME_TAC(SPECL [`256`; rand t] (ARITH_RULE `!a b. MIN a b <= a`)) THEN
    ABBREV_TAC(mk_eq(mk_var("ci"^string_of_int m,`:num`),t))) (0--3) THEN
  (fun (asl,w) ->
    let hs,ks = partition (fun (_,th) -> REJX4_IS_ABBREV(concl th)) asl in
    let cth = end_itlist CONJ (map snd hs) in
    (null_meta,[("",ASSUME(concl cth))::ks,w],
     fun i ths -> PROVE_HYP (INSTANTIATE_ALL i cth) (hd ths)));;

let REJX4_ABBREV m =
  let eq = mk_eq(mk_comb(`MIN 256`,rejx4_count (el m REJX4_INPS) `i:num`),
                 mk_var("ci"^string_of_int m,`:num`)) in
  fun (asl,w) ->
    tryfind (fun (_,th) -> find (fun th' -> concl th' = eq) (CONJUNCTS th))
            asl;;

(*** A copy of the loop on one more block, and its results ***)

let REJX4_BLOCK_TAC m s =
  let inp = el m REJX4_INPS in
  SUBGOAL_THEN
   (mk_eq(list_mk_comb(`wordlist_from_memory:int64#num->armstate->
                         (12 word)list`,
                       [mk_pair(REJX4_BUF m,`112`); s]),
          rejx4_block inp `i:num`))
  ASSUME_TAC THENL
   [MATCH_MP_TAC REJ_WORDLIST_FROM_BYTES THEN EXISTS_TAC `168` THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th ->
      if can (term_match [] `!k n. n <= 168 ==> a = b`) (concl th) &&
         free_in inp (concl th)
      then MP_TAC(SPECL [`3 + i`; `168`] th) else NO_TAC) THEN
    REWRITE_TAC[LE_REFL; ARITH_RULE `168 * (3 + i) = 504 + 168 * i`;
                ARITH_RULE `(3 + i) + 1 = 3 + i + 1`] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASSUME_TAC(INST_TYPE [`:12`,`:N`]
   (ISPECL [`112`; rand(rejx4_block inp `i:num`)] LENGTH_WORDLIST_OF_NUM));;

let REJX4_COMBINE_TAC m s =
  let inp = el m REJX4_INPS and vec = el m REJX4_VECS in
  let c = mk_var("ci"^string_of_int m,`:num`) in
  let l1 = mk_comb(`SUB_LIST(0,256):(16 word)list->(16 word)list`,
                   mk_comb(`REJ_SAMPLE`,rejx4_fields inp `i:num`))
  and l2 = mk_comb(mk_comb(`SUB_LIST:num#num->(16 word)list->(16 word)list`,
                           mk_pair(`0`,mk_binop `(-):num->num->num` `256` c)),
                   mk_comb(`REJ_SAMPLE`,rejx4_block inp `i:num`)) in
  let lenl1 = mk_eq(mk_comb(`LENGTH:(16 word)list->num`,l1),c) in
  REJ_POST_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP REJ_BYTES16_OF_WORDLIST o check
   (can (term_match [] `wordlist_from_memory(a,n) s = l:int16 list`) o
    concl)) THEN
  SUBGOAL_THEN lenl1 ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN
    W(fun gl -> REWRITE_TAC[REJX4_ABBREV m gl]); ALL_TAC] THEN
  MP_TAC(ISPECL [vec; c; l1; l2; s] REJ_BYTES16_APPEND_N) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  W(fun gl ->
    let th = REWRITE_RULE [REJX4_ABBREV m gl]
             (ISPECL [mk_comb(`shake128`,inp); `i:num`] REJX4_SAMPLE_SUC) in
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN
    MP_TAC(AP_TERM `LENGTH:(16 word)list->num` th)) THEN
  REWRITE_TAC[LENGTH_APPEND; ASSUME lenl1] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [LENGTH_SUB_LIST] THEN
  REWRITE_TAC[SUB_0] THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[SYM th]));;

(*** For a polynomial with 256 samples already, those after one more ***)
(*** block, which are the same                                       ***)

let REJX4_SKIP_TAC m =
  let inp = el m REJX4_INPS in
  let c = mk_var("ci"^string_of_int m,`:num`) in
  let d0 = rejx4_done m `i:num` and d1 = rejx4_done m `i + 1` in
  SUBGOAL_THEN d0 ASSUME_TAC THENL
   [W(fun gl -> MP_TAC(REJX4_ABBREV m gl)) THEN
    REWRITE_TAC[ASSUME(mk_eq(c,`256`));
                ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`];
    ALL_TAC] THEN
  SUBGOAL_THEN d1 ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC (rejx4_count inp `i:num`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REJ_COUNT_MONO THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,rejx4_count inp `i + 1`),`256`))
   (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THENL
   [ASM_REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`]; ALL_TAC] THEN
  MP_TAC(ISPECL [mk_comb(`shake128`,inp); `i:num`; `i + 1`]
                REJ_SAMPLE_FINAL) THEN
  ASM_REWRITE_TAC[ARITH_RULE `i <= i + 1`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME(mk_eq(c,`256`))]);;

(*** Whether there are 256 samples for all four after one more block ***)

let REJX4_LS_TAC =
  SUBGOAL_THEN (mk_eq(`i + 1 < k0`,mk_neg(REJX4_DONE `i + 1`)))
   ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[TAUT `(a <=> ~b) <=> (b <=> ~a)`] THEN EQ_TAC THENL
     [DISCH_THEN(fun dth -> DISCH_THEN(fun lth ->
        REJX4_MINIMALITY_TAC `i + 1` THEN REWRITE_TAC[dth; lth]));
      DISCH_TAC THEN SUBGOAL_THEN `i + 1 = k0` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`i < k0`; `~(i + 1 < k0)`] THEN ARITH_TAC;
        REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Simulating the code of the loop body for each polynomial in turn, until   *)
(* the PC is one of the targets: one step at a time, deciding the branches,  *)
(* and the copy of the loop as a whole from its header.                      *)
(* ------------------------------------------------------------------------- *)

let current_state_num (asl,w) =
  let s = fst(dest_var(rand w)) in
  int_of_string(String.sub s 1 (String.length s - 1));;

(*** Linear arithmetic with only the facts about the variables given, ***)
(*** much faster than SIMPLE_ARITH_TAC with all the facts             ***)

let REJX4_ARITH_TAC vs =
  let numty = `:num` in
  let is_num_relop tm =
    exists (fun op -> is_binary op tm &&
                      (let x,_ = dest_binary op tm in type_of x = numty))
           ["=";"<";"<=";">";">="] in
  let ok tm =
    (is_num_relop tm || (is_neg tm && is_num_relop (dest_neg tm))) &&
    intersect (frees tm) vs <> [] &&
    not(can (find_term (fun t -> match t with
          Const(n,_) -> mem n ["read"; "write"; "val"; "word"] | _ -> false))
         tm) in
  W(fun (asl,w) ->
    MAP_EVERY (MP_TAC o snd) (filter (fun (_,th) -> ok(concl th)) asl) THEN
    CONV_TAC ARITH_RULE);;

(*** Rewrite only the PC, keeping the facts used in it ***)

let REJX4_PC_RULE_TAC =
  let pat = `read PC (s:armstate) = x:int64` in
  fun ths ->
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] pat) (concl th)
      then REWRITE_RULE ths th else th);;

(*** Decide a conditional branch on the numbers of samples ***)

let REJX4_DECIDE_BRANCH_TAC g =
  let p = current_pc g in
  match find_terms is_cond p with
    [] -> ALL_TAC g
  | t::_ ->
      let c = lhand(rator t) in
      let tac = REJX4_ARITH_TAC (frees c) in
      ((SUBGOAL_THEN c (fun th -> REJX4_PC_RULE_TAC [EQT_INTRO th]) THENL
         [tac; ALL_TAC]) ORELSE
       (SUBGOAL_THEN (mk_neg c) (fun th -> REJX4_PC_RULE_TAC [EQF_INTRO th])
        THENL [tac; ALL_TAC])) g;;

let REJX4_STEP_TAC n =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC [n] THEN
  W(fun g ->
    if find_terms is_cond (current_pc g) = [] then ALL_TAC else
    TRY W32_SMALL_TAC THEN
    CMP_SFLAGS_TAC `word_sub (word x) (word y):int32` WORD_CMP_32_FLAGS THEN
    REJX4_DECIDE_BRANCH_TAC);;

(*** The copy of the loop for polynomial m, from its header ***)

let REJX4_LOOPI_TAC call m n =
  let inp = el m REJX4_INPS in
  let c = mk_var("ci"^string_of_int m,`:num`) in
  REJX4_BLOCK_TAC m (mk_var("s"^string_of_int(n-1),`:armstate`)) THEN
  call (m + 6)
   [list_mk_comb(`read:(armstate,int64)component->armstate->int64`,
            [el m REJX4_OUTS; `s:armstate`]); c; `read X1 s`; `168`;
    rejx4_block inp `i:num`; `pc:num`] n THEN
  REJX4_COMBINE_TAC m (mk_var("s"^string_of_int n,`:armstate`)) THEN
  (let l = REJX4_LOOP_DATA (m + 6) in
   if l.rej_full = l.rej_end then ALL_TAC else
   let d1 = rejx4_done m `i + 1` in
   ASM_CASES_TAC d1 THEN
   FIRST_ASSUM(fun th ->
     REJX4_PC_RULE_TAC [ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`; th]));;

let REJX4_HEADERS =
  map (fun k -> rej_target (REJX4_LOOP_DATA k).rej_header,k - 6) [6;7;8;9];;

let rec REJX4_RUN_TAC call targets (asl,w) =
  let p = current_pc (asl,w) in
  if mem p targets || find_terms is_cond p <> [] then ALL_TAC (asl,w) else
  let n = current_state_num (asl,w) + 1 in
  let tac = try REJX4_LOOPI_TAC call (assoc p REJX4_HEADERS) n
            with Failure _ -> REJX4_STEP_TAC n in
  (tac THEN REJX4_RUN_TAC call targets) (asl,w);;

let rejx4_label s = rej_target ("mlkem_poly_rej_uniform_x4_" ^ s);;

(*** The stage for polynomial m in the loop body, from the test of ***)
(*** whether it has 256 samples already                            ***)

let REJX4_STAGE_TAC call m targets =
  let c = mk_var("ci"^string_of_int m,`:num`) in
  let d0 = rejx4_done m `i:num` in
  ASM_CASES_TAC (mk_eq(c,`256`)) THENL
   [REJX4_SKIP_TAC m;
    SUBGOAL_THEN (mk_binop `(<):num->num->bool` c `256`) ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN (mk_neg d0) ASSUME_TAC THENL
     [W(fun gl -> MP_TAC(REJX4_ABBREV m gl)) THEN
      POP_ASSUM MP_TAC THEN ARITH_TAC;
      ALL_TAC]] THEN
  REJX4_RUN_TAC call (map rejx4_label targets);;

(*** The facts about whether a polynomial has 256 samples ***)

let REJX4_IS_DONE_FACT tm =
  let tm' = if is_neg tm then dest_neg tm else tm in
  is_binary "<=" tm' && lhand tm' = `256`;;

(*** The exit of loop5, decided from what is known of the samples, ***)
(*** or by cases on the test                                       ***)

let REJX4_EXIT_SPLIT_TAC =
  W(fun (asl,w) ->
    REJX4_PC_RULE_TAC
     (filter (fun th -> REJX4_IS_DONE_FACT(concl th)) (map snd asl))) THEN
  W(fun g ->
    match find_terms is_cond (current_pc g) with
      [] -> ALL_TAC
    | t::_ ->
      ASM_CASES_TAC (lhand(rator t)) THEN
      FIRST_ASSUM(fun th -> REJX4_PC_RULE_TAC [th]));;

let REJX4_CLOSE_TAC =
  REJX4_EXIT_SPLIT_TAC THEN
  W(fun g ->
    let lt = `i + 1 < k0` in
    let t = if current_pc g = rejx4_label "loop5" then lt else mk_neg lt in
    SUBGOAL_THEN t (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REWRITE_TAC[] THEN NO_TAC; ALL_TAC]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* The parts of the proof.                                                   *)
(* ------------------------------------------------------------------------- *)

let REJX4_INTRO_TAC =
  MAP_EVERY X_GEN_TAC
   [`vec0:int64`; `vec1:int64`; `vec2:int64`; `vec3:int64`; `seed:int64`;
    `inp0:byte list`; `inp1:byte list`; `inp2:byte list`; `inp3:byte list`;
    `k:num`; `guard:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 3312 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              GSYM REJ_SAMPLE] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> ASSUME_TAC th THEN
              LABEL_TAC "H_MEMSET" (REWRITE_RULE[memset_contract] th))
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC));;

(*** From the entry to the header of loop4, through loop1 to loop3 ***)

let REJX4_PART1_TAC =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (1--3) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (4--6) THEN
  REJX4_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (7--26) THEN
  REJX4_NORMALIZE_TAC THEN
  LOCAL_INIT_X4_TAC [`read X0 s`; `pc:num`; `read X30 s`] 27 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (28--36) THEN
  REJX4_NORMALIZE_TAC THEN REJX4_GOT_TAC THEN
  LOCAL_ABSORB_X4_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`; `34`;
    `num_of_bytelist(inp0:byte list)`; `num_of_bytelist(inp1:byte list)`;
    `num_of_bytelist(inp2:byte list)`; `num_of_bytelist(inp3:byte list)`;
    `guard:int64`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 37 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (38--46) THEN
  REJX4_NORMALIZE_TAC THEN
  MAP_EVERY (fun m -> KECCAK_STATE_AT_TAC (REJX4_ST m)) (0--3) THEN
  LOCAL_SQUEEZE_X4_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `3`; `read X5 s`;
    `S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`;
    `pc:num`; `read SP s`; `read X30 s`] 47 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  REJX4_NORMALIZE_TAC THEN
  MAP_EVERY (fun m ->
    let n = 48 + 6 * m in
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC
     (n--(n + 4)) THEN
    REJX4_NORMALIZE_TAC THEN
    REJX4_INPUT0_TAC m (mk_var("s"^string_of_int(n + 4),`:armstate`)) THEN
    REJX4_LOOP0_TAC m (n + 5)) (0--2) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (66--70) THEN
  REJX4_NORMALIZE_TAC THEN
  REJX4_INPUT0_TAC 3 `s70:armstate` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** loop4, from its header, giving the samples from the first three  ***)
(*** blocks for the fourth polynomial, and its exit                    ***)

let REJX4_LOOP4_TAC =
  REJX4_LOOP0_TAC 3 1 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`]);;

(*** If no more block is needed, to the exit of loop5 ***)

let REJX4_NOLOOP_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN
  ENSURES_INIT_TAC "s0" THEN REJX4_LOOP4_TAC THEN
  REJX4_PC_RULE_TAC [ASSUME(rejx4_done0 3)] THEN
  MAP_EVERY (fun inp ->
    let c = mk_comb(`MIN 256`,rejx4_count0 inp) in
    SUBGOAL_THEN (mk_eq(c,`256`))
     (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN ASM_REWRITE_TAC[];
      ALL_TAC]) REJX4_INPS THEN
  REJX4_RUN_TAC REJX4_LOOP_CALL [rejx4_label "loop5_exit"] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun inp ->
    MP_TAC(ISPECL [mk_comb(`shake128`,inp); `0`; `k:num`]
                  REJ_SAMPLE_FINAL) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]) REJX4_INPS THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ASM_REWRITE_TAC[];;

(*** If more blocks are needed, from loop4 to the header of loop5 ***)

let REJX4_ENTER_TAC =
  SUBGOAL_THEN (mk_neg(rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES]
                                  (REJX4_DONE `0`)))))
   ASSUME_TAC THENL
   [REJX4_MINIMALITY_TAC `0` THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `~(k0 = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN REJX4_LOOP4_TAC THEN
  ASM_CASES_TAC (rejx4_done0 3) THEN
  FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(fun th' ->
    if concl th' = concl th then th' else REWRITE_RULE[th] th')) THENL
   [ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (2--6) THEN
    REJX4_TESTREGS_TAC [`X25`; `X26`; `X24`] THEN
    FIRST_ASSUM(fun th ->
      if is_neg(concl th) && is_conj(dest_neg(concl th))
      then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (7--9);
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (2--4)] THEN
  REJX4_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ASM_REWRITE_TAC[];;

(*** The body of loop5, from 3 + i blocks of each to 3 + i + 1 ***)

(*** In the body of loop5, after the first j polynomials, the samples ***)
(*** for those after one more block and for the others before it       ***)

let REJX4_MID j =
  let t1 = list_mk_conj(REJX4_POLYS REJX4_CTRS (0--(j-1))) in
  let t1 = vsubst [`i + 1`,`i:num`] t1 in
  let rest m =
    let r = el m REJX4_CTRS and vec = el m REJX4_VECS
    and inp = el m REJX4_INPS
    and c = mk_var("ci"^string_of_int m,`:num`) in
    vsubst [r,`R:(armstate,int64)component`; vec,`vec:int64`;
            inp,`inp:byte list`; c,`c:num`]
     `read (R:(armstate,int64)component) s = word c /\
      read (memory :> bytes(vec,2 * c)) s =
      num_of_wordlist(SUB_LIST(0,256) (REJ_SAMPLE(wordlist_of_num
        (336 + 112 * i)
        (num_of_bytelist(list_of_seq (shake128 inp) (504 + 168 * i))))))` in
  let st m =
    vsubst [REJX4_ST m,`st:int64`; el m REJX4_SVS,`S:1600 word`]
     `read (memory :> bytes(st,200)) s =
      val(keccak_squeeze (3 + i + 1) (S:1600 word))` in
  let blk m =
    vsubst [REJX4_BUF m,`buf:int64`; el m REJX4_SVS,`S:1600 word`]
     `read (memory :> bytes(buf,168)) s =
      val(keccak_squeeze (3 + i + 1) (S:1600 word)) MOD 2 EXP (8 * 168)` in
  mk_abs(`s:armstate`,
    list_mk_conj(conjuncts t1 @
                 flat(map (conjuncts o rest) (j--3)) @
                 map blk (j--3) @
                 map st (0--3) @
                 [`read X27 s = word 3328`; `read X19 s = word 255`;
                  `read X8 s = vec3`] @ conjuncts REJX4_FRAME));;

(*** The first polynomial ***)

let REJX4_BODY0_TAC =
  ENSURES_INIT_TAC "s0" THEN

  (*** Squeezing one more block from each state ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (1--6) THEN
  REJX4_NORMALIZE_TAC THEN
  MAP_EVERY (fun m -> KECCAK_STATE_AT_TAC (REJX4_ST m)) (0--3) THEN
  LOCAL_SQUEEZE_X4_TAC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `1`; `read X5 s`;
    `keccak_squeeze (3 + i) (S0:1600 word)`;
    `keccak_squeeze (3 + i) (S1:1600 word)`;
    `keccak_squeeze (3 + i) (S2:1600 word)`;
    `keccak_squeeze (3 + i) (S3:1600 word)`;
    `pc:num`; `read SP s`; `read X30 s`] 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600; MULT_CLAUSES;
                              REJ_NSUM_1; EXP; ADD_CLAUSES;
                              KECCAK_SQUEEZE_ADD;
                              ARITH_RULE `1 + 3 + i = 3 + i + 1`]) THEN
  REJX4_NORMALIZE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (8--8) THEN

  (*** Sampling from the block after the samples so far, if fewer ***)
  (*** than 256                                                   ***)

  REJX4_STAGE_TAC REJX4_LOOP_CALL 0 ["loop6_exit"] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** The second polynomial ***)

let REJX4_BODY1_TAC =
  ENSURES_INIT_TAC "s0" THEN
  REJX4_STAGE_TAC REJX4_LOOP_CALL 1 ["loop7_exit2"] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(*** The last two polynomials, and the test of whether all four have ***)
(*** 256 samples now                                                ***)

let REJX4_BODY23_TAC =
  ENSURES_INIT_TAC "s0" THEN
  REJX4_STAGE_TAC REJX4_LOOP_CALL 2 ["loop8_exit1"; "loop8_exit2"] THEN
  REJX4_STAGE_TAC REJX4_LOOP_CALL 3 ["loop5"; "loop9_exit2"] THEN

  (*** The test of whether there are 256 samples for all four now ***)

  W(fun g ->
    if current_pc g = rejx4_label "loop9_exit2" then
      let n = current_state_num g in
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC
       ((n + 1)--(n + 4)) THEN
      REJX4_TESTREGS_TAC [`X25`; `X26`; `X24`]
    else ALL_TAC) THEN
  REJX4_CLOSE_TAC;;

let REJX4_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REJX4_LS_TAC THEN
  REJX4_ABBREV_TAC THEN
  ENSURES_SEQUENCE_TAC `pc + mlkem_poly_rej_uniform_x4_loop6_exit`
   (REJX4_MID 1) THEN CONJ_TAC THENL
   [REJX4_BODY0_TAC;
    ENSURES_SEQUENCE_TAC `pc + mlkem_poly_rej_uniform_x4_loop7_exit2`
     (REJX4_MID 2) THEN CONJ_TAC THENL
     [REJX4_BODY1_TAC; REJX4_BODY23_TAC]];;

let REJX4_EXIT_TAC =
  ENSURES_INIT_TAC "s0" THEN
  MAP_EVERY (fun inp ->
    SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,rejx4_count inp `k0:num`),`256`))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC]) REJX4_INPS THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  MAP_EVERY (fun inp ->
    MP_TAC(ISPECL [mk_comb(`shake128`,inp); `k0:num`; `k:num`]
                  REJ_SAMPLE_FINAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC])
   REJX4_INPS THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

let REJX4_LOOP_TAC =
  ENSURES_WHILE_UP2_TAC `k0:num` `pc + mlkem_poly_rej_uniform_x4_loop5`
   `pc + mlkem_poly_rej_uniform_x4_loop5_exit` REJX4_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; REJX4_ENTER_TAC; REJX4_BODY_TAC; REJX4_EXIT_TAC];;

(*** Releasing the state, zeroing the buffers, the stack guard, return ***)

let REJX4_FINAL_TAC =
  let tac inp =
    let l = mk_comb(`SUB_LIST(0,256):(16 word)list->(16 word)list`,
                    mk_comb(`REJ_SAMPLE`,rejx4_fields inp `k:num`)) in
    let lth = mk_eq(mk_comb(`LENGTH:(16 word)list->num`,l),`256`) in
    SUBGOAL_THEN lth ASSUME_TAC THENL
     [REWRITE_TAC[LENGTH_SUB_LIST; SUB_0;
                  ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [SYM(ASSUME lth)] THEN
    MATCH_MP_TAC REJ_WORDLIST_OF_BYTES16 THEN REWRITE_TAC[ASSUME lth] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN ASM_REWRITE_TAC[] in
  REPEAT CONJ_TAC THENL map tac REJX4_INPS;;

let REJX4_PART3_TAC =
  ENSURES_INIT_TAC "s0" THEN REJX4_GOT_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (1--2) THEN
  LOCAL_RELEASE_X4_TAC
   [`read X0 s`; `mf:int64`; `ea:int64`; `el:num`; `ev:num`; `pc:num`;
    `read SP s`; `read X30 s`] 3 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (4--7) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC 7 THEN
  LIBC_CALL_TAC "H_MEMSET" MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC
   [`read X0 s`; `read X1 s`; `read X2 s`; `read X30 s`] 12 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (13--13) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (14--27) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REJX4_FINAL_TAC;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!vec0 vec1 vec2 vec3 seed (inp0:byte list) (inp1:byte list)
   (inp2:byte list) (inp3:byte list) k guard mf ea el ev pc stackpointer
   returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        LENGTH inp0 = 34 /\ LENGTH inp1 = 34 /\
        LENGTH inp2 = 34 /\ LENGTH inp3 = 34 /\
        ALL (\inp. 256 <= LENGTH(FILTER (\x. val x < 3329)
                            (MAP (word_zx:12 word->16 word)
                              (wordlist_of_num (336 + 112 * k)
                                (num_of_bytelist
                                  (list_of_seq (shake128 inp)
                                               (504 + 168 * k)))))))
            [inp0; inp1; inp2; inp3] /\
        PAIRWISE nonoverlapping
         [(vec0,512); (vec1,512); (vec2,512); (vec3,512);
          (word_sub stackpointer (word 3312),3312)] /\
        ALLPAIRS nonoverlapping
         [(vec0,512); (vec1,512); (vec2,512); (vec3,512);
          (word_sub stackpointer (word 3312),3312)]
         [(seed,34); (word_add seed (word 64),34);
          (word_add seed (word 128),34); (word_add seed (word 192),34);
          (word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8);
          (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_poly_rej_uniform_x4) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [vec0; vec1; vec2; vec3; seed] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(seed,34)) s = num_of_bytelist inp0 /\
                  read (memory :> bytes(word_add seed (word 64),34)) s =
                  num_of_bytelist inp1 /\
                  read (memory :> bytes(word_add seed (word 128),34)) s =
                  num_of_bytelist inp2 /\
                  read (memory :> bytes(word_add seed (word 192),34)) s =
                  num_of_bytelist inp3)
             (\s. read PC s = returnaddress /\
                  wordlist_from_memory(vec0,256) s =
                  SUB_LIST(0,256)
                   (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                       (wordlist_of_num (336 + 112 * k)
                         (num_of_bytelist
                           (list_of_seq (shake128 inp0) (504 + 168 * k)))))) /\
                  wordlist_from_memory(vec1,256) s =
                  SUB_LIST(0,256)
                   (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                       (wordlist_of_num (336 + 112 * k)
                         (num_of_bytelist
                           (list_of_seq (shake128 inp1) (504 + 168 * k)))))) /\
                  wordlist_from_memory(vec2,256) s =
                  SUB_LIST(0,256)
                   (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                       (wordlist_of_num (336 + 112 * k)
                         (num_of_bytelist
                           (list_of_seq (shake128 inp2) (504 + 168 * k)))))) /\
                  wordlist_from_memory(vec3,256) s =
                  SUB_LIST(0,256)
                   (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                       (wordlist_of_num (336 + 112 * k)
                         (num_of_bytelist
                           (list_of_seq (shake128 inp3) (504 + 168 * k)))))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(vec0,512); memory :> bytes(vec1,512);
                memory :> bytes(vec2,512); memory :> bytes(vec3,512);
                memory :> bytes(word_sub stackpointer (word 3312),3312)])`;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;


(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof, as for mlkem_poly_rej_uniform,     *)
(* with the least k for which all four have 256 samples. It assumes the      *)
(* combined contract for memset in utils/mlkem_native_libc_full.ml, as the   *)
(* combined theorem for mlkem_shake128x4_absorb_once does, which implies the *)
(* safety contract for the other calls. The events of an iteration of loop5  *)
(* depend on which polynomials already have 256 samples, on the exits taken  *)
(* by loop8 and loop9 and on the test at the end, so the template gives them *)
(* by cases on these conditions, all of which are functions of the seeds.    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/subroutine_signatures.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;

let PREJ4_ARGS =
  [`vec0:int64`; `vec1:int64`; `vec2:int64`; `vec3:int64`;
   `seed:int64`; `inp0:byte list`; `inp1:byte list`;
   `inp2:byte list`; `inp3:byte list`; `guard:int64`;
   `mf:int64`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`];;

let PREJ4_LEAVES = ref ([]:term list);;

let PREJ4_SAFE_TEMPLATE =
  let args = PREJ4_ARGS in
  let fty = itlist (fun a t -> mk_fun_ty (type_of a) t) args
                   `:(uarch_event)list` in
  let ftyi = itlist (fun a t -> mk_fun_ty (type_of a) t) args
                    (mk_fun_ty `:num` `:(uarch_event)list`) in
  let app n = list_mk_comb(mk_var(n,fty),args) in
  let leaf code =
    let v = mk_var("f_ev_loop_" ^ code,ftyi) in
    PREJ4_LEAVES := v :: !PREJ4_LEAVES;
    mk_comb(list_mk_comb(v,args),`i:num`) in
  let k0 = mk_comb(`(minimal):(num->bool)->num`,
                   mk_abs(`n:num`,REJX4_DONE `n:num`)) in
  let d m = rejx4_done m `i:num` and e m = rejx4_done m `i + 1` in
  let t = mk_binop `(<):num->num->bool` `i + 1` k0 in
  let cnd c a b = mk_cond(c,a,b) in
  let stage3 code from22 =
    cnd (d 3)
     (if from22 then cnd t (leaf(code ^ "s1")) (leaf(code ^ "s0"))
      else leaf(code ^ "s"))
     (cnd (e 3) (cnd t (leaf(code ^ "r11")) (leaf(code ^ "r10")))
                (leaf(code ^ "r0"))) in
  let stage2 code =
    cnd (d 2) (stage3 (code ^ "s") true)
     (cnd (e 2) (stage3 (code ^ "r1") true) (stage3 (code ^ "r0") false)) in
  let ap = `APPEND:(uarch_event)list->(uarch_event)list->(uarch_event)list` in
  let seg0 = cnd (d 0) (leaf "0s") (leaf "0r")
  and seg1 = cnd (d 1) (leaf "1s") (leaf "1r")
  and seg23 = stage2 "" in
  let loop = mk_abs(`i:num`,
    list_mk_comb(ap,[seg23; list_mk_comb(ap,[seg1; seg0])])) in
  let enum = list_mk_comb(`ENUMERATEL:num->(num->(uarch_event)list)->
                                     (uarch_event)list`,[k0;loop]) in
  let enter = cnd (rejx4_done0 3) (app "f_ev_enter1") (app "f_ev_enter0") in
  let mid = mk_cond(mk_eq(k0,`0`),app "f_ev_skip",
              list_mk_comb(ap,[app "f_ev_exit";
                list_mk_comb(ap,[enum; enter])])) in
  let body = list_mk_comb(ap,[app "f_ev_p3";
               list_mk_comb(ap,[mid; app "f_ev_p1"])]) in
  list_mk_abs(args,body);;

let PREJ4_SAFE_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    let sth = CONJUNCT2(MATCH_MP MEMSET_FULL_CONTRACT th) in
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (REWRITE_RULE[memset_safety_contract] sth) "H_MEMSET" THEN
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLKEM_NATIVE_SHAKE128X4_RELEASE_GCC12_O3_IMAGE_SUBROUTINE_SAFE
               sth) "H_RELEASE") THEN
  FIRST_X_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP
       MLKEM_NATIVE_SHAKE128X4_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_FULL th)
     "H_ABSORB") THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE128X4_INIT_GCC12_O3_IMAGE_SUBROUTINE_SAFE "H_INIT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O3_IMAGE_SUBROUTINE_FULL
    "H_SQUEEZE" THEN
  MAP_EVERY (fun (k,th) ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC th ("H_LOOP" ^ string_of_int k))
   (zip [1;2;3;4;6;7;8;9]
        MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_LOOPS_FULL) THEN
  CONCRETIZE_F_EVENTS_TAC PREJ4_SAFE_TEMPLATE THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              GSYM REJ_SAMPLE] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REJX4_SETUP_TAC THEN REJX4_ABSORBED_TAC THEN REJX4_MINIMAL_TAC;;

let PREJ4_ALLOWED =
  [`pc:num`; `vec0:int64`; `vec1:int64`; `vec2:int64`; `vec3:int64`;
   `seed:int64`; `inp0:byte list`; `inp1:byte list`; `inp2:byte list`;
   `inp3:byte list`; `guard:int64`; `mf:int64`; `stackpointer:int64`;
   `returnaddress:int64`; `i:num`; `k0:num`; `e2:(uarch_event)list`;
   `ci0:num`; `ci1:num`; `ci2:num`; `ci3:num`] @ !PREJ4_LEAVES;;

(*** The end of a buffer as given to a loop lemma, buf + buflen with buf ***)
(*** = base + 512 * m, in the form computed by the code, base + (512 * m ***)
(*** + 504); only such sums are rewritten, so that the earlier events   ***)
(*** (which become part of the callee's trace) keep their form          ***)

let PREJ4_ADDR_CONV =
  let norm = RAND_CONV(REWRITE_CONV[GSYM ADD_ASSOC] THENC
                       DEPTH_CONV NUM_ADD_CONV) in
  fun tm ->
    match tm with
      Comb(Comb(Const("word_add",_),_),Comb(Const("word",_),_)) ->
        CHANGED_CONV
         (TRY_CONV(REWR_CONV(GSYM WORD_ADD_ASSOC) THENC
                   RAND_CONV(REWR_CONV(GSYM WORD_ADD))) THENC
          RAND_CONV norm) tm
    | _ -> failwith "PREJ4_ADDR_CONV";;

let PREJ4_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O3_mc,
       MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O3_mc,safety_th)
      ilist n THENL
     [TRY(CONV_TAC(DEPTH_CONV PREJ4_ADDR_CONV) THEN REWRITE_TAC[]) THEN
      EXISTS_E2_TAC (ref PREJ4_ALLOWED);
      LABEL_TAC name safety_th]);;

let PREJ4_LOOP_CALL k ilist n =
  PREJ4_SAFE_CALL_TAC ("H_LOOP" ^ string_of_int k)
   (`e:(uarch_event)list` :: ilist) n;;

let PREJ4_LOOP0_TAC = REJX4_LOOP0_GEN_TAC PREJ4_LOOP_CALL;;

(*** DISCHARGE_SAFETY_PROPERTY_TAC, with only the facts about events    ***)
(*** for the check of the memory accesses. With all the assumptions, the ***)
(*** arithmetic of each failed attempt to place an access in a region   ***)
(*** takes seconds, and a segment minutes. The trace is associated to   ***)
(*** the right first, as the check expects                              ***)

let PREJ4_KEEP_EVENTS_TAC (asl,w) =
  let keep th =
    let c = concl th in
    (match strip_comb c with
       Const("memaccess_inbounds",_),_ -> true | _ -> false) ||
    (is_eq c && is_var(lhs c) && type_of(lhs c) = `:(uarch_event)list`) in
  null_meta,[filter (keep o snd) asl,w],(fun i ths -> hd ths);;

(*** The existential witness for the events becomes a metavariable, so ***)
(*** it is renamed first to a name used nowhere else: with the default  ***)
(*** name (a variant of e2), it can clash with the variable chosen for  ***)
(*** the events of a callee in a later case, which its instantiation    ***)
(*** then replaces                                                      ***)

let PREJ4_META_COUNT = ref 0;;

let PREJ4_DISCHARGE_TAC =
  W(fun (asl,w) ->
    let v,_ = dest_exists w in
    PREJ4_META_COUNT := !PREJ4_META_COUNT + 1;
    CONV_TAC(GEN_ALPHA_CONV
      (mk_var("e2_seg" ^ string_of_int(!PREJ4_META_COUNT),type_of v)))) THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    (if is_conj w then CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]
     else ALL_TAC) THEN
    PREJ4_KEEP_EVENTS_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let PREJ4_SAFE_PART1_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (1--3) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (4--6) THEN
  REJX4_BUFFER_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (7--26) THEN
  REJX4_NORMALIZE_TAC THEN
  PREJ4_SAFE_CALL_TAC "H_INIT"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read X30 s`] 27 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (28--36) THEN
  REJX4_NORMALIZE_TAC THEN REJX4_GOT_TAC THEN
  PREJ4_SAFE_CALL_TAC "H_ABSORB"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X3 s`; `read X4 s`; `34`;
    `num_of_bytelist(inp0:byte list)`; `num_of_bytelist(inp1:byte list)`;
    `num_of_bytelist(inp2:byte list)`; `num_of_bytelist(inp3:byte list)`;
    `guard:int64`; `pc:num`; `read SP s`; `read X30 s`] 37 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (38--46) THEN
  REJX4_NORMALIZE_TAC THEN
  MAP_EVERY (fun m -> KECCAK_STATE_AT_TAC (REJX4_ST m)) (0--3) THEN
  PREJ4_SAFE_CALL_TAC "H_SQUEEZE"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X3 s`; `3`; `read X5 s`;
    `S0:1600 word`; `S1:1600 word`; `S2:1600 word`; `S3:1600 word`;
    `pc:num`; `read SP s`; `read X30 s`] 47 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
  REJX4_NORMALIZE_TAC THEN
  MAP_EVERY (fun m ->
    let n = 48 + 6 * m in
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC
     (n--(n + 4)) THEN
    REJX4_NORMALIZE_TAC THEN
    REJX4_INPUT0_TAC m (mk_var("s"^string_of_int(n + 4),`:armstate`)) THEN
    PREJ4_LOOP0_TAC m (n + 5)) (0--2) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (66--70) THEN
  REJX4_NORMALIZE_TAC THEN
  REJX4_INPUT0_TAC 3 `s70:armstate` THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  PREJ4_DISCHARGE_TAC;;

let PREJ4_SAFE_NOLOOP_TAC =
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES; ADD_CLAUSES]) THEN
  REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  PREJ4_LOOP0_TAC 3 1 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`]) THEN
  REJX4_PC_RULE_TAC [ASSUME(rejx4_done0 3)] THEN
  MAP_EVERY (fun inp ->
    let c = mk_comb(`MIN 256`,rejx4_count0 inp) in
    SUBGOAL_THEN (mk_eq(c,`256`))
     (fun th -> REWRITE_TAC[th] THEN RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN ASM_REWRITE_TAC[];
      ALL_TAC]) REJX4_INPS THEN
  REJX4_RUN_TAC PREJ4_LOOP_CALL [rejx4_label "loop5_exit"] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun inp ->
    MP_TAC(ISPECL [mk_comb(`shake128`,inp); `0`; `k:num`]
                  REJ_SAMPLE_FINAL) THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LE_0] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]) REJX4_INPS THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  ASM_REWRITE_TAC[] THEN PREJ4_DISCHARGE_TAC;;

(*** The trace e2 before a segment is kept as a variable: at the start  ***)
(*** of the segment, the same expression in the postcondition is folded ***)
(*** into e2, and its definition is taken out of the assumptions, so    ***)
(*** that no rewriting expands e2 or changes its definition. Otherwise  ***)
(*** the check of the memory accesses expands e2 and looks at all the   ***)
(*** earlier events again, which takes minutes for each case. The bound ***)
(*** e2 of the postcondition is renamed first, and the folding is done  ***)
(*** at the outermost match only, as it can't be done under a binder of ***)
(*** a variable of the definition (e2, or i inside the expression). If  ***)
(*** the expression is associated differently in the postcondition (at  ***)
(*** the exit of loop5), both are associated to the right first         ***)

let PREJ4_E2_TAC =
  let is_e2eq th =
    let c = concl th in
    is_eq c && is_var(lhs c) && fst(dest_var(lhs c)) = "e2" in
  let rename t =
    let v,_ = dest_exists t in
    if fst(dest_var v) = "e2" then GEN_ALPHA_CONV (mk_var("e2'",type_of v)) t
    else failwith "rename" in
  let fold th = CHANGED_TAC(GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM th]) in
  CONV_TAC(ONCE_DEPTH_CONV rename) THEN
  FIRST_X_ASSUM(fun th ->
    if is_e2eq th then
      fold th ORELSE
      (REWRITE_TAC[GSYM APPEND_ASSOC] THEN
       fold(REWRITE_RULE[GSYM APPEND_ASSOC] th))
    else NO_TAC);;

let PREJ4_FINAL_TAC ths =
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC ths THEN ASM_REWRITE_TAC[];;

let PREJ4_SAFE_ENTER_TAC =
  SUBGOAL_THEN (mk_neg(rhs(concl(REWRITE_CONV[MULT_CLAUSES; ADD_CLAUSES]
                                  (REJX4_DONE `0`)))))
   ASSUME_TAC THENL
   [REJX4_MINIMALITY_TAC `0` THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `~(k0 = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  PREJ4_E2_TAC THEN
  PREJ4_LOOP0_TAC 3 1 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`]) THEN
  ASM_CASES_TAC (rejx4_done0 3) THEN
  FIRST_ASSUM(fun th -> RULE_ASSUM_TAC(fun th' ->
    if concl th' = concl th then th' else REWRITE_RULE[th] th')) THENL
   [ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (2--6) THEN
    REJX4_TESTREGS_TAC [`X25`; `X26`; `X24`] THEN
    FIRST_ASSUM(fun th ->
      if is_neg(concl th) && is_conj(dest_neg(concl th))
      then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (7--9);
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (2--4)] THEN
  REJX4_NORMALIZE_TAC THEN
  PREJ4_FINAL_TAC [MULT_CLAUSES; ADD_CLAUSES] THEN
  REJ_DECIDE_CONDS_TAC THEN REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN
  PREJ4_DISCHARGE_TAC;;

(*** The numbers of samples so far in terms of the seeds again, as the  ***)
(*** events must not depend on the abbreviations                       ***)

let PREJ4_UNABBREV_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    let cs = CONJUNCTS th in
    if exists (REJX4_IS_ABBREV o concl) cs then
      MAP_EVERY (fun c -> if REJX4_IS_ABBREV(concl c)
                          then SUBST_ALL_TAC(SYM c) else ASSUME_TAC c) cs
    else NO_TAC));;

(*** The events of a part of an iteration, with the conditions decided ***)

let PREJ4_SEG_DISCHARGE_TAC =
  REJ_DECIDE_CONDS_TAC THEN REJ_DECIDE_CONDS_TAC THEN
  PREJ4_UNABBREV_TAC THEN PREJ4_DISCHARGE_TAC;;

let PREJ4_SAFE_CLOSE_TAC =
  REJX4_EXIT_SPLIT_TAC THEN
  W(fun g ->
    let lt = `i + 1 < k0` in
    let t = if current_pc g = rejx4_label "loop5" then lt else mk_neg lt in
    SUBGOAL_THEN t (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THENL
     [ASM_REWRITE_TAC[] THEN NO_TAC; ALL_TAC]) THEN
  PREJ4_FINAL_TAC [] THEN PREJ4_SEG_DISCHARGE_TAC;;

(*** The events of an iteration of loop5 as those of its three parts, ***)
(*** after the polynomials 0, 1 and 2-3, and the sequence point after ***)
(*** the first, whose events are seg0 after the earlier ones          ***)

let PREJ4_SPLIT_EVENTS_TAC =
  REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC];;

let PREJ4_SEQ0_TAC pcterm mid =
  W(fun (asl,w) ->
    let post = rand(rator w) in
    let ex = find_term (fun t -> is_exists t &&
               fst(dest_var(fst(dest_exists t))) = "e2") post in
    let v,bod = dest_exists ex in
    let c1,rest = dest_conj bod in
    let eq,c3 = dest_conj rest in
    let _,seg1rest = dest_binary "APPEND" (rhs eq) in
    let _,seg0tail = dest_binary "APPEND" seg1rest in
    let ex' = mk_exists(v,list_mk_conj[c1; mk_eq(lhs eq,seg0tail); c3]) in
    let inv = let s,b = dest_abs mid in mk_abs(s,mk_conj(b,ex')) in
    ENSURES_SEQUENCE_TAC pcterm inv);;

let PREJ4_SAFE_BODY0_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  PREJ4_E2_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (1--6) THEN
  REJX4_NORMALIZE_TAC THEN
  MAP_EVERY (fun m -> KECCAK_STATE_AT_TAC (REJX4_ST m)) (0--3) THEN
  PREJ4_SAFE_CALL_TAC "H_SQUEEZE"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X3 s`; `1`; `read X5 s`;
    `keccak_squeeze (3 + i) (S0:1600 word)`;
    `keccak_squeeze (3 + i) (S1:1600 word)`;
    `keccak_squeeze (3 + i) (S2:1600 word)`;
    `keccak_squeeze (3 + i) (S3:1600 word)`;
    `pc:num`; `read SP s`; `read X30 s`] 7 THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600; MULT_CLAUSES;
                              REJ_NSUM_1; EXP; ADD_CLAUSES;
                              KECCAK_SQUEEZE_ADD;
                              ARITH_RULE `1 + 3 + i = 3 + i + 1`]) THEN
  REJX4_NORMALIZE_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (8--8) THEN
  REJX4_STAGE_TAC PREJ4_LOOP_CALL 0 ["loop6_exit"] THEN
  PREJ4_FINAL_TAC [] THEN
  PREJ4_SEG_DISCHARGE_TAC;;

let PREJ4_SAFE_BODY1_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  PREJ4_E2_TAC THEN
  REJX4_STAGE_TAC PREJ4_LOOP_CALL 1 ["loop7_exit2"] THEN
  PREJ4_FINAL_TAC [] THEN
  PREJ4_SEG_DISCHARGE_TAC;;

let PREJ4_SAFE_BODY23_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  PREJ4_E2_TAC THEN
  REJX4_STAGE_TAC PREJ4_LOOP_CALL 2 ["loop8_exit1"; "loop8_exit2"] THEN
  REJX4_STAGE_TAC PREJ4_LOOP_CALL 3 ["loop5"; "loop9_exit2"] THEN
  W(fun g ->
    if current_pc g = rejx4_label "loop9_exit2" then
      let n = current_state_num g in
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC
       ((n + 1)--(n + 4)) THEN
      REJX4_TESTREGS_TAC [`X25`; `X26`; `X24`]
    else ALL_TAC) THEN
  PREJ4_SAFE_CLOSE_TAC;;

let PREJ4_SAFE_BODY_TAC =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REJX4_LS_TAC THEN REJX4_ABBREV_TAC THEN PREJ4_SPLIT_EVENTS_TAC THEN
  PREJ4_SEQ0_TAC `pc + mlkem_poly_rej_uniform_x4_loop6_exit`
   (REJX4_MID 1) THEN CONJ_TAC THENL
   [PREJ4_SAFE_BODY0_TAC;
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_rej_uniform_x4_loop7_exit2`
     (REJX4_MID 2) THEN CONJ_TAC THENL
     [PREJ4_SAFE_BODY1_TAC; PREJ4_SAFE_BODY23_TAC]];;

let PREJ4_SAFE_EXIT_TAC =
  REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  PREJ4_E2_TAC THEN
  MAP_EVERY (fun inp ->
    SUBGOAL_THEN (mk_eq(mk_comb(`MIN 256`,rejx4_count inp `k0:num`),`256`))
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[ARITH_RULE `MIN 256 x = 256 <=> 256 <= x`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC]) REJX4_INPS THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  MAP_EVERY (fun inp ->
    MP_TAC(ISPECL [mk_comb(`shake128`,inp); `k0:num`; `k:num`]
                  REJ_SAMPLE_FINAL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC])
   REJX4_INPS THEN
  PREJ4_FINAL_TAC [] THEN
  PREJ4_DISCHARGE_TAC;;

let PREJ4_SAFE_LOOP_TAC =
  REWRITE_TAC[EQF_INTRO(ASSUME `~(k0 = 0)`)] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k0:num` `pc + mlkem_poly_rej_uniform_x4_loop5`
   `pc + mlkem_poly_rej_uniform_x4_loop5_exit`
    REJX4_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    PREJ4_SAFE_ENTER_TAC;
    PREJ4_SAFE_BODY_TAC;
    PREJ4_SAFE_EXIT_TAC];;

let PREJ4_SAFE_PART3_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
    is_eq(concl th) && rhs(concl th) = `k0:num`)) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  PREJ4_E2_TAC THEN
  REJX4_GOT_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (1--2) THEN
  PREJ4_SAFE_CALL_TAC "H_RELEASE"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
    `read X30 s`] 3 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (4--7) THEN
  LIBC_PLT_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC 7 THEN
  LIBC_SAFE_CALL_TAC "H_MEMSET" MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
    `read X30 s`] (ref PREJ4_ALLOWED) 12 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (13--13) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_EXEC (14--27) THEN
  PREJ4_FINAL_TAC [] THEN
  PREJ4_DISCHARGE_TAC;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
   memset_full_contract mf ea el ev
   ==> exists f_events.
        forall e vec0 vec1 vec2 vec3 seed (inp0:byte list) (inp1:byte list)
               (inp2:byte list) (inp3:byte list) k guard pc stackpointer
               returnaddress.
         aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
         aligned 16 stackpointer /\
         LENGTH inp0 = 34 /\ LENGTH inp1 = 34 /\
         LENGTH inp2 = 34 /\ LENGTH inp3 = 34 /\
         ALL (\inp. 256 <= LENGTH(FILTER (\x. val x < 3329)
                             (MAP (word_zx:12 word->16 word)
                               (wordlist_of_num (336 + 112 * k)
                                 (num_of_bytelist
                                   (list_of_seq (shake128 inp)
                                                (504 + 168 * k)))))))
             [inp0; inp1; inp2; inp3] /\
         PAIRWISE nonoverlapping
          [(vec0,512); (vec1,512); (vec2,512); (vec3,512);
           (word_sub stackpointer (word 3312),3312)] /\
         ALLPAIRS nonoverlapping
          [(vec0,512); (vec1,512); (vec2,512); (vec3,512);
           (word_sub stackpointer (word 3312),3312)]
          [(seed,34); (word_add seed (word 64),34);
           (word_add seed (word 128),34); (word_add seed (word 192),34);
           (word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
           (guard,8);
           (word(pc + got_memset),8); (ea,el)]
         ==> ensures arm
              (\s. aligned_bytes_loaded s (word pc)
                     mlkem_native_libmlkem_gcc12_O3_mc /\
                   read PC s = word (pc + mlkem_poly_rej_uniform_x4) /\
                   read SP s = stackpointer /\
                   read X30 s = returnaddress /\
                   C_ARGUMENTS [vec0; vec1; vec2; vec3; seed] s /\
                   read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                     guard /\
                   read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                   read (memory :> bytes(ea,el)) s = ev /\
                   read (memory :> bytes(seed,34)) s = num_of_bytelist inp0 /\
                   read (memory :> bytes(word_add seed (word 64),34)) s =
                   num_of_bytelist inp1 /\
                   read (memory :> bytes(word_add seed (word 128),34)) s =
                   num_of_bytelist inp2 /\
                   read (memory :> bytes(word_add seed (word 192),34)) s =
                   num_of_bytelist inp3 /\
                   read events s = e)
              (\s. read PC s = returnaddress /\
                   (exists e2.
                      read events s = APPEND e2 e /\
                      e2 = f_events vec0 vec1 vec2 vec3 seed inp0 inp1 inp2
                             inp3 guard mf pc
                             (word_sub stackpointer (word 3312))
                             returnaddress /\
                      memaccess_inbounds e2
                       [seed,34; word_add seed (word 64),34;
                        word_add seed (word 128),34;
                        word_add seed (word 192),34;
                        vec0,512; vec1,512; vec2,512; vec3,512;
                        word_sub stackpointer (word 3312),3312;
                        word(pc + got_stack_chk_guard),8; guard,8;
                        word(pc + got_memset),8;
                        ea,el;
                        word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                       [vec0,512; vec1,512; vec2,512; vec3,512;
                        word_sub stackpointer (word 3312),3312]))
              (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
               MAYCHANGE
                [memory :> bytes(vec0,512); memory :> bytes(vec1,512);
                 memory :> bytes(vec2,512); memory :> bytes(vec3,512);
                 memory :> bytes(word_sub stackpointer (word 3312),3312)])`;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_REJ_UNIFORM_X4_GCC12_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
