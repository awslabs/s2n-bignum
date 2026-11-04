(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of a polynomial from a seed by rejection. This is the    *)
(* code for mlkem_poly_rej_uniform from mlkem-native's portable C            *)
(* implementation compiled by gcc 12 with -O3 (see mlkem_native/README.md),  *)
(* which absorbs the 34 bytes of the seed into a SHAKE128 state, squeezes    *)
(* three blocks of 168 bytes and samples the coefficients below 3329 from    *)
(* them, and then squeezes one more block and samples from it until there    *)
(* are 256, before zeroing the state and the buffer. Unlike at -O2, the      *)
(* sampling of mlk_rej_uniform_c is inlined, as two copies of its loop, one  *)
(* for the first three blocks (loop1) and one for each further block (loop3, *)
(* inside the loop loop2 that squeezes the blocks). The code is in the whole *)
(* image (see libmlkem.ml), and the two copies of the loop are verified      *)
(* there with the tool in rej_uniform.ml.                                    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O3/rej_uniform.ml";;

(*** The code in the image:

    mlkem_poly_rej_uniform:
       +0x0: sub     sp, sp, #0x340
       +0x4: adrp    x2, <page>
       +0x8: ldr     x2, [x2, #4088]  // got_stack_chk_guard
       +0xc: stp     x19, x20, [sp]
      +0x10: add     x20, sp, #0x5f
      +0x14: and     x20, x20, #0xffffffffffffffe0
      +0x18: stp     x21, x22, [sp, #16]
      +0x1c: add     x21, x20, #0x200
      +0x20: mov     x22, x0
      +0x24: stp     x23, x24, [sp, #32]
      +0x28: mov     x23, x1
      +0x2c: mov     x0, x21
      +0x30: str     x30, [sp, #48]
      +0x34: mov     w19, #0x0
      +0x38: ldr     x1, [x2]
      +0x3c: str     x1, [sp, #824]
      +0x40: mov     x1, #0x0
      +0x44: bl      mlkem_shake128_init
      +0x48: mov     x1, x23
      +0x4c: mov     x0, x21
      +0x50: mov     x2, #0x22
      +0x54: bl      mlkem_shake128_absorb_once
      +0x58: mov     x1, #0x3
      +0x5c: mov     x2, x21
      +0x60: mov     x0, x20
      +0x64: bl      mlkem_shake128_squeezeblocks
      +0x68: add     x5, x20, #0x1f8
      +0x6c: mov     x1, x20
      +0x70: mov     w7, #0xd00
      +0x74: mov     w6, #0xff
      +0x78: b       loop1
      +0x7c: cmp     w2, #0xd00
      +0x80: ccmp    w19, w6, #0x2, le
      +0x84: b.hi    join2
      +0x88: mov     w3, w19
      +0x8c: add     w19, w3, #0x1
      +0x90: strh    w2, [x22, w3, uxtw #1]
      +0x94: cmp     w19, #0x100
      +0x98: b.eq    join3
      +0x9c: add     x1, x1, #0x3
      +0xa0: cmp     x1, x5
      +0xa4: b.eq    loop1_exit3
      +0xa8: ldrb    w0, [x1, #1]
      +0xac: ldrb    w4, [x1]
      +0xb0: ldrb    w2, [x1, #2]
      +0xb4: lsr     w3, w0, #4
      +0xb8: orr     w0, w4, w0, lsl #8
      +0xbc: and     w0, w0, #0xfff
      +0xc0: orr     w2, w3, w2, lsl #4
      +0xc4: cmp     w0, #0xd00
      +0xc8: b.gt    +0x7c
      +0xcc: add     w3, w19, #0x1
      +0xd0: strh    w0, [x22, w19, uxtw #1]
      +0xd4: cmp     w3, #0xff
      +0xd8: mov     w19, w3
      +0xdc: ccmp    w2, w7, #0x0, ls
      +0xe0: b.le    join1
      +0xe4: cmp     w19, #0x100
      +0xe8: b.ne    join2
      +0xec: nop
      +0xf0: mov     x0, x21
      +0xf4: bl      mlkem_shake128_release
      +0xf8: mov     x0, x20
      +0xfc: mov     x2, #0x1f8
     +0x100: mov     w1, #0x0
     +0x104: bl      memset
     +0x108: adrp    x0, <page>
     +0x10c: ldr     x0, [x0, #4088]  // got_stack_chk_guard
     +0x110: ldr     x2, [sp, #824]
     +0x114: ldr     x1, [x0]
     +0x118: subs    x2, x2, x1
     +0x11c: mov     x1, #0x0
     +0x120: b.ne    +0x1cc
     +0x124: ldp     x19, x20, [sp]
     +0x128: ldp     x21, x22, [sp, #16]
     +0x12c: ldp     x23, x24, [sp, #32]
     +0x130: ldr     x30, [sp, #48]
     +0x134: add     sp, sp, #0x340
     +0x138: ret
     +0x13c: add     x24, x20, #0xa8
     +0x140: mov     w23, #0xd00
     +0x144: nop
     +0x148: mov     x2, x21
     +0x14c: mov     x0, x20
     +0x150: mov     x1, #0x1
     +0x154: bl      mlkem_shake128_squeezeblocks
     +0x158: mov     x2, x20
     +0x15c: b       loop3
     +0x160: cmp     w19, #0xff
     +0x164: ccmp    w3, w23, #0x0, ls
     +0x168: b.gt    join6
     +0x16c: mov     w4, w19
     +0x170: add     w19, w4, #0x1
     +0x174: strh    w3, [x22, w4, uxtw #1]
     +0x178: cmp     w19, #0x100
     +0x17c: b.eq    join3
     +0x180: add     x2, x2, #0x3
     +0x184: cmp     x2, x24
     +0x188: b.eq    loop2
     +0x18c: ldrb    w1, [x2, #1]
     +0x190: ldrb    w5, [x2]
     +0x194: ldrb    w3, [x2, #2]
     +0x198: lsr     w4, w1, #4
     +0x19c: orr     w1, w5, w1, lsl #8
     +0x1a0: and     w1, w1, #0xfff
     +0x1a4: orr     w3, w4, w3, lsl #4
     +0x1a8: cmp     w1, #0xd00
     +0x1ac: b.gt    +0x160
     +0x1b0: add     w4, w19, #0x1
     +0x1b4: strh    w1, [x22, w19, uxtw #1]
     +0x1b8: cmp     w4, #0xff
     +0x1bc: mov     w19, w4
     +0x1c0: ccmp    w3, w23, #0x0, ls
     +0x1c4: b.gt    join5
     +0x1c8: b       join4
     +0x1cc: bl      stack_chk_fail
 ***)

let MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_poly_rej_uniform"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* The two copies of the sampling loop. The first samples from the three     *)
(* blocks in the buffer at X20, from offset 0, with X1 the pointer, X5 its   *)
(* end and X19 the counter, and exits to loop1_exit2 when there are 256      *)
(* coefficients and to loop1_exit3 at the end of the buffer. The second      *)
(* samples from one block at X20 with X2 the pointer and X24 its end, and    *)
(* exits to the same point loop3_exit1 when there are 256 coefficients and   *)
(* to loop2, to squeeze another block, at the end of the buffer.             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O3_LOOP1 =
  { rej_exec = MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O3_EXEC;
    rej_header = "mlkem_poly_rej_uniform_loop1";
    rej_full = "mlkem_poly_rej_uniform_loop1_exit2";
    rej_end = "mlkem_poly_rej_uniform_loop1_exit3";
    rej_ptr = "X1"; rej_endreg = "X5"; rej_ctr = "X19"; rej_out = "X22";
    rej_consts = ["X6",255; "X7",3328];
    rej_fields = "X0","X2";
    rej_regs = ["X0"; "X1"; "X2"; "X3"; "X4"; "X19"] };;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O3_LOOP3 =
  { rej_exec = MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O3_EXEC;
    rej_header = "mlkem_poly_rej_uniform_loop3";
    rej_full = "mlkem_poly_rej_uniform_loop3_exit1";
    rej_end = "mlkem_poly_rej_uniform_loop3_exit2";
    rej_ptr = "X2"; rej_endreg = "X24"; rej_ctr = "X19"; rej_out = "X22";
    rej_consts = ["X23",3328];
    rej_fields = "X1","X3";
    rej_regs = ["X1"; "X2"; "X3"; "X4"; "X5"; "X19"] };;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O3_LOOP1_FULL =
  REJ_LOOP_FULL MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O3_LOOP1;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O3_LOOP1_CORRECT =
  REJ_LOOP_CORRECT MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O3_LOOP1
   MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O3_LOOP1_FULL;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O3_LOOP3_FULL =
  REJ_LOOP_FULL MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O3_LOOP3;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O3_LOOP3_CORRECT =
  REJ_LOOP_CORRECT MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O3_LOOP3
   MLKEM_NATIVE_POLY_REJ_UNIFORM_GCC12_O3_LOOP3_FULL;;
