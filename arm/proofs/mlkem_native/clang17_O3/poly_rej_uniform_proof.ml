(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of a polynomial from a seed by rejection. This is the    *)
(* code for mlkem_poly_rej_uniform from mlkem-native's portable C            *)
(* implementation compiled by clang 17 with -O3 (see                         *)
(* mlkem_native/README.md), which absorbs the 34 bytes of the seed into a    *)
(* SHAKE128 state, squeezes three blocks of 168 bytes and samples the        *)
(* coefficients below 3329 from them, and then squeezes one more block and   *)
(* samples from it until there are 256, before zeroing the state and the     *)
(* buffer. As at gcc -O3, the sampling of mlk_rej_uniform_c is inlined, as   *)
(* two copies of its loop, one for the first three blocks (loop1) and one    *)
(* for each further block (loop3, inside the loop loop2 that squeezes the    *)
(* blocks). The code is in the whole image (see libmlkem.ml), and the two    *)
(* copies of the loop are verified there with the tool in rej_uniform.ml.    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/clang17_O3/rej_uniform_proof.ml";;

(*** The code in the image:

    mlkem_poly_rej_uniform:
       +0x0: stp     x29, x30, [sp, #-48]!
       +0x4: stp     x28, x21, [sp, #16]
       +0x8: stp     x20, x19, [sp, #32]
       +0xc: mov     x29, sp
      +0x10: sub     x9, sp, #0x2f0
      +0x14: and     sp, x9, #0xffffffffffffffe0
      +0x18: adrp    x8, <page>
      +0x1c: mov     x19, x0
      +0x20: add     x0, sp, #0x200
      +0x24: mov     x20, x1
      +0x28: ldr     x8, [x8, #4088]  // got_stack_chk_guard
      +0x2c: ldr     x8, [x8]
      +0x30: str     x8, [sp, #744]
      +0x34: bl      <mlkem_shake128_init>
      +0x38: add     x0, sp, #0x200
      +0x3c: mov     x1, x20
      +0x40: mov     w2, #0x22
      +0x44: bl      <mlkem_shake128_absorb_once>
      +0x48: mov     x0, sp
      +0x4c: add     x2, sp, #0x200
      +0x50: mov     w1, #0x3
      +0x54: mov     x21, sp
      +0x58: bl      <mlkem_shake128_squeezeblocks>
      +0x5c: mov     x8, xzr
      +0x60: mov     x20, xzr
      +0x64: add     x9, x21, x8
      +0x68: ldrb    w11, [x9]
      +0x6c: ldrb    w10, [x9, #1]
      +0x70: bfi     w11, w10, #8, #4
      +0x74: cmp     w11, #0xd00
      +0x78: b.hi    <mlkem_poly_rej_uniform+0x88>
      +0x7c: add     x12, x20, #0x1
      +0x80: strh    w11, [x19, x20, lsl #1]
      +0x84: mov     x20, x12
      +0x88: cmp     x20, #0xff
      +0x8c: b.hi    <mlkem_poly_rej_uniform+0xb0>
      +0x90: ldrb    w9, [x9, #2]
      +0x94: lsr     w10, w10, #4
      +0x98: orr     w9, w10, w9, lsl #4
      +0x9c: cmp     w9, #0xd00
      +0xa0: b.hi    <mlkem_poly_rej_uniform+0xb0>
      +0xa4: add     x10, x20, #0x1
      +0xa8: strh    w9, [x19, x20, lsl #1]
      +0xac: mov     x20, x10
      +0xb0: cmp     x20, #0xff
      +0xb4: b.hi    <mlkem_poly_rej_uniform+0xc8>
      +0xb8: add     x9, x8, #0x3
      +0xbc: add     x8, x8, #0x3
      +0xc0: cmp     x9, #0x1f6
      +0xc4: b.cc    <mlkem_poly_rej_uniform+0x64>
      +0xc8: cmp     x20, #0xff
      +0xcc: b.hi    <mlkem_poly_rej_uniform+0x15c>
      +0xd0: mov     x21, sp
      +0xd4: b       <mlkem_poly_rej_uniform+0xe0>
      +0xd8: cmp     x20, #0x100
      +0xdc: b.cs    <mlkem_poly_rej_uniform+0x15c>
      +0xe0: mov     x0, sp
      +0xe4: add     x2, sp, #0x200
      +0xe8: mov     w1, #0x1
      +0xec: bl      <mlkem_shake128_squeezeblocks>
      +0xf0: mov     x8, xzr
      +0xf4: add     x10, x21, x8
      +0xf8: ldrb    w11, [x10]
      +0xfc: ldrb    w9, [x10, #1]
     +0x100: ldrb    w10, [x10, #2]
     +0x104: bfi     w11, w9, #8, #4
     +0x108: cmp     w11, #0xd00
     +0x10c: b.hi    <mlkem_poly_rej_uniform+0x11c>
     +0x110: add     x12, x20, #0x1
     +0x114: strh    w11, [x19, x20, lsl #1]
     +0x118: mov     x20, x12
     +0x11c: cmp     x20, #0xff
     +0x120: b.hi    <mlkem_poly_rej_uniform+0x140>
     +0x124: lsr     w9, w9, #4
     +0x128: orr     w9, w9, w10, lsl #4
     +0x12c: cmp     w9, #0xd00
     +0x130: b.hi    <mlkem_poly_rej_uniform+0x140>
     +0x134: add     x10, x20, #0x1
     +0x138: strh    w9, [x19, x20, lsl #1]
     +0x13c: mov     x20, x10
     +0x140: cmp     x20, #0xff
     +0x144: b.hi    <mlkem_poly_rej_uniform+0xd8>
     +0x148: add     x9, x8, #0x3
     +0x14c: add     x8, x8, #0x3
     +0x150: cmp     x9, #0xa6
     +0x154: b.cc    <mlkem_poly_rej_uniform+0xf4>
     +0x158: b       <mlkem_poly_rej_uniform+0xd8>
     +0x15c: add     x0, sp, #0x200
     +0x160: bl      <mlkem_shake128_release>
     +0x164: movi    v0.2d, #0x0
     +0x168: str     xzr, [sp, #496]
     +0x16c: mov     x8, sp
     +0x170: stp     q0, q0, [sp, #16]
     +0x174: stp     q0, q0, [sp, #48]
     +0x178: stp     q0, q0, [sp, #80]
     +0x17c: stp     q0, q0, [sp, #112]
     +0x180: stp     q0, q0, [sp, #144]
     +0x184: stp     q0, q0, [sp, #176]
     +0x188: stp     q0, q0, [sp, #208]
     +0x18c: stp     q0, q0, [sp, #240]
     +0x190: stp     q0, q0, [sp, #272]
     +0x194: stp     q0, q0, [sp, #304]
     +0x198: stp     q0, q0, [sp, #336]
     +0x19c: stp     q0, q0, [sp, #368]
     +0x1a0: stp     q0, q0, [sp, #400]
     +0x1a4: stp     q0, q0, [sp, #432]
     +0x1a8: stp     q0, q0, [sp, #464]
     +0x1ac: str     q0, [sp]
     +0x1b0: adrp    x8, <page>
     +0x1b4: ldr     x8, [x8, #4088]  // got_stack_chk_guard
     +0x1b8: ldr     x9, [sp, #744]
     +0x1bc: ldr     x8, [x8]
     +0x1c0: cmp     x8, x9
     +0x1c4: b.ne    <mlkem_poly_rej_uniform+0x1dc>
     +0x1c8: mov     sp, x29
     +0x1cc: ldp     x20, x19, [sp, #32]
     +0x1d0: ldp     x28, x21, [sp, #16]
     +0x1d4: ldp     x29, x30, [sp], #48
     +0x1d8: ret     
     +0x1dc: bl      <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_rej_uniform"];;

(* ------------------------------------------------------------------------- *)
(* The two copies of the sampling loop. The first samples from the three     *)
(* blocks in the buffer at X21, from offset 0, with X8 the index and X20 the *)
(* counter, and exits to loop1_exit both when there are 256 coefficients and *)
(* at the end of the buffer. The second samples from one block at X21 in the *)
(* same way, and exits to loop3_exit1 when there are 256 coefficients and to *)
(* loop3_exit2, which branches to loop3_exit1, at the end of the buffer.     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O3_LOOP1 =
  { rej_exec = MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O3_EXEC;
    rej_header = "mlkem_poly_rej_uniform_loop1";
    rej_full = "mlkem_poly_rej_uniform_loop1_exit";
    rej_end = "mlkem_poly_rej_uniform_loop1_exit";
    rej_base = "X21"; rej_ofs = 0; rej_idx = "X8"; rej_buflen = 504;
    rej_ctr = "X20"; rej_out = "X19";
    rej_fields = "X11","X9"; rej_flag = None;
    rej_regs = ["X8"; "X9"; "X10"; "X11"; "X12"; "X20"] };;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O3_LOOP3 =
  { rej_exec = MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O3_EXEC;
    rej_header = "mlkem_poly_rej_uniform_loop3";
    rej_full = "mlkem_poly_rej_uniform_loop3_exit1";
    rej_end = "mlkem_poly_rej_uniform_loop3_exit2";
    rej_base = "X21"; rej_ofs = 0; rej_idx = "X8"; rej_buflen = 168;
    rej_ctr = "X20"; rej_out = "X19";
    rej_fields = "X11","X9"; rej_flag = None;
    rej_regs = ["X8"; "X9"; "X10"; "X11"; "X12"; "X20"] };;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O3_LOOP1_FULL =
  REJ_LOOP_FULL MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O3_LOOP1;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O3_LOOP1_CORRECT =
  REJ_LOOP_CORRECT MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O3_LOOP1
   MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O3_LOOP1_FULL;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O3_LOOP3_FULL =
  REJ_LOOP_FULL MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O3_LOOP3;;

let MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O3_LOOP3_CORRECT =
  REJ_LOOP_CORRECT MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O3_LOOP3
   MLKEM_NATIVE_POLY_REJ_UNIFORM_CLANG17_O3_LOOP3_FULL;;
