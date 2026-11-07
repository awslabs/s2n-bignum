(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 4 bits per coefficient. This is the    *)
(* code for mlkem_poly_decompress_d4 from mlkem-native's portable C          *)
(* implementation compiled by clang 17 with -O3 (see mlkem_native/README.md).*)
(* It is verified in the whole image (see libmlkem.ml).                      *)
(*                                                                           *)
(* The compiler has vectorized the loop completely, with a vector of 3329    *)
(* made by DUP, after a check that the input and the output do not overlap,  *)
(* with one branch for each of the two orders of the arrays; if they         *)
(* overlap, the code falls back to a scalar loop. Since the specification    *)
(* requires them not to overlap, only the vector code runs. Unlike at gcc    *)
(* -O3, it reads no constants from the read-only data and so, as at gcc -O2, *)
(* the safety theorem has no read-only region.                               *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/overlap.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_decompress_d4:
       +0x0: add     x8, x1, #0x80
       +0x4: cmp     x8, x0
       +0x8: b.ls    <mlkem_poly_decompress_d4+0x60>
       +0xc: add     x8, x0, #0x200
      +0x10: cmp     x8, x1
      +0x14: b.ls    join1                       ---+
      +0x18: mov     x8, xzr                        |
      +0x1c: add     x9, x0, #0x2                   |
      +0x20: mov     w10, #0xd01                    |
      +0x24: mov     w11, #0x8                      |
      +0x28: ldrb    w12, [x1, x8]               <+ |
      +0x2c: and     w12, w12, #0xf               | |
      +0x30: madd    w12, w12, w10, w11           | |
      +0x34: lsr     w12, w12, #4                 | |
      +0x38: sturh   w12, [x9, #-2]               | |
      +0x3c: ldrb    w12, [x1, x8]                | |
      +0x40: add     x8, x8, #0x1                 | |
      +0x44: cmp     x8, #0x80                    | |
      +0x48: lsr     w12, w12, #4                 | |
      +0x4c: madd    w12, w12, w10, w11           | |
      +0x50: lsr     w12, w12, #4                 | |
      +0x54: strh    w12, [x9], #4                | |
      +0x58: b.ne    loop1                       -+ |
      +0x5c: ret                                    |
      +0x60: movi    v1.16b, #0xf
      +0x64: ldr     q2, [x1]
      +0x68: mov     w8, #0xd01
      +0x6c: add     x9, x0, #0x1e0
      +0x70: ushr    v3.16b, v2.16b, #4
      +0x74: and     v2.16b, v2.16b, v1.16b
      +0x78: dup     v0.8h, w8
      +0x7c: uxtl2   v4.8h, v2.16b
      +0x80: mov     x8, x0
      +0x84: uxtl    v2.8h, v2.8b
      +0x88: uxtl2   v5.8h, v3.16b
      +0x8c: umull   v6.4s, v2.4h, v0.4h
      +0x90: uxtl    v3.8h, v3.8b
      +0x94: umull2  v2.4s, v2.8h, v0.8h
      +0x98: umull2  v7.4s, v4.8h, v0.8h
      +0x9c: rshrn   v16.4h, v6.4s, #4
      +0xa0: umull   v6.4s, v3.4h, v0.4h
      +0xa4: umull   v4.4s, v4.4h, v0.4h
      +0xa8: umull2  v3.4s, v3.8h, v0.8h
      +0xac: rshrn2  v16.8h, v2.4s, #4
      +0xb0: rshrn   v17.4h, v6.4s, #4
      +0xb4: umull   v2.4s, v5.4h, v0.4h
      +0xb8: rshrn   v18.4h, v4.4s, #4
      +0xbc: umull2  v4.4s, v5.8h, v0.8h
      +0xc0: rshrn2  v17.8h, v3.4s, #4
      +0xc4: rshrn2  v18.8h, v7.4s, #4
      +0xc8: rshrn   v19.4h, v2.4s, #4
      +0xcc: st2     {v16.8h-v17.8h}, [x8], #32
      +0xd0: rshrn2  v19.8h, v4.4s, #4
      +0xd4: st2     {v18.8h-v19.8h}, [x8]
      +0xd8: add     x8, x0, #0x40
      +0xdc: ldr     q2, [x1, #16]
      +0xe0: and     v3.16b, v2.16b, v1.16b
      +0xe4: ushr    v2.16b, v2.16b, #4
      +0xe8: uxtl2   v4.8h, v3.16b
      +0xec: uxtl    v3.8h, v3.8b
      +0xf0: uxtl2   v5.8h, v2.16b
      +0xf4: umull   v6.4s, v3.4h, v0.4h
      +0xf8: uxtl    v2.8h, v2.8b
      +0xfc: umull2  v3.4s, v3.8h, v0.8h
      +0x100: umull2  v7.4s, v4.8h, v0.8h
      +0x104: umull   v4.4s, v4.4h, v0.4h
      +0x108: rshrn   v16.4h, v6.4s, #4
      +0x10c: umull   v6.4s, v2.4h, v0.4h
      +0x110: umull2  v2.4s, v2.8h, v0.8h
      +0x114: rshrn2  v16.8h, v3.4s, #4
      +0x118: rshrn   v3.4h, v4.4s, #4
      +0x11c: rshrn   v17.4h, v6.4s, #4
      +0x120: umull   v6.4s, v5.4h, v0.4h
      +0x124: umull2  v5.4s, v5.8h, v0.8h
      +0x128: rshrn2  v3.8h, v7.4s, #4
      +0x12c: rshrn2  v17.8h, v2.4s, #4
      +0x130: rshrn   v4.4h, v6.4s, #4
      +0x134: st2     {v16.8h-v17.8h}, [x8]
      +0x138: add     x8, x0, #0x60
      +0x13c: rshrn2  v4.8h, v5.4s, #4
      +0x140: st2     {v3.8h-v4.8h}, [x8]
      +0x144: add     x8, x0, #0x80
      +0x148: ldr     q2, [x1, #32]
      +0x14c: and     v3.16b, v2.16b, v1.16b
      +0x150: ushr    v2.16b, v2.16b, #4
      +0x154: uxtl2   v4.8h, v3.16b
      +0x158: uxtl    v3.8h, v3.8b
      +0x15c: uxtl2   v5.8h, v2.16b
      +0x160: umull   v6.4s, v3.4h, v0.4h
      +0x164: uxtl    v2.8h, v2.8b
      +0x168: umull2  v3.4s, v3.8h, v0.8h
      +0x16c: umull2  v7.4s, v4.8h, v0.8h
      +0x170: umull   v4.4s, v4.4h, v0.4h
      +0x174: rshrn   v16.4h, v6.4s, #4
      +0x178: umull   v6.4s, v2.4h, v0.4h
      +0x17c: umull2  v2.4s, v2.8h, v0.8h
      +0x180: rshrn2  v16.8h, v3.4s, #4
      +0x184: rshrn   v3.4h, v4.4s, #4
      +0x188: rshrn   v17.4h, v6.4s, #4
      +0x18c: umull   v6.4s, v5.4h, v0.4h
      +0x190: umull2  v5.4s, v5.8h, v0.8h
      +0x194: rshrn2  v3.8h, v7.4s, #4
      +0x198: rshrn2  v17.8h, v2.4s, #4
      +0x19c: rshrn   v4.4h, v6.4s, #4
      +0x1a0: st2     {v16.8h-v17.8h}, [x8]
      +0x1a4: add     x8, x0, #0xa0
      +0x1a8: rshrn2  v4.8h, v5.4s, #4
      +0x1ac: st2     {v3.8h-v4.8h}, [x8]
      +0x1b0: add     x8, x0, #0xc0
      +0x1b4: ldr     q2, [x1, #48]
      +0x1b8: and     v3.16b, v2.16b, v1.16b
      +0x1bc: ushr    v2.16b, v2.16b, #4
      +0x1c0: uxtl2   v4.8h, v3.16b
      +0x1c4: uxtl    v3.8h, v3.8b
      +0x1c8: uxtl2   v5.8h, v2.16b
      +0x1cc: umull   v6.4s, v3.4h, v0.4h
      +0x1d0: uxtl    v2.8h, v2.8b
      +0x1d4: umull2  v3.4s, v3.8h, v0.8h
      +0x1d8: umull2  v7.4s, v4.8h, v0.8h
      +0x1dc: umull   v4.4s, v4.4h, v0.4h
      +0x1e0: rshrn   v16.4h, v6.4s, #4
      +0x1e4: umull   v6.4s, v2.4h, v0.4h
      +0x1e8: umull2  v2.4s, v2.8h, v0.8h
      +0x1ec: rshrn2  v16.8h, v3.4s, #4
      +0x1f0: rshrn   v3.4h, v4.4s, #4
      +0x1f4: rshrn   v17.4h, v6.4s, #4
      +0x1f8: umull   v6.4s, v5.4h, v0.4h
      +0x1fc: umull2  v5.4s, v5.8h, v0.8h
      +0x200: rshrn2  v3.8h, v7.4s, #4
      +0x204: rshrn2  v17.8h, v2.4s, #4
      +0x208: rshrn   v4.4h, v6.4s, #4
      +0x20c: st2     {v16.8h-v17.8h}, [x8]
      +0x210: add     x8, x0, #0xe0
      +0x214: rshrn2  v4.8h, v5.4s, #4
      +0x218: st2     {v3.8h-v4.8h}, [x8]
      +0x21c: add     x8, x0, #0x100
      +0x220: ldr     q2, [x1, #64]
      +0x224: and     v3.16b, v2.16b, v1.16b
      +0x228: ushr    v2.16b, v2.16b, #4
      +0x22c: uxtl2   v4.8h, v3.16b
      +0x230: uxtl    v3.8h, v3.8b
      +0x234: uxtl2   v5.8h, v2.16b
      +0x238: umull   v6.4s, v3.4h, v0.4h
      +0x23c: uxtl    v2.8h, v2.8b
      +0x240: umull2  v3.4s, v3.8h, v0.8h
      +0x244: umull2  v7.4s, v4.8h, v0.8h
      +0x248: umull   v4.4s, v4.4h, v0.4h
      +0x24c: rshrn   v16.4h, v6.4s, #4
      +0x250: umull   v6.4s, v2.4h, v0.4h
      +0x254: umull2  v2.4s, v2.8h, v0.8h
      +0x258: rshrn2  v16.8h, v3.4s, #4
      +0x25c: rshrn   v3.4h, v4.4s, #4
      +0x260: rshrn   v17.4h, v6.4s, #4
      +0x264: umull   v6.4s, v5.4h, v0.4h
      +0x268: umull2  v5.4s, v5.8h, v0.8h
      +0x26c: rshrn2  v3.8h, v7.4s, #4
      +0x270: rshrn2  v17.8h, v2.4s, #4
      +0x274: rshrn   v4.4h, v6.4s, #4
      +0x278: st2     {v16.8h-v17.8h}, [x8]
      +0x27c: add     x8, x0, #0x120
      +0x280: rshrn2  v4.8h, v5.4s, #4
      +0x284: st2     {v3.8h-v4.8h}, [x8]
      +0x288: add     x8, x0, #0x140
      +0x28c: ldr     q2, [x1, #80]
      +0x290: and     v3.16b, v2.16b, v1.16b
      +0x294: ushr    v2.16b, v2.16b, #4
      +0x298: uxtl2   v4.8h, v3.16b
      +0x29c: uxtl    v3.8h, v3.8b
      +0x2a0: uxtl2   v5.8h, v2.16b
      +0x2a4: umull   v6.4s, v3.4h, v0.4h
      +0x2a8: uxtl    v2.8h, v2.8b
      +0x2ac: umull2  v3.4s, v3.8h, v0.8h
      +0x2b0: umull2  v7.4s, v4.8h, v0.8h
      +0x2b4: umull   v4.4s, v4.4h, v0.4h
      +0x2b8: rshrn   v16.4h, v6.4s, #4
      +0x2bc: umull   v6.4s, v2.4h, v0.4h
      +0x2c0: umull2  v2.4s, v2.8h, v0.8h
      +0x2c4: rshrn2  v16.8h, v3.4s, #4
      +0x2c8: rshrn   v3.4h, v4.4s, #4
      +0x2cc: rshrn   v17.4h, v6.4s, #4
      +0x2d0: umull   v6.4s, v5.4h, v0.4h
      +0x2d4: umull2  v5.4s, v5.8h, v0.8h
      +0x2d8: rshrn2  v3.8h, v7.4s, #4
      +0x2dc: rshrn2  v17.8h, v2.4s, #4
      +0x2e0: rshrn   v4.4h, v6.4s, #4
      +0x2e4: st2     {v16.8h-v17.8h}, [x8]
      +0x2e8: add     x8, x0, #0x160
      +0x2ec: rshrn2  v4.8h, v5.4s, #4
      +0x2f0: st2     {v3.8h-v4.8h}, [x8]
      +0x2f4: add     x8, x0, #0x180
      +0x2f8: ldr     q2, [x1, #96]
      +0x2fc: and     v3.16b, v2.16b, v1.16b
      +0x300: ushr    v2.16b, v2.16b, #4
      +0x304: uxtl2   v4.8h, v3.16b
      +0x308: uxtl    v3.8h, v3.8b
      +0x30c: uxtl2   v5.8h, v2.16b
      +0x310: umull   v6.4s, v3.4h, v0.4h
      +0x314: uxtl    v2.8h, v2.8b
      +0x318: umull2  v3.4s, v3.8h, v0.8h
      +0x31c: umull   v7.4s, v4.4h, v0.4h
      +0x320: rshrn   v16.4h, v6.4s, #4
      +0x324: umull   v6.4s, v2.4h, v0.4h
      +0x328: umull2  v4.4s, v4.8h, v0.8h
      +0x32c: rshrn2  v16.8h, v3.4s, #4
      +0x330: rshrn   v18.4h, v7.4s, #4
      +0x334: umull2  v2.4s, v2.8h, v0.8h
      +0x338: rshrn   v17.4h, v6.4s, #4
      +0x33c: umull   v3.4s, v5.4h, v0.4h
      +0x340: rshrn2  v18.8h, v4.4s, #4
      +0x344: umull2  v4.4s, v5.8h, v0.8h
      +0x348: rshrn2  v17.8h, v2.4s, #4
      +0x34c: rshrn   v19.4h, v3.4s, #4
      +0x350: st2     {v16.8h-v17.8h}, [x8]
      +0x354: add     x8, x0, #0x1a0
      +0x358: rshrn2  v19.8h, v4.4s, #4
      +0x35c: st2     {v18.8h-v19.8h}, [x8]
      +0x360: add     x8, x0, #0x1c0
      +0x364: ldr     q2, [x1, #112]
      +0x368: and     v1.16b, v2.16b, v1.16b
      +0x36c: ushr    v2.16b, v2.16b, #4
      +0x370: uxtl2   v3.8h, v1.16b
      +0x374: uxtl    v1.8h, v1.8b
      +0x378: umull2  v6.4s, v3.8h, v0.8h
      +0x37c: umull   v5.4s, v1.4h, v0.4h
      +0x380: umull2  v1.4s, v1.8h, v0.8h
      +0x384: umull   v3.4s, v3.4h, v0.4h
      +0x388: uxtl2   v4.8h, v2.16b
      +0x38c: rshrn   v16.4h, v5.4s, #4
      +0x390: uxtl    v2.8h, v2.8b
      +0x394: rshrn   v18.4h, v3.4s, #4
      +0x398: umull   v5.4s, v2.4h, v0.4h
      +0x39c: rshrn2  v16.8h, v1.4s, #4
      +0x3a0: umull   v1.4s, v4.4h, v0.4h
      +0x3a4: umull2  v2.4s, v2.8h, v0.8h
      +0x3a8: umull2  v0.4s, v4.8h, v0.8h
      +0x3ac: rshrn2  v18.8h, v6.4s, #4
      +0x3b0: rshrn   v17.4h, v5.4s, #4
      +0x3b4: rshrn   v19.4h, v1.4s, #4
      +0x3b8: rshrn2  v17.8h, v2.4s, #4
      +0x3bc: rshrn2  v19.8h, v0.4s, #4
      +0x3c0: st2     {v16.8h-v17.8h}, [x8]
      +0x3c4: st2     {v18.8h-v19.8h}, [x9]
      +0x3c8: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_decompress_d4"];;

(* ------------------------------------------------------------------------- *)
(* The computation of the 16-bit lanes for the low and high 4-bit fields of  *)
(* a byte b, as the vector code does it with AND and USHR, UXTL, MLA with    *)
(* 3329 on top of 8 and USHR #4, checked for all values of the byte.         *)
(* ------------------------------------------------------------------------- *)

let D4_LANES_STMT =
  `!b:byte.
     word_ushr
      (word_add (word 8)
        (word_mul (word_shl (word_zx (word_and (word 15) b)) 0)
                  (word 3329))) 4:int16 =
     word((3329 * val b MOD 16 + 8) DIV 16) /\
     word_ushr
      (word_add (word 8)
        (word_mul (word_shl (word_zx (word_ushr b 4)) 0) (word 3329))) 4:int16 =
     word((3329 * val b DIV 16 + 8) DIV 16)`;;

let D4_LANES = assume_spec D4_LANES_STMT;;

(*** The 4-bit fields of a byte of the input given as a number ***)

let D4_NIBBLES_STMT =
  `(!n k. ((n DIV 2 EXP k) MOD 256) MOD 16 = (n DIV 2 EXP k) MOD 2 EXP 4) /\
   (!n k. ((n DIV 2 EXP k) MOD 256) DIV 16 =
          (n DIV 2 EXP (k + 4)) MOD 2 EXP 4)`;;

let D4_NIBBLES = assume_spec D4_NIBBLES_STMT;;

(*** The 128-bit loads of the input from its bytes b j ***)

let D4_MERGES = map (fun k ->
  let addr = if k = 0 then `a:int64` else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`a:int64`),
            mk_comb(`word:num->int64`, mk_small_numeral(16 * k))) in
  READ_MEMORY_MERGE_CONV 4
   (vsubst [addr,`x:int64`] `read (memory :> bytes128 x) s0`)) (0--7);;

let D4_INPUT_TAC =
  SUBGOAL_THEN
   `?b:num->byte. (!j. word((n DIV 2 EXP (8 * j)) MOD 256) = b j) /\
                  (!j. val(b j) = (n DIV 2 EXP (8 * j)) MOD 256)`
   STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\j. word((n DIV 2 EXP (8 * j)) MOD 256):byte` THEN
    REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < 128 ==> read (memory :> bytes8 (word_add a (word j))) s0 = b j`
   MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && is_eq(snd(dest_forall(concl th))) &&
         is_comb(rhs(snd(dest_forall(concl th)))) &&
         rator(rhs(snd(dest_forall(concl th)))) = `b:num->byte`
      then SUBST1_TAC(SYM(SPEC `j:num` th)) THEN ASSUME_TAC th
      else NO_TAC) THEN
    MP_TAC(SPECL [`a:int64`; `128`; `n:num`; `j:num`; `s0:armstate`]
                 READ_MEMORY_BYTES8_OF_NUM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  MAP_EVERY MP_TAC D4_MERGES THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes8 a) s = x`];;

(*** The 32-byte stores, as the 16 coefficients in each: each 16-bit part
 *** of a store is one of the lanes, found by bit-blasting, and its value
 *** is given by D4_LANES ***)

let D4_LANES2_STMT =
  `!b:byte.
     word((val(word_mul (word_zx (word_shl (word_zx (word_ushr b 4):int16) 0):
                         int32) (word 3329)) + 8) DIV 16):int16 =
     word((3329 * val b DIV 16 + 8) DIV 16) /\
     word((val(word_mul (word_zx (word_shl (word_zx (word_and (word 15) b):
                                            int16) 0):int32)
                        (word 3329)) + 8) DIV 16):int16 =
     word((3329 * val b MOD 16 + 8) DIV 16)`;;

let D4_LANES2 = assume_spec D4_LANES2_STMT;;

(*** The 32-byte stores, as the 16 coefficients in each: each 16-bit part
 *** of a store is one of the lanes, found by bit-blasting, and its value
 *** is given by D4_LANES2 ***)

let d4_lanepat = `word((3329 * x + 8) DIV 16):int16`;;

let D4_LANE_RULE th =
  let th = CONV_RULE(RAND_CONV(REWRITE_CONV[D4_LANES2])) th in
  let v = rand(concl th) in
  let ls = setify(find_terms (can (term_match [] d4_lanepat)) v) in
  let gs = map (fun t -> genvar(type_of t)) ls in
  let v' = subst (zip gs ls) v in
  let bth = tryfind (fun g -> BITBLAST_RULE(mk_eq(v',g))) gs in
  CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]))
   (TRANS th (INST (zip ls gs) bth));;

let D4_STORES_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
    check (can (term_match [] `read (memory :> bytes256 a) s = x`) o
           concl))) THEN
  REPEAT(DISCH_THEN(fun th ->
    MAP_EVERY (ASSUME_TAC o D4_LANE_RULE) (CONJUNCTS th)));;

(* ------------------------------------------------------------------------- *)
(* The check for overlap has one branch for each order of the arrays: with   *)
(* the input a (128 bytes) and the output r (512 bytes), the scalar loop is  *)
(* taken unless a + 128 <= r or r + 512 <= a. In either case the vector code *)
(* is entered at the same instruction, after 3 or 6 steps respectively.      *)
(* ------------------------------------------------------------------------- *)

let D4_RESOLVE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_FLAG; VAL_WORD_SUB_EQ_0]) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read PC s = if p then x else y`) c then
      let p = rand(rator(rator(rand c))) in
      let decide q = SUBGOAL_THEN q (fun th' ->
        ASSUME_TAC(REWRITE_RULE[th'] th)) THENL [ASM_ARITH_TAC; ALL_TAC] in
      decide p ORELSE decide (mk_neg p)
    else failwith "D4_RESOLVE_TAC");;

let D4_CHECK_TAC (body:int->tactic) =
  MP_TAC(SPECL [`r:int64`; `a:int64`; `512`; `128`]
                NONOVERLAPPING_ALIAS_CHECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_CLANG17_O3_EXEC (1--3) THEN
  ASM_CASES_TAC `val(word_add a (word 128):int64) <= val(r:int64)` THENL
   [D4_RESOLVE_TAC THEN body 3;
    D4_RESOLVE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_CLANG17_O3_EXEC (4--6) THEN
    D4_RESOLVE_TAC THEN body 6];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 4 in common/fips203.ml, the    *)
(* result for a 4-bit field y is the integer closest to 3329 * y / 16,       *)
(* rounding up on ties, i.e. (3329 * y + 8) DIV 16.                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,128)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                  read PC s = word (pc + mlkem_poly_decompress_d4) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,128)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((3329 * (n DIV 2 EXP (4 * i)) MOD 2 EXP 4 + 8)
                               DIV 16))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,128]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_poly_decompress_d4) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2 [a,128; r,512] [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_DECOMPRESS_D4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
