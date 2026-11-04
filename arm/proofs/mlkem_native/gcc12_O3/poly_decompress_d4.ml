(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decompression of a polynomial from 4 bits per coefficient. This is the    *)
(* code for mlkem_poly_decompress_d4 from mlkem-native's portable C          *)
(* implementation compiled by gcc 12 with -O3 (see mlkem_native/README.md).  *)
(* It is verified in the whole image (see libmlkem.ml).                      *)
(*                                                                           *)
(* The compiler has vectorized the loop completely, with a vector of 3329    *)
(* from the read-only data, after a check that the input and the output do   *)
(* not overlap; if they do, the code falls back to the scalar loop of -O2.   *)
(* Since the specification requires them not to overlap, only the vector     *)
(* code runs. The safety theorem therefore has the 16 bytes of constants     *)
(* among the regions read, unlike that of gcc12_O2.                          *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/utils/mlkem_native_overlap.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_decompress_d4:
       +0x0: add     x4, x0, #0x200
       +0x4: add     x2, x1, #0x80
       +0x8: cmp     x1, x4
       +0xc: ccmp    x0, x2, #0x2, cc
      +0x10: b.cc    <mlkem_poly_decompress_d4+0x2fc>
      +0x14: ldr     q7, [x1]
      +0x18: adrp    x2, <page>
      +0x1c: movi    v0.8h, #0x8
      +0x20: add     x15, x0, #0x40
      +0x24: movi    v6.16b, #0xf
      +0x28: add     x14, x0, #0x60
      +0x2c: ushr    v16.16b, v7.16b, #4
      +0x30: add     x13, x0, #0x80
      +0x34: ldr     q1, [x2, #2368]  // mlkem_poly_decompress_d4_consts
      +0x38: add     x12, x0, #0xa0
      +0x3c: and     v7.16b, v7.16b, v6.16b
      +0x40: add     x11, x0, #0xc0
      +0x44: uxtl    v19.8h, v16.8b
      +0x48: add     x10, x0, #0xe0
      +0x4c: mov     v17.16b, v0.16b
      +0x50: add     x9, x0, #0x100
      +0x54: uxtl2   v16.8h, v16.16b
      +0x58: add     x8, x0, #0x120
      +0x5c: uxtl    v18.8h, v7.8b
      +0x60: add     x7, x0, #0x140
      +0x64: uxtl2   v7.8h, v7.16b
      +0x68: add     x6, x0, #0x160
      +0x6c: mla     v17.8h, v19.8h, v1.8h
      +0x70: add     x5, x0, #0x180
      +0x74: mov     v19.16b, v0.16b
      +0x78: add     x4, x0, #0x1a0
      +0x7c: add     x3, x0, #0x1c0
      +0x80: add     x2, x0, #0x1e0
      +0x84: ushr    v5.8h, v17.8h, #4
      +0x88: mla     v19.8h, v18.8h, v1.8h
      +0x8c: mov     v18.16b, v0.16b
      +0x90: ushr    v4.8h, v19.8h, #4
      +0x94: mla     v18.8h, v7.8h, v1.8h
      +0x98: mov     v7.16b, v0.16b
      +0x9c: mov     v19.16b, v0.16b
      +0xa0: st2     {v4.8h-v5.8h}, [x0], #32
      +0xa4: mla     v7.8h, v16.8h, v1.8h
      +0xa8: ushr    v2.8h, v18.8h, #4
      +0xac: mov     v18.16b, v0.16b
      +0xb0: ushr    v3.8h, v7.8h, #4
      +0xb4: st2     {v2.8h-v3.8h}, [x0]
      +0xb8: ldr     q7, [x1, #16]
      +0xbc: and     v16.16b, v7.16b, v6.16b
      +0xc0: ushr    v7.16b, v7.16b, #4
      +0xc4: uxtl    v17.8h, v16.8b
      +0xc8: uxtl2   v16.8h, v16.16b
      +0xcc: uxtl    v20.8h, v7.8b
      +0xd0: uxtl2   v7.8h, v7.16b
      +0xd4: mla     v19.8h, v17.8h, v1.8h
      +0xd8: mov     v17.16b, v0.16b
      +0xdc: mla     v18.8h, v16.8h, v1.8h
      +0xe0: mov     v16.16b, v0.16b
      +0xe4: ushr    v4.8h, v19.8h, #4
      +0xe8: mla     v17.8h, v20.8h, v1.8h
      +0xec: ushr    v2.8h, v18.8h, #4
      +0xf0: mla     v16.8h, v7.8h, v1.8h
      +0xf4: mov     v19.16b, v0.16b
      +0xf8: ushr    v5.8h, v17.8h, #4
      +0xfc: mov     v18.16b, v0.16b
     +0x100: ushr    v3.8h, v16.8h, #4
     +0x104: st2     {v4.8h-v5.8h}, [x15]
     +0x108: st2     {v2.8h-v3.8h}, [x14]
     +0x10c: ldr     q7, [x1, #32]
     +0x110: and     v16.16b, v7.16b, v6.16b
     +0x114: ushr    v7.16b, v7.16b, #4
     +0x118: uxtl    v17.8h, v16.8b
     +0x11c: uxtl2   v16.8h, v16.16b
     +0x120: uxtl    v20.8h, v7.8b
     +0x124: uxtl2   v7.8h, v7.16b
     +0x128: mla     v19.8h, v17.8h, v1.8h
     +0x12c: mov     v17.16b, v0.16b
     +0x130: mla     v18.8h, v16.8h, v1.8h
     +0x134: mov     v16.16b, v0.16b
     +0x138: ushr    v4.8h, v19.8h, #4
     +0x13c: mla     v17.8h, v20.8h, v1.8h
     +0x140: ushr    v2.8h, v18.8h, #4
     +0x144: mla     v16.8h, v7.8h, v1.8h
     +0x148: mov     v19.16b, v0.16b
     +0x14c: ushr    v5.8h, v17.8h, #4
     +0x150: mov     v18.16b, v0.16b
     +0x154: ushr    v3.8h, v16.8h, #4
     +0x158: st2     {v4.8h-v5.8h}, [x13]
     +0x15c: st2     {v2.8h-v3.8h}, [x12]
     +0x160: ldr     q7, [x1, #48]
     +0x164: and     v16.16b, v7.16b, v6.16b
     +0x168: ushr    v7.16b, v7.16b, #4
     +0x16c: uxtl    v17.8h, v16.8b
     +0x170: uxtl2   v16.8h, v16.16b
     +0x174: uxtl    v20.8h, v7.8b
     +0x178: uxtl2   v7.8h, v7.16b
     +0x17c: mla     v19.8h, v17.8h, v1.8h
     +0x180: mov     v17.16b, v0.16b
     +0x184: mla     v18.8h, v16.8h, v1.8h
     +0x188: mov     v16.16b, v0.16b
     +0x18c: ushr    v4.8h, v19.8h, #4
     +0x190: mla     v17.8h, v20.8h, v1.8h
     +0x194: ushr    v2.8h, v18.8h, #4
     +0x198: mla     v16.8h, v7.8h, v1.8h
     +0x19c: mov     v19.16b, v0.16b
     +0x1a0: ushr    v5.8h, v17.8h, #4
     +0x1a4: mov     v18.16b, v0.16b
     +0x1a8: ushr    v3.8h, v16.8h, #4
     +0x1ac: st2     {v4.8h-v5.8h}, [x11]
     +0x1b0: st2     {v2.8h-v3.8h}, [x10]
     +0x1b4: ldr     q7, [x1, #64]
     +0x1b8: and     v16.16b, v7.16b, v6.16b
     +0x1bc: ushr    v7.16b, v7.16b, #4
     +0x1c0: uxtl    v17.8h, v16.8b
     +0x1c4: uxtl2   v16.8h, v16.16b
     +0x1c8: uxtl    v20.8h, v7.8b
     +0x1cc: uxtl2   v7.8h, v7.16b
     +0x1d0: mla     v19.8h, v17.8h, v1.8h
     +0x1d4: mov     v17.16b, v0.16b
     +0x1d8: mla     v18.8h, v16.8h, v1.8h
     +0x1dc: mov     v16.16b, v0.16b
     +0x1e0: ushr    v4.8h, v19.8h, #4
     +0x1e4: mla     v17.8h, v20.8h, v1.8h
     +0x1e8: ushr    v2.8h, v18.8h, #4
     +0x1ec: mla     v16.8h, v7.8h, v1.8h
     +0x1f0: mov     v19.16b, v0.16b
     +0x1f4: ushr    v5.8h, v17.8h, #4
     +0x1f8: mov     v18.16b, v0.16b
     +0x1fc: ushr    v3.8h, v16.8h, #4
     +0x200: st2     {v4.8h-v5.8h}, [x9]
     +0x204: st2     {v2.8h-v3.8h}, [x8]
     +0x208: ldr     q7, [x1, #80]
     +0x20c: and     v16.16b, v7.16b, v6.16b
     +0x210: ushr    v7.16b, v7.16b, #4
     +0x214: uxtl    v17.8h, v16.8b
     +0x218: uxtl2   v16.8h, v16.16b
     +0x21c: uxtl    v20.8h, v7.8b
     +0x220: uxtl2   v7.8h, v7.16b
     +0x224: mla     v19.8h, v17.8h, v1.8h
     +0x228: mov     v17.16b, v0.16b
     +0x22c: mla     v18.8h, v16.8h, v1.8h
     +0x230: mov     v16.16b, v0.16b
     +0x234: ushr    v4.8h, v19.8h, #4
     +0x238: mla     v17.8h, v20.8h, v1.8h
     +0x23c: ushr    v2.8h, v18.8h, #4
     +0x240: mla     v16.8h, v7.8h, v1.8h
     +0x244: mov     v19.16b, v0.16b
     +0x248: ushr    v5.8h, v17.8h, #4
     +0x24c: mov     v18.16b, v0.16b
     +0x250: ushr    v3.8h, v16.8h, #4
     +0x254: st2     {v4.8h-v5.8h}, [x7]
     +0x258: st2     {v2.8h-v3.8h}, [x6]
     +0x25c: ldr     q7, [x1, #96]
     +0x260: and     v16.16b, v7.16b, v6.16b
     +0x264: ushr    v7.16b, v7.16b, #4
     +0x268: uxtl    v17.8h, v16.8b
     +0x26c: uxtl2   v16.8h, v16.16b
     +0x270: uxtl    v20.8h, v7.8b
     +0x274: uxtl2   v7.8h, v7.16b
     +0x278: mla     v19.8h, v17.8h, v1.8h
     +0x27c: mov     v17.16b, v0.16b
     +0x280: mla     v18.8h, v16.8h, v1.8h
     +0x284: mov     v16.16b, v0.16b
     +0x288: ushr    v4.8h, v19.8h, #4
     +0x28c: mla     v17.8h, v20.8h, v1.8h
     +0x290: ushr    v2.8h, v18.8h, #4
     +0x294: mla     v16.8h, v7.8h, v1.8h
     +0x298: ushr    v5.8h, v17.8h, #4
     +0x29c: mov     v17.16b, v0.16b
     +0x2a0: ushr    v3.8h, v16.8h, #4
     +0x2a4: st2     {v4.8h-v5.8h}, [x5]
     +0x2a8: st2     {v2.8h-v3.8h}, [x4]
     +0x2ac: ldr     q7, [x1, #112]
     +0x2b0: and     v6.16b, v7.16b, v6.16b
     +0x2b4: ushr    v7.16b, v7.16b, #4
     +0x2b8: uxtl    v16.8h, v6.8b
     +0x2bc: uxtl2   v6.8h, v6.16b
     +0x2c0: uxtl    v18.8h, v7.8b
     +0x2c4: uxtl2   v7.8h, v7.16b
     +0x2c8: mla     v17.8h, v16.8h, v1.8h
     +0x2cc: mov     v16.16b, v0.16b
     +0x2d0: ushr    v4.8h, v17.8h, #4
     +0x2d4: mla     v16.8h, v6.8h, v1.8h
     +0x2d8: mov     v6.16b, v0.16b
     +0x2dc: mla     v0.8h, v7.8h, v1.8h
     +0x2e0: ushr    v2.8h, v16.8h, #4
     +0x2e4: mla     v6.8h, v18.8h, v1.8h
     +0x2e8: ushr    v3.8h, v0.8h, #4
     +0x2ec: ushr    v5.8h, v6.8h, #4
     +0x2f0: st2     {v4.8h-v5.8h}, [x3]
     +0x2f4: st2     {v2.8h-v3.8h}, [x2]
     +0x2f8: ret
     +0x2fc: mov     x2, x1
     +0x300: mov     x1, x0
     +0x304: mov     w3, #0xd01
     +0x308: ldrb    w0, [x2]
     +0x30c: add     x1, x1, #0x4
     +0x310: and     w0, w0, #0xf
     +0x314: mul     w0, w0, w3
     +0x318: add     w0, w0, #0x8
     +0x31c: lsr     w0, w0, #4
     +0x320: sturh   w0, [x1, #-4]
     +0x324: ldrb    w0, [x2], #1
     +0x328: lsr     w0, w0, #4
     +0x32c: mul     w0, w0, w3
     +0x330: add     w0, w0, #0x8
     +0x334: lsr     w0, w0, #4
     +0x338: sturh   w0, [x1, #-2]
     +0x33c: cmp     x4, x1
     +0x340: b.ne    <mlkem_poly_decompress_d4+0x308>
     +0x344: ret
 ***)

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_poly_decompress_d4"];;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O3_CONSTANTS =
  MLKEM_NATIVE_IMAGE_CONST_RULE (layout "mlkem_poly_decompress_d4_consts")
   128;;

(* ------------------------------------------------------------------------- *)
(* The computation of the 16-bit lanes for the low and high 4-bit fields of  *)
(* a byte b, as the vector code does it with AND and USHR, UXTL, MLA with    *)
(* 3329 on top of 8 and USHR #4, checked for all values of the byte.         *)
(* ------------------------------------------------------------------------- *)

let D4_LANES = prove
 (`!b:byte.
     word_ushr
      (word_add (word 8)
        (word_mul (word_shl (word_zx (word_and (word 15) b)) 0)
                  (word 3329))) 4:int16 =
     word((3329 * val b MOD 16 + 8) DIV 16) /\
     word_ushr
      (word_add (word 8)
        (word_mul (word_shl (word_zx (word_ushr b 4)) 0) (word 3329))) 4:int16 =
     word((3329 * val b DIV 16 + 8) DIV 16)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `!v. v < 256
        ==> word_ushr
             (word_add (word 8)
               (word_mul (word_shl (word_zx (word_and (word 15) (word v:byte)))
                                   0)
                         (word 3329))) 4:int16 =
            word((3329 * v MOD 16 + 8) DIV 16) /\
            word_ushr
             (word_add (word 8)
               (word_mul (word_shl (word_zx (word_ushr (word v:byte) 4)) 0)
                         (word 3329))) 4:int16 =
            word((3329 * v DIV 16 + 8) DIV 16)`
   (MP_TAC o SPEC `val(b:byte)`) THENL
   [CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC WORD_RED_CONV));
    REWRITE_TAC[WORD_VAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    ARITH_TAC]);;

(*** The 4-bit fields of a byte of the input given as a number ***)

let D4_NIBBLES = prove
 (`(!n k. ((n DIV 2 EXP k) MOD 256) MOD 16 = (n DIV 2 EXP k) MOD 2 EXP 4) /\
   (!n k. ((n DIV 2 EXP k) MOD 256) DIV 16 =
          (n DIV 2 EXP (k + 4)) MOD 2 EXP 4)`,
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN REPEAT STRIP_TAC THEN
  SPEC_TAC(`n DIV 2 EXP k`,`x:num`) THEN GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `256 = 16 * 16`; MOD_MOD; DIV_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

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

let d4_lanepat =
  `word_ushr (word_add (word 8) (word_mul (x:int16) (word 3329))) 4:int16`;;

let D4_LANE_RULE th =
  let v = rand(concl th) in
  let ls = setify(find_terms (can (term_match [] d4_lanepat)) v) in
  let gs = map (fun t -> genvar(type_of t)) ls in
  let v' = subst (zip gs ls) v in
  let bth = tryfind (fun g -> BITBLAST_RULE(mk_eq(v',g))) gs in
  REWRITE_RULE[D4_LANES]
   (CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]))
     (TRANS th (INST (zip ls gs) bth)));;

let D4_STORES_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
    check (can (term_match [] `read (memory :> bytes256 a) s = x`) o
           concl))) THEN
  REPEAT(DISCH_THEN(fun th ->
    MAP_EVERY (ASSUME_TAC o D4_LANE_RULE) (CONJUNCTS th)));;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decompress 4 in common/fips203.ml, the    *)
(* result for a 4-bit field y is the integer closest to 3329 * y / 16,       *)
(* rounding up on ties, i.e. (3329 * y + 8) DIV 16.                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT =
  prove
 (`!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,128)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
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
              MAYCHANGE [memory :> bytes(r,512)])`,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `n:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_INIT_TAC "s0" THEN
  D4_INPUT_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O3_CONSTANTS) THEN

  (*** The overlap check, and the vector code ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O3_EXEC (1--5) THEN
  ALIAS_BRANCH_TAC `r:int64` `512` `a:int64` `128` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O3_EXEC (6--7) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O3_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (8--191) THEN
  D4_STORES_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Each coefficient from its 4-bit field ***)

  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[D4_NIBBLES] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 4 = 16`]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_decompress_d4_signature =
  ([("r", "int16_t[static 256]", "false");
    ("a", "uint8_t[static 128]", "true")],
   "void",
   [("a", "128", 1)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:
      [`word(pc + mlkem_poly_decompress_d4_consts):int64`,`16`]
    ~keep_maychanges:true
    mlkem_native_poly_decompress_d4_signature
    MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O3_EXEC;;

let MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,128]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_poly_decompress_d4) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2
                         [a,128; r,512;
                          word (pc + mlkem_poly_decompress_d4_consts),16]
                         [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (returnaddress:int64).
      f_ev a r pc returnaddress:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O3_EXEC (1--5) THEN
  ALIAS_BRANCH_TAC `r:int64` `512` `a:int64` `128` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O3_EXEC (6--7) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D4_GCC12_O3_EXEC (8--191) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
