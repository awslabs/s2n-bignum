(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of polynomial coefficients from 12-bit chunks of a byte array.  *)
(* This is the code for mlkem_poly_frombytes from mlkem-native's portable C  *)
(* implementation compiled by gcc 12 with -O3 (see mlkem_native/README.md).  *)
(* It is verified in the whole image (see libmlkem.ml).                      *)
(*                                                                           *)
(* The compiler has vectorized the loop completely, with LD3 and ST2, after  *)
(* a check that the input and the output do not overlap; if they do, the     *)
(* code falls back to the scalar loop of -O2. Since the specification        *)
(* requires them not to overlap, only the vector code runs. It saves X19,    *)
(* X20 and X30 in a 32-byte frame on the stack, and uses X18 as a temporary, *)
(* so unlike those of gcc12_O2 the specifications have the stack pointer and *)
(* this frame, and X18 among the registers changed.                          *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/overlap.ml";;
needs "arm/proofs/mlkem_native/interleave.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_frombytes:
       +0x0: add     x2, x0, #0x200
       +0x4: add     x6, x1, #0x180
       +0x8: cmp     x1, x2
       +0xc: ccmp    x0, x6, #0x2, cc
      +0x10: b.cc    <mlkem_poly_frombytes+0x2d8>
      +0x14: stp     x19, x20, [sp, #-32]!
      +0x18: mov     x2, x1
      +0x1c: add     x20, x0, #0x40
      +0x20: str     x30, [sp, #16]
      +0x24: add     x19, x0, #0x60
      +0x28: add     x18, x0, #0x80
      +0x2c: add     x17, x0, #0xa0
      +0x30: ld3     {v1.16b-v3.16b}, [x2], #48
      +0x34: add     x15, x0, #0xc0
      +0x38: add     x14, x0, #0xe0
      +0x3c: add     x12, x0, #0x100
      +0x40: add     x11, x0, #0x120
      +0x44: add     x9, x0, #0x140
      +0x48: shll    v17.8h, v2.8b, #8
      +0x4c: add     x8, x0, #0x160
      +0x50: uxtl    v18.8h, v1.8b
      +0x54: add     x6, x0, #0x180
      +0x58: ushr    v6.16b, v2.16b, #4
      +0x5c: add     x5, x0, #0x1a0
      +0x60: shll2   v0.8h, v2.16b, #8
      +0x64: add     x4, x0, #0x1c0
      +0x68: bic     v17.8h, #0xf0, lsl #8
      +0x6c: add     x3, x0, #0x1e0
      +0x70: uxtl2   v16.8h, v1.16b
      +0x74: add     x30, x1, #0x60
      +0x78: add     x16, x1, #0x90
      +0x7c: add     x13, x1, #0xc0
      +0x80: bic     v0.8h, #0xf0, lsl #8
      +0x84: add     x10, x1, #0xf0
      +0x88: orr     v4.16b, v17.16b, v18.16b
      +0x8c: add     x7, x1, #0x120
      +0x90: uxtl    v18.8h, v6.8b
      +0x94: add     x1, x1, #0x150
      +0x98: ushll   v17.8h, v3.8b, #4
      +0x9c: uxtl2   v6.8h, v6.16b
      +0xa0: ushll2  v3.8h, v3.16b, #4
      +0xa4: orr     v0.16b, v0.16b, v16.16b
      +0xa8: orr     v5.16b, v18.16b, v17.16b
      +0xac: orr     v1.16b, v6.16b, v3.16b
      +0xb0: st2     {v4.8h-v5.8h}, [x0], #32
      +0xb4: st2     {v0.8h-v1.8h}, [x0]
      +0xb8: ld3     {v1.16b-v3.16b}, [x2]
      +0xbc: shll    v17.8h, v2.8b, #8
      +0xc0: uxtl    v18.8h, v1.8b
      +0xc4: ushr    v6.16b, v2.16b, #4
      +0xc8: mov     v16.16b, v1.16b
      +0xcc: bic     v17.8h, #0xf0, lsl #8
      +0xd0: shll2   v0.8h, v2.16b, #8
      +0xd4: uxtl2   v7.8h, v16.16b
      +0xd8: orr     v4.16b, v17.16b, v18.16b
      +0xdc: uxtl    v18.8h, v6.8b
      +0xe0: ushll   v17.8h, v3.8b, #4
      +0xe4: uxtl2   v6.8h, v6.16b
      +0xe8: ushll2  v3.8h, v3.16b, #4
      +0xec: bic     v0.8h, #0xf0, lsl #8
      +0xf0: orr     v5.16b, v18.16b, v17.16b
      +0xf4: orr     v1.16b, v6.16b, v3.16b
      +0xf8: orr     v0.16b, v0.16b, v7.16b
      +0xfc: st2     {v4.8h-v5.8h}, [x20]
     +0x100: st2     {v0.8h-v1.8h}, [x19]
     +0x104: ld3     {v1.16b-v3.16b}, [x30]
     +0x108: ldr     x30, [sp, #16]
     +0x10c: shll    v17.8h, v2.8b, #8
     +0x110: uxtl    v18.8h, v1.8b
     +0x114: ushr    v6.16b, v2.16b, #4
     +0x118: mov     v16.16b, v1.16b
     +0x11c: bic     v17.8h, #0xf0, lsl #8
     +0x120: shll2   v0.8h, v2.16b, #8
     +0x124: uxtl2   v7.8h, v16.16b
     +0x128: orr     v4.16b, v17.16b, v18.16b
     +0x12c: uxtl    v18.8h, v6.8b
     +0x130: ushll   v17.8h, v3.8b, #4
     +0x134: uxtl2   v6.8h, v6.16b
     +0x138: ushll2  v3.8h, v3.16b, #4
     +0x13c: bic     v0.8h, #0xf0, lsl #8
     +0x140: orr     v5.16b, v18.16b, v17.16b
     +0x144: orr     v1.16b, v6.16b, v3.16b
     +0x148: orr     v0.16b, v0.16b, v7.16b
     +0x14c: st2     {v4.8h-v5.8h}, [x18]
     +0x150: st2     {v0.8h-v1.8h}, [x17]
     +0x154: ld3     {v1.16b-v3.16b}, [x16]
     +0x158: shll    v17.8h, v2.8b, #8
     +0x15c: uxtl    v18.8h, v1.8b
     +0x160: ushr    v6.16b, v2.16b, #4
     +0x164: mov     v16.16b, v1.16b
     +0x168: bic     v17.8h, #0xf0, lsl #8
     +0x16c: shll2   v0.8h, v2.16b, #8
     +0x170: uxtl2   v7.8h, v16.16b
     +0x174: orr     v4.16b, v17.16b, v18.16b
     +0x178: uxtl    v18.8h, v6.8b
     +0x17c: ushll   v17.8h, v3.8b, #4
     +0x180: uxtl2   v6.8h, v6.16b
     +0x184: ushll2  v3.8h, v3.16b, #4
     +0x188: bic     v0.8h, #0xf0, lsl #8
     +0x18c: orr     v5.16b, v18.16b, v17.16b
     +0x190: orr     v1.16b, v6.16b, v3.16b
     +0x194: orr     v0.16b, v0.16b, v7.16b
     +0x198: st2     {v4.8h-v5.8h}, [x15]
     +0x19c: st2     {v0.8h-v1.8h}, [x14]
     +0x1a0: ld3     {v1.16b-v3.16b}, [x13]
     +0x1a4: shll    v17.8h, v2.8b, #8
     +0x1a8: uxtl    v18.8h, v1.8b
     +0x1ac: ushr    v6.16b, v2.16b, #4
     +0x1b0: mov     v16.16b, v1.16b
     +0x1b4: bic     v17.8h, #0xf0, lsl #8
     +0x1b8: shll2   v0.8h, v2.16b, #8
     +0x1bc: uxtl2   v7.8h, v16.16b
     +0x1c0: orr     v4.16b, v17.16b, v18.16b
     +0x1c4: uxtl    v18.8h, v6.8b
     +0x1c8: ushll   v17.8h, v3.8b, #4
     +0x1cc: uxtl2   v6.8h, v6.16b
     +0x1d0: ushll2  v3.8h, v3.16b, #4
     +0x1d4: bic     v0.8h, #0xf0, lsl #8
     +0x1d8: orr     v5.16b, v18.16b, v17.16b
     +0x1dc: orr     v1.16b, v6.16b, v3.16b
     +0x1e0: orr     v0.16b, v0.16b, v7.16b
     +0x1e4: st2     {v4.8h-v5.8h}, [x12]
     +0x1e8: st2     {v0.8h-v1.8h}, [x11]
     +0x1ec: ld3     {v1.16b-v3.16b}, [x10]
     +0x1f0: shll    v17.8h, v2.8b, #8
     +0x1f4: uxtl    v18.8h, v1.8b
     +0x1f8: ushr    v6.16b, v2.16b, #4
     +0x1fc: mov     v16.16b, v1.16b
     +0x200: bic     v17.8h, #0xf0, lsl #8
     +0x204: shll2   v0.8h, v2.16b, #8
     +0x208: uxtl2   v7.8h, v16.16b
     +0x20c: orr     v4.16b, v17.16b, v18.16b
     +0x210: uxtl    v18.8h, v6.8b
     +0x214: ushll   v17.8h, v3.8b, #4
     +0x218: uxtl2   v6.8h, v6.16b
     +0x21c: ushll2  v3.8h, v3.16b, #4
     +0x220: bic     v0.8h, #0xf0, lsl #8
     +0x224: orr     v5.16b, v18.16b, v17.16b
     +0x228: orr     v1.16b, v6.16b, v3.16b
     +0x22c: orr     v0.16b, v0.16b, v7.16b
     +0x230: st2     {v4.8h-v5.8h}, [x9]
     +0x234: st2     {v0.8h-v1.8h}, [x8]
     +0x238: ld3     {v1.16b-v3.16b}, [x7]
     +0x23c: shll    v17.8h, v2.8b, #8
     +0x240: uxtl    v18.8h, v1.8b
     +0x244: ushr    v6.16b, v2.16b, #4
     +0x248: mov     v16.16b, v1.16b
     +0x24c: bic     v17.8h, #0xf0, lsl #8
     +0x250: shll2   v0.8h, v2.16b, #8
     +0x254: uxtl2   v7.8h, v16.16b
     +0x258: orr     v4.16b, v17.16b, v18.16b
     +0x25c: uxtl    v18.8h, v6.8b
     +0x260: ushll   v17.8h, v3.8b, #4
     +0x264: uxtl2   v6.8h, v6.16b
     +0x268: ushll2  v3.8h, v3.16b, #4
     +0x26c: bic     v0.8h, #0xf0, lsl #8
     +0x270: orr     v5.16b, v18.16b, v17.16b
     +0x274: orr     v1.16b, v6.16b, v3.16b
     +0x278: orr     v0.16b, v0.16b, v7.16b
     +0x27c: st2     {v4.8h-v5.8h}, [x6]
     +0x280: st2     {v0.8h-v1.8h}, [x5]
     +0x284: ld3     {v1.16b-v3.16b}, [x1]
     +0x288: shll    v17.8h, v2.8b, #8
     +0x28c: uxtl    v18.8h, v1.8b
     +0x290: ushr    v6.16b, v2.16b, #4
     +0x294: mov     v16.16b, v1.16b
     +0x298: bic     v17.8h, #0xf0, lsl #8
     +0x29c: shll2   v0.8h, v2.16b, #8
     +0x2a0: uxtl2   v7.8h, v16.16b
     +0x2a4: orr     v4.16b, v17.16b, v18.16b
     +0x2a8: uxtl    v18.8h, v6.8b
     +0x2ac: ushll   v17.8h, v3.8b, #4
     +0x2b0: uxtl2   v6.8h, v6.16b
     +0x2b4: ushll2  v3.8h, v3.16b, #4
     +0x2b8: bic     v0.8h, #0xf0, lsl #8
     +0x2bc: orr     v5.16b, v18.16b, v17.16b
     +0x2c0: orr     v1.16b, v6.16b, v3.16b
     +0x2c4: orr     v0.16b, v0.16b, v7.16b
     +0x2c8: st2     {v4.8h-v5.8h}, [x4]
     +0x2cc: st2     {v0.8h-v1.8h}, [x3]
     +0x2d0: ldp     x19, x20, [sp], #32
     +0x2d4: ret
     +0x2d8: ldrb    w2, [x1, #1]
     +0x2dc: add     x0, x0, #0x4
     +0x2e0: ldrb    w4, [x1, #2]
     +0x2e4: ldrb    w5, [x1], #3
     +0x2e8: ubfiz   w3, w2, #8, #4
     +0x2ec: lsl     w4, w4, #4
     +0x2f0: orr     w3, w3, w5
     +0x2f4: orr     w2, w4, w2, lsr #4
     +0x2f8: sturh   w3, [x0, #-4]
     +0x2fc: sturh   w2, [x0, #-2]
     +0x300: cmp     x1, x6
     +0x304: b.ne    <mlkem_poly_frombytes+0x2d8>
     +0x308: ret
 ***)

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_poly_frombytes"];;

(* ------------------------------------------------------------------------- *)
(* The input as 128 words of 24 bits w k, each holding two coefficients, and *)
(* its 128-bit parts, as LD3 reads them, as joins of their bytes.            *)
(* ------------------------------------------------------------------------- *)

let FB_BYTES = prove
 (`!a n k s j.
        read (memory :> bytes(a,384)) s = n /\ k < 128 /\ j < 3
        ==> read (memory :> bytes8(word_add a (word(3 * k + j)))) s =
            word_subword (word(n DIV 2 EXP (24 * k)):24 word) (8 * j,8)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `384`; `n:num`; `3 * k + j`; `s:armstate`]
                READ_MEMORY_BYTES8_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 8 = 256`] THEN
  REWRITE_TAC[ARITH_RULE `8 * (3 * k + j) = 24 * k + 8 * j`]);;

let FB_FIELD = prove
 (`!n k e. e < 2
           ==> word((n DIV 2 EXP (12 * (2 * k + e))) MOD 2 EXP 12):int16 =
               word_zx(word_subword (word(n DIV 2 EXP (24 * k)):24 word)
                                    (12 * e,12):12 word)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o rand o
    snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[word_zx; VAL_WORD] THEN CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[MOD_MOD_REFL; DIV_DIV; GSYM EXP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `24 * k + 12 * e = 12 * (2 * k + e)`]);;

let FB_MERGES = map (fun k ->
  let addr = if k = 0 then `a:int64` else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`a:int64`),
            mk_comb(`word:num->int64`, mk_small_numeral(16 * k))) in
  READ_MEMORY_MERGE_CONV 4
   (vsubst [addr,`x:int64`] `read (memory :> bytes128 x) s0`)) (0--23);;

let FB_INPUT_TAC =
  SUBGOAL_THEN `?w:num->24 word. !k. word(n DIV 2 EXP (24 * k)) = w k`
   STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\k. word(n DIV 2 EXP (24 * k)):24 word` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k < 128
        ==> read (memory :> bytes8 (word_add a (word(3 * k)))) s0 =
            word_subword ((w:num->24 word) k) (0,8) /\
            read (memory :> bytes8 (word_add a (word(3 * k + 1)))) s0 =
            word_subword (w k) (8,8) /\
            read (memory :> bytes8 (word_add a (word(3 * k + 2)))) s0 =
            word_subword (w k) (16,8)`
   MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && free_in `w:num->24 word` (concl th)
      then REWRITE_TAC[GSYM th] THEN ASSUME_TAC th else NO_TAC) THEN
    MP_TAC(CONV_RULE(NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_CLAUSES])
     (SPECL [`a:int64`; `n:num`; `k:num`; `s0:armstate`; `0`] FB_BYTES)) THEN
    MP_TAC(CONV_RULE NUM_REDUCE_CONV
     (SPECL [`a:int64`; `n:num`; `k:num`; `s0:armstate`; `1`] FB_BYTES)) THEN
    MP_TAC(CONV_RULE NUM_REDUCE_CONV
     (SPECL [`a:int64`; `n:num`; `k:num`; `s0:armstate`; `2`] FB_BYTES)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  MAP_EVERY MP_TAC FB_MERGES THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes8 a) s = x`];;

(*** After each step, the registers loaded by LD3 as joins of bytes ***)

let FB_SIMD_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> match t with
              Const("word_subdeinterleave",_) -> true | _ -> false))
           (concl th)
    then CONV_RULE(RAND_CONV(SIMD_SIMPLIFY_CONV []))
          (CONV_RULE(TOP_DEPTH_CONV MLKEM_NATIVE_INTERLEAVE_CONV) th)
    else th) THEN
  SIMD_SIMPLIFY_TAC[];;

(*** The 32-byte stores, as the 16 coefficients in each ***)

let FB_STORES_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
    check (can (term_match [] `read (memory :> bytes256 a) s = x`) o
           concl))) THEN
  REPEAT(DISCH_THEN(fun th ->
    MAP_EVERY (ASSUME_TAC o
      CONV_RULE(RAND_CONV(SIMD_SIMPLIFY_CONV [])) o
      CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD])))
     (CONJUNCTS th)));;

(*** The coefficients as the 12-bit fields of the w k ***)

let FB_FIELDS_TAC =
  FIRST_ASSUM(fun def ->
    if is_forall(concl def) && free_in `w:num->24 word` (concl def) &&
       not(is_imp(snd(dest_forall(concl def))))
    then
      let ths = map (fun i ->
        let k = i / 2 and e = i mod 2 in
        let th = MP (SPECL [`n:num`; mk_small_numeral k; mk_small_numeral e]
                           FB_FIELD)
                    (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                                 (mk_small_numeral e) `2`))) in
        CONV_RULE(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV))
         (REWRITE_RULE[def; ARITH_RULE `2 EXP 12 = 4096`] th)) (0--255) in
      REWRITE_TAC ths
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_decode 12 in common/fips203.ml,           *)
(* coefficient i of the result is bits 12 * i to 12 * i + 11 of the number   *)
(* given by the 384 bytes. The frame for X19, X20 and X30 is below the       *)
(* stack pointer at entry.                                                   *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a n pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,384)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,libmlkem_size); (a,384); (r,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_poly_frombytes) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,384)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE [memory :> bytes(r,512);
                         memory :> bytes(word_sub stackpointer (word 32),32)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_INIT_TAC "s0" THEN
  FB_INPUT_TAC THEN

  (*** The overlap check, and the vector code ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O3_EXEC (1--5) THEN
  ALIAS_BRANCH_TAC `r:int64` `512` `a:int64` `384` THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O3_EXEC [k] THEN
    FB_SIMD_TAC) (6--182) THEN
  FB_STORES_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** Each coefficient from its 12-bit field ***)

  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN FB_FIELDS_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O3_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,384] /\
           ALL (nonoverlapping (word_sub stackpointer (word 32),32))
               [word pc,libmlkem_size; a,384; r,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_poly_frombytes) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc (word_sub stackpointer (word 32))
                                       returnaddress /\
                         memaccess_inbounds e2
                          [a,384; r,512; word_sub stackpointer (word 32),32]
                          [r,512; word_sub stackpointer (word 32),32]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE [memory :> bytes (r,512);
                           memory :> bytes(word_sub stackpointer (word 32),32)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      f_ev a r pc stackpointer returnaddress:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O3_EXEC (1--5) THEN
  ALIAS_BRANCH_TAC `r:int64` `512` `a:int64` `384` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O3_EXEC (6--182) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, as for       *)
(* gcc12_O2, with the same simulation as for correctness.                    *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O3_IMAGE_SUBROUTINE_FULL = prove
 (`exists f_events.
       forall e r a n pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,384] /\
           ALL (nonoverlapping (word_sub stackpointer (word 32),32))
               [word pc,libmlkem_size; a,384; r,512]
           ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_poly_frombytes) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read (memory :> bytes(a,384)) s = n /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :> bytes16
                                   (word_add r (word(2 * i)))) s =
                             word((n DIV 2 EXP (12 * i)) MOD 2 EXP 12)) /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc (word_sub stackpointer (word 32))
                                       returnaddress /\
                         memaccess_inbounds e2
                          [a,384; r,512; word_sub stackpointer (word 32),32]
                          [r,512; word_sub stackpointer (word 32),32]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE [memory :> bytes (r,512);
                           memory :> bytes(word_sub stackpointer (word 32),32)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      f_ev a r pc stackpointer returnaddress:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  FB_INPUT_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O3_EXEC (1--5) THEN
  ALIAS_BRANCH_TAC `r:int64` `512` `a:int64` `384` THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O3_EXEC [k] THEN
    FB_SIMD_TAC) (6--182) THEN
  FB_STORES_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN FB_FIELDS_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN BITBLAST_TAC;
    DISCHARGE_SAFETY_PROPERTY_TAC]);;
