(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Centered binomial distribution with eta = 3. This is the code for         *)
(* mlkem_poly_cbd3 from mlkem-native's portable C implementation compiled by *)
(* gcc 12 with -O3 (see mlkem_native/README.md). It is verified in the whole *)
(* image (see libmlkem.ml).                                                  *)
(*                                                                           *)
(* The compiler has vectorized the loop, 64 coefficients per iteration with  *)
(* LD3 and two ST4, after a check that the input and the output do not       *)
(* overlap; if they do, the code falls back to a scalar loop. Since the      *)
(* specification requires them not to overlap, only the vector code runs.    *)
(* It saves D8, D9 and D10 in a 32-byte frame on the stack, so unlike those  *)
(* of gcc12_O2 the specifications have the stack pointer and this frame, and *)
(* it reads one vector of constants rather than two. The four iterations of  *)
(* the loop are simulated one after the other.                               *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/utils/mlkem_native_overlap.ml";;
needs "arm/proofs/utils/mlkem_native_interleave.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_cbd3:
       +0x0: mov     x3, x0
       +0x4: mov     x0, x1
       +0x8: add     x1, x3, #0x200
       +0xc: add     x7, x0, #0xc0
      +0x10: cmp     x0, x1
      +0x14: ccmp    x3, x7, #0x2, cc
      +0x18: b.cc    <mlkem_poly_cbd3+0x218>
      +0x1c: adrp    x1, <page>
      +0x20: stp     d8, d9, [sp, #-32]!
      +0x24: movi    v4.8h, #0x7
      +0x28: str     d10, [sp, #16]
      +0x2c: ldr     q7, [x1, #2720]  // mlkem_poly_cbd3_consts
      +0x30: mov     x1, x3
      +0x34: ld3     {v22.16b-v24.16b}, [x0], #48
      +0x38: mov     x2, x1
      +0x3c: add     x1, x1, #0x80
      +0x40: uxtl    v0.8h, v22.8b
      +0x44: shll    v20.8h, v23.8b, #8
      +0x48: uxtl    v2.8h, v24.8b
      +0x4c: uxtl2   v1.8h, v22.16b
      +0x50: shll2   v6.8h, v23.16b, #8
      +0x54: uxtl    v8.4s, v20.4h
      +0x58: uxtl    v3.4s, v0.4h
      +0x5c: shll    v9.4s, v2.4h, #16
      +0x60: uxtl2   v5.8h, v24.16b
      +0x64: uxtl2   v20.4s, v20.8h
      +0x68: orr     v3.16b, v3.16b, v8.16b
      +0x6c: uxtl    v21.4s, v1.4h
      +0x70: uxtl    v8.4s, v6.4h
      +0x74: uxtl2   v0.4s, v0.8h
      +0x78: orr     v3.16b, v3.16b, v9.16b
      +0x7c: uxtl2   v6.4s, v6.8h
      +0x80: orr     v0.16b, v0.16b, v20.16b
      +0x84: shll2   v20.4s, v2.8h, #16
      +0x88: uxtl2   v2.4s, v1.8h
      +0x8c: orr     v1.16b, v21.16b, v8.16b
      +0x90: shll    v8.4s, v5.4h, #16
      +0x94: orr     v0.16b, v0.16b, v20.16b
      +0x98: ushr    v22.4s, v3.4s, #1
      +0x9c: ushr    v21.4s, v3.4s, #2
      +0xa0: orr     v1.16b, v1.16b, v8.16b
      +0xa4: orr     v2.16b, v2.16b, v6.16b
      +0xa8: shll2   v5.4s, v5.8h, #16
      +0xac: ushr    v20.4s, v0.4s, #1
      +0xb0: and     v21.16b, v21.16b, v7.16b
      +0xb4: ushr    v6.4s, v1.4s, #1
      +0xb8: orr     v2.16b, v2.16b, v5.16b
      +0xbc: and     v22.16b, v22.16b, v7.16b
      +0xc0: ushr    v5.4s, v1.4s, #2
      +0xc4: ushr    v24.4s, v0.4s, #2
      +0xc8: ushr    v23.4s, v2.4s, #2
      +0xcc: add     v22.4s, v22.4s, v21.4s
      +0xd0: and     v6.16b, v6.16b, v7.16b
      +0xd4: and     v21.16b, v3.16b, v7.16b
      +0xd8: and     v3.16b, v20.16b, v7.16b
      +0xdc: and     v20.16b, v5.16b, v7.16b
      +0xe0: ushr    v5.4s, v2.4s, #1
      +0xe4: add     v22.4s, v22.4s, v21.4s
      +0xe8: and     v24.16b, v24.16b, v7.16b
      +0xec: and     v21.16b, v0.16b, v7.16b
      +0xf0: add     v0.4s, v6.4s, v20.4s
      +0xf4: and     v20.16b, v1.16b, v7.16b
      +0xf8: and     v1.16b, v5.16b, v7.16b
      +0xfc: and     v5.16b, v23.16b, v7.16b
     +0x100: add     v3.4s, v3.4s, v24.4s
     +0x104: add     v0.4s, v0.4s, v20.4s
     +0x108: and     v20.16b, v2.16b, v7.16b
     +0x10c: add     v1.4s, v1.4s, v5.4s
     +0x110: add     v3.4s, v3.4s, v21.4s
     +0x114: shrn    v5.4h, v0.4s, #3
     +0x118: shrn    v6.4h, v22.4s, #3
     +0x11c: add     v1.4s, v1.4s, v20.4s
     +0x120: uzp1    v26.8h, v22.8h, v3.8h
     +0x124: shrn    v9.4h, v0.4s, #9
     +0x128: shrn2   v6.8h, v3.4s, #3
     +0x12c: uzp1    v2.8h, v0.8h, v1.8h
     +0x130: shrn2   v5.8h, v1.4s, #3
     +0x134: shrn    v25.4h, v22.4s, #6
     +0x138: shrn    v24.4h, v22.4s, #9
     +0x13c: shrn2   v9.8h, v1.4s, #9
     +0x140: and     v6.16b, v6.16b, v4.16b
     +0x144: shrn2   v25.8h, v3.4s, #6
     +0x148: shrn2   v24.8h, v3.4s, #9
     +0x14c: and     v26.16b, v26.16b, v4.16b
     +0x150: shrn    v8.4h, v22.4s, #12
     +0x154: and     v5.16b, v5.16b, v4.16b
     +0x158: and     v2.16b, v2.16b, v4.16b
     +0x15c: sub     v16.8h, v26.8h, v6.8h
     +0x160: shrn    v27.4h, v0.4s, #6
     +0x164: shrn    v21.4h, v0.4s, #12
     +0x168: sub     v28.8h, v2.8h, v5.8h
     +0x16c: shrn    v20.4h, v0.4s, #15
     +0x170: and     v10.16b, v25.16b, v4.16b
     +0x174: and     v26.16b, v9.16b, v4.16b
     +0x178: and     v25.16b, v24.16b, v4.16b
     +0x17c: ushr    v5.4s, v0.4s, #18
     +0x180: mov     v24.8b, v8.8b
     +0x184: ushr    v9.4s, v1.4s, #18
     +0x188: ushr    v8.4s, v3.4s, #18
     +0x18c: shrn    v23.4h, v22.4s, #15
     +0x190: ushr    v6.4s, v22.4s, #18
     +0x194: shrn2   v27.8h, v1.4s, #6
     +0x198: shrn2   v24.8h, v3.4s, #12
     +0x19c: shrn2   v23.8h, v3.4s, #15
     +0x1a0: shrn2   v21.8h, v1.4s, #12
     +0x1a4: shrn2   v20.8h, v1.4s, #15
     +0x1a8: ushr    v3.4s, v3.4s, #21
     +0x1ac: ushr    v2.4s, v22.4s, #21
     +0x1b0: uzp1    v6.8h, v6.8h, v8.8h
     +0x1b4: ushr    v0.4s, v0.4s, #21
     +0x1b8: uzp1    v5.8h, v5.8h, v9.8h
     +0x1bc: ushr    v1.4s, v1.4s, #21
     +0x1c0: uzp1    v2.8h, v2.8h, v3.8h
     +0x1c4: and     v27.16b, v27.16b, v4.16b
     +0x1c8: and     v24.16b, v24.16b, v4.16b
     +0x1cc: and     v23.16b, v23.16b, v4.16b
     +0x1d0: and     v21.16b, v21.16b, v4.16b
     +0x1d4: and     v20.16b, v20.16b, v4.16b
     +0x1d8: and     v6.16b, v6.16b, v4.16b
     +0x1dc: and     v3.16b, v5.16b, v4.16b
     +0x1e0: uzp1    v0.8h, v0.8h, v1.8h
     +0x1e4: sub     v17.8h, v10.8h, v25.8h
     +0x1e8: sub     v29.8h, v27.8h, v26.8h
     +0x1ec: sub     v18.8h, v24.8h, v23.8h
     +0x1f0: sub     v30.8h, v21.8h, v20.8h
     +0x1f4: sub     v19.8h, v6.8h, v2.8h
     +0x1f8: sub     v31.8h, v3.8h, v0.8h
     +0x1fc: st4     {v16.8h-v19.8h}, [x2], #64
     +0x200: st4     {v28.8h-v31.8h}, [x2]
     +0x204: cmp     x0, x7
     +0x208: b.ne    <mlkem_poly_cbd3+0x34>
     +0x20c: ldr     d10, [sp, #16]
     +0x210: ldp     d8, d9, [sp], #32
     +0x214: ret
     +0x218: movi    v5.4h, #0x7
     +0x21c: mov     w4, #0x9249
     +0x220: mov     x2, x0
     +0x224: movk    w4, #0x24, lsl #16
     +0x228: ldrb    w0, [x2, #1]
     +0x22c: add     x2, x2, #0x3
     +0x230: ldurb   w1, [x2, #-1]
     +0x234: ldurb   w5, [x2, #-3]
     +0x238: lsl     w0, w0, #8
     +0x23c: orr     w1, w0, w1, lsl #16
     +0x240: orr     w1, w1, w5
     +0x244: and     w5, w1, w4
     +0x248: and     w0, w4, w1, lsr #2
     +0x24c: and     w1, w4, w1, lsr #1
     +0x250: add     w0, w0, w1
     +0x254: add     w0, w0, w5
     +0x258: fmov    s1, w0
     +0x25c: fmov    s0, w0
     +0x260: ushr    v4.2s, v1.2s, #12
     +0x264: ushr    v3.2s, v1.2s, #18
     +0x268: ubfx    x1, x0, #9, #3
     +0x26c: fmov    d1, x0
     +0x270: ushr    v0.2s, v0.2s, #6
     +0x274: ubfx    x6, x0, #3, #3
     +0x278: mov     v1.d[1], x1
     +0x27c: fmov    d2, x6
     +0x280: ubfx    x5, x0, #15, #3
     +0x284: mov     v2.h[1], w1
     +0x288: mov     v1.s[1], v0.s[0]
     +0x28c: fmov    s0, w0
     +0x290: mov     v2.h[2], w5
     +0x294: ushr    v0.2s, v0.2s, #21
     +0x298: mov     v1.s[2], v4.s[0]
     +0x29c: mov     v2.h[3], v0.h[0]
     +0x2a0: mov     v1.s[3], v3.s[0]
     +0x2a4: xtn     v0.4h, v1.4s
     +0x2a8: and     v0.8b, v0.8b, v5.8b
     +0x2ac: sub     v0.4h, v0.4h, v2.4h
     +0x2b0: str     d0, [x3], #8
     +0x2b4: cmp     x2, x7
     +0x2b8: b.ne    <mlkem_poly_cbd3+0x228>
     +0x2bc: ret
 ***)

let MLKEM_NATIVE_POLY_CBD3_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_poly_cbd3"];;

(*** The vector 0x249249 of 32-bit lanes, a mask for the low bit of each
 *** group of three bits of 24 ***)

let MLKEM_NATIVE_POLY_CBD3_GCC12_O3_CONSTANTS =
  MLKEM_NATIVE_IMAGE_CONST_RULE (layout "mlkem_poly_cbd3_consts") 128;;

(*** The three bytes for four coefficients, as parts of a 24-bit word ***)

let CBD3_BYTES = prove
 (`!a n i s j.
        read (memory :> bytes(a,192)) s = n /\ i < 64 /\ j < 3
        ==> read (memory :> bytes8(word_add a (word(3 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (24 * i)):24 word) (8 * j,8)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `192`; `n:num`; `3 * i + j`; `s:armstate`]
                READ_MEMORY_BYTES8_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 8 = 256`] THEN
  REWRITE_TAC[ARITH_RULE `8 * (3 * i + j) = 24 * i + 8 * j`]);;

(* ------------------------------------------------------------------------- *)
(* As at -O2, coefficient j of 4 for a 24-bit word t comes from the 6-bit    *)
(* field j of t (CBD3_LANE, with the lemmas of gcc12_O2). Here each 32-bit   *)
(* lane of the vector code holds the 24 bits of one group of three bytes,    *)
(* adds its groups of three bits with the mask 0x249249, and the fields are  *)
(* then taken out with SHRN, USHR, UZP1 and AND with 7 and subtracted.       *)
(* ------------------------------------------------------------------------- *)

let SIXBIT_BIT = prove
 (`!n m k. k < 6
           ==> (n DIV 2 EXP (m + k)) MOD 2 =
               (((n DIV 2 EXP m) MOD 64) DIV 2 EXP k) MOD 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SPEC_TAC(`n DIV 2 EXP m`,`x:num`) THEN GEN_TAC THEN
  GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV) [GSYM(SPEC `2` EXP_1)] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; ARITH_RULE `64 = 2 EXP 6`;
              MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `k < 6 ==> MIN 6 (k + 1) = k + 1`]);;

let CBD3_FIELD = prove
 (`!m. m < 64
       ==> word_sub
            (word_zx (word_add (word_add (word_and (word m:6 word) (word 1))
                                         (word_and (word_ushr (word m) 1)
                                                   (word 1)))
                               (word_and (word_ushr (word m) 2) (word 1))))
            (word_zx (word_add (word_add (word_and (word_ushr (word m:6 word)
                                                              3) (word 1))
                                         (word_and (word_ushr (word m) 4)
                                                   (word 1)))
                               (word_ushr (word m) 5))):int16 =
           iword(&(m MOD 2 + (m DIV 2) MOD 2 + (m DIV 4) MOD 2) -
                 &((m DIV 8) MOD 2 + (m DIV 16) MOD 2 + (m DIV 32) MOD 2))`,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                      WORD_RED_CONV)));;

let CBD3_LANE = prove
 (`!n i j w:24 word.
      j < 4 /\ word(n DIV 2 EXP (24 * i)) = w
      ==> let x:6 word = word_subword w (6 * j,6) in
          word_sub
            (word_zx (word_add (word_add (word_and x (word 1))
                                         (word_and (word_ushr x 1) (word 1)))
                               (word_and (word_ushr x 2) (word 1))))
            (word_zx (word_add (word_add (word_and (word_ushr x 3) (word 1))
                                         (word_and (word_ushr x 4) (word 1)))
                               (word_ushr x 5))):int16 =
          iword(&((n DIV 2 EXP (6 * (4 * i + j))) MOD 2 +
                  (n DIV 2 EXP (6 * (4 * i + j) + 1)) MOD 2 +
                  (n DIV 2 EXP (6 * (4 * i + j) + 2)) MOD 2) -
                &((n DIV 2 EXP (6 * (4 * i + j) + 3)) MOD 2 +
                  (n DIV 2 EXP (6 * (4 * i + j) + 4)) MOD 2 +
                  (n DIV 2 EXP (6 * (4 * i + j) + 5)) MOD 2))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `word_subword (word(n DIV 2 EXP (24 * i)):24 word) (6 * j,6):6 word =
    word((n DIV 2 EXP (6 * (4 * i + j))) MOD 64)`
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o lhand o snd) THEN
    ANTS_TAC THENL
     [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 6 = 64`] THEN
    REWRITE_TAC[ARITH_RULE `24 * i + 6 * j = 6 * (4 * i + j)`];
    ALL_TAC] THEN
  SIMP_TAC[CBD3_FIELD; MOD_LT_EQ; ARITH_EQ] THEN
  SIMP_TAC[SIXBIT_BIT; ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GEN_ALL(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`x:num`; `2`; `32`] MOD_MOD))]);;

(*** The input as 64 words of 24 bits w k, and the 128-bit parts of it that
 *** LD3 reads as joins of their bytes ***)

let CBD3_MERGES = map (fun k ->
  let addr = if k = 0 then `a:int64` else
    mk_comb(mk_comb(`word_add:int64->int64->int64`,`a:int64`),
            mk_comb(`word:num->int64`, mk_small_numeral(16 * k))) in
  READ_MEMORY_MERGE_CONV 4
   (vsubst [addr,`x:int64`] `read (memory :> bytes128 x) s0`)) (0--11);;

let CBD3_INPUT_TAC =
  SUBGOAL_THEN `?w:num->24 word. !k. word(n DIV 2 EXP (24 * k)) = w k`
   STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\k. word(n DIV 2 EXP (24 * k)):24 word` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k < 64
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
     (SPECL [`a:int64`; `n:num`; `k:num`; `s0:armstate`; `0`] CBD3_BYTES)) THEN
    MP_TAC(CONV_RULE NUM_REDUCE_CONV
     (SPECL [`a:int64`; `n:num`; `k:num`; `s0:armstate`; `1`] CBD3_BYTES)) THEN
    MP_TAC(CONV_RULE NUM_REDUCE_CONV
     (SPECL [`a:int64`; `n:num`; `k:num`; `s0:armstate`; `2`] CBD3_BYTES)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  MAP_EVERY MP_TAC CBD3_MERGES THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes8 a) s = x`];;

(*** After each step: the registers loaded by LD3 and the 128-bit parts of
 *** the memory written by ST4 as joins, and the subwords taken through
 *** AND and OR to the lanes of single groups ***)

let CBD3_SIMPLIFY_CONV =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC REWR_CONV WORD_SUBWORD_OR ORELSEC
    WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV;;

let CBD3_SIMD_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (fun t -> match t with
              Const(("word_subdeinterleave"|"word_interleave"),_) -> true
            | _ -> false)) (concl th)
    then CONV_RULE(RAND_CONV CBD3_SIMPLIFY_CONV)
          (CONV_RULE(TOP_DEPTH_CONV MLKEM_NATIVE_INTERLEAVE_CONV) th)
    else th) THEN
  TRY(FIRST_X_ASSUM(ASSUME_TAC o CONV_RULE(RAND_CONV CBD3_SIMPLIFY_CONV) o
    check (can (term_match [] `read X (s:armstate):int128 = whatever`) o
           concl)));;

(*** The restored D registers, as zero extensions of the 64 bits saved ***)

let CBD3_DREG = prove
 (`!x:int64. word_zx(word_zx x:int128):int64 = x`,
  BITBLAST_TAC);;

(*** The loop branch, between pointers with known offsets ***)

let CBD3_BRANCH_TAC =
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read PC s = if p then x else y`) (concl th)
    then CONV_RULE(RAND_CONV
          (REWRITE_CONV[WORD_RULE
            `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`]
           THENC DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
           REWRITE_CONV[])) th
    else th);;

let CBD3_STEPS_TAC k =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O3_EXEC [k] THEN CBD3_SIMD_TAC;;

let CBD3_ITERATION_TAC it =
  MAP_EVERY CBD3_STEPS_TAC ((14 + 118 * it)--(131 + 118 * it)) THEN
  CBD3_BRANCH_TAC;;

(*** The stored coefficients, from the 32 stores of 16 bytes ***)

let CBD3_STORES_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
    check (fun th -> can (term_match []
                     `read (memory :> bytes128 a) s = x`) (concl th) &&
                     free_in `r:int64` (concl th)))) THEN
  REPEAT(DISCH_THEN(fun th ->
    MAP_EVERY (ASSUME_TAC o
      CONV_RULE(RAND_CONV CBD3_SIMPLIFY_CONV) o
      CONV_RULE(LAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD])))
     (CONJUNCTS th)));;

(*** Each coefficient i = 4 * g + c in the canonical form of CBD3_LANE for
 *** the field c of w g, to be bit-blasted against the stored value ***)

let CBD3_FIELDS_TAC =
  let norm = CONV_RULE(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) in
  FIRST_ASSUM(fun def ->
    if is_forall(concl def) && free_in `w:num->24 word` (concl def) &&
       not(is_imp(snd(dest_forall(concl def))))
    then
      let ths = map (fun i ->
        let g = i / 4 and c = i mod 4 in
        let gt = mk_small_numeral g and ct = mk_small_numeral c in
        let wg = mk_comb(`w:num->24 word`,gt) in
        let th = MP (SPECL [`n:num`; gt; ct; wg] CBD3_LANE)
                    (CONJ (EQT_ELIM(NUM_LT_CONV(mk_binop
                             `(<):num->num->bool` ct `4`)))
                          (SPEC gt def)) in
        GSYM(norm(CONV_RULE(TOP_DEPTH_CONV let_CONV) th))) (0--255) in
      REWRITE_TAC ths
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. As for mlkem_cbd 3 in common/fips203.ml, coefficient i *)
(* of the result is the number of 1 bits among bits 6 * i to 6 * i + 2 of    *)
(* the 192 bytes as a number n, minus the number among bits 6 * i + 3 to     *)
(* 6 * i + 5, here as a 16-bit integer rather than modulo 3329.              *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_CBD3_GCC12_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (`!r a n pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,192)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,libmlkem_size); (a,192); (r,512)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                  read PC s = word (pc + mlkem_poly_cbd3) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes(a,192)) s = n)
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes16(word_add r (word(2 * i)))) s =
                          iword(&((n DIV 2 EXP (6 * i)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 1)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 2)) MOD 2) -
                                &((n DIV 2 EXP (6 * i + 3)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 4)) MOD 2 +
                                  (n DIV 2 EXP (6 * i + 5)) MOD 2)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,512);
                         memory :> bytes(word_sub stackpointer
                                                 (word 32),32)])`,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 32 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_PRESERVED_DREG_TAC "d8_init" `D8` THEN
  ENSURES_PRESERVED_DREG_TAC "d9_init" `D9` THEN
  ENSURES_PRESERVED_DREG_TAC "d10_init" `D10` THEN
  ENSURES_INIT_TAC "s0" THEN
  CBD3_INPUT_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o
    MATCH_MP MLKEM_NATIVE_POLY_CBD3_GCC12_O3_CONSTANTS) THEN

  (*** The overlap check, the setup, the four iterations and the exit ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O3_EXEC (1--7) THEN
  ALIAS_BRANCH_TAC `r:int64` `512` `a:int64` `192` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O3_EXEC (8--8) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O3_EXEC (9--13) THEN
  MAP_EVERY CBD3_ITERATION_TAC (0--3) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O3_EXEC (486--488) THEN
  CBD3_STORES_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[CBD3_DREG] THEN

  (*** Each coefficient from its 6-bit field ***)

  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_MULT_CONV ORELSEC NUM_ADD_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN CBD3_FIELDS_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let MLKEM_NATIVE_POLY_CBD3_GCC12_O3_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e r a pc stackpointer returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           aligned 16 stackpointer /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,192] /\
           ALL (nonoverlapping (word_sub stackpointer (word 32),32))
               [word pc,libmlkem_size; a,192; r,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O3_mc /\
                    read PC s = word (pc + mlkem_poly_cbd3) /\
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
                          [a,192; r,512;
                           word (pc + mlkem_poly_cbd3_consts),16;
                           word_sub stackpointer (word 32),32]
                          [r,512; word_sub stackpointer (word 32),32]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512);
                           memory :> bytes(word_sub stackpointer
                                                   (word 32),32)])`,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      f_ev a r pc stackpointer returnaddress:(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_CBD3_GCC12_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_PRESERVED_DREG_TAC "d8_init" `D8` THEN
  ENSURES_PRESERVED_DREG_TAC "d9_init" `D9` THEN
  ENSURES_PRESERVED_DREG_TAC "d10_init" `D10` THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O3_EXEC (1--7) THEN
  ALIAS_BRANCH_TAC `r:int64` `512` `a:int64` `192` THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O3_EXEC (8--8) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O3_EXEC (9--13) THEN
  MAP_EVERY (fun it ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O3_EXEC
     ((14 + 118 * it)--(131 + 118 * it)) THEN
    CBD3_BRANCH_TAC) (0--3) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_O3_EXEC (486--488) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[CBD3_DREG] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
