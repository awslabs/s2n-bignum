(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Centered binomial distribution with eta = 3. This is the code for         *)
(* mlkem_poly_cbd3 from mlkem-native's portable C implementation compiled by *)
(* clang 17 with -O2 (see mlkem_native/README.md). It is verified in the     *)
(* whole image (see libmlkem.ml).                                            *)
(*                                                                           *)
(* The compiler has vectorized the loop, 64 coefficients for each iteration  *)
(* from 48 bytes, with one LD3, TBL and shifts to put the three bytes of     *)
(* each group in a 32-bit lane, and two ST4, after a check that the input    *)
(* and the output do not overlap, with one branch for each of the two orders *)
(* of the arrays; if they overlap, the code falls back to a loop that        *)
(* handles one group of three bytes at a time. Since the specification       *)
(* requires them not to overlap, only the vector code runs. It saves no      *)
(* registers on the stack, so as at gcc -O2 the specifications have no stack *)
(* frame, but it reads four vectors of byte indices for TBL from the         *)
(* read-only data (the mask 0x249249 is made with MOV and MOVK), which the   *)
(* safety theorem has among the regions read. The four iterations of the     *)
(* vector loop are simulated one after the other.                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/overlap.ml";;
needs "arm/proofs/mlkem_native/interleave.ml";;
needs "arm/proofs/mlkem_native/clang17_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_poly_cbd3:
       +0x0: add     x8, x1, #0xc0
       +0x4: cmp     x8, x0
       +0x8: b.ls    <mlkem_poly_cbd3+0xb8>
       +0xc: add     x8, x0, #0x200
      +0x10: cmp     x8, x1
      +0x14: b.ls    <mlkem_poly_cbd3+0xb8>
      +0x18: adrp    x10, <page>
      +0x1c: adrp    x11, <page>
      +0x20: mov     w9, #0x9249
      +0x24: movi    v0.2s, #0x7
      +0x28: mov     x8, xzr
      +0x2c: movk    w9, #0x24, lsl #16
      +0x30: ldr     d1, [x10, #640]
      +0x34: add     x10, x1, #0x1
      +0x38: ldr     d2, [x11, #648]
      +0x3c: ldurh   w11, [x10, #-1]
      +0x40: add     x14, x0, x8
      +0x44: ldrb    w12, [x10, #1]
      +0x48: add     x8, x8, #0x8
      +0x4c: add     x10, x10, #0x3
      +0x50: cmp     x8, #0x200
      +0x54: orr     w11, w11, w12, lsl #16
      +0x58: and     w12, w11, w9
      +0x5c: and     w13, w9, w11, lsr #1
      +0x60: and     w11, w9, w11, lsr #2
      +0x64: add     w12, w13, w12
      +0x68: add     w11, w12, w11
      +0x6c: and     w12, w11, #0x7
      +0x70: ubfx    w13, w11, #3, #3
      +0x74: sub     w12, w12, w13
      +0x78: dup     v3.2s, w11
      +0x7c: strh    w12, [x14]
      +0x80: ubfx    w12, w11, #18, #3
      +0x84: sub     w11, w12, w11, lsr #21
      +0x88: ushl    v4.2s, v3.2s, v1.2s
      +0x8c: ushl    v3.2s, v3.2s, v2.2s
      +0x90: and     v4.8b, v4.8b, v0.8b
      +0x94: and     v3.8b, v3.8b, v0.8b
      +0x98: sub     v3.2s, v4.2s, v3.2s
      +0x9c: strh    w11, [x14, #6]
      +0xa0: mov     w15, v3.s[1]
      +0xa4: fmov    w13, s3
      +0xa8: strh    w13, [x14, #2]
      +0xac: strh    w15, [x14, #4]
      +0xb0: b.ne    <mlkem_poly_cbd3+0x3c>
      +0xb4: b       <mlkem_poly_cbd3+0x330>
      +0xb8: adrp    x9, <page>
      +0xbc: adrp    x10, <page>
      +0xc0: adrp    x11, <page>
      +0xc4: mov     x8, xzr
      +0xc8: movi    v3.4s, #0x7
      +0xcc: ldr     q0, [x9, #336]
      +0xd0: adrp    x9, <page>
      +0xd4: ldr     q1, [x10, #352]
      +0xd8: mov     w10, #0x9249
      +0xdc: movk    w10, #0x24, lsl #16
      +0xe0: ldr     q2, [x11, #3312]
      +0xe4: ldr     q4, [x9, #368]
      +0xe8: dup     v5.4s, w10
      +0xec: add     x9, x1, x8
      +0xf0: add     x8, x8, #0x30
      +0xf4: cmp     x8, #0xc0
      +0xf8: ld3     {v16.16b-v18.16b}, [x9]
      +0xfc: add     x9, x0, #0x80
     +0x100: tbl     v21.16b, {v17.16b}, v4.16b
     +0x104: tbl     v23.16b, {v17.16b}, v1.16b
     +0x108: tbl     v24.16b, {v17.16b}, v0.16b
     +0x10c: tbl     v22.16b, {v17.16b}, v2.16b
     +0x110: tbl     v6.16b, {v16.16b}, v0.16b
     +0x114: tbl     v7.16b, {v16.16b}, v1.16b
     +0x118: tbl     v19.16b, {v16.16b}, v2.16b
     +0x11c: tbl     v20.16b, {v16.16b}, v4.16b
     +0x120: tbl     v25.16b, {v18.16b}, v0.16b
     +0x124: tbl     v26.16b, {v18.16b}, v1.16b
     +0x128: tbl     v27.16b, {v18.16b}, v2.16b
     +0x12c: tbl     v16.16b, {v18.16b}, v4.16b
     +0x130: shl     v17.4s, v24.4s, #8
     +0x134: shl     v18.4s, v21.4s, #8
     +0x138: shl     v21.4s, v23.4s, #8
     +0x13c: shl     v22.4s, v22.4s, #8
     +0x140: orr     v18.16b, v18.16b, v20.16b
     +0x144: shl     v16.4s, v16.4s, #16
     +0x148: orr     v7.16b, v21.16b, v7.16b
     +0x14c: orr     v6.16b, v17.16b, v6.16b
     +0x150: shl     v17.4s, v25.4s, #16
     +0x154: shl     v20.4s, v27.4s, #16
     +0x158: shl     v21.4s, v26.4s, #16
     +0x15c: orr     v19.16b, v22.16b, v19.16b
     +0x160: orr     v6.16b, v6.16b, v17.16b
     +0x164: orr     v7.16b, v7.16b, v21.16b
     +0x168: orr     v17.16b, v19.16b, v20.16b
     +0x16c: orr     v16.16b, v18.16b, v16.16b
     +0x170: ushr    v22.4s, v6.4s, #1
     +0x174: ushr    v23.4s, v16.4s, #1
     +0x178: ushr    v24.4s, v7.4s, #1
     +0x17c: ushr    v25.4s, v17.4s, #1
     +0x180: and     v18.16b, v16.16b, v5.16b
     +0x184: ushr    v16.4s, v16.4s, #2
     +0x188: and     v19.16b, v17.16b, v5.16b
     +0x18c: and     v20.16b, v7.16b, v5.16b
     +0x190: and     v21.16b, v6.16b, v5.16b
     +0x194: and     v23.16b, v23.16b, v5.16b
     +0x198: and     v25.16b, v25.16b, v5.16b
     +0x19c: and     v24.16b, v24.16b, v5.16b
     +0x1a0: and     v22.16b, v22.16b, v5.16b
     +0x1a4: ushr    v6.4s, v6.4s, #2
     +0x1a8: ushr    v17.4s, v17.4s, #2
     +0x1ac: ushr    v7.4s, v7.4s, #2
     +0x1b0: add     v21.4s, v22.4s, v21.4s
     +0x1b4: add     v20.4s, v24.4s, v20.4s
     +0x1b8: add     v19.4s, v25.4s, v19.4s
     +0x1bc: add     v18.4s, v23.4s, v18.4s
     +0x1c0: and     v6.16b, v6.16b, v5.16b
     +0x1c4: and     v22.16b, v7.16b, v5.16b
     +0x1c8: and     v7.16b, v17.16b, v5.16b
     +0x1cc: and     v16.16b, v16.16b, v5.16b
     +0x1d0: add     v17.4s, v18.4s, v16.4s
     +0x1d4: add     v16.4s, v19.4s, v7.4s
     +0x1d8: add     v7.4s, v21.4s, v6.4s
     +0x1dc: add     v6.4s, v20.4s, v22.4s
     +0x1e0: ushr    v23.4s, v7.4s, #3
     +0x1e4: ushr    v25.4s, v6.4s, #3
     +0x1e8: ushr    v26.4s, v7.4s, #9
     +0x1ec: and     v18.16b, v7.16b, v3.16b
     +0x1f0: ushr    v27.4s, v6.4s, #9
     +0x1f4: and     v19.16b, v6.16b, v3.16b
     +0x1f8: and     v23.16b, v23.16b, v3.16b
     +0x1fc: and     v25.16b, v25.16b, v3.16b
     +0x200: sub     v19.4s, v19.4s, v25.4s
     +0x204: sub     v18.4s, v18.4s, v23.4s
     +0x208: ushr    v23.4s, v7.4s, #6
     +0x20c: ushr    v25.4s, v6.4s, #6
     +0x210: ushr    v22.4s, v17.4s, #3
     +0x214: ushr    v24.4s, v16.4s, #3
     +0x218: and     v23.16b, v23.16b, v3.16b
     +0x21c: and     v25.16b, v25.16b, v3.16b
     +0x220: and     v26.16b, v26.16b, v3.16b
     +0x224: and     v27.16b, v27.16b, v3.16b
     +0x228: and     v20.16b, v16.16b, v3.16b
     +0x22c: and     v21.16b, v17.16b, v3.16b
     +0x230: and     v24.16b, v24.16b, v3.16b
     +0x234: and     v22.16b, v22.16b, v3.16b
     +0x238: sub     v25.4s, v25.4s, v27.4s
     +0x23c: sub     v23.4s, v23.4s, v26.4s
     +0x240: sub     v22.4s, v21.4s, v22.4s
     +0x244: sub     v24.4s, v20.4s, v24.4s
     +0x248: uzp1    v18.8h, v18.8h, v19.8h
     +0x24c: uzp1    v19.8h, v23.8h, v25.8h
     +0x250: ushr    v23.4s, v16.4s, #6
     +0x254: ushr    v25.4s, v17.4s, #6
     +0x258: ushr    v26.4s, v16.4s, #9
     +0x25c: ushr    v27.4s, v17.4s, #9
     +0x260: and     v23.16b, v23.16b, v3.16b
     +0x264: and     v25.16b, v25.16b, v3.16b
     +0x268: and     v26.16b, v26.16b, v3.16b
     +0x26c: and     v27.16b, v27.16b, v3.16b
     +0x270: sub     v25.4s, v25.4s, v27.4s
     +0x274: sub     v23.4s, v23.4s, v26.4s
     +0x278: uzp1    v26.8h, v24.8h, v22.8h
     +0x27c: ushr    v22.4s, v17.4s, #12
     +0x280: ushr    v24.4s, v17.4s, #15
     +0x284: and     v22.16b, v22.16b, v3.16b
     +0x288: and     v24.16b, v24.16b, v3.16b
     +0x28c: uzp1    v27.8h, v23.8h, v25.8h
     +0x290: ushr    v23.4s, v16.4s, #12
     +0x294: sub     v22.4s, v22.4s, v24.4s
     +0x298: ushr    v24.4s, v16.4s, #15
     +0x29c: and     v23.16b, v23.16b, v3.16b
     +0x2a0: and     v24.16b, v24.16b, v3.16b
     +0x2a4: sub     v23.4s, v23.4s, v24.4s
     +0x2a8: ushr    v24.4s, v6.4s, #12
     +0x2ac: uzp1    v28.8h, v23.8h, v22.8h
     +0x2b0: ushr    v22.4s, v6.4s, #15
     +0x2b4: and     v23.16b, v24.16b, v3.16b
     +0x2b8: and     v22.16b, v22.16b, v3.16b
     +0x2bc: ushr    v24.4s, v17.4s, #18
     +0x2c0: sub     v22.4s, v23.4s, v22.4s
     +0x2c4: ushr    v23.4s, v16.4s, #18
     +0x2c8: ushr    v17.4s, v17.4s, #21
     +0x2cc: ushr    v16.4s, v16.4s, #21
     +0x2d0: bic     v24.4s, #0x38
     +0x2d4: bic     v23.4s, #0x38
     +0x2d8: sub     v17.4s, v24.4s, v17.4s
     +0x2dc: sub     v16.4s, v23.4s, v16.4s
     +0x2e0: ushr    v24.4s, v7.4s, #12
     +0x2e4: ushr    v23.4s, v7.4s, #15
     +0x2e8: uzp1    v29.8h, v16.8h, v17.8h
     +0x2ec: ushr    v16.4s, v6.4s, #18
     +0x2f0: ushr    v17.4s, v7.4s, #18
     +0x2f4: and     v24.16b, v24.16b, v3.16b
     +0x2f8: ushr    v7.4s, v7.4s, #21
     +0x2fc: and     v23.16b, v23.16b, v3.16b
     +0x300: ushr    v6.4s, v6.4s, #21
     +0x304: sub     v23.4s, v24.4s, v23.4s
     +0x308: bic     v17.4s, #0x38
     +0x30c: bic     v16.4s, #0x38
     +0x310: sub     v6.4s, v16.4s, v6.4s
     +0x314: sub     v7.4s, v17.4s, v7.4s
     +0x318: st4     {v26.8h-v29.8h}, [x0], #64
     +0x31c: uzp1    v20.8h, v23.8h, v22.8h
     +0x320: uzp1    v21.8h, v7.8h, v6.8h
     +0x324: st4     {v18.8h-v21.8h}, [x0]
     +0x328: mov     x0, x9
     +0x32c: b.ne    <mlkem_poly_cbd3+0xec>
     +0x330: ret
 ***)

let MLKEM_NATIVE_POLY_CBD3_CLANG17_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O2_mc
   [layout_range "mlkem_poly_cbd3"];;

(*** The four vectors of byte indices for TBL in the vector code ***)

let MLKEM_NATIVE_POLY_CBD3_CLANG17_O2_CONSTANTS =
  map (fun k ->
    MLKEM_NATIVE_IMAGE_CONST_RULE
     (layout("mlkem_poly_cbd3_const" ^ string_of_int k)) 128) (1--4);;

let CBD3_CONSTANTS_TAC =
  MAP_EVERY (fun th -> FIRST_ASSUM(fun ath ->
      if can (term_match [] `aligned_bytes_loaded s0 (word pc)
                               mlkem_native_libmlkem_clang17_O2_mc`)
             (concl ath)
      then ASSUME_TAC(MATCH_MP th ath) else failwith ""))
    MLKEM_NATIVE_POLY_CBD3_CLANG17_O2_CONSTANTS;;

(*** The three bytes for four coefficients, as parts of a 24-bit word ***)

let CBD3_BYTES_STMT =
  `!a n i s j.
        read (memory :> bytes(a,192)) s = n /\ i < 64 /\ j < 3
        ==> read (memory :> bytes8(word_add a (word(3 * i + j)))) s =
            word_subword (word(n DIV 2 EXP (24 * i)):24 word) (8 * j,8)`;;

let CBD3_BYTES = assume_spec CBD3_BYTES_STMT;;

(* ------------------------------------------------------------------------- *)
(* As at -O2, coefficient j of 4 for a 24-bit word t comes from the 6-bit    *)
(* field j of t (CBD3_LANE, with the lemmas of gcc12_O2). Here each 32-bit   *)
(* lane of the vector code holds the 24 bits of one group of three bytes,    *)
(* adds its groups of three bits with the mask 0x249249, and the fields are  *)
(* then taken out with SHRN, USHR, UZP1 and AND with 7 and subtracted.       *)
(* ------------------------------------------------------------------------- *)

let SIXBIT_BIT_STMT =
  `!n m k. k < 6
           ==> (n DIV 2 EXP (m + k)) MOD 2 =
               (((n DIV 2 EXP m) MOD 64) DIV 2 EXP k) MOD 2`;;

let SIXBIT_BIT = assume_spec SIXBIT_BIT_STMT;;

let CBD3_FIELD_STMT =
  `!m. m < 64
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
                 &((m DIV 8) MOD 2 + (m DIV 16) MOD 2 + (m DIV 32) MOD 2))`;;

let CBD3_FIELD = assume_spec CBD3_FIELD_STMT;;

let CBD3_LANE_STMT =
  `!n i j w:24 word.
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
                  (n DIV 2 EXP (6 * (4 * i + j) + 5)) MOD 2))`;;

let CBD3_LANE = assume_spec CBD3_LANE_STMT;;

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

(* ------------------------------------------------------------------------- *)
(* The check for overlap has one branch for each order of the arrays: with   *)
(* the input a (192 bytes) and the output r (512 bytes), the scalar loop is  *)
(* taken unless a + 192 <= r or r + 512 <= a. In either case the vector code *)
(* is entered at the same instruction, after 3 or 6 steps respectively.      *)
(* ------------------------------------------------------------------------- *)

let CBD3_RESOLVE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[VAL_WORD_SUB_FLAG; VAL_WORD_SUB_EQ_0]) THEN
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read PC s = if p then x else y`) c then
      let p = rand(rator(rator(rand c))) in
      let decide q = SUBGOAL_THEN q (fun th' ->
        ASSUME_TAC(REWRITE_RULE[th'] th)) THENL [ASM_ARITH_TAC; ALL_TAC] in
      decide p ORELSE decide (mk_neg p)
    else failwith "CBD3_RESOLVE_TAC");;

let CBD3_CHECK_TAC (body:int->tactic) =
  MP_TAC(SPECL [`r:int64`; `a:int64`; `512`; `192`]
                NONOVERLAPPING_ALIAS_CHECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  DISCH_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_CLANG17_O2_EXEC (1--3) THEN
  ASM_CASES_TAC `val(word_add a (word 192):int64) <= val(r:int64)` THENL
   [CBD3_RESOLVE_TAC THEN body 3;
    CBD3_RESOLVE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_CLANG17_O2_EXEC (4--6) THEN
    CBD3_RESOLVE_TAC THEN body 6];;

(*** The vector code from join1 on: the setup of 13 steps with the page
 *** of the constants computed by ADRP (steps 1, 2, 3 and 7), four
 *** iterations of 145 steps, and the return ***)

let CBD3_ADRP_STEPS = [1;2;3;7];;

let CBD3_BODY_TAC (simp:tactic) off =
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_CLANG17_O2_EXEC [k + off] THEN
    (if mem k CBD3_ADRP_STEPS then MLKEM_NATIVE_ADRP_TAC else ALL_TAC) THEN
    simp) (1--594);;

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
(* Correctness proof. As for mlkem_cbd 3 in common/fips203/fips203.ml,       *)
(* coefficient i of the result is the number of 1 bits among bits 6 * i to 6 *)
(* * i + 2 of the 192 bytes as a number n, minus the number among bits 6 * i *)
(* + 3 to 6 * i + 5, here as a 16-bit integer rather than modulo 3329.       *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_POLY_CBD3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!r a n pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,512)) [(word pc,libmlkem_size); (a,192)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O2_mc /\
                  read PC s = word (pc + mlkem_poly_cbd3) /\
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
              MAYCHANGE [memory :> bytes(r,512)])`;;

let MLKEM_NATIVE_POLY_CBD3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_CBD3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let mlkem_native_poly_cbd3_signature =
  ([("r", "int16_t[static 256]", "false");
    ("a", "uint8_t[static 192]", "true")],
   "void",
   [("a", "192", 1)],
   [("r", "256", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + mlkem_poly_cbd3_consts):int64`,
                       `mlkem_poly_cbd3_consts_size:num`]
    ~keep_maychanges:true
    mlkem_native_poly_cbd3_signature
    MLKEM_NATIVE_POLY_CBD3_CLANG17_O2_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_CBD3_CLANG17_O2_EXEC;;

let MLKEM_NATIVE_POLY_CBD3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e r a pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (r,512)) [word pc,libmlkem_size; a,192]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_clang17_O2_mc /\
                    read PC s = word (pc + mlkem_poly_cbd3) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a r pc returnaddress /\
                         memaccess_inbounds e2
                         [a,192; r,512;
                          word (pc + mlkem_poly_cbd3_consts),
                          mlkem_poly_cbd3_consts_size]
                         [r,512]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes (r,512)])`;;

let MLKEM_NATIVE_POLY_CBD3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_CBD3_CLANG17_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
