(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar product of 4-element polynomial vectors in NTT domain.             *)
(* This is the code for mlkem1024_polyvec_basemul_acc_montgomery_cached from *)
(* mlkem-native's portable C implementation compiled by clang 17 with -O3    *)
(* (see mlkem_native/README.md), verified in the whole image (see            *)
(* libmlkem.ml) with the specification of the gcc 12 -O2 code.               *)
(*                                                                           *)
(* As with gcc 12 -O3, clang has vectorized the loop over the pairs of       *)
(* coefficients, 8 pairs at a time with LD2 and ST2, unless the output may   *)
(* overlap one of the inputs, in which case it uses a scalar loop. Unlike    *)
(* gcc, it checks the output against each of the three inputs, with CMP and  *)
(* CCMP computing with the addresses modulo 2^64, and makes its vectors of   *)
(* constants with DUP and MVNI. When the output does not overlap the inputs  *)
(* the checks always take the vector loop, so that is the only path         *)
(* verified here. The Montgomery reduction computes the low half of the      *)
(* quotient as the high half of the 32-bit product of the sum by             *)
(* 3329^-1 mod 2^16 shifted left by 16, as clang's mlkem_poly_tomont does.   *)
(*                                                                           *)
(* Since the constants are not loaded from the read-only data, the safety    *)
(* theorem has the same regions as for gcc 12 -O2.                           *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/utils/mlkem_native_overlap.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image, the vector loop from +0x4c to +0x170 and the
 *** scalar loop from +0x178:

    mlkem1024_polyvec_basemul_acc_montgomery_cached:
       +0x0: add     x8, x3, #0x400
       +0x4: add     x10, x0, #0x200
       +0x8: cmp     x8, x0
       +0xc: add     x9, x2, #0x800
      +0x10: ccmp    x10, x3, #0x0, hi
      +0x14: add     x11, x1, #0x800
      +0x18: cset    w8, hi
      +0x1c: cmp     x9, x0
      +0x20: ccmp    x10, x2, #0x0, hi
      +0x24: cset    w9, hi
      +0x28: cmp     x10, x1
      +0x2c: ccmp    x11, x0, #0x0, hi
      +0x30: b.hi    <join1>
      +0x34: tbnz    w8, #0, join1
      +0x38: cbnz    w9, join1
      +0x3c: mov     w9, #0xf3010000
      +0x40: mov     x8, xzr
      +0x44: mvni    v1.4s, #0xd, lsl #8
      +0x48: dup     v0.4s, w9
      +0x4c: add     x10, x1, x8
      +0x50: add     x9, x2, x8
      +0x54: add     x11, x10, #0x200
      +0x58: ldr     q20, [x3]
      +0x5c: ldr     q23, [x3, #256]
      +0x60: ld2     {v6.8h-v7.8h}, [x10]
      +0x64: ld2     {v16.8h-v17.8h}, [x9]
      +0x68: ld2     {v18.8h-v19.8h}, [x11]
      +0x6c: add     x11, x9, #0x200
      +0x70: smull   v3.4s, v16.4h, v6.4h
      +0x74: smull2  v2.4s, v16.8h, v6.8h
      +0x78: ld2     {v21.8h-v22.8h}, [x11]
      +0x7c: smull   v5.4s, v17.4h, v6.4h
      +0x80: add     x11, x10, #0x400
      +0x84: smull2  v4.4s, v17.8h, v6.8h
      +0x88: add     x10, x10, #0x600
      +0x8c: smlal   v3.4s, v20.4h, v7.4h
      +0x90: smlal2  v2.4s, v20.8h, v7.8h
      +0x94: ld2     {v24.8h-v25.8h}, [x11]
      +0x98: smlal   v5.4s, v16.4h, v7.4h
      +0x9c: add     x11, x9, #0x400
      +0xa0: smlal2  v4.4s, v16.8h, v7.8h
      +0xa4: add     x9, x9, #0x600
      +0xa8: smlal   v3.4s, v23.4h, v19.4h
      +0xac: smlal2  v2.4s, v23.8h, v19.8h
      +0xb0: ld2     {v6.8h-v7.8h}, [x11]
      +0xb4: smlal   v5.4s, v21.4h, v19.4h
      +0xb8: smlal2  v4.4s, v21.8h, v19.8h
      +0xbc: smlal   v3.4s, v21.4h, v18.4h
      +0xc0: ldr     q16, [x3, #512]
      +0xc4: smlal2  v2.4s, v21.8h, v18.8h
      +0xc8: ld2     {v26.8h-v27.8h}, [x10]
      +0xcc: smlal   v5.4s, v22.4h, v18.4h
      +0xd0: smlal   v3.4s, v16.4h, v25.4h
      +0xd4: smlal2  v4.4s, v22.8h, v18.8h
      +0xd8: smlal2  v2.4s, v16.8h, v25.8h
      +0xdc: ldr     q16, [x3, #768]
      +0xe0: smlal   v5.4s, v6.4h, v25.4h
      +0xe4: ld2     {v17.8h-v18.8h}, [x9]
      +0xe8: smlal   v3.4s, v6.4h, v24.4h
      +0xec: add     x9, x0, x8
      +0xf0: smlal2  v4.4s, v6.8h, v25.8h
      +0xf4: add     x8, x8, #0x20
      +0xf8: smlal2  v2.4s, v6.8h, v24.8h
      +0xfc: add     x3, x3, #0x10
     +0x100: smlal   v5.4s, v7.4h, v24.4h
     +0x104: cmp     x8, #0x200
     +0x108: smlal   v3.4s, v16.4h, v27.4h
     +0x10c: smlal2  v4.4s, v7.8h, v24.8h
     +0x110: smlal2  v2.4s, v16.8h, v27.8h
     +0x114: smlal   v5.4s, v17.4h, v27.4h
     +0x118: smlal   v3.4s, v17.4h, v26.4h
     +0x11c: smlal2  v4.4s, v17.8h, v27.8h
     +0x120: smlal2  v2.4s, v17.8h, v26.8h
     +0x124: smlal   v5.4s, v18.4h, v26.4h
     +0x128: mul     v6.4s, v3.4s, v0.4s
     +0x12c: smlal2  v4.4s, v18.8h, v26.8h
     +0x130: mul     v7.4s, v2.4s, v0.4s
     +0x134: mul     v16.4s, v5.4s, v0.4s
     +0x138: sshr    v6.4s, v6.4s, #16
     +0x13c: mul     v17.4s, v4.4s, v0.4s
     +0x140: mul     v6.4s, v6.4s, v1.4s
     +0x144: sshr    v7.4s, v7.4s, #16
     +0x148: sshr    v16.4s, v16.4s, #16
     +0x14c: mul     v7.4s, v7.4s, v1.4s
     +0x150: addhn   v18.4h, v6.4s, v3.4s
     +0x154: mul     v3.4s, v16.4s, v1.4s
     +0x158: sshr    v6.4s, v17.4s, #16
     +0x15c: addhn2  v18.8h, v7.4s, v2.4s
     +0x160: mul     v2.4s, v6.4s, v1.4s
     +0x164: addhn   v19.4h, v3.4s, v5.4s
     +0x168: addhn2  v19.8h, v2.4s, v4.4s
     +0x16c: st2     {v18.8h-v19.8h}, [x9]
     +0x170: b.ne    <loop1>
     +0x174: b       <join2>
     +0x178: mov     x8, xzr
     +0x17c: mov     w9, #0xf3010000
     +0x180: mov     w10, #0xfffff2ff
     +0x184: add     x11, x1, x8
     +0x188: add     x13, x2, x8
     +0x18c: ldrsh   w12, [x3]
     +0x190: ldrsh   w4, [x3, #256]
     +0x194: ldrsh   w14, [x11, #2]
     +0x198: ldrsh   w16, [x13]
     +0x19c: ldrsh   w15, [x11]
     +0x1a0: ldrsh   w17, [x13, #2]
     +0x1a4: mul     w12, w12, w14
     +0x1a8: ldrsh   w18, [x11, #514]
     +0x1ac: mul     w14, w16, w14
     +0x1b0: ldrsh   w6, [x13, #512]
     +0x1b4: madd    w12, w16, w15, w12
     +0x1b8: ldrsh   w5, [x11, #512]
     +0x1bc: madd    w14, w17, w15, w14
     +0x1c0: ldrsh   w16, [x13, #514]
     +0x1c4: madd    w12, w4, w18, w12
     +0x1c8: ldrsh   w15, [x11, #1026]
     +0x1cc: madd    w14, w6, w18, w14
     +0x1d0: ldrsh   w17, [x3, #512]
     +0x1d4: madd    w12, w6, w5, w12
     +0x1d8: ldrsh   w4, [x13, #1024]
     +0x1dc: madd    w14, w16, w5, w14
     +0x1e0: ldrsh   w18, [x11, #1024]
     +0x1e4: ldrsh   w16, [x13, #1026]
     +0x1e8: madd    w12, w17, w15, w12
     +0x1ec: madd    w14, w4, w15, w14
     +0x1f0: ldrsh   w17, [x11, #1538]
     +0x1f4: ldrsh   w15, [x3, #768]
     +0x1f8: madd    w12, w4, w18, w12
     +0x1fc: ldrsh   w4, [x13, #1536]
     +0x200: madd    w14, w16, w18, w14
     +0x204: ldrsh   w11, [x11, #1536]
     +0x208: add     x3, x3, #0x2
     +0x20c: ldrsh   w13, [x13, #1538]
     +0x210: madd    w12, w15, w17, w12
     +0x214: madd    w14, w4, w17, w14
     +0x218: madd    w12, w4, w11, w12
     +0x21c: madd    w11, w13, w11, w14
     +0x220: mul     w13, w12, w9
     +0x224: mul     w14, w11, w9
     +0x228: asr     w13, w13, #16
     +0x22c: asr     w14, w14, #16
     +0x230: madd    w12, w13, w10, w12
     +0x234: add     x13, x0, x8
     +0x238: madd    w11, w14, w10, w11
     +0x23c: add     x8, x8, #0x4
     +0x240: lsr     w12, w12, #16
     +0x244: cmp     x8, #0x200
     +0x248: lsr     w11, w11, #16
     +0x24c: strh    w12, [x13]
     +0x250: strh    w11, [x13, #2]
     +0x254: b.ne    <loop2>
     +0x258: ret
 ***)

let MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem1024_polyvec_basemul_acc_montgomery_cached"];;

(* ------------------------------------------------------------------------- *)
(* Definitions used to state specification, as for mlkem_basemul_k4.         *)
(* ------------------------------------------------------------------------- *)

let pmull = define
  `pmull (x0: int) (x1 : int) (y0 : int) (y1 : int) = x1 * y1 + x0 * y0`;;

let pmull_acc4 = define
  `pmull_acc4 (x00: int) (x01 : int) (y00 : int) (y01 : int)
              (x10: int) (x11 : int) (y10 : int) (y11 : int)
              (x20: int) (x21 : int) (y20 : int) (y21 : int)
              (x30: int) (x31 : int) (y30 : int) (y31 : int) =
              pmull x30 x31 y30 y31 + pmull x20 x21 y20 y21 +
              pmull x10 x11 y10 y11 + pmull x00 x01 y00 y01`;;

let pmul_acc4 = define
  `pmul_acc4 (x00: int) (x01 : int) (y00 : int) (y01 : int)
             (x10: int) (x11 : int) (y10 : int) (y11 : int)
             (x20: int) (x21 : int) (y20 : int) (y21 : int)
             (x30: int) (x31 : int) (y30 : int) (y31 : int) =
             (&(inverse_mod 3329 65536) *
    pmull_acc4 x00 x01 y00 y01 x10 x11 y10 y11 x20 x21 y20 y21
               x30 x31 y30 y31) rem &3329`;;

let basemul4_even = define
 `basemul4_even x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t = \i.
    pmul_acc4 (x0 (2 * i)) (x0 (2 * i + 1))
              (y0 (2 * i)) (y0t i)
              (x1 (2 * i)) (x1 (2 * i + 1))
              (y1 (2 * i)) (y1t i)
              (x2 (2 * i)) (x2 (2 * i + 1))
              (y2 (2 * i)) (y2t i)
              (x3 (2 * i)) (x3 (2 * i + 1))
              (y3 (2 * i)) (y3t i)`;;

let basemul4_odd = define
 `basemul4_odd x0 y0 x1 y1 x2 y2 x3 y3 = \i.
  pmul_acc4 (x0 (2 * i)) (x0 (2 * i + 1))
            (y0 (2 * i + 1)) (y0 (2 * i))
            (x1 (2 * i)) (x1 (2 * i + 1))
            (y1 (2 * i + 1)) (y1 (2 * i))
            (x2 (2 * i)) (x2 (2 * i + 1))
            (y2 (2 * i + 1)) (y2 (2 * i))
            (x3 (2 * i)) (x3 (2 * i + 1))
            (y3 (2 * i + 1)) (y3 (2 * i))`;;

(* ------------------------------------------------------------------------- *)
(* The checks for overlap. For the output r of m bytes and an input b of n   *)
(* bytes, CMP and CCMP give the condition for the scalar loop, b + n > r and *)
(* r + m > b as unsigned numbers, in the form below. When the regions do not *)
(* overlap it is false, by NONOVERLAPPING_ALIAS_CHECK.                       *)
(* ------------------------------------------------------------------------- *)

let BASEMUL_ALIAS = prove
 (`!r b:int64 m n.
     nonoverlapping (r,m) (b,n) /\ ~(m = 0) /\ ~(n = 0) /\
     m < 2 EXP 64 /\ n < 2 EXP 64
     ==> ~((if val r <= val (word_add b (word n)) /\
               ~(val (word_sub (word_add b (word n)) r) = 0)
            then &(val (word_add r (word m))) - &(val b):int =
                 &(val (word_sub (word_add r (word m)) b))
            else F) /\
           ~(if val r <= val (word_add b (word n)) /\
                ~(val (word_sub (word_add b (word n)) r) = 0)
             then val (word_sub (word_add r (word m)) b) = 0
             else F))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP NONOVERLAPPING_ALIAS_CHECK) THEN
  REWRITE_TAC[VAL_WORD_SUB_FLAG; VAL_WORD_SUB_EQ_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

(*** Simplify the three conditions in the assumptions, after the branch
 *** for the third one has been simulated
 ***)

let BASEMUL_ALIAS_TAC =
  MAP_EVERY (fun (r,m,b,n) ->
    MP_TAC(SPECL [r; b; m; n] BASEMUL_ALIAS) THEN
    ANTS_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN
      ONCE_REWRITE_TAC[NONOVERLAPPING_SYM] THEN
      ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
      ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))])
   [`dst:int64`,`512`,`srcBt:int64`,`1024`;
    `dst:int64`,`512`,`srcB:int64`,`2048`;
    `srcA:int64`,`2048`,`dst:int64`,`512`];;

(* ------------------------------------------------------------------------- *)
(* The Montgomery reduction of a lane t, with q = 62209 * 2^16, 62209 being  *)
(* 3329^-1 mod 2^16: the arithmetic shift of t * q gives the sign extension  *)
(* of the low half of t * 62209, the quotient of montred_neon.               *)
(* ------------------------------------------------------------------------- *)

let WORD_ISHR_16_SUBWORD = prove
 (`!w:int32. word_ishr w 16 = word_sx(word_subword w (16,16):int16)`,
  BITBLAST_TAC);;

let BASEMUL_LANE = prove
 (`!t:int32.
     word_subword
      (word_add (word_mul (word_ishr (word_mul t (word 4076929024)) 16)
                          (word 4294963967)) t) (16,16):int16 =
     montred_scalar t`,
  GEN_TAC THEN REWRITE_TAC[GSYM MONTRED_NEON_SCALAR; montred_neon] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_ISHR_16_SUBWORD] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_MUL; VAL_WORD;
              DIMINDEX_16; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(t:int32)`,`v:num`) THEN GEN_TAC THEN
  REWRITE_TAC[MOD_MOD_REFL; DIV_1] THEN
  REWRITE_TAC[ARITH_RULE `v * 4076929024 = 65536 * v * 62209`;
              ARITH_RULE `4294967296 = 65536 * 65536`] THEN
  REWRITE_TAC[MOD_MULT2] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ; MOD_MOD_REFL] THEN
  REWRITE_TAC[MOD_MOD; ARITH_EQ; MOD_MULT_LMOD]);;

let BASEMUL_LANE_CONV =
  let pat = lhand(snd(strip_forall(concl BASEMUL_LANE))) in
  fun tm -> INSTANTIATE (term_match [] pat tm) (SPEC_ALL BASEMUL_LANE);;

(*** One step of the simulation of the vector loop ***)

let BASEMUL_STEP_TAC n =
  ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_EXEC [n] THEN
  SIMD_SIMPLIFY_TAC[] THEN
  RULE_ASSUM_TAC(fun th ->
    if free_in `word_ishr:int32->num->int32` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV BASEMUL_LANE_CONV) th else th);;

(*** The loop test, at the end of the body ***)

let BASEMUL_LOOP_FLAG = prove
 (`!i. i < 16
       ==> (~(val (word_add (word (32 * i))
                            (word 18446744073709551136):int64) = 0) <=>
            i + 1 < 16)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  ASM_CASES_TAC `i = 15` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `i < 16 /\ ~(i = 15)
    ==> 32 * i + 18446744073709551136 < 18446744073709551616`] THEN
  SIMPLE_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, as for gcc 12 -O3.                                     *)
(* ------------------------------------------------------------------------- *)

(*** The addresses of the coefficients relative to those of the loads and
 *** stores, in the form that the simulation gives to the addresses
 ***)

let BM_ADDR_AB_GEN = prove
 (`!a:int64 n i k. word_add a (word(n + 2 * (16 * i + k))) =
                   word_add (word_add a (word(32 * i + n))) (word(2 * k))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let BM_ADDR_CD_GEN = prove
 (`!a:int64 n i k. word_add a (word(n + 2 * (8 * i + k))) =
                   word_add (word_add a (word(16 * i + n))) (word(2 * k))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(*** The forms for the coefficients of polynomial j of the vectors, whose
 *** offset is n = 512 * j for the inputs and n = 256 * j for the cache
 ***)

let BM_ADDR_AB n =
  if n = 0 then
    REWRITE_RULE[ADD_CLAUSES]
     (SPEC `0` (CONV_RULE(ONCE_DEPTH_CONV(REWR_CONV SWAP_FORALL_THM))
                 BM_ADDR_AB_GEN))
  else SPEC (mk_small_numeral n)
        (CONV_RULE(ONCE_DEPTH_CONV(REWR_CONV SWAP_FORALL_THM))
           BM_ADDR_AB_GEN);;

let BM_ADDR_CD n =
  if n = 0 then
    REWRITE_RULE[ADD_CLAUSES]
     (SPEC `0` (CONV_RULE(ONCE_DEPTH_CONV(REWR_CONV SWAP_FORALL_THM))
                 BM_ADDR_CD_GEN))
  else SPEC (mk_small_numeral n)
        (CONV_RULE(ONCE_DEPTH_CONV(REWR_CONV SWAP_FORALL_THM))
           BM_ADDR_CD_GEN);;

(*** Instantiate the quantified input fact for f at the n coefficients from
 *** m * i, with the addresses relative to the base of the vector load
 ***)

let BM_LOAD_TAC f m n ath =
  FIRST_ASSUM(fun th ->
    if is_forall(concl th) && free_in f (concl th) then
      MAP_EVERY (fun k ->
        MP_TAC(SPEC (subst [mk_small_numeral m,`m:num`;
                            mk_small_numeral k,`k:num`] `m * i + k`) th) THEN
        ANTS_TAC THENL
         [ASM_ARITH_TAC;
          DISCH_THEN(ASSUME_TAC o REWRITE_RULE[WORD_ADD_0] o
                     CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
                     REWRITE_RULE[ath])]) (0--(n-1))
    else failwith "BM_LOAD_TAC");;

let BM_ADDR_E = prove
 (`!a:int64 i k. word_add a (word(4 * (8 * i + k))) =
                 word_add (word_add a (word(32 * i))) (word(4 * k))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let BM_ADDR_F = prove
 (`!a:int64 i k. word_add a (word(4 * (8 * i + k) + 2)) =
                 word_add (word_add a (word(32 * i))) (word(4 * k + 2))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(*** The indices of the coefficients of pair 8 * i + k, for k < 8 ***)

let BM_IDX_RULES =
  List.concat (map (fun k ->
    let kt = mk_small_numeral k in
    [ARITH_RULE(subst [kt,`k:num`; mk_small_numeral(2 * k),`c:num`]
       `2 * (8 * i + k) = 16 * i + c`);
     ARITH_RULE(subst [kt,`k:num`; mk_small_numeral(2 * k + 1),`c:num`]
       `2 * (8 * i + k) + 1 = 16 * i + c`)]) (0--7));;

(*** The congruence for a lane, a Montgomery-reduced sum of products ***)

let BM_CONG_TAC =
  ASSUM_LIST(fun ths -> W(fun (asl,w) ->
    let tm = rand(rand(lhand(rator w))) in
    let th1 = WEAKEN_INTCONG_RULE (num 3329) (GEN_CONGBOUND_RULE ths tm) in
    let th2 = MATCH_MP CONGBOUND_MONTRED_SCALAR th1 in
    let th3 = MP th2 (EQT_ELIM(INT_REDUCE_CONV(lhand(concl th2)))) in
    MP_TAC(CONJUNCT1 th3))) THEN
  REWRITE_TAC[basemul4_even; basemul4_odd;
              pmul_acc4; pmull_acc4; pmull; o_THM] THEN
  REWRITE_TAC BM_IDX_RULES THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC INT_RING;;

(*** The loop invariant, with 8 * i pairs of outputs done ***)

let basemul_k4_inv =
 `\i s. read X0 s = dst /\ read X1 s = srcA /\ read X2 s = srcB /\
        read X3 s = word_add srcBt (word(16 * i)) /\
        read X8 s = word(32 * i) /\
        read X30 s = returnaddress /\
        read Q0 s = word 0xf3010000f3010000f3010000f3010000 /\
        read Q1 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        (!i. i < 256
             ==> read(memory :> bytes16
                  (word_add srcA (word (2 * i)))) s = x0 i) /\
        (!i. i < 256
             ==> read(memory :> bytes16
                  (word_add srcB (word (2 * i)))) s = y0 i) /\
        (!i. i < 128
             ==> read(memory :> bytes16
                  (word_add srcBt (word (2 * i)))) s = y0t i) /\
        (!i. i < 256
             ==> read(memory :> bytes16
                  (word_add srcA (word (512 + 2 * i)))) s = x1 i) /\
        (!i. i < 256
             ==> read(memory :> bytes16
                  (word_add srcB (word (512 + 2 * i)))) s = y1 i) /\
        (!i. i < 128
             ==> read(memory :> bytes16
                  (word_add srcBt (word (256 + 2 * i)))) s = y1t i) /\
        (!i. i < 256
             ==> read(memory :> bytes16
                  (word_add srcA (word (1024 + 2 * i)))) s = x2 i) /\
        (!i. i < 256
             ==> read(memory :> bytes16
                  (word_add srcB (word (1024 + 2 * i)))) s = y2 i) /\
        (!i. i < 128
             ==> read(memory :> bytes16
                  (word_add srcBt (word (512 + 2 * i)))) s = y2t i) /\
        (!i. i < 256
             ==> read(memory :> bytes16
                  (word_add srcA (word (1536 + 2 * i)))) s = x3 i) /\
        (!i. i < 256
             ==> read(memory :> bytes16
                  (word_add srcB (word (1536 + 2 * i)))) s = y3 i) /\
        (!i. i < 128
             ==> read(memory :> bytes16
                  (word_add srcBt (word (768 + 2 * i)))) s = y3t i) /\
        ((!i. i < 256
              ==> abs(ival(x0 i)) <= &2 pow 12 /\
                  abs(ival(x1 i)) <= &2 pow 12 /\
                  abs(ival(x2 i)) <= &2 pow 12 /\
                  abs(ival(x3 i)) <= &2 pow 12)
         ==> (!j. j < 8 * i
                  ==> (ival(read(memory :> bytes16
                         (word_add dst (word (4 * j)))) s) ==
                       basemul4_even (ival o x0) (ival o y0) (ival o y0t)
                                     (ival o x1) (ival o y1) (ival o y1t)
                                     (ival o x2) (ival o y2) (ival o y2t)
                                     (ival o x3) (ival o y3) (ival o y3t)
                                     j) (mod &3329) /\
                      (ival(read(memory :> bytes16
                         (word_add dst (word (4 * j + 2)))) s) ==
                       basemul4_odd (ival o x0) (ival o y0)
                                     (ival o x1) (ival o y1)
                                     (ival o x2) (ival o y2)
                                     (ival o x3) (ival o y3)
                                     j) (mod &3329)))`;;

let basemul_k4_goal =
 `!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t x2 y2 y2t x3 y3 y3t
    pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
     ALL (nonoverlapping (dst, 512))
         [(word pc, libmlkem_size); (srcA, 2048); (srcB, 2048); (srcBt, 1024)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc)
              mlkem_native_libmlkem_clang17_O3_mc /\
            read PC s =
              word (pc + mlkem1024_polyvec_basemul_acc_montgomery_cached) /\
            read X30 s = returnaddress /\
            C_ARGUMENTS [dst; srcA; srcB; srcBt] s  /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (2 * i)))) s = x0 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (2 * i)))) s = y0 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (2 * i)))) s = y0t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (512 + 2 * i)))) s = x1 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (512 + 2 * i)))) s = y1 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (256 + 2 * i)))) s = y1t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (1024 + 2 * i)))) s = x2 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (1024 + 2 * i)))) s = y2 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (512 + 2 * i)))) s = y2t i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (1536 + 2 * i)))) s = x3 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB (word (1536 + 2 * i)))) s = y3 i) /\
            (!i. i < 128
                 ==> read(memory :> bytes16
                      (word_add srcBt (word (768 + 2 * i)))) s = y3t i))
       (\s. read PC s = returnaddress /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                       abs(ival(x1 i)) <= &2 pow 12 /\
                       abs(ival(x2 i)) <= &2 pow 12 /\
                       abs(ival(x3 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul4_even
                            (ival o x0) (ival o y0) (ival o y0t) (ival o x1)
                            (ival o y1) (ival o y1t) (ival o x2) (ival o y2)
                            (ival o y2t) (ival o x3) (ival o y3) (ival o y3t)
                            i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul4_odd
                            (ival o x0) (ival o y0) (ival o x1) (ival o y1)
                            (ival o x2) (ival o y2) (ival o x3) (ival o y3)
                            i) (mod &3329))))
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
        MAYCHANGE [memory :> bytes(dst, 512)])`;;

let MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (basemul_k4_goal,
  MAP_EVERY X_GEN_TAC
   [`srcA:int64`; `srcB:int64`; `srcBt:int64`; `dst:int64`;
    `x0:num->int16`; `y0:num->int16`; `y0t:num->int16`;
    `x1:num->int16`; `y1:num->int16`; `y1t:num->int16`;
    `x2:num->int16`; `y2:num->int16`; `y2t:num->int16`;
    `x3:num->int16`; `y3:num->int16`; `y3t:num->int16`;
    `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The vector loop, with the loop test at the end of the body ***)

  ENSURES_WHILE_UP2_TAC `16`
   `pc + mlkem1024_polyvec_basemul_acc_montgomery_cached_loop1`
   `pc + mlkem1024_polyvec_basemul_acc_montgomery_cached_loop1_exit`
   basemul_k4_inv THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The checks for overlap, which go to the vector code, and the
     *** setup of the pointers and the constants
     ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_EXEC (1--13) THEN
    BASEMUL_ALIAS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_EXEC (14--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0; CONJUNCT1 LT];

    (*** The loop body, computing 8 pairs of output coefficients from
     *** 256-bit and 128-bit loads of the inputs
     ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    BM_LOAD_TAC `x0:num->int16` 16 16 (BM_ADDR_AB 0) THEN
    BM_LOAD_TAC `y0:num->int16` 16 16 (BM_ADDR_AB 0) THEN
    BM_LOAD_TAC `y0t:num->int16` 8 8 (BM_ADDR_CD 0) THEN
    BM_LOAD_TAC `x1:num->int16` 16 16 (BM_ADDR_AB 512) THEN
    BM_LOAD_TAC `y1:num->int16` 16 16 (BM_ADDR_AB 512) THEN
    BM_LOAD_TAC `y1t:num->int16` 8 8 (BM_ADDR_CD 256) THEN
    BM_LOAD_TAC `x2:num->int16` 16 16 (BM_ADDR_AB 1024) THEN
    BM_LOAD_TAC `y2:num->int16` 16 16 (BM_ADDR_AB 1024) THEN
    BM_LOAD_TAC `y2t:num->int16` 8 8 (BM_ADDR_CD 512) THEN
    BM_LOAD_TAC `x3:num->int16` 16 16 (BM_ADDR_AB 1536) THEN
    BM_LOAD_TAC `y3:num->int16` 16 16 (BM_ADDR_AB 1536) THEN
    BM_LOAD_TAC `y3t:num->int16` 8 8 (BM_ADDR_CD 768) THEN
    MAP_EVERY (fun t -> MP_TAC(READ_MEMORY_MERGE_CONV 4 t))
     [`read(memory :> bytes256(word_add srcA (word(32 * i)))) s0`;
      `read(memory :> bytes256(word_add srcB (word(32 * i)))) s0`;
      `read(memory :> bytes256(word_add srcA (word(32 * i + 512)))) s0`;
      `read(memory :> bytes256(word_add srcB (word(32 * i + 512)))) s0`;
      `read(memory :> bytes256(word_add srcA (word(32 * i + 1024)))) s0`;
      `read(memory :> bytes256(word_add srcB (word(32 * i + 1024)))) s0`;
      `read(memory :> bytes256(word_add srcA (word(32 * i + 1536)))) s0`;
      `read(memory :> bytes256(word_add srcB (word(32 * i + 1536)))) s0`] THEN
    MAP_EVERY (fun t -> MP_TAC(READ_MEMORY_MERGE_CONV 3 t))
     [`read(memory :> bytes128(word_add srcBt (word(16 * i)))) s0`;
      `read(memory :> bytes128(word_add srcBt (word(16 * i + 256)))) s0`;
      `read(memory :> bytes128(word_add srcBt (word(16 * i + 512)))) s0`;
      `read(memory :> bytes128(word_add srcBt (word(16 * i + 768)))) s0`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
    MAP_EVERY BASEMUL_STEP_TAC (1--74) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
        CONV_RULE (SIMD_SIMPLIFY_CONV []) o
        CONV_RULE(READ_MEMORY_SPLIT_CONV 4) o
        check (fun th ->
          can (term_match [] `read (memory :> bytes256 a) s74 = x`)
              (concl th) && free_in `dst:int64` (concl th)))) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[BASEMUL_LOOP_FLAG] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 32`;
                  ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC]) THEN

    (*** The output pairs j < 8 * i, from the invariant, and the new ones
     *** 8 * i + k for k < 8
     ***)

    DISCH_TAC THEN
    MAP_EVERY (fun c ->
      FIRST_ASSUM(MP_TAC o SPEC (subst [mk_small_numeral c,`c:num`]
                                     `16 * i + c`) o
                  check (fun th -> is_forall(concl th) &&
                                   free_in `abs:int->int` (concl th))) THEN
      ANTS_TAC THENL [UNDISCH_TAC `i < 16` THEN ARITH_TAC; STRIP_TAC])
     (0--15) THEN
    X_GEN_TAC `j:num` THEN
    ASM_CASES_TAC `j < 8 * i` THEN ASM_REWRITE_TAC[] THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `?k. k < 8 /\ j = 8 * i + k` STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `j - 8 * i` THEN
      MAP_EVERY UNDISCH_TAC [`j < 8 * (i + 1)`; `~(j < 8 * i)`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `j:num`)) THEN
    UNDISCH_TAC `k < 8` THEN SPEC_TAC(`k:num`,`k:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[BM_ADDR_E; BM_ADDR_F] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN BM_CONG_TAC;

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_basemul_k4 ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_basemul_k4" subroutine_signatures)
    MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_EXEC;;

let MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_IMAGE_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e srcA srcB srcBt dst pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (dst,512))
           [word pc,libmlkem_size; srcA,2048; srcB,2048; srcBt,1024]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                      mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s =
                      word (pc
                             + mlkem1024_polyvec_basemul_acc_montgomery_cached)
                              /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [dst; srcA; srcB; srcBt] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events srcA srcB srcBt dst pc returnaddress /\
                        memaccess_inbounds e2
                         [srcA,2048; srcB,2048; srcBt,1024; dst,512]
                         [dst,512])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE [memory :> bytes(dst, 512)])`,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(srcA:int64) (srcB:int64) (srcBt:int64) (dst:int64) (pc:num)
      (returnaddress:int64).
      APPEND
        (f_ev_epil srcA srcB srcBt dst pc returnaddress)
        (APPEND
          (ENUMERATEL 16
            (\i. f_ev_loop srcA srcB srcBt dst pc returnaddress i))
          (f_ev_prol srcA srcB srcBt dst pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `16`
   `pc + mlkem1024_polyvec_basemul_acc_montgomery_cached_loop1`
   `pc + mlkem1024_polyvec_basemul_acc_montgomery_cached_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X0 s = dst /\ read X1 s = srcA /\ read X2 s = srcB /\
           read X3 s = word_add srcBt (word(16 * i)) /\
           read X8 s = word(32 * i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The checks for overlap and the setup ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_EXEC (1--13) THEN
    BASEMUL_ALIAS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_EXEC (14--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_EXEC (1--74) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[BASEMUL_LOOP_FLAG] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 32`;
                  ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop exit and the return ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K4_CLANG17_O3_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;
