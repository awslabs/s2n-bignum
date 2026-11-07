(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Scalar product of 2-element polynomial vectors in NTT domain.             *)
(* This is the code for mlkem512_polyvec_basemul_acc_montgomery_cached from  *)
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

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/overlap.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image, the vector loop from +0x50 to +0x108 and the
 *** scalar loop from +0x110:

    mlkem512_polyvec_basemul_acc_montgomery_cached:
       +0x0: add     x8, x3, #0x200
       +0x4: add     x10, x0, #0x200
       +0x8: cmp     x8, x0
       +0xc: add     x9, x2, #0x400
      +0x10: ccmp    x10, x3, #0x0, hi
      +0x14: add     x11, x1, #0x400
      +0x18: cset    w8, hi
      +0x1c: cmp     x9, x0
      +0x20: ccmp    x10, x2, #0x0, hi
      +0x24: cset    w9, hi
      +0x28: cmp     x10, x1
      +0x2c: ccmp    x11, x0, #0x0, hi
      +0x30: b.hi    <join1>
      +0x34: tbnz    w8, #0, join1
      +0x38: cbnz    w9, join1
      +0x3c: mov     w10, #0xf3010000
      +0x40: mov     x8, xzr
      +0x44: add     x9, x3, #0x100
      +0x48: mvni    v1.4s, #0xd, lsl #8
      +0x4c: dup     v0.4s, w10
      +0x50: add     x10, x1, x8
      +0x54: add     x11, x2, x8
      +0x58: ldur    q17, [x9, #-256]
      +0x5c: ldr     q18, [x9], #16
      +0x60: ld2     {v2.8h-v3.8h}, [x10]
      +0x64: add     x10, x10, #0x200
      +0x68: ld2     {v4.8h-v5.8h}, [x11]
      +0x6c: ld2     {v6.8h-v7.8h}, [x10]
      +0x70: add     x10, x11, #0x200
      +0x74: smull   v16.4s, v4.4h, v2.4h
      +0x78: smull2  v19.4s, v4.8h, v2.8h
      +0x7c: ld2     {v21.8h-v22.8h}, [x10]
      +0x80: smull   v20.4s, v5.4h, v2.4h
      +0x84: add     x10, x0, x8
      +0x88: smull2  v23.4s, v5.8h, v2.8h
      +0x8c: add     x8, x8, #0x20
      +0x90: smlal   v16.4s, v17.4h, v3.4h
      +0x94: cmp     x8, #0x200
      +0x98: smlal2  v19.4s, v17.8h, v3.8h
      +0x9c: smlal   v20.4s, v4.4h, v3.4h
      +0xa0: smlal2  v23.4s, v4.8h, v3.8h
      +0xa4: smlal   v16.4s, v18.4h, v7.4h
      +0xa8: smlal2  v19.4s, v18.8h, v7.8h
      +0xac: smlal   v20.4s, v21.4h, v7.4h
      +0xb0: smlal2  v23.4s, v21.8h, v7.8h
      +0xb4: smlal   v16.4s, v21.4h, v6.4h
      +0xb8: smlal2  v19.4s, v21.8h, v6.8h
      +0xbc: smlal   v20.4s, v22.4h, v6.4h
      +0xc0: smlal2  v23.4s, v22.8h, v6.8h
      +0xc4: mul     v2.4s, v16.4s, v0.4s
      +0xc8: mul     v3.4s, v19.4s, v0.4s
      +0xcc: mul     v4.4s, v20.4s, v0.4s
      +0xd0: mul     v5.4s, v23.4s, v0.4s
      +0xd4: sshr    v2.4s, v2.4s, #16
      +0xd8: sshr    v3.4s, v3.4s, #16
      +0xdc: mul     v2.4s, v2.4s, v1.4s
      +0xe0: sshr    v4.4s, v4.4s, #16
      +0xe4: mul     v3.4s, v3.4s, v1.4s
      +0xe8: addhn   v6.4h, v2.4s, v16.4s
      +0xec: mul     v2.4s, v4.4s, v1.4s
      +0xf0: sshr    v4.4s, v5.4s, #16
      +0xf4: addhn2  v6.8h, v3.4s, v19.4s
      +0xf8: mul     v3.4s, v4.4s, v1.4s
      +0xfc: addhn   v7.4h, v2.4s, v20.4s
     +0x100: addhn2  v7.8h, v3.4s, v23.4s
     +0x104: st2     {v6.8h-v7.8h}, [x10]
     +0x108: b.ne    <loop1>
     +0x10c: b       <join2>
     +0x110: mov     x8, xzr
     +0x114: mov     w9, #0xf3010000
     +0x118: add     x10, x3, #0x100
     +0x11c: mov     w11, #0xfffff2ff
     +0x120: add     x12, x1, x8
     +0x124: add     x14, x2, x8
     +0x128: ldursh  w13, [x10, #-256]
     +0x12c: ldrsh   w15, [x10]
     +0x130: add     x10, x10, #0x2
     +0x134: ldrsh   w16, [x12, #2]
     +0x138: ldrsh   w17, [x14]
     +0x13c: ldrsh   w18, [x12]
     +0x140: ldrsh   w3, [x14, #2]
     +0x144: mul     w13, w13, w16
     +0x148: mul     w16, w17, w16
     +0x14c: ldrsh   w4, [x12, #514]
     +0x150: madd    w13, w17, w18, w13
     +0x154: ldrsh   w17, [x14, #512]
     +0x158: madd    w16, w3, w18, w16
     +0x15c: ldrsh   w12, [x12, #512]
     +0x160: ldrsh   w14, [x14, #514]
     +0x164: madd    w13, w15, w4, w13
     +0x168: madd    w15, w17, w4, w16
     +0x16c: madd    w13, w17, w12, w13
     +0x170: madd    w12, w14, w12, w15
     +0x174: mul     w14, w13, w9
     +0x178: mul     w15, w12, w9
     +0x17c: asr     w14, w14, #16
     +0x180: asr     w15, w15, #16
     +0x184: madd    w13, w14, w11, w13
     +0x188: add     x14, x0, x8
     +0x18c: madd    w12, w15, w11, w12
     +0x190: add     x8, x8, #0x4
     +0x194: lsr     w13, w13, #16
     +0x198: cmp     x8, #0x200
     +0x19c: lsr     w12, w12, #16
     +0x1a0: strh    w13, [x14]
     +0x1a4: strh    w12, [x14, #2]
     +0x1a8: b.ne    <loop2>
     +0x1ac: ret
 ***)

let MLKEM_NATIVE_BASEMUL_K2_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem512_polyvec_basemul_acc_montgomery_cached"];;

(* ------------------------------------------------------------------------- *)
(* Definitions used to state specification, as for mlkem_basemul_k2.         *)
(* ------------------------------------------------------------------------- *)

let pmull = define
  `pmull (x0: int) (x1 : int) (y0 : int) (y1 : int) = x1 * y1 + x0 * y0`;;

let pmull_acc2 = define
    `pmull_acc2 (x00: int) (x01 : int) (y00 : int) (y01 : int)
          (x10: int) (x11 : int) (y10 : int) (y11 : int) =
      pmull x10 x11 y10 y11 + pmull x00 x01 y00 y01`;;

let pmul_acc2 = define
    `pmul_acc2 (x00: int) (x01 : int) (y00 : int) (y01 : int)
          (x10: int) (x11 : int) (y10 : int) (y11 : int) =
     (&(inverse_mod 3329 65536) *
      pmull_acc2 x00 x01 y00 y01 x10 x11 y10 y11) rem &3329`;;

let basemul2_even = define
   `basemul2_even x0 y0 y0t x1 y1 y1t = \i.
      pmul_acc2 (x0 (2 * i)) (x0 (2 * i + 1))
                (y0 (2 * i)) (y0t i)
                (x1 (2 * i)) (x1 (2 * i + 1))
                (y1 (2 * i)) (y1t i)`;;

let basemul2_odd = define
 `basemul2_odd x0 y0 x1 y1 = \i.
    pmul_acc2 (x0 (2 * i)) (x0 (2 * i + 1))
              (y0 (2 * i + 1)) (y0 (2 * i))
              (x1 (2 * i)) (x1 (2 * i + 1))
              (y1 (2 * i + 1)) (y1 (2 * i))`;;

(* ------------------------------------------------------------------------- *)
(* The checks for overlap. For the output r of m bytes and an input b of n   *)
(* bytes, CMP and CCMP give the condition for the scalar loop, b + n > r and *)
(* r + m > b as unsigned numbers, in the form below. When the regions do not *)
(* overlap it is false, by NONOVERLAPPING_ALIAS_CHECK.                       *)
(* ------------------------------------------------------------------------- *)

let BASEMUL_ALIAS_STMT =
  `!r b:int64 m n.
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
             else F))`;;

let BASEMUL_ALIAS = assume_spec BASEMUL_ALIAS_STMT;;

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
   [`dst:int64`,`512`,`srcBt:int64`,`512`;
    `dst:int64`,`512`,`srcB:int64`,`1024`;
    `srcA:int64`,`1024`,`dst:int64`,`512`];;

(* ------------------------------------------------------------------------- *)
(* The Montgomery reduction of a lane t, with q = 62209 * 2^16, 62209 being  *)
(* 3329^-1 mod 2^16: the arithmetic shift of t * q gives the sign extension  *)
(* of the low half of t * 62209, the quotient of montred_neon.               *)
(* ------------------------------------------------------------------------- *)

let WORD_ISHR_16_SUBWORD_STMT =
  `!w:int32. word_ishr w 16 = word_sx(word_subword w (16,16):int16)`;;

let WORD_ISHR_16_SUBWORD = assume_spec WORD_ISHR_16_SUBWORD_STMT;;

let BASEMUL_LANE_STMT =
  `!t:int32.
     word_subword
      (word_add (word_mul (word_ishr (word_mul t (word 4076929024)) 16)
                          (word 4294963967)) t) (16,16):int16 =
     montred_scalar t`;;

let BASEMUL_LANE = assume_spec BASEMUL_LANE_STMT;;

let BASEMUL_LANE_CONV =
  let pat = lhand(snd(strip_forall(concl BASEMUL_LANE))) in
  fun tm -> INSTANTIATE (term_match [] pat tm) (SPEC_ALL BASEMUL_LANE);;

(*** One step of the simulation of the vector loop ***)

let BASEMUL_STEP_TAC n =
  ARM_STEPS_TAC MLKEM_NATIVE_BASEMUL_K2_CLANG17_O3_EXEC [n] THEN
  SIMD_SIMPLIFY_TAC[] THEN
  RULE_ASSUM_TAC(fun th ->
    if free_in `word_ishr:int32->num->int32` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV BASEMUL_LANE_CONV) th else th);;

(*** The loop test, at the end of the body ***)

let BASEMUL_LOOP_FLAG_STMT =
  `!i. i < 16
       ==> (~(val (word_add (word (32 * i))
                            (word 18446744073709551136):int64) = 0) <=>
            i + 1 < 16)`;;

let BASEMUL_LOOP_FLAG = assume_spec BASEMUL_LOOP_FLAG_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof, as for gcc 12 -O3.                                     *)
(* ------------------------------------------------------------------------- *)

(*** The addresses of the coefficients relative to those of the loads and
 *** stores, in the form that the simulation gives to the addresses
 ***)

let BM_ADDR_A_STMT =
  `!a:int64 i k. word_add a (word(2 * (16 * i + k))) =
                 word_add (word_add a (word(32 * i))) (word(2 * k))`;;

let BM_ADDR_A = assume_spec BM_ADDR_A_STMT;;

let BM_ADDR_B_STMT =
  `!a:int64 i k. word_add a (word(512 + 2 * (16 * i + k))) =
                 word_add (word_add a (word(32 * i + 512))) (word(2 * k))`;;

let BM_ADDR_B = assume_spec BM_ADDR_B_STMT;;

let BM_ADDR_C_STMT =
  `!a:int64 i k. word_add a (word(2 * (8 * i + k))) =
                 word_add (word_add a (word(16 * i))) (word(2 * k))`;;

let BM_ADDR_C = assume_spec BM_ADDR_C_STMT;;

let BM_ADDR_D_STMT =
  `!a:int64 i k. word_add a (word(256 + 2 * (8 * i + k))) =
                 word_add (word_add a (word(16 * i + 256))) (word(2 * k))`;;

let BM_ADDR_D = assume_spec BM_ADDR_D_STMT;;

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

let BM_ADDR_E_STMT =
  `!a:int64 i k. word_add a (word(4 * (8 * i + k))) =
                 word_add (word_add a (word(32 * i))) (word(4 * k))`;;

let BM_ADDR_E = assume_spec BM_ADDR_E_STMT;;

let BM_ADDR_F_STMT =
  `!a:int64 i k. word_add a (word(4 * (8 * i + k) + 2)) =
                 word_add (word_add a (word(32 * i))) (word(4 * k + 2))`;;

let BM_ADDR_F = assume_spec BM_ADDR_F_STMT;;

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
  REWRITE_TAC[basemul2_even; basemul2_odd;
              pmul_acc2; pmull_acc2; pmull; o_THM] THEN
  REWRITE_TAC BM_IDX_RULES THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC INT_RING;;

(*** The loop invariant, with 8 * i pairs of outputs done ***)

let basemul_k2_inv =
 `\i s. read X0 s = dst /\ read X1 s = srcA /\ read X2 s = srcB /\
        read X3 s = srcBt /\
        read X8 s = word(32 * i) /\
        read X9 s = word_add (word_add srcBt (word(16 * i))) (word 256) /\
        read X30 s = returnaddress /\
        read Q0 s = word 0xf3010000f3010000f3010000f3010000 /\
        read Q1 s = word 0xfffff2fffffff2fffffff2fffffff2ff /\
        (!i. i < 256
             ==> read(memory :> bytes16
                  (word_add srcA (word (2 * i)))) s = x0 i) /\
        (!i. i < 256
             ==> read(memory :> bytes16
                  (word_add srcB  (word (2 * i)))) s = y0 i) /\
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
        ((!i. i < 256
              ==> abs(ival(x0 i)) <= &2 pow 12 /\
                  abs(ival(x1 i)) <= &2 pow 12)
         ==> (!j. j < 8 * i
                  ==> (ival(read(memory :> bytes16
                         (word_add dst (word (4 * j)))) s) ==
                       basemul2_even (ival o x0) (ival o y0) (ival o y0t)
                                     (ival o x1) (ival o y1) (ival o y1t)
                                     j) (mod &3329) /\
                      (ival(read(memory :> bytes16
                         (word_add dst (word (4 * j + 2)))) s) ==
                       basemul2_odd (ival o x0) (ival o y0) (ival o x1)
                       (ival o y1) j) (mod &3329)))`;;

let basemul_k2_goal =
 `!srcA srcB srcBt dst x0 y0 y0t x1 y1 y1t pc returnaddress.
     aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
     ALL (nonoverlapping (dst, 512))
         [(word pc, libmlkem_size); (srcA, 1024); (srcB, 1024); (srcBt, 512)]
     ==>
     ensures arm
       (\s. aligned_bytes_loaded s (word pc)
              mlkem_native_libmlkem_clang17_O3_mc /\
            read PC s =
              word (pc + mlkem512_polyvec_basemul_acc_montgomery_cached) /\
            read X30 s = returnaddress /\
            C_ARGUMENTS [dst; srcA; srcB; srcBt] s  /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcA (word (2 * i)))) s = x0 i) /\
            (!i. i < 256
                 ==> read(memory :> bytes16
                      (word_add srcB  (word (2 * i)))) s = y0 i) /\
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
                      (word_add srcBt (word (256 + 2 * i)))) s = y1t i))
       (\s. read PC s = returnaddress /\
            ((!i. i < 256
                  ==> abs(ival(x0 i)) <= &2 pow 12 /\
                      abs(ival(x1 i)) <= &2 pow 12)
             ==> (!i. i < 128
                      ==> (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i)))) s) ==
                           basemul2_even (ival o x0) (ival o y0) (ival o y0t)
                                         (ival o x1) (ival o y1) (ival o y1t)
                                         i) (mod &3329) /\
                          (ival(read(memory :> bytes16
                             (word_add dst (word (4 * i + 2)))) s) ==
                           basemul2_odd (ival o x0) (ival o y0) (ival o x1)
                           (ival o y1) i) (mod &3329))))
       (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
        MAYCHANGE [memory :> bytes(dst, 512)])`;;

let MLKEM_NATIVE_BASEMUL_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  basemul_k2_goal;;

let MLKEM_NATIVE_BASEMUL_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_BASEMUL_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** The C signature is the same as that of mlkem_basemul_k2 ***)

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:true
    (assoc "mlkem_basemul_k2" subroutine_signatures)
    MLKEM_NATIVE_BASEMUL_K2_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_BASEMUL_K2_CLANG17_O3_EXEC;;

let MLKEM_NATIVE_BASEMUL_K2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e srcA srcB srcBt dst pc returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       ALL (nonoverlapping (dst,512))
           [word pc,libmlkem_size; srcA,1024; srcB,1024; srcBt,512]
       ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc)
                  mlkem_native_libmlkem_clang17_O3_mc /\
                read PC s =
                  word (pc + mlkem512_polyvec_basemul_acc_montgomery_cached) /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [dst; srcA; srcB; srcBt] s /\
                read events s = e)
           (\s. read PC s = returnaddress /\
                exists e2.
                  read events s = APPEND e2 e /\
                  e2 = f_events srcA srcB srcBt dst pc returnaddress /\
                  memaccess_inbounds e2
                   [srcA,1024; srcB,1024; srcBt,512; dst,512]
                   [dst,512])
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
            MAYCHANGE [memory :> bytes(dst, 512)])`;;

let MLKEM_NATIVE_BASEMUL_K2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_BASEMUL_K2_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
