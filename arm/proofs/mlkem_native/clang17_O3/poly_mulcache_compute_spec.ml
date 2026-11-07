(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Precomputation of the mulcache for polynomial multiplication.             *)
(* This is the code for mlkem_poly_mulcache_compute from mlkem-native's      *)
(* portable C implementation compiled by clang 17 with -O3 (see              *)
(* mlkem_native/README.md), verified in the whole image (see libmlkem.ml)    *)
(* with the specification of the gcc 12 -O2 code.                            *)
(*                                                                           *)
(* Unless the output may overlap the input, by a check that computes with    *)
(* the addresses modulo 2^64, clang has vectorized the first 112 of the 128  *)
(* outputs and unrolled them completely: 7 blocks of straight-line code,     *)
(* each loading 32 input coefficients with LD4, whose first and third        *)
(* registers are the odd coefficients needed, and storing 16 outputs with    *)
(* ST2. Each output is a Montgomery multiplication by a zeta or its          *)
(* negation, both of which the code loads as vectors of constants from the   *)
(* read-only data (mlkem_poly_mulcache_compute_constK), together with the    *)
(* zetas times 3329^-1 mod 2^16, shifted left by 16, so that the low half    *)
(* of the quotient is the high half of a 32-bit product, as for              *)
(* mlkem_poly_tomont. The code then goes on with the scalar loop for the     *)
(* last 8 pairs of outputs, which reads the zetas from rodata_mlk_zetas. If  *)
(* the arrays may overlap, the scalar loop computes all the outputs. When    *)
(* they do not overlap the check always takes the vector code, also when an  *)
(* array wraps around the end of the address space, so that is the only     *)
(* path verified here.                                                       *)
(*                                                                           *)
(* The safety theorem therefore lists mlkem_poly_mulcache_compute_consts as  *)
(* read-only data besides the zetas.                                         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native.ml";;
needs "arm/proofs/mlkem_native/overlap.ml";;
needs "arm/proofs/mlkem_native/interleave.ml";;
needs "arm/proofs/mlkem_native/clang17_O3/libmlkem.ml";;

(*** The code in the image. The first block is from +0x24 to +0xf4, and the
 *** six others follow the same pattern, with the next vectors of constants
 *** and with the addresses 64 bytes further on in the input and 32 bytes in
 *** the output each time:

    mlkem_poly_mulcache_compute:
       +0x0: add     x8, x1, #0x2
       +0x4: add     x9, x1, #0x200
       +0x8: cmp     x9, x0
       +0xc: b.ls    <join1>
      +0x10: add     x9, x0, #0x100
      +0x14: cmp     x8, x9
      +0x18: b.cs    <join1>
      +0x1c: mov     x11, xzr
      +0x20: b       <join2>
      +0x24: ld4     {v1.8h-v4.8h}, [x8]
      +0x28: adrp    x8, <page>
      +0x2c: adrp    x9, <page>
      +0x30: adrp    x11, <page>
      +0x34: adrp    x10, <page>
      +0x38: mvni    v0.4s, #0xd, lsl #8
      +0x3c: ldr     d5, [x8, #1648]
      +0x40: adrp    x8, <page>
      +0x44: ldr     d6, [x9, #1656]
      +0x48: adrp    x9, <page>
      +0x4c: ldr     q7, [x11, #1072]
      +0x50: adrp    x11, <page>
      +0x54: ldr     d16, [x8, #1672]
      +0x58: adrp    x8, <page>
      +0x5c: sxtl    v17.4s, v1.4h
      +0x60: ldr     q23, [x10, #1056]
      +0x64: sxtl2   v18.4s, v1.8h
      +0x68: adrp    x10, <page>
      +0x6c: ext     v19.16b, v1.16b, v1.16b, #8
      +0x70: smull   v6.4s, v1.4h, v6.4h
      +0x74: sxtl    v20.4s, v3.4h
      +0x78: sxtl2   v21.4s, v3.8h
      +0x7c: ext     v22.16b, v3.16b, v3.16b, #8
      +0x80: smull   v1.4s, v3.4h, v16.4h
      +0x84: ldr     q4, [x11, #1104]
      +0x88: mul     v3.4s, v17.4s, v7.4s
      +0x8c: ldr     q2, [x9, #1088]
      +0x90: mul     v7.4s, v18.4s, v23.4s
      +0x94: ldr     d16, [x8, #1664]
      +0x98: mul     v4.4s, v20.4s, v4.4s
      +0x9c: mov     x8, x0
      +0xa0: mul     v2.4s, v21.4s, v2.4s
      +0xa4: add     x9, x1, #0x42
      +0xa8: sshr    v3.4s, v3.4s, #16
      +0xac: adrp    x11, <page>
      +0xb0: sshr    v7.4s, v7.4s, #16
      +0xb4: mul     v3.4s, v3.4s, v0.4s
      +0xb8: sshr    v4.4s, v4.4s, #16
      +0xbc: smull   v5.4s, v19.4h, v5.4h
      +0xc0: mul     v7.4s, v7.4s, v0.4s
      +0xc4: mul     v4.4s, v4.4s, v0.4s
      +0xc8: addhn   v17.4h, v3.4s, v6.4s
      +0xcc: ldr     d6, [x10, #1688]
      +0xd0: sshr    v2.4s, v2.4s, #16
      +0xd4: adrp    x10, <page>
      +0xd8: smull   v3.4s, v22.4h, v16.4h
      +0xdc: mul     v2.4s, v2.4s, v0.4s
      +0xe0: addhn2  v17.8h, v7.4s, v5.4s
      +0xe4: ldr     q7, [x11, #1120]
      +0xe8: addhn   v18.4h, v4.4s, v1.4s
      +0xec: adrp    x11, <page>
      +0xf0: addhn2  v18.8h, v2.4s, v3.4s
      +0xf4: st2     {v17.8h-v18.8h}, [x8], #32
      ...
     +0x528: st2     {v18.8h-v19.8h}, [x8]
     +0x52c: lsl     x9, x11, #1
     +0x530: add     x10, x1, x11, lsl #3
     +0x534: add     x11, x0, x11, lsl #2
     +0x538: mov     w8, #0xf3010000
     +0x53c: add     x10, x10, #0x6
     +0x540: add     x11, x11, #0x2
     +0x544: mov     w12, #0xfffff2ff
     +0x548: adrp    x13, <page>
     +0x54c: add     x13, x13, #0x840
     +0x550: add     x14, x13, x9
     +0x554: ldursh  w15, [x10, #-4]
     +0x558: add     x9, x9, #0x2
     +0x55c: cmp     x9, #0x80
     +0x560: ldrsh   w14, [x14, #128]
     +0x564: mul     w15, w14, w15
     +0x568: neg     w14, w14
     +0x56c: sxth    w14, w14
     +0x570: mul     w16, w15, w8
     +0x574: asr     w16, w16, #16
     +0x578: madd    w15, w16, w12, w15
     +0x57c: lsr     w15, w15, #16
     +0x580: sturh   w15, [x11, #-2]
     +0x584: ldrsh   w15, [x10]
     +0x588: add     x10, x10, #0x8
     +0x58c: mul     w14, w15, w14
     +0x590: mul     w15, w14, w8
     +0x594: asr     w15, w15, #16
     +0x598: madd    w14, w15, w12, w14
     +0x59c: lsr     w14, w14, #16
     +0x5a0: strh    w14, [x11], #4
     +0x5a4: b.ne    <loop1>
     +0x5a8: ret
 ***)

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_CLANG17_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_clang17_O3_mc
   [layout_range "mlkem_poly_mulcache_compute"];;

(* ------------------------------------------------------------------------- *)
(* The check for overlap. With the output dst of 256 bytes and the input     *)
(* src of 512 bytes, the code takes the vector path if src + 512 <= dst or   *)
(* dst + 256 <= src + 2, computing modulo 2^64. When the arrays do not       *)
(* overlap, one of these holds: otherwise, as shown by                       *)
(* NONOVERLAPPING_ALIAS_CHECK, dst + 256 <= src, so src + 2 would wrap       *)
(* around, and then the start of dst would be within the part of src after   *)
(* the wraparound.                                                           *)
(* ------------------------------------------------------------------------- *)

let MULCACHE_ALIAS_CHECK_STMT =
  `!dst src:int64.
     nonoverlapping (dst,256) (src,512)
     ==> ~(val dst <= val (word_add src (word 512)) /\
           ~(val (word_sub (word_add src (word 512)) dst) = 0)) \/
         val(word_add dst (word 256)) <= val(word_add src (word 2))`;;

let MULCACHE_ALIAS_CHECK = assume_spec MULCACHE_ALIAS_CHECK_STMT;;

(*** The first condition, as the simulation gives it, and using one of the
 *** conditions in a case of the proof
 ***)

let MULCACHE_CHECK_1 =
 `~(val (dst:int64) <= val (word_add src (word 512):int64) /\
    ~(val (word_sub (word_add src (word 512)) dst:int64) = 0))`;;

let USE_CASE_TAC c =
  FIRST_X_ASSUM(fun th ->
    if concl th = c then RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Montgomery multiplication of the vector code. Lane k of the product  *)
(* of x by the zeta z is computed as                                         *)
(*                                                                           *)
(*   (sx(x) * q >> 16) * -3329 + sx(x) * z, high half                        *)
(*                                                                           *)
(* with q = (z * 62209 mod 2^16) * 2^16, 62209 being 3329^-1 mod 2^16, so    *)
(* the arithmetic shift gives the sign extension of the low half of          *)
(* x * z * 62209, which is the quotient of montred_neon. The scalar loop     *)
(* computes the quotient in the same way from the product, with q = 62209 *  *)
(* 2^16, and takes the high half with a logical shift.                       *)
(* ------------------------------------------------------------------------- *)

let WORD_ISHR_16_SUBWORD_STMT =
  `!w:int32. word_ishr w 16 = word_sx(word_subword w (16,16):int16)`;;

let WORD_ISHR_16_SUBWORD = assume_spec WORD_ISHR_16_SUBWORD_STMT;;

let MULCACHE_QUOT_STMT =
  `!y:int32 z r.
     (z * 62209) MOD 65536 = r
     ==> word_ishr (word_mul y (word (65536 * r))) 16 =
         word_sx (word_mul (word_subword (word_mul y (word z)) (0,16))
                           (word 62209):int16)`;;

let MULCACHE_QUOT = assume_spec MULCACHE_QUOT_STMT;;

(*** A lane of the vector code, given the constants z and q ***)

let MULCACHE_LANE_STMT =
  `!x:int16 z q.
     65536 * (z * 62209) MOD 65536 = q
     ==> word_subword
          (word_add
            (word_mul
              (word_ishr (word_mul (word_shl (word_sx x:int32) 0) (word q)) 16)
              (word 4294963967))
            (word_mul (word_sx x) (word z))) (16,16):int16 =
         montred_scalar (word_mul (word_sx x) (word z))`;;

let MULCACHE_LANE = assume_spec MULCACHE_LANE_STMT;;

let MULCACHE_LANE_CONV =
  let pat = lhand(rand(snd(strip_forall(concl MULCACHE_LANE)))) in
  fun tm ->
    let ins = term_match [] pat tm in
    let th = INSTANTIATE ins (SPEC_ALL MULCACHE_LANE) in
    MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))));;

(*** The scalar loop ***)

let WORD_ZX_USHR_16_STMT =
  `!w:int32. word_zx(word_ushr w 16):int16 = word_subword w (16,16)`;;

let WORD_ZX_USHR_16 = assume_spec WORD_ZX_USHR_16_STMT;;

let MULCACHE_SCALAR_STMT =
  `!t:int32.
     word_zx (word_ushr
               (word_add t
                 (word_mul (word_ishr (word_mul t (word 4076929024)) 16)
                           (word 4294963967))) 16):int16 =
     montred_scalar t`;;

let MULCACHE_SCALAR = assume_spec MULCACHE_SCALAR_STMT;;

(* ------------------------------------------------------------------------- *)
(* The congruence and the bound for an output of the vector code, with the   *)
(* zeta as a constant z (as a 32-bit word), and the tactic that proves them  *)
(* for an output coefficient.                                                *)
(* ------------------------------------------------------------------------- *)

let MULCACHE_PROD_BOUND_STMT =
  `!a b:int. abs a <= &32768 /\ abs b <= &1664 ==> abs(a * b) <= &54525952`;;

let MULCACHE_PROD_BOUND = assume_spec MULCACHE_PROD_BOUND_STMT;;

let MULCACHE_LANE_CONG_STMT =
  `!x:int16 z c.
     (&169 * ival(word z:int32) == c) (mod &3329) /\
     abs(ival(word z:int32)) <= &1664
     ==> (ival(montred_scalar (word_mul (word_sx x) (word z))) ==
          ival x * c) (mod &3329) /\
         abs(ival(montred_scalar (word_mul (word_sx x) (word z)))) <= &3328`;;

let MULCACHE_LANE_CONG = assume_spec MULCACHE_LANE_CONG_STMT;;

let MULCACHE_LANE_CONG1_STMT =
  `!x:int16 z c.
     (&169 * ival(word z:int32) == c) (mod &3329) /\
     abs(ival(word z:int32)) <= &1664
     ==> (ival(montred_scalar (word_mul (word_sx x) (word z))) ==
          ival x * c) (mod &3329)`;;

let MULCACHE_LANE_CONG1 = assume_spec MULCACHE_LANE_CONG1_STMT;;

let MULCACHE_LANE_BOUND_STMT =
  `!x:int16 z.
     abs(ival(word z:int32)) <= &1664
     ==> abs(ival(montred_scalar (word_mul (word_sx x) (word z)))) <= &3328`;;

let MULCACHE_LANE_BOUND = assume_spec MULCACHE_LANE_BOUND_STMT;;

let MULCACHE_VEC_OUTPUT_TAC =
  (MATCH_MP_TAC MULCACHE_LANE_BOUND ORELSE
   (REWRITE_TAC[mulcache; o_THM] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITREVERSE7_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[INT_CONG_RREM] THEN MATCH_MP_TAC MULCACHE_LANE_CONG1)) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* The same for the outputs of the scalar loop, as for gcc 12 -O2, with the  *)
(* zetas read from the table mlk_zetas (see utils/mlkem_native.ml).          *)
(* ------------------------------------------------------------------------- *)

let MLK_ZETAS_MULCACHE_STMT =
  `!i. i < 64
       ==> abs(EL (64 + i) mlk_zetas) <= &1664 /\
           (&169 * EL (64 + i) mlk_zetas ==
            &17 pow (2 * bitreverse7 (2 * i) + 1)) (mod &3329) /\
           (&169 * --(EL (64 + i) mlk_zetas) ==
            &17 pow (2 * bitreverse7 (2 * i + 1) + 1)) (mod &3329)`;;

let MLK_ZETAS_MULCACHE = assume_spec MLK_ZETAS_MULCACHE_STMT;;

let MLK_ZETAS_MULCACHE_IVAL_STMT =
  `!i. i < 64
       ==> ival(iword(EL (64 + i) mlk_zetas):int16) = EL (64 + i) mlk_zetas /\
           abs(ival(iword(EL (64 + i) mlk_zetas):int16)) <= &1664 /\
           (&169 * ival(iword(EL (64 + i) mlk_zetas):int16) ==
            &17 pow (2 * bitreverse7 (2 * i) + 1)) (mod &3329) /\
           (&169 * --ival(iword(EL (64 + i) mlk_zetas):int16) ==
            &17 pow (2 * bitreverse7 (2 * i + 1) + 1)) (mod &3329)`;;

let MLK_ZETAS_MULCACHE_IVAL = assume_spec MLK_ZETAS_MULCACHE_IVAL_STMT;;

let WORD_ZX_NEG_SX_STMT =
  `!z:int16. word_zx(word_sub (word 0) (word_sx z:int32)):int16 = word_neg z`;;

let WORD_ZX_NEG_SX = assume_spec WORD_ZX_NEG_SX_STMT;;

let CONG_MONT_ZETA = INTEGER_RULE
 `!n a z p x r:int. (r == a * (x * z)) (mod n) /\ (a * z == p) (mod n)
                    ==> (r == x * p) (mod n)`;;

let CONG_MONT_ZETA' = INTEGER_RULE
 `!n a z p x r:int. (r == a * (z * x)) (mod n) /\ (a * z == p) (mod n)
                    ==> (r == x * p) (mod n)`;;

(*** Instantiate a quantified input fact at a particular index, with the
 *** address in the form that the simulation uses
 ***)

let MSPEC_TAC (f,idx,rule) =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_forall c &&
       (let b = snd(dest_forall c) in
        is_imp b && is_eq(rand b) && can (find_term ((=) f)) (rhs(rand b)))
    then MP_TAC(SPEC idx th) else failwith "MSPEC_TAC") THEN
  ANTS_TAC THENL
   [W(fun (asl,w) -> MP_TAC(ARITH_RULE (mk_imp(`i < 8`,w)))) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(ASSUME_TAC o CONV_RULE(ONCE_DEPTH_CONV(REWR_CONV rule)))];;

let MULCACHE_LOOP_INPUTS_TAC =
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLK_ZETAS_LOADED o
    MATCH_MP (MLKEM_NATIVE_IMAGE_DATA_RULE mlk_zetas_data
               (layout "rodata_mlk_zetas"))) THEN
  MAP_EVERY MSPEC_TAC
   [`mlk_zetas`,`120 + i`,
      ARITH_RULE `2 * (120 + i) = (2 * i + 112) + 128`;
    `x:num->int16`,`4 * i + 225`,
      ARITH_RULE `2 * (4 * i + 225) = 8 * i + 450`;
    `x:num->int16`,`4 * i + 227`,
      ARITH_RULE `2 * (4 * i + 227) = 8 * i + 454`];;

(*** Prove the result for one output coefficient of iteration i ***)

let MULCACHE_OUTPUT_TAC =
  UNDISCH_THEN `i < 8` (fun th ->
    ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE
     [ARITH_RULE `64 + 56 + i = 120 + i`;
      ARITH_RULE `2 * (56 + i) = 2 * i + 112`;
      ARITH_RULE `(2 * i + 112) + 1 = 2 * i + 113`]
     (MATCH_MP MLK_ZETAS_MULCACHE_IVAL
       (MATCH_MP (ARITH_RULE `i < 8 ==> 56 + i < 64`) th)))) THEN
  ASSUM_LIST(fun ths -> W(fun (asl,w) ->
    let tm = rand(rand(lhand(rator(lhand w)))) in
    let th1 = WEAKEN_INTCONG_RULE (num 3329) (GEN_CONGBOUND_RULE ths tm) in
    let th2 = MATCH_MP CONGBOUND_MONTRED_SCALAR th1 in
    let th3 = CONV_RULE(ONCE_DEPTH_CONV INVERSE_MOD_CONV)
               (MP th2 (EQT_ELIM(INT_REDUCE_CONV(lhand(concl th2))))) in
    let cth,bth = CONJ_PAIR th3 in
    let prod = rand(rand(rator(concl cth))) in
    CONJ_TAC THENL
     [REWRITE_TAC[mulcache; o_THM; INT_CONG_RREM;
                  ARITH_RULE `2 * (2 * i + 112) + 1 = 4 * i + 225`;
                  ARITH_RULE `2 * (2 * i + 113) + 1 = 4 * i + 227`] THEN
      FIRST
       [MATCH_MP_TAC CONG_MONT_ZETA THEN
        MAP_EVERY EXISTS_TAC [`&169:int`; rand prod] THEN
        CONJ_TAC THENL [ACCEPT_TAC cth; ASM_REWRITE_TAC[]];
        MATCH_MP_TAC CONG_MONT_ZETA' THEN
        MAP_EVERY EXISTS_TAC [`&169:int`; lhand prod] THEN
        CONJ_TAC THENL [ACCEPT_TAC cth; ASM_REWRITE_TAC[]]];
      MP_TAC bth THEN CONV_TAC(LAND_CONV INT_REDUCE_CONV) THEN
      INT_ARITH_TAC]));;

(* ------------------------------------------------------------------------- *)
(* The simulation of the vector code.                                        *)
(* ------------------------------------------------------------------------- *)

(*** The 56 vectors of constants, 28 of 128 bits and then 28 of 64 bits ***)

let MULCACHE_CONSTANTS =
  map (fun k ->
    MLKEM_NATIVE_IMAGE_CONST_RULE
     (layout("mlkem_poly_mulcache_compute_const" ^ string_of_int k))
     (if k <= 28 then 128 else 64)) (1--56);;

(*** The 28 128-bit parts of the input read by the LD4s, from src + 2 ***)

let MULCACHE_INPUTS_TAC =
  FIRST_ASSUM(MP_TAC o check (fun th ->
      is_forall(concl th) && free_in `src:int64` (concl th))) THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
  MAP_EVERY (fun k ->
      MP_TAC(CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV
                                   NORMALIZE_RELATIVE_ADDRESS_CONV))
       (READ_MEMORY_MERGE_CONV 3
        (subst [mk_small_numeral(2 + 16 * k),`n:num`]
           `read(memory :> bytes128 (word_add src (word n))) s0`))))
   (0--27) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN REPEAT DISCH_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`];;

(*** One step, with the address of the constants after an ADRP, the lanes
 *** after LD4 and ST2, and the Montgomery multiplications
 ***)

let MULCACHE_STEP_TAC n =
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_CLANG17_O3_EXEC [n] THEN
  MLKEM_NATIVE_ADRP_TAC THEN MLKEM_NATIVE_INTERLEAVE_TAC THEN
  SIMD_SIMPLIFY_TAC[] THEN
  RULE_ASSUM_TAC(fun th ->
    if free_in `word_ishr:int32->num->int32` (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV MULCACHE_LANE_CONV) th else th);;

let ADDR_NORM_CONV =
  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
  REWRITE_CONV[GSYM ADD_ASSOC] THENC NUM_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

(*** The invariant of the scalar loop, at iteration i for outputs
 *** 2 * i + 112 and 2 * i + 113
 ***)

let mulcache_inv =
 `\i s. read X9 s = word(2 * i + 112) /\
        read X10 s = word_add (word_add src (word(8 * i))) (word 454) /\
        read X11 s = word_add (word_add dst (word(4 * i))) (word 226) /\
        read X13 s = word(pc + rodata_mlk_zetas) /\
        read X8 s = word 4076929024 /\ read X12 s = word 4294963967 /\
        read X30 s = returnaddress /\
        (!j. j < 256
             ==> read(memory :> bytes16(word_add src (word (2 * j)))) s =
                 x j) /\
        (!j. j < 2 * i + 112
             ==> let z_j = read(memory :> bytes16
                              (word_add dst (word (2 * j)))) s in
                 (ival z_j == (mulcache (ival o x)) j) (mod &3329) /\
                 abs(ival z_j) <= &3328)`;;

let MULCACHE_LOOP_FLAG_STMT =
  `!i. i < 8
       ==> (~(val (word_add (word (2 * i + 112))
                            (word 18446744073709551490):int64) = 0) <=>
            i + 1 < 8)`;;

let MULCACHE_LOOP_FLAG = assume_spec MULCACHE_LOOP_FLAG_STMT;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!dst src x pc returnaddress.
    aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
    ALL (nonoverlapping (dst,256)) [(word pc,libmlkem_size); (src,512)]
    ==> ensures arm
      (\s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_clang17_O3_mc /\
           read PC s = word (pc + mlkem_poly_mulcache_compute) /\
           read X30 s = returnaddress /\
           C_ARGUMENTS [dst; src] s /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add src (word (2 * i)))) s =
                    x i))
      (\s. read PC s = returnaddress /\
           !i. i < 128
               ==> let z_i = read(memory :> bytes16
                                (word_add dst (word (2 * i)))) s in
                   (ival z_i == (mulcache (ival o x)) i) (mod &3329) /\
                   abs(ival z_i) <= &3328)
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(dst,256)])`;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** As for gcc 12 -O2, with the vectors of constants as a second read-only
 *** object besides the zetas
 ***)

let mlkem_native_poly_mulcache_compute_signature =
  ([("x", "int16_t[static 128]", "false");
    ("a", "int16_t[static 256]", "true")],
   "void",
   [("a", "256", 2)],
   [("x", "128", 2)],
   []);;

let full_spec,public_vars = mk_safety_spec
    ~readonly_objects:[`word(pc + rodata_mlk_zetas):int64`,`256`;
                       `word(pc + mlkem_poly_mulcache_compute_consts):int64`,
                       `mlkem_poly_mulcache_compute_consts_size:num`]
    ~keep_maychanges:true
    mlkem_native_poly_mulcache_compute_signature
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_CLANG17_O3_EXEC;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
       forall e dst src pc returnaddress.
           aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
           ALL (nonoverlapping (dst,256)) [word pc,libmlkem_size; src,512]
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                     mlkem_native_libmlkem_clang17_O3_mc /\
                    read PC s = word (pc + mlkem_poly_mulcache_compute) /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [dst; src] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    exists e2.
                        read events s = APPEND e2 e /\
                        e2 = f_events src dst pc returnaddress /\
                        memaccess_inbounds e2
                         [src,512; dst,256;
                          word (pc + rodata_mlk_zetas),256;
                          word (pc + mlkem_poly_mulcache_compute_consts),
                          mlkem_poly_mulcache_compute_consts_size]
                         [dst,256])
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE [memory :> bytes(dst,256)])`;;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT;;
