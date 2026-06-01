(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Use hint to correct high bits of decomposition (ML-DSA, param 65/87).     *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;


(**** print_literal_from_elf "arm/mldsa/mldsa_poly_use_hint_32.o";;
 ****)

let mldsa_poly_use_hint_32_mc = define_assert_from_elf
 "mldsa_poly_use_hint_32_mc" "arm/mldsa/mldsa_poly_use_hint_32.o"
(*** BYTECODE START ***)
[
  0x529c0024;       (* arm_MOV W4 (rvalue (word 57345)) *)
  0x72a00fe4;       (* arm_MOVK W4 (word 127) 16 *)
  0x4e040c94;       (* arm_DUP_GEN Q20 X4 32 128 *)
  0x529c2005;       (* arm_MOV W5 (rvalue (word 57600)) *)
  0x72a00f65;       (* arm_MOVK W5 (word 123) 16 *)
  0x4e040cb5;       (* arm_DUP_GEN Q21 X5 32 128 *)
  0x529fc007;       (* arm_MOV W7 (rvalue (word 65024)) *)
  0x72a000e7;       (* arm_MOVK W7 (word 7) 16 *)
  0x4e040cf6;       (* arm_DUP_GEN Q22 X7 32 128 *)
  0x5280802b;       (* arm_MOV W11 (rvalue (word 1025)) *)
  0x72a8020b;       (* arm_MOVK W11 (word 16400) 16 *)
  0x4e040d77;       (* arm_DUP_GEN Q23 X11 32 128 *)
  0x4f0005f8;       (* arm_MOVI Q24 (word 64424509455) *)
  0xd2800203;       (* arm_MOV X3 (rvalue (word 16)) *)
  0x3dc00421;       (* arm_LDR Q1 X1 (Immediate_Offset (word 16)) *)
  0x3dc00822;       (* arm_LDR Q2 X1 (Immediate_Offset (word 32)) *)
  0x3dc00c23;       (* arm_LDR Q3 X1 (Immediate_Offset (word 48)) *)
  0x3cc40420;       (* arm_LDR Q0 X1 (Postimmediate_Offset (word 64)) *)
  0x3dc00445;       (* arm_LDR Q5 X2 (Immediate_Offset (word 16)) *)
  0x3dc00846;       (* arm_LDR Q6 X2 (Immediate_Offset (word 32)) *)
  0x3dc00c47;       (* arm_LDR Q7 X2 (Immediate_Offset (word 48)) *)
  0x3cc40444;       (* arm_LDR Q4 X2 (Postimmediate_Offset (word 64)) *)
  0x4eb7b431;       (* arm_SQDMULH_VEC Q17 Q1 Q23 32 128 *)
  0x4f2e2631;       (* arm_SRSHR_VEC Q17 Q17 18 32 128 *)
  0x4eb53439;       (* arm_CMGT_VEC Q25 Q1 Q21 32 128 *)
  0x6eb69621;       (* arm_MLS_VEC Q1 Q17 Q22 32 128 *)
  0x4e791e31;       (* arm_BIC_VEC Q17 Q17 Q25 128 *)
  0x4eb98421;       (* arm_ADD_VEC Q1 Q1 Q25 32 128 *)
  0x6ea09821;       (* arm_CMLE_VEC_ZERO Q1 Q1 32 128 *)
  0x4f001421;       (* arm_ORR_VEC Q1 Q1 (rvalue (word 79228162532711081671548469249)) 128 *)
  0x4ea59431;       (* arm_MLA_VEC Q17 Q1 Q5 32 128 *)
  0x4e381e31;       (* arm_AND_VEC Q17 Q17 Q24 128 *)
  0x4eb7b452;       (* arm_SQDMULH_VEC Q18 Q2 Q23 32 128 *)
  0x4f2e2652;       (* arm_SRSHR_VEC Q18 Q18 18 32 128 *)
  0x4eb53459;       (* arm_CMGT_VEC Q25 Q2 Q21 32 128 *)
  0x6eb69642;       (* arm_MLS_VEC Q2 Q18 Q22 32 128 *)
  0x4e791e52;       (* arm_BIC_VEC Q18 Q18 Q25 128 *)
  0x4eb98442;       (* arm_ADD_VEC Q2 Q2 Q25 32 128 *)
  0x6ea09842;       (* arm_CMLE_VEC_ZERO Q2 Q2 32 128 *)
  0x4f001422;       (* arm_ORR_VEC Q2 Q2 (rvalue (word 79228162532711081671548469249)) 128 *)
  0x4ea69452;       (* arm_MLA_VEC Q18 Q2 Q6 32 128 *)
  0x4e381e52;       (* arm_AND_VEC Q18 Q18 Q24 128 *)
  0x4eb7b473;       (* arm_SQDMULH_VEC Q19 Q3 Q23 32 128 *)
  0x4f2e2673;       (* arm_SRSHR_VEC Q19 Q19 18 32 128 *)
  0x4eb53479;       (* arm_CMGT_VEC Q25 Q3 Q21 32 128 *)
  0x6eb69663;       (* arm_MLS_VEC Q3 Q19 Q22 32 128 *)
  0x4e791e73;       (* arm_BIC_VEC Q19 Q19 Q25 128 *)
  0x4eb98463;       (* arm_ADD_VEC Q3 Q3 Q25 32 128 *)
  0x6ea09863;       (* arm_CMLE_VEC_ZERO Q3 Q3 32 128 *)
  0x4f001423;       (* arm_ORR_VEC Q3 Q3 (rvalue (word 79228162532711081671548469249)) 128 *)
  0x4ea79473;       (* arm_MLA_VEC Q19 Q3 Q7 32 128 *)
  0x4e381e73;       (* arm_AND_VEC Q19 Q19 Q24 128 *)
  0x4eb7b410;       (* arm_SQDMULH_VEC Q16 Q0 Q23 32 128 *)
  0x4f2e2610;       (* arm_SRSHR_VEC Q16 Q16 18 32 128 *)
  0x4eb53419;       (* arm_CMGT_VEC Q25 Q0 Q21 32 128 *)
  0x6eb69600;       (* arm_MLS_VEC Q0 Q16 Q22 32 128 *)
  0x4e791e10;       (* arm_BIC_VEC Q16 Q16 Q25 128 *)
  0x4eb98400;       (* arm_ADD_VEC Q0 Q0 Q25 32 128 *)
  0x6ea09800;       (* arm_CMLE_VEC_ZERO Q0 Q0 32 128 *)
  0x4f001420;       (* arm_ORR_VEC Q0 Q0 (rvalue (word 79228162532711081671548469249)) 128 *)
  0x4ea49410;       (* arm_MLA_VEC Q16 Q0 Q4 32 128 *)
  0x4e381e10;       (* arm_AND_VEC Q16 Q16 Q24 128 *)
  0x3d800411;       (* arm_STR Q17 X0 (Immediate_Offset (word 16)) *)
  0x3d800812;       (* arm_STR Q18 X0 (Immediate_Offset (word 32)) *)
  0x3d800c13;       (* arm_STR Q19 X0 (Immediate_Offset (word 48)) *)
  0x3c840410;       (* arm_STR Q16 X0 (Postimmediate_Offset (word 64)) *)
  0xf1000463;       (* arm_SUBS X3 X3 (rvalue (word 1)) *)
  0x54fff961;       (* arm_BNE (word 2096940) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLDSA_USE_HINT_32_EXEC = ARM_MK_EXEC_RULE mldsa_poly_use_hint_32_mc;;

(* Per-element word function matching the assembly computation *)
let mldsa_use_hint_32_asm = new_definition
  `mldsa_use_hint_32_asm (a:int32) (h:int32) : int32 =
   let a1 = word_ishr_round (word_2smulh a (word 1074791425)) 18 in
   let m:int32 = word_neg(word(bitval(word_igt a (word 8118528)))) in
   let a0 = word_add (word_sub a (word_mul a1 (word 523776))) m in
   let a1' = word_and a1 (word_not m) in
   let delta:int32 = word_or (word_neg(word(bitval(word_ile a0 (word 0))))) (word 1) in
   word_and (word_add a1' (word_mul delta h)) (word 15)`;;

(* Numeric description of the assembly's UseHint path, exposing the Barrett
   approximation used by the code. Connected to the FIPS 204 definition
   mldsa_use_hint_32 via MLDSA_USE_HINT_32_EQUIV below. *)
let mldsa_use_hint_32_code = new_definition
  `mldsa_use_hint_32_code (a:num) (h:num) =
   let a1 = ((((a + 127) DIV 128) * 1025 + 2097152) DIV 4194304) MOD 16 in
   let a0:int = &a - &a1 * &523776 in
   let a0' = if a0 > &4190208 then a0 - &8380417 else a0 in
   if h = 0 then a1
   else if a0' > &0 then (a1 + 1) MOD 16
   else (a1 + 15) MOD 16`;;

(* ========================================================================= *)
(* Functional correctness helper lemmas                                       *)
(* ========================================================================= *)

let WORD_2SMULH_NOSATURATE_32 = prove(
  `!a:int32. val a < 8380417
   ==> word_2smulh a (word 1074791425:int32) : int32 =
       iword((&2 * &(val a) * &1074791425) div &2 pow 32)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[word_2smulh; DIMINDEX_32] THEN
  ASM_SIMP_TAC[MLDSA_IVAL_VAL] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[iword_saturate; word_INT_MIN; word_INT_MAX; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
  SIMP_TAC[INT_OF_NUM_DIV] THEN
  REWRITE_TAC[INT_POS_NEG_BOUND] THEN
  SUBGOAL_THEN `~(&((2 * val(a:int32) * 1074791425) DIV 4294967296):int > &2147483647)`
    (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `(2 * val(a:int32) * 1074791425) DIV 4294967296 <= 2147483647`
    (fun th -> MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LE] th) THEN INT_ARITH_TAC) THEN
  TRANS_TAC LE_TRANS `(2 * 8380416 * 1074791425) DIV 4294967296` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC;
   CONV_TAC NUM_REDUCE_CONV]);;

let VAL_DECOMPOSE_A1 = prove(
  `!a:int32. val a < 8380417
   ==> val(word_ishr_round (word_2smulh a (word 1074791425:int32)) 18 : int32)
       = ((2 * val a * 1074791425) DIV 4294967296 + 131072) DIV 262144`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[WORD_2SMULH_NOSATURATE_32] THEN
  SUBGOAL_THEN `(2 * val(a:int32) * 1074791425) DIV 4294967296 < 2147483648`
    ASSUME_TAC THENL
  [TRANS_TAC LT_TRANS `(2 * 8380416 * 1074791425) DIV 4294967296 + 1` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x <= y ==> x < y + 1`) THEN
    MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN SIMP_TAC[INT_OF_NUM_DIV] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[VAL_IWORD_NUM_32] THEN
  ABBREV_TAC `t:int32 = iword(&((2 * val(a:int32) * 1074791425) DIV 4294967296))` THEN
  SUBGOAL_THEN `val(t:int32) = (2 * val(a:int32) * 1074791425) DIV 4294967296`
    ASSUME_TAC THENL
  [EXPAND_TAC "t" THEN MATCH_MP_TAC VAL_IWORD_NUM_32 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `val(t:int32) < 2147483648` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[word_ishr_round] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
  SUBGOAL_THEN `ival(t:int32) = &(val t)` ASSUME_TAC THENL
  [SIMP_TAC[ival; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
   COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN SIMP_TAC[INT_OF_NUM_DIV] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `(val(t:int32) + 131072) DIV 262144 < 2147483648` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   TRANS_TAC LT_TRANS `(4194303 + 131072) DIV 262144 + 1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x <= y ==> x < y + 1`) THEN
    MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
  ASM_SIMP_TAC[VAL_IWORD_NUM_32] THEN MATCH_MP_TAC VAL_IWORD_NUM_32 THEN
  UNDISCH_THEN `val(t:int32) = (2 * val(a:int32) * 1074791425) DIV 4294967296`
    (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]);;

let WORD_IGT_THRESHOLD_32 = BITBLAST_RULE
  `!a:int32. val a < 8380417
    ==> word_igt a (word 8118528:int32) <=> val a > 8118528`;;

let A1_BOUND = prove(
  `!a. a < 8380417
   ==> ((a + 127) DIV 128 * 1025 + 2097152) DIV 4194304 <= 16`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `128` (SPEC `8380416 + 127` (SPEC `a + 127` DIV_MONO))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ABBREV_TAC `d = (a + 127) DIV 128` THEN
  MP_TAC(SPEC `4194304` (SPEC `69205952` (SPEC `d * 1025 + 2097152` DIV_MONO))) THEN
  ANTS_TAC THENL
  [SUBGOAL_THEN `d * 1025 <= 65472 * 1025` MP_TAC THENL
   [ASM_SIMP_TAC[LE_MULT_RCANCEL]; CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC];
   CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;

let A1_WRAP = prove(
  `!a. 8118528 < a /\ a < 8380417
   ==> ((a + 127) DIV 128 * 1025 + 2097152) DIV 4194304 = 16`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `16 <= ((a + 127) DIV 128 * 1025 + 2097152) DIV 4194304`
    ASSUME_TAC THENL
  [MP_TAC(SPEC `128` (SPEC `a + 127` (SPEC `8118529 + 127` DIV_MONO))) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
   ABBREV_TAC `d = (a + 127) DIV 128` THEN
   MP_TAC(SPEC `4194304` (SPEC `d * 1025 + 2097152` (SPEC `67108977` DIV_MONO))) THEN
   ANTS_TAC THENL
   [SUBGOAL_THEN `63427 * 1025 <= d * 1025` MP_TAC THENL
    [ASM_SIMP_TAC[LE_MULT_RCANCEL]; CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC];
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPEC `a:num` A1_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_ARITH_TAC);;

let A1_BOUND_NOWRAP = prove(
  `!a. a <= 8118528
   ==> ((a + 127) DIV 128 * 1025 + 2097152) DIV 4194304 <= 15`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `128` (SPEC `8118528 + 127` (SPEC `a + 127` DIV_MONO))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  ABBREV_TAC `d = (a + 127) DIV 128` THEN
  MP_TAC(SPEC `4194304` (SPEC `67108802` (SPEC `d * 1025 + 2097152` DIV_MONO))) THEN
  ANTS_TAC THENL
  [SUBGOAL_THEN `d * 1025 <= 63426 * 1025` MP_TAC THENL
   [ASM_SIMP_TAC[LE_MULT_RCANCEL]; CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC];
   CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;

let A0_UPPER_32 = prove(
  `!a. a <= 8118528
   ==> a < (((a + 127) DIV 128 * 1025 + 2097152) DIV 4194304 + 1) * 523776`,
  GEN_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `nv = ((a + 127) DIV 128 * 1025 + 2097152) DIV 4194304` THEN
  SUBGOAL_THEN `nv * 4194304 <= (a + 127) DIV 128 * 1025 + 2097152` ASSUME_TAC THENL
  [EXPAND_TAC "nv" THEN
   MP_TAC(SPECL [`(a + 127) DIV 128 * 1025 + 2097152`; `4194304`] (CONJUNCT1 DIVISION_SIMP)) THEN
   ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(a + 127) DIV 128 <= 63426` ASSUME_TAC THENL
  [MP_TAC(SPEC `128` (SPEC `8118528 + 127` (SPEC `a + 127` DIV_MONO))) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `nv * 4194304 <= 63426 * 1025 + 2097152` ASSUME_TAC THENL
  [SUBGOAL_THEN `(a + 127) DIV 128 * 1025 <= 63426 * 1025` MP_TAC THENL
   [REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ASM_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `nv <= 15` ASSUME_TAC THENL
  [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

let WORD_SUB_SIGN_32 = BITBLAST_RULE
  `!a:int32 b:int32. val b <= 7856640 /\ val a <= 8118528 ==>
   ((bit 31 (word_sub a b) \/ word_sub a b = word 0) <=> val a <= val b)`;;

let WRAP_A0_NEGATIVE = BITBLAST_RULE
  `!a:int32. val a < 8380417 /\ val a > 8118528
   ==> bit 31 (word_add (word_sub a (word 8380416:int32)) (word 4294967295:int32))`;;

(* Barrett equivalence: assembly and C decomposition formulas agree.
   Both compute round_half_down(a / 523776) via different Barrett
   approximation paths. Proved by case analysis on 17 output intervals
   using DIV_MONO to sandwich both LHS and RHS to the same constant. *)
let BARRETT_INTERVAL_32 = prove(
  `!a lo hi k.
    lo <= a /\ a <= hi /\
    k * 262144 <= (2 * lo * 1074791425) DIV 4294967296 + 131072 /\
    (2 * hi * 1074791425) DIV 4294967296 + 131072 < (k + 1) * 262144 /\
    k * 4194304 <= (lo + 127) DIV 128 * 1025 + 2097152 /\
    (hi + 127) DIV 128 * 1025 + 2097152 < (k + 1) * 4194304
    ==> ((2 * a * 1074791425) DIV 4294967296 + 131072) DIV 262144 = k /\
        ((a + 127) DIV 128 * 1025 + 2097152) DIV 4194304 = k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THEN MATCH_MP_TAC DIV_SANDWICH THEN CONV_TAC NUM_REDUCE_CONV THENL
  [CONJ_TAC THENL
   [TRANS_TAC LE_TRANS `(2 * lo * 1074791425) DIV 4294967296 + 131072` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `x + 131072 <= y + 131072 <=> x <= y`] THEN
    MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC;
    TRANS_TAC LET_TRANS `(2 * hi * 1074791425) DIV 4294967296 + 131072` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `x + 131072 <= y + 131072 <=> x <= y`] THEN
    MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC];
   CONJ_TAC THENL
   [TRANS_TAC LE_TRANS `(lo + 127) DIV 128 * 1025 + 2097152` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `x + 2097152 <= y + 2097152 <=> x <= y`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
    MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC;
    TRANS_TAC LET_TRANS `(hi + 127) DIV 128 * 1025 + 2097152` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `x + 2097152 <= y + 2097152 <=> x <= y`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
    MATCH_MP_TAC DIV_MONO THEN ASM_ARITH_TAC]]);;

let BARRETT_EQUIV = prove(
  `!a. a < 8380417 ==>
  ((2 * a * 1074791425) DIV 4294967296 + 131072) DIV 262144 =
  ((a + 127) DIV 128 * 1025 + 2097152) DIV 4194304`,
  GEN_TAC THEN DISCH_TAC THEN
  let intervals = [
    (0, 261888); (261889, 785664); (785665, 1309440); (1309441, 1833216);
    (1833217, 2356992); (2356993, 2880768); (2880769, 3404544);
    (3404545, 3928320); (3928321, 4452096); (4452097, 4975872);
    (4975873, 5499648); (5499649, 6023424); (6023425, 6547200);
    (6547201, 7070976); (7070977, 7594752); (7594753, 8118528);
    (8118529, 8380416)] in
  let mk_le hi =
    mk_comb(mk_comb(`(<=):num->num->bool`, mk_var("a",`:num`)),
            mk_small_numeral hi) in
  let apply_interval k (lo, hi) =
    let th = SPECL [`a:num`; mk_small_numeral lo;
                    mk_small_numeral hi; mk_small_numeral k]
                   BARRETT_INTERVAL_32 in
    MP_TAC th THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC in
  let rec cascade k = function
    | [(lo,hi)] -> apply_interval k (lo,hi)
    | (lo,hi)::rest ->
        ASM_CASES_TAC (mk_le hi) THENL
        [apply_interval k (lo,hi); cascade (k+1) rest]
    | [] -> failwith "empty" in
  cascade 0 intervals);;



(* ========================================================================= *)
(* Element-level functional correctness                                       *)
(* ========================================================================= *)

let ELEMENT_CORRECT = prove(
  `!a:int32 h:int32.
     val a < 8380417 /\ val h <= 1
     ==> val(mldsa_use_hint_32_asm a h) = mldsa_use_hint_32_code (val a) (val h)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mldsa_use_hint_32_asm; mldsa_use_hint_32_code] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `nv = ((val(a:int32) + 127) DIV 128 * 1025 + 2097152) DIV 4194304` THEN
  SUBGOAL_THEN `val(word_ishr_round (word_2smulh (a:int32) (word 1074791425)) 18 : int32) = nv` ASSUME_TAC THENL
  [EXPAND_TAC "nv" THEN TRANS_TAC EQ_TRANS `((2 * val(a:int32) * 1074791425) DIV 4294967296 + 131072) DIV 262144` THEN CONJ_TAC THENL [MATCH_MP_TAC VAL_DECOMPOSE_A1 THEN ASM_REWRITE_TAC[]; MATCH_MP_TAC BARRETT_EQUIV THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `nv <= 16` ASSUME_TAC THENL [MP_TAC(SPEC `val(a:int32)` A1_BOUND) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `word_igt (a:int32) (word 8118528:int32) <=> val a > 8118528` SUBST1_TAC THENL [MP_TAC(SPEC `a:int32` WORD_IGT_THRESHOLD_32) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `val(a:int32) > 8118528` THEN ASM_REWRITE_TAC[bitval] THENL
  [
    SUBGOAL_THEN `nv = 16` SUBST_ALL_TAC THENL [MP_TAC(SPEC `val(a:int32)` A1_WRAP) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `word_ishr_round (word_2smulh (a:int32) (word 1074791425)) 18 = (word 16:int32)` (fun th -> REWRITE_TAC[th]) THENL [ONCE_REWRITE_TAC[GSYM WORD_VAL] THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ILE_ZERO_32] THEN
    MP_TAC(SPEC `a:int32` WRAP_A0_NEGATIVE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[bitval] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[INT_MUL_LZERO; INT_SUB_RZERO] THEN
    SUBGOAL_THEN `~((if int_gt (&(val(a:int32))) (&4190208) then &(val a) - &8380417 else &(val a):int) > &0)` ASSUME_TAC THENL
    [REWRITE_TAC[INT_GT; INT_NOT_LT] THEN COND_CASES_TAC THENL
     [MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT] (ASSUME `val(a:int32) < 8380417`)) THEN INT_ARITH_TAC;
      POP_ASSUM(MP_TAC o REWRITE_RULE[INT_GT; INT_NOT_LT]) THEN
      MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_GT; INT_GT] (ASSUME `val(a:int32) > 8118528`)) THEN INT_ARITH_TAC];
     ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `val(h:int32) = 0` THEN ASM_REWRITE_TAC[] THENL
    [SUBGOAL_THEN `h:int32 = word 0` SUBST1_TAC THENL [REWRITE_TAC[GSYM VAL_EQ_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN CONV_TAC WORD_REDUCE_CONV;
     SUBGOAL_THEN `h:int32 = word 1` SUBST1_TAC THENL [REWRITE_TAC[GSYM VAL_EQ_1] THEN ASM_ARITH_TAC; ALL_TAC] THEN CONV_TAC WORD_REDUCE_CONV]
  ;
    SUBGOAL_THEN `nv <= 15` ASSUME_TAC THENL [MP_TAC(SPEC `val(a:int32)` A1_BOUND_NOWRAP) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `nv MOD 16 = nv` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `word_ishr_round (word_2smulh (a:int32) (word 1074791425)) 18 = (word nv:int32)` (fun th -> REWRITE_TAC[th]) THENL [GEN_REWRITE_TAC LAND_CONV [GSYM WORD_VAL] THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC WORD_REDUCE_CONV THEN REWRITE_TAC[WORD_AND_REFL] THEN REWRITE_TAC[WORD_ILE_ZERO_32; WORD_ADD_0] THEN
    SUBGOAL_THEN `nv * 523776 <= 7856640` ASSUME_TAC THENL [SUBGOAL_THEN `nv * 523776 <= 15 * 523776` MP_TAC THENL [REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]; ALL_TAC] THEN
    SUBGOAL_THEN `val(word_mul (word nv:int32) (word 523776:int32)) = nv * 523776` ASSUME_TAC THENL [REWRITE_TAC[VAL_WORD_MUL; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN SUBGOAL_THEN `nv MOD 4294967296 = nv` SUBST1_TAC THENL [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word_mul (word nv:int32) (word 523776:int32)) <= 7856640` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(bit 31 (word_sub (a:int32) (word_mul (word nv:int32) (word 523776:int32))) \/ word_sub a (word_mul (word nv) (word 523776)) = word 0) <=> ~(&(val a) - &nv * &523776 > &0)` SUBST1_TAC THENL
    [MP_TAC(ISPECL [`a:int32`; `word_mul (word nv:int32) (word 523776:int32)`] WORD_SUB_SIGN_32) THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_CASES_TAC `val(a:int32) <= nv * 523776` THENL
     [ASM_REWRITE_TAC[] THEN MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_MUL] (REWRITE_RULE[GSYM INT_OF_NUM_LE] (ASSUME `val(a:int32) <= nv * 523776`))) THEN INT_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `nv * 523776 < val(a:int32)` ASSUME_TAC THENL [UNDISCH_TAC `~(val(a:int32) <= nv * 523776)` THEN ARITH_TAC; ALL_TAC] THEN MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_MUL] (REWRITE_RULE[GSYM INT_OF_NUM_LT] (ASSUME `nv * 523776 < val(a:int32)`))) THEN INT_ARITH_TAC]; ALL_TAC] THEN
    REWRITE_TAC[bitval] THEN
    ASM_CASES_TAC `val(h:int32) = 0` THEN ASM_REWRITE_TAC[] THENL
    [SUBGOAL_THEN `h:int32 = word 0` SUBST1_TAC THENL [REWRITE_TAC[GSYM VAL_EQ_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN REWRITE_TAC[WORD_MUL_0; WORD_ADD_0; WORD_AND_ONES_32] THEN REWRITE_TAC[VAL_WORD_AND_15_32] THEN SUBGOAL_THEN `val(word nv:int32) = nv` SUBST1_TAC THENL [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN `h:int32 = word 1` SUBST1_TAC THENL [REWRITE_TAC[GSYM VAL_EQ_1] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[WORD_MUL_1_32; WORD_AND_ONES_32] THEN
    SUBGOAL_THEN `val(word nv:int32) = nv` ASSUME_TAC THENL [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word nv:int32) <= 15` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(int_gt (&(val(a:int32)) - &nv * &523776) (&4190208))` ASSUME_TAC THENL
    [REWRITE_TAC[INT_GT; INT_NOT_LT] THEN MP_TAC(SPEC `val(a:int32)` A0_UPPER_32) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_ADD] (ASSUME `val(a:int32) < (nv + 1) * 523776`)) THEN INT_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `val(a:int32) <= nv * 523776` THENL
    [MP_TAC(SPECL [`val(a:int32)`; `nv:num`; `523776`] REAL_INT_GT_BRIDGE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
     MP_TAC(SPECL [`val(a:int32)`; `nv:num`; `523776`] REAL_INT_GT_BRIDGE_POS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[bitval] THEN CONV_TAC WORD_REDUCE_CONV THEN
    REWRITE_TAC[VAL_WORD_AND_15_32; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `16 = 2 EXP 4`; ARITH_RULE `4294967296 = 2 EXP 32`; MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[ARITH_RULE `4294967295 = 15 + 268435455 * 16`; ARITH_RULE `n + (15 + 268435455 * 16) = (n + 15) + 268435455 * 16`; MOD_MULT_ADD] THEN
    SUBGOAL_THEN `nv MOD 4294967296 = nv` (fun th -> REWRITE_TAC[th]) THEN TRY(MATCH_MP_TAC MOD_LT) THEN ASM_ARITH_TAC]);;


let ELEMENT_CORRECT_WORD = prove(
  `!a:int32 h:int32.
     val a < 8380417 /\ val h <= 1
     ==> mldsa_use_hint_32_asm a h =
         word(mldsa_use_hint_32_code (val a) (val h))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM WORD_VAL] THEN
  AP_TERM_TAC THEN MP_TAC(SPECL [`a:int32`; `h:int32`] ELEMENT_CORRECT) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;


(* ========================================================================= *)
(* FIPS 204 = code-aligned equivalence                                       *)
(* ========================================================================= *)
(*                                                                           *)
(* Bridges mldsa_use_hint_32 (FIPS 204 Algorithm 40, used in the public      *)
(* postcondition) to mldsa_use_hint_32_code (the Barrett-style numeric form  *)
(* the assembly actually computes). The main correctness proof states its    *)
(* postcondition in FIPS 204 terms and rewrites with this equivalence in the *)
(* strengthening branch to expose the code-aligned form for symbolic         *)
(* execution.                                                                *)
(* ========================================================================= *)

let LINEARIZE_DIV_MOD_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    free_in `r MOD 523776` (concl th) ||
    free_in `r DIV 523776` (concl th)))) THEN
  MP_TAC(SPECL [`r:num`; `523776`] (CONJUNCT1 DIVISION_SIMP)) THEN
  SPEC_TAC(`r MOD 523776`, `m:num`) THEN
  SPEC_TAC(`r DIV 523776`, `q:num`) THEN
  REPEAT GEN_TAC THEN ASM_ARITH_TAC;;

(* Prove r DIV 523776 = k via DIV_SANDWICH + LE_MULT_RCANCEL *)
let DIV_523776_TAC k =
  let k_num = mk_small_numeral k and km1 = mk_small_numeral (k-1)
  and kp1 = mk_small_numeral (k+1)
  and q = mk_var("q",`:num`) and le = `(<=):num->num->bool`
  and lt = `(<):num->num->bool`
  and c = `523776` in
  let mk_mul a b = mk_binop (rator(rator `0*0`)) a b in
  MATCH_MP_TAC DIV_SANDWICH THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    free_in `r MOD 523776` (concl th) ||
    free_in `r DIV 523776` (concl th)))) THEN
  MP_TAC(SPECL [`r:num`; c] (CONJUNCT1 DIVISION_SIMP)) THEN
  SPEC_TAC(`r MOD 523776`, `m:num`) THEN
  SPEC_TAC(`r DIV 523776`, q) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC(mk_comb(mk_comb(le, q), km1)) THENL
  [SUBGOAL_THEN(mk_comb(mk_comb(le, mk_mul q c),
                mk_mul km1 c)) ASSUME_TAC THENL
   [ASM_SIMP_TAC[LE_MULT_RCANCEL]; ALL_TAC] THEN
   CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
   SUBGOAL_THEN(mk_comb(mk_comb(le, mk_mul k_num c),
                mk_mul q c)) ASSUME_TAC THENL
   [ASM_SIMP_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
   ASM_CASES_TAC(mk_comb(mk_comb(lt, k_num), q)) THENL
   [SUBGOAL_THEN(mk_comb(mk_comb(le, mk_mul kp1 c),
                 mk_mul q c)) ASSUME_TAC THENL
    [ASM_SIMP_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]];;

(* Replace (r - r MOD 523776) DIV 523776 with r DIV 523776 *)
let DIV_MOD_TO_DIV_TAC =
  SUBGOAL_THEN `(r - r MOD 523776) DIV 523776 = r DIV 523776` SUBST1_TAC THENL
  [MP_TAC(SPECL [`r:num`; `523776`] (CONJUNCT1 DIVISION_SIMP)) THEN
   DISCH_TAC THEN
   SUBGOAL_THEN `r - r MOD 523776 = 523776 * r DIV 523776` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`523776`; `r DIV 523776`] DIV_MULT) THEN
   CONV_TAC NUM_REDUCE_CONV; ALL_TAC];;

(* Lower half nowrap: dismiss wrap cond, reduce, prove r DIV 523776 = k *)
let DECOMPOSE_R1_LOWER_TAC =
  SUBGOAL_THEN `~((&r:int) - &(r MOD 523776) = &8380416)` (fun th -> REWRITE_TAC[th]) THENL
  [ASM_SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_EQ] THEN LINEARIZE_DIV_MOD_TAC;
   ALL_TAC] THEN
  ASM_SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_DIV; NUM_OF_INT_OF_NUM] THEN
  DIV_MOD_TO_DIV_TAC THEN
  CONV_TAC SYM_CONV THEN
  LINEARIZE_DIV_MOD_TAC;;

(* Upper half nowrap: dismiss wrap cond, reduce, prove r DIV 523776 + 1 = k *)
let DECOMPOSE_R1_UPPER_TAC =
  SUBGOAL_THEN `r MOD 523776 <= r` ASSUME_TAC THENL
  [MESON_TAC[MOD_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `r MOD 523776 < 523776` ASSUME_TAC THENL
  [MP_TAC(SPECL [`r:num`; `523776`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((&r:int) - (&(r MOD 523776) - &523776) = &8380416)` (fun th -> REWRITE_TAC[th]) THENL
  [REWRITE_TAC[INT_ARITH `(a:int) - (b - c) = d <=> a + c - b = d`] THEN
   ASM_SIMP_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_SUB; INT_OF_NUM_EQ] THEN
   LINEARIZE_DIV_MOD_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&r:int) - (&(r MOD 523776) - &523776) =
                &(r - r MOD 523776 + 523776)` SUBST1_TAC THENL
  [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; GSYM INT_OF_NUM_ADD] THEN
   INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_DIV; NUM_OF_INT_OF_NUM] THEN
  MP_TAC(SPECL [`r:num`; `523776`] (CONJUNCT1 DIVISION_SIMP)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `r - r MOD 523776 + 523776 = 523776 * (r DIV 523776 + 1)`
    SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`523776`; `r DIV 523776 + 1`] DIV_MULT) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    free_in `r MOD 523776` (concl th) ||
    free_in `r DIV 523776` (concl th)))) THEN
  MP_TAC(SPECL [`r:num`; `523776`] (CONJUNCT1 DIVISION_SIMP)) THEN
  SPEC_TAC(`r MOD 523776`, `m:num`) THEN
  SPEC_TAC(`r DIV 523776`, `q:num`) THEN
  REPEAT GEN_TAC THEN ASM_ARITH_TAC;;

let DECOMPOSE_R1_NOWRAP_TAC =
  ASM_CASES_TAC `r MOD 523776 * 2 <= 523776` THEN ASM_REWRITE_TAC[] THEN
  TRY DECOMPOSE_R1_LOWER_TAC THEN TRY DECOMPOSE_R1_UPPER_TAC;;

let DECOMPOSE_32_R1_EQUIV = time prove(
  `!r. r < 8380417 ==>
   (((r + 127) DIV 128 * 1025 + 2097152) DIV 4194304) MOD 16 =
   decompose_32_r1 r`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `r <= 8118528` THENL
  [ALL_TAC;
   (* Wrap zone *)
   SUBGOAL_THEN `8118528 < r` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `decompose_32_r1 r = 0` SUBST1_TAC THENL
   [REWRITE_TAC[decompose_32_r1; mldsa_decompose_32; mldsa_cmod] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    SUBGOAL_THEN `r MOD 523776 <= r` ASSUME_TAC THENL
    [MESON_TAC[MOD_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `r MOD 523776 < 523776` ASSUME_TAC THENL
    [MP_TAC(SPECL [`r:num`; `523776`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `r MOD 523776 * 2 <= 523776` THEN ASM_REWRITE_TAC[] THENL
    [(* Lower wrap: r DIV 523776 = 16 *)
     SUBGOAL_THEN `r DIV 523776 = 16` ASSUME_TAC THENL
     [DIV_523776_TAC 16; ALL_TAC] THEN
     SUBGOAL_THEN `16 * 523776 + r MOD 523776 = r` MP_TAC THENL
     [MP_TAC(SPECL [`r:num`; `523776`] (CONJUNCT1 DIVISION_SIMP)) THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
     DISCH_TAC THEN ASM_SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_EQ] THEN
     ASM_ARITH_TAC;
     (* Upper wrap: r DIV 523776 = 15 *)
     SUBGOAL_THEN `r DIV 523776 = 15` ASSUME_TAC THENL
     [DIV_523776_TAC 15; ALL_TAC] THEN
     SUBGOAL_THEN `15 * 523776 + r MOD 523776 = r` MP_TAC THENL
     [MP_TAC(SPECL [`r:num`; `523776`] (CONJUNCT1 DIVISION_SIMP)) THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
     DISCH_TAC THEN
     SUBGOAL_THEN `(&r:int) - (&(r MOD 523776) - &523776) =
                   &(r - r MOD 523776 + 523776)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; GSYM INT_OF_NUM_ADD] THEN
      INT_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
   MP_TAC(SPEC `r:num` A1_WRAP) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV] THEN
  (* Nowrap zone: unfold and do interval cascade *)
  REWRITE_TAC[decompose_32_r1; mldsa_decompose_32; mldsa_cmod] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `r MOD 523776 <= r` ASSUME_TAC THENL
  [MESON_TAC[MOD_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `r MOD 523776 < 523776` ASSUME_TAC THENL
  [MP_TAC(SPECL [`r:num`; `523776`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
  let intervals = [
    (0, 261888); (261889, 785664); (785665, 1309440);
    (1309441, 1833216); (1833217, 2356992); (2356993, 2880768);
    (2880769, 3404544); (3404545, 3928320); (3928321, 4452096);
    (4452097, 4975872); (4975873, 5499648); (5499649, 6023424);
    (6023425, 6547200); (6547201, 7070976); (7070977, 7594752);
    (7594753, 8118528)] in
  let mk_le hi =
    mk_comb(mk_comb(`(<=):num->num->bool`, mk_var("r",`:num`)),
            mk_small_numeral hi) in
  let apply_interval k (lo, hi) =
    let th = SPECL [`r:num`; mk_small_numeral lo;
                    mk_small_numeral hi; mk_small_numeral k]
                   BARRETT_INTERVAL_32 in
    MP_TAC th THEN CONV_TAC NUM_REDUCE_CONV THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DECOMPOSE_R1_NOWRAP_TAC in
  let rec cascade k = function
    | [(lo,hi)] -> apply_interval k (lo,hi)
    | (lo,hi)::rest ->
        ASM_CASES_TAC (mk_le hi) THENL
        [apply_interval k (lo,hi); cascade (k+1) rest]
    | [] -> failwith "empty" in
  cascade 0 intervals);;

let R1_IS_DIV_LOWER = prove(
  `!r. r < 8380417 /\ r MOD 523776 * 2 <= 523776 /\
       ~((&r:int) - &(r MOD 523776) = &8380416) ==>
   (((r + 127) DIV 128 * 1025 + 2097152) DIV 4194304) MOD 16 = r DIV 523776`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `r:num` DECOMPOSE_32_R1_EQUIV) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `r:num` LOWER_NONWRAP_R1) THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let R1_IS_DIV_PLUS1_UPPER = prove(
  `!r. r < 8380417 /\ ~(r MOD 523776 * 2 <= 523776) /\
       ~((&r:int) - (&(r MOD 523776) - &523776) = &8380416) ==>
   (((r + 127) DIV 128 * 1025 + 2097152) DIV 4194304) MOD 16 =
   r DIV 523776 + 1`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `r:num` DECOMPOSE_32_R1_EQUIV) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `r:num` UPPER_NONWRAP_R1) THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]);;

(* Upper nowrap: substitute Barrett = r DIV 523776 + 1, use INT_MOD_RESIDUE *)
let R0_SIGN_UPPER_NOWRAP_TAC =
  MP_TAC(SPEC `r:num` R1_IS_DIV_PLUS1_UPPER) THEN
  ANTS_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPECL [`r:num`; `523776`] INT_MOD_RESIDUE)) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_ARITH `(a:int) - (b + &1) * c = a - b * c - c`] THEN
  REWRITE_TAC[INT_ARITH `x - &523776 > &0 <=> x > &523776`;
              INT_ARITH `x - &523776 - &8380417 > &0 <=> x > &8904193`;
              INT_OF_NUM_GT] THEN
  ASM_ARITH_TAC;;

(* Lower nowrap: substitute Barrett = r DIV 523776, use INT_MOD_RESIDUE *)
let R0_SIGN_LOWER_NOWRAP_TAC =
  MP_TAC(SPEC `r:num` R1_IS_DIV_LOWER) THEN
  ANTS_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPECL [`r:num`; `523776`] INT_MOD_RESIDUE)) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_ARITH `x - &8380417 > &0 <=> x > &8380417`;
              INT_OF_NUM_GT] THEN
  ASM_ARITH_TAC;;

(* Wrap: derive 8118528 < r, use DECOMPOSE_32_R1_EQUIV to get Barrett = 0 *)
let R0_SIGN_WRAP_TAC =
  SUBGOAL_THEN `8118528 < r` ASSUME_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o check (fun th ->
     can (find_term (fun t -> t = `&8380416:int`)) (concl th) &&
     not(is_neg(concl th)))) THEN
   ASM_SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_EQ;
     INT_ARITH `(a:int) - (b - c) = d <=> a + c - b = d`;
     GSYM INT_OF_NUM_ADD] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `r:num` DECOMPOSE_32_R1_EQUIV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[decompose_32_r1; mldsa_decompose_32; mldsa_cmod] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[INT_MUL_LZERO; INT_SUB_RZERO] THEN
  REWRITE_TAC[INT_ARITH `x - &1 > &0 <=> x > &1`;
              INT_ARITH `(x - &523776) - &1 > &0 <=> x > &523777`;
              INT_ARITH `x - &8380417 > &0 <=> x > &8380417`;
              INT_OF_NUM_GT] THEN
  ASM_ARITH_TAC;;

let DECOMPOSE_32_R0_SIGN = time prove(
  `!r. r < 8380417 ==>
    let a1 = (((r + 127) DIV 128 * 1025 + 2097152) DIV 4194304) MOD 16 in
    let a0':int = if (&r:int) - &a1 * &523776 > &4190208
                  then &r - &a1 * &523776 - &8380417
                  else &r - &a1 * &523776 in
    (decompose_32_r0 r > &0 <=> a0' > &0) /\
    (decompose_32_r0 r <= &0 <=> ~(a0' > &0))`,
  GEN_TAC THEN DISCH_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[INT_ARITH `(x:int) <= &0 <=> ~(x > &0)`] THEN
  MATCH_MP_TAC(TAUT `(p <=> q) ==> (p <=> q) /\ (~p <=> ~q)`) THEN
  REWRITE_TAC[decompose_32_r0; mldsa_decompose_32; mldsa_cmod] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[SND; FST] THEN
  SUBGOAL_THEN `r MOD 523776 <= r` ASSUME_TAC THENL
  [MESON_TAC[MOD_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `r MOD 523776 < 523776` ASSUME_TAC THENL
  [MP_TAC(SPECL [`r:num`; `523776`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `r MOD 523776 * 2 <= 523776` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  TRY R0_SIGN_LOWER_NOWRAP_TAC THEN
  TRY R0_SIGN_UPPER_NOWRAP_TAC THEN
  TRY R0_SIGN_WRAP_TAC THEN
  TRY(
    (* Contradiction: lower nowrap with > 4190208 *)
    MP_TAC(SPEC `r:num` R1_IS_DIV_LOWER) THEN
    ANTS_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(CONV_RULE NUM_REDUCE_CONV
      (SPECL [`r:num`; `523776`] INT_MOD_RESIDUE)) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(&r:int) - &((((r + 127) DIV 128 * 1025 + 2097152) DIV
      4194304) MOD 16) * &523776 = &(r MOD 523776)` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(&(r MOD 523776) > (&4190208:int))` MP_TAC THENL
    [REWRITE_TAC[INT_NOT_LT; INT_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[INT_OF_NUM_GT] THEN ASM_ARITH_TAC
  ));;

let MLDSA_USE_HINT_32_EQUIV = prove(
  `!r h. r < 8380417 /\ h <= 1
         ==> mldsa_use_hint_32 h r = mldsa_use_hint_32_code r h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MLDSA_USE_HINT_32_UNFOLD] THEN
  REWRITE_TAC[mldsa_use_hint_32_code] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPEC `r:num` DECOMPOSE_32_R1_EQUIV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `r:num` DECOMPOSE_32_R0_SIGN) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  ASM_CASES_TAC `h = 0` THENL
  [ASM_REWRITE_TAC[ARITH_RULE `~(0 = 1)`]; ALL_TAC] THEN
  SUBGOAL_THEN `h = 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `decompose_32_r0 r > &0` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

(* ========================================================================= *)
(* Strengthen-post utility for the FIPS-aligned correctness proof            *)
(* ========================================================================= *)

let ENSURES_STRENGTHEN_POST = prove(
  `!P (Q:armstate->bool) Q' R.
     ensures arm P Q' R /\ (!s. Q' s ==> Q s) ==> ensures arm P Q R`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[ensures] THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `s0:armstate` THEN MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MP_TAC(BETA_RULE(ISPECL [`arm`;
    `\s':armstate. (Q':armstate->bool) s' /\ (R:armstate->armstate->bool) (s0:armstate) s'`;
    `\s':armstate. (Q:armstate->bool) s' /\ (R:armstate->armstate->bool) (s0:armstate) s'`]
    EVENTUALLY_MONO)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; MESON_TAC[]]);;


(* ========================================================================= *)
(* Correctness (FIPS 204-aligned)                                            *)
(* ========================================================================= *)

(* Postcondition is stated in terms of mldsa_use_hint_32 from FIPS 204
   (Algorithm 40), with the output bound < 16 as a corollary. The bounds
   on val(x i) / val(y i) appear as antecedents inside the postcondition
   (decompose-style): the assembly executes regardless of input ranges,
   and only the FIPS-equivalence + output bound require the input bounds. *)
let MLDSA_USE_HINT_32_CORRECT = prove
 (`!b a h x y pc.
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_32_mc) (b, 1024) /\
    nonoverlapping (b, 1024) (a, 1024) /\
    nonoverlapping (b, 1024) (h, 1024)
    ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mldsa_poly_use_hint_32_mc /\
               read PC s = word pc /\
               C_ARGUMENTS [b; a; h] s /\
               (!i. i < 256 ==>
                 read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
               (!i. i < 256 ==>
                 read(memory :> bytes32(word_add h (word(4 * i)))) s = y i))
          (\s. read PC s = word(pc + LENGTH mldsa_poly_use_hint_32_mc - 4) /\
               ((!i. i < 256 ==> val(x i:int32) < 8380417) /\
                (!i. i < 256 ==> val(y i:int32) <= 1)
                ==> (!i. i < 256 ==>
                      read(memory :> bytes32(word_add b (word(4 * i)))) s =
                        word(mldsa_use_hint_32 (val(y i)) (val(x i)))) /\
                    (!i. i < 256 ==>
                      val(read(memory :> bytes32
                        (word_add b (word(4 * i)))) s) < 16)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(b, 1024)])`,

  MAP_EVERY X_GEN_TAC
    [`b:int64`; `a:int64`; `h:int64`;
     `x:num->int32`; `y:num->int32`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL;
              fst MLDSA_USE_HINT_32_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GLOBALIZE_PRECONDITION_TAC THEN
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV EXPAND_CASES_CONV))) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SOME_FLAGS; MODIFIABLE_SIMD_REGS] THEN

  (* Initialize and merge memory (input bounds NOT used yet). *)
  ENSURES_INIT_TAC "s0" THEN
  MEMORY_128_FROM_32_TAC "a" 0 64 THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC WORD_REDUCE_CONV THEN
  STRIP_TAC THEN
  MEMORY_128_FROM_32_TAC "h" 0 64 THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN CONV_TAC WORD_REDUCE_CONV THEN
  STRIP_TAC THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN

  (* Simulate 878 instructions (the assembly is bound-independent). *)
  MAP_EVERY (fun n -> ARM_STEPS_TAC MLDSA_USE_HINT_32_EXEC [n] THEN
                      SIMD_SIMPLIFY_TAC[])
        (1--878) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (* Pick up the postcondition's input-bound antecedents
     (val(x i) < 8380417 /\ val(y i) <= 1) as assumptions. *)
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN

  (* Split bytes128 -> bytes32 for output memory. *)
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE (SIMD_SIMPLIFY_CONV []) o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
    check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

  (* Expand output cases, substitute. *)
  CONV_TAC(TOP_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV THENC DEPTH_CONV NUM_ADD_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN

  (* Push word_subword through SIMD ops to per-element form. *)
  REWRITE_TAC[WORD_SUBWORD_AND; WORD_SUBWORD_OR] THEN
  let WSN_TAC = REWRITE_TAC(map (fun n -> prove(
    subst [mk_small_numeral n, `n:num`]
      `!x:int128. word_subword(word_not x) (n,32):int32 = word_not(word_subword x (n,32))`,
    GEN_TAC THEN MATCH_MP_TAC WORD_SUBWORD_NOT THEN
    REWRITE_TAC[DIMINDEX_32; DIMINDEX_128] THEN ARITH_TAC)) [0;32;64;96]) in
  WSN_TAC THEN
  CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN

  (* Build the per-element FIPS-eq lemma EC_FINAL by composing
     ELEMENT_CORRECT_WORD with the asm definition unfold. *)
  let EC_DEEP =
    CONV_RULE(DEPTH_CONV WORD_NUM_RED_CONV)
     (CONV_RULE(DEPTH_CONV(INT_RED_CONV ORELSEC NUM_RED_CONV))
       (CONV_RULE(TOP_DEPTH_CONV let_CONV)
         (REWRITE_RULE[mldsa_use_hint_32_asm; word_2smulh; word_ishr_round;
                        DIMINDEX_32] ELEMENT_CORRECT_WORD))) in
  let EC_FINAL = ONCE_REWRITE_RULE[WORD_AND_SYM]
    (ONCE_REWRITE_RULE[WORD_OR_SYM] EC_DEEP) in

  (* Pre-rewrite mldsa_use_hint_32 -> _code via the equivalence at all
     occurrences in the goal. IMP_REWRITE_TAC handles the conditional lemma
     and leaves index-bound side conditions (i < 256) which we close
     uniformly via ARITH below. *)
  REPEAT (IMP_REWRITE_TAC[MLDSA_USE_HINT_32_EQUIV]) THEN

  (* Split into per-element leaf goals (FIPS-eq + val<16) plus index-bound
     side conditions left over from IMP_REWRITE_TAC. Each FIPS-eq leaf is
     closed by EC_FINAL; each val<16 leaf is closed by reducing val(word ..)
     to MOD via VAL_WORD then bounding mldsa_use_hint_32_code < 16. *)
  REPEAT CONJ_TAC THEN
  (FIRST [
    MATCH_MP_TAC EC_FINAL THEN CONJ_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC(ARITH_RULE `x < 16 ==> x MOD 4294967296 < 16`) THEN
      REWRITE_TAC[mldsa_use_hint_32_code] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      REWRITE_TAC[MOD_LT_EQ; ARITH_EQ];
    ARITH_TAC]));;


(* ========================================================================= *)
(* Public subroutine correctness (FIPS 204-aligned)                          *)
(* ========================================================================= *)

(* Subroutine form: derives directly from MLDSA_USE_HINT_32_CORRECT by adding
   the X30 -> RET return wiring via ARM_ADD_RETURN_NOSTACK_TAC. The bound
   antecedents inside the postcondition pass through unchanged (decompose
   pattern). *)
let MLDSA_USE_HINT_32_SUBROUTINE_CORRECT = prove
 (`!b a h x y pc returnaddress.
    nonoverlapping (word pc, LENGTH mldsa_poly_use_hint_32_mc) (b, 1024) /\
    nonoverlapping (b, 1024) (a, 1024) /\
    nonoverlapping (b, 1024) (h, 1024)
    ==> ensures arm
          (\s. aligned_bytes_loaded s (word pc) mldsa_poly_use_hint_32_mc /\
               read PC s = word pc /\
               read X30 s = returnaddress /\
               C_ARGUMENTS [b; a; h] s /\
               (!i. i < 256 ==>
                 read(memory :> bytes32(word_add a (word(4 * i)))) s = x i) /\
               (!i. i < 256 ==>
                 read(memory :> bytes32(word_add h (word(4 * i)))) s = y i))
          (\s. read PC s = returnaddress /\
               ((!i. i < 256 ==> val(x i:int32) < 8380417) /\
                (!i. i < 256 ==> val(y i:int32) <= 1)
                ==> (!i. i < 256 ==>
                      read(memory :> bytes32(word_add b (word(4 * i)))) s =
                        word(mldsa_use_hint_32 (val(y i)) (val(x i)))) /\
                    (!i. i < 256 ==>
                      val(read(memory :> bytes32
                        (word_add b (word(4 * i)))) s) < 16)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
           MAYCHANGE [memory :> bytes(b, 1024)])`,
  REWRITE_TAC[fst MLDSA_USE_HINT_32_EXEC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ARM_ADD_RETURN_NOSTACK_TAC MLDSA_USE_HINT_32_EXEC
    (CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
      (REWRITE_RULE[fst MLDSA_USE_HINT_32_EXEC]
         MLDSA_USE_HINT_32_CORRECT)));;


(* ========================================================================= *)
(* Constant-time and memory safety proof.                                    *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;


let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mldsa_poly_use_hint_32" subroutine_signatures)
    MLDSA_USE_HINT_32_SUBROUTINE_CORRECT
    MLDSA_USE_HINT_32_EXEC;;

let MLDSA_USE_HINT_32_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e b a h pc returnaddress.
           nonoverlapping (word pc,LENGTH mldsa_poly_use_hint_32_mc) (b,1024) /\
           nonoverlapping (b,1024) (a,1024) /\
           nonoverlapping (b,1024) (h,1024)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mldsa_poly_use_hint_32_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [b; a; h] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events a h b pc returnaddress /\
                         memaccess_inbounds e2 [a,1024; h,1024; b,1024]
                         [b,1024]))
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLDSA_USE_HINT_32_EXEC);;

