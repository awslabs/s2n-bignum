(*
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 *)

(* ========================================================================= *)
(* Functional correctness of poly_decompose_32:                              *)
(* Decompose polynomial coefficients into (a1, a0) where a = a1*2*GAMMA2+a0  *)
(* for GAMMA2 = (Q-1)/32 = 261888 (ML-DSA-65/87)                             *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(**** print_literal_from_elf "arm/mldsa/mldsa_decompose_32.o";;
 ****)

let mldsa_decompose_32_mc = define_assert_from_elf "mldsa_decompose_32_mc" "arm/mldsa/mldsa_decompose_32.o"
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
  0xd2800203;       (* arm_MOV X3 (rvalue (word 16)) *)
  0x3dc00020;       (* arm_LDR Q0 X1 (Immediate_Offset (word 0)) *)
  0x3dc00421;       (* arm_LDR Q1 X1 (Immediate_Offset (word 16)) *)
  0x3dc00822;       (* arm_LDR Q2 X1 (Immediate_Offset (word 32)) *)
  0x3dc00c23;       (* arm_LDR Q3 X1 (Immediate_Offset (word 48)) *)
  0x4eb7b425;       (* arm_SQDMULH_VEC Q5 Q1 Q23 32 128 *)
  0x4f2e24a5;       (* arm_SRSHR_VEC Q5 Q5 18 32 128 *)
  0x4eb53438;       (* arm_CMGT_VEC Q24 Q1 Q21 32 128 *)
  0x6eb694a1;       (* arm_MLS_VEC Q1 Q5 Q22 32 128 *)
  0x4e781ca5;       (* arm_BIC_VEC Q5 Q5 Q24 128 *)
  0x4eb88421;       (* arm_ADD_VEC Q1 Q1 Q24 32 128 *)
  0x4eb7b446;       (* arm_SQDMULH_VEC Q6 Q2 Q23 32 128 *)
  0x4f2e24c6;       (* arm_SRSHR_VEC Q6 Q6 18 32 128 *)
  0x4eb53458;       (* arm_CMGT_VEC Q24 Q2 Q21 32 128 *)
  0x6eb694c2;       (* arm_MLS_VEC Q2 Q6 Q22 32 128 *)
  0x4e781cc6;       (* arm_BIC_VEC Q6 Q6 Q24 128 *)
  0x4eb88442;       (* arm_ADD_VEC Q2 Q2 Q24 32 128 *)
  0x4eb7b467;       (* arm_SQDMULH_VEC Q7 Q3 Q23 32 128 *)
  0x4f2e24e7;       (* arm_SRSHR_VEC Q7 Q7 18 32 128 *)
  0x4eb53478;       (* arm_CMGT_VEC Q24 Q3 Q21 32 128 *)
  0x6eb694e3;       (* arm_MLS_VEC Q3 Q7 Q22 32 128 *)
  0x4e781ce7;       (* arm_BIC_VEC Q7 Q7 Q24 128 *)
  0x4eb88463;       (* arm_ADD_VEC Q3 Q3 Q24 32 128 *)
  0x4eb7b404;       (* arm_SQDMULH_VEC Q4 Q0 Q23 32 128 *)
  0x4f2e2484;       (* arm_SRSHR_VEC Q4 Q4 18 32 128 *)
  0x4eb53418;       (* arm_CMGT_VEC Q24 Q0 Q21 32 128 *)
  0x6eb69480;       (* arm_MLS_VEC Q0 Q4 Q22 32 128 *)
  0x4e781c84;       (* arm_BIC_VEC Q4 Q4 Q24 128 *)
  0x4eb88400;       (* arm_ADD_VEC Q0 Q0 Q24 32 128 *)
  0x3d800405;       (* arm_STR Q5 X0 (Immediate_Offset (word 16)) *)
  0x3d800806;       (* arm_STR Q6 X0 (Immediate_Offset (word 32)) *)
  0x3d800c07;       (* arm_STR Q7 X0 (Immediate_Offset (word 48)) *)
  0x3c840404;       (* arm_STR Q4 X0 (Postimmediate_Offset (word 64)) *)
  0x3d800421;       (* arm_STR Q1 X1 (Immediate_Offset (word 16)) *)
  0x3d800822;       (* arm_STR Q2 X1 (Immediate_Offset (word 32)) *)
  0x3d800c23;       (* arm_STR Q3 X1 (Immediate_Offset (word 48)) *)
  0x3c840420;       (* arm_STR Q0 X1 (Postimmediate_Offset (word 64)) *)
  0xf1000463;       (* arm_SUBS X3 X3 (rvalue (word 1)) *)
  0x54fffb61;       (* arm_BNE (word 2097004) *)
  0xd65f03c0        (* arm_RET X30 *)
];;
(*** BYTECODE END ***)

let MLDSA_DECOMPOSE_32_EXEC = ARM_MK_EXEC_RULE mldsa_decompose_32_mc;;

(* ========================================================================= *)
(* Constants                                                                 *)
(* ========================================================================= *)

let LENGTH_MLDSA_DECOMPOSE_32_MC =
  REWRITE_CONV[mldsa_decompose_32_mc] `LENGTH mldsa_decompose_32_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let MLDSA_DECOMPOSE_32_CORE_START = new_definition
  `MLDSA_DECOMPOSE_32_CORE_START = 0`;;

let MLDSA_DECOMPOSE_32_POSTAMBLE_LENGTH = new_definition
  `MLDSA_DECOMPOSE_32_POSTAMBLE_LENGTH = 4`;;

let MLDSA_DECOMPOSE_32_CORE_END = new_definition
  `MLDSA_DECOMPOSE_32_CORE_END =
     LENGTH mldsa_decompose_32_mc - MLDSA_DECOMPOSE_32_POSTAMBLE_LENGTH`;;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_MLDSA_DECOMPOSE_32_MC;
              MLDSA_DECOMPOSE_32_CORE_START; MLDSA_DECOMPOSE_32_CORE_END;
              MLDSA_DECOMPOSE_32_POSTAMBLE_LENGTH] THENC
  NUM_REDUCE_CONV THENC REWRITE_CONV [ADD_0];;

(* ========================================================================= *)
(* Word-level helper functions                                               *)
(* Per-lane operations matching the assembly's SQDMULH+SRSHR, BIC, MLS+ADD   *)
(* ========================================================================= *)

(* h32: quotient = srshr(sqdmulh(x, magic), 18) ≈ round(x / 523776) *)
let h32 = define
  `h32 (x:int32) : int32 =
   iword((ival((iword_saturate:int->int32)
     ((&2 * ival x * &1074791425) div &4294967296)) +
     &131072) div &262144)`;;

(* decompose32_a1: a1 = h AND (NOT mask) where mask = -1 if x > threshold *)
let decompose32_a1 = define
  `decompose32_a1 (x:int32) : int32 =
   word_and (h32 x)
     (word_not(word_neg(word(bitval(ival x > &8118528)))))`;;

(* decompose32_a0: a0 = (x - h*2*GAMMA2) + mask *)
let decompose32_a0 = define
  `decompose32_a0 (x:int32) : int32 =
   word_add (word_sub x (word_mul (h32 x) (word 523776)))
     (word_neg(word(bitval(ival x > &8118528))))`;;

(* ival equals val across the full non-negative int32 range (val < 2^31) *)
let IVAL_EQ_VAL = prove(
  `!x:int32. val x < 2 EXP 31 ==> ival x = &(val x)`,
  GEN_TAC THEN REWRITE_TAC[IVAL_VAL; DIMINDEX_32] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `bit (32 - 1) (x:int32) = F` ASSUME_TAC THENL [
    REWRITE_TAC[BIT_VAL; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_ARITH_TAC;
    ASM_REWRITE_TAC[bitval] THEN INT_ARITH_TAC]);;

(* ========================================================================= *)
(* Mathematical correctness lemmas                                           *)
(* Connect word-level decompose32_a1/a0 to spec-level mldsa_decompose_32     *)
(* ========================================================================= *)

(* Case split: a1 is either h32 or 0 depending on the threshold *)
let DECOMPOSE32_A1_CASES = prove(
  `!x:int32. decompose32_a1 x =
     if ival x > &8118528 then word 0 else h32 x`,
  REWRITE_TAC[decompose32_a1] THEN BITBLAST_TAC);;

(* Case split: a0 subtracts 1 in the special case *)
let DECOMPOSE32_A0_CASES = prove(
  `!x:int32. decompose32_a0 x =
     if ival x > &8118528
     then word_sub (word_sub x (word_mul (h32 x) (word 523776))) (word 1)
     else word_sub x (word_mul (h32 x) (word 523776))`,
  GEN_TAC THEN REWRITE_TAC[decompose32_a0] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[bitval] THEN CONV_TAC WORD_RULE);;

(* ========================================================================= *)
(* Barrett reduction correctness for h32                                     *)
(* Shows that SQDMULH+SRSHR computes round(x / 523776) correctly             *)
(* ========================================================================= *)

(* Algebraic expansion: n*K + q*E = q*D*P + r*K
   where K=2149582850, M=523776, D=262144, P=4294967296, E=1024 *)
let BARRETT32_EXPAND = prove(
  `!n. n * 2149582850 + (n DIV 523776) * 1024 =
       (n DIV 523776) * 262144 * 4294967296 + (n MOD 523776) * 2149582850`,
  GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `523776`] DIVISION) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [th]) ASSUME_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC NUM_RING);;

(* Barrett reduction: (n*K) DIV P with rounding = round(n / M) *)
let BARRETT32_CORRECT = prove(
  `!n. n < 8380417 ==>
    ((n * 2149582850) DIV 4294967296 + 131072) DIV 262144 =
    (if n MOD 523776 * 2 <= 523776
     then n DIV 523776
     else n DIV 523776 + 1)`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `n = 8380416` THENL [
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  ABBREV_TAC `q = n DIV 523776` THEN
  ABBREV_TAC `r = n MOD 523776` THEN
  SUBGOAL_THEN `n = q * 523776 + r` ASSUME_TAC THENL [
    EXPAND_TAC "q" THEN EXPAND_TAC "r" THEN
    MESON_TAC[DIVISION; ARITH_RULE `~(523776 = 0)`]; ALL_TAC] THEN
  SUBGOAL_THEN `r < 523776` ASSUME_TAC THENL [
    EXPAND_TAC "r" THEN SIMP_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `q <= 15` ASSUME_TAC THENL [
    EXPAND_TAC "q" THEN ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `~(523776 = 0)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `n:num` BARRETT32_EXPAND) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  COND_CASES_TAC THENL [
    (* Round-down case: r * 2 <= 523776, so r <= 261888 *)
    ABBREV_TAC `d = ((q * 523776 + r) * 2149582850) DIV 4294967296` THEN
    MP_TAC(SPECL [`(q * 523776 + r) * 2149582850`; `4294967296`] DIVISION) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `d * 4294967296 + q * 1024 <= q * 262144 * 4294967296 + r * 2149582850` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `q * 262144 * 4294967296 + r * 2149582850 < (d + 1) * 4294967296 + q * 1024` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `r * 2149582850 <= 261888 * 2149582850` ASSUME_TAC THENL [
      MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC DIV_SANDWICH THEN CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THENL [
      MP_TAC(ARITH_RULE `261888 * 2149582850 < 131072 * 4294967296`) THEN ASM_ARITH_TAC;
      MP_TAC(ARITH_RULE `261888 * 2149582850 < 131072 * 4294967296`) THEN ASM_ARITH_TAC];
    (* Round-up case: ~(r * 2 <= 523776), so r >= 261889 *)
    ABBREV_TAC `d = ((q * 523776 + r) * 2149582850) DIV 4294967296` THEN
    MP_TAC(SPECL [`(q * 523776 + r) * 2149582850`; `4294967296`] DIVISION) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `d * 4294967296 + q * 1024 <= q * 262144 * 4294967296 + r * 2149582850` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `q * 262144 * 4294967296 + r * 2149582850 < (d + 1) * 4294967296 + q * 1024` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `261889 * 2149582850 <= r * 2149582850` ASSUME_TAC THENL [
      MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `r * 2149582850 < 523776 * 2149582850` ASSUME_TAC THENL [
      REWRITE_TAC[LT_MULT_RCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `q * 1024 <= 15 * 1024` ASSUME_TAC THENL [
      MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC DIV_SANDWICH THEN CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THENL [
      MP_TAC(ARITH_RULE `131072 * 4294967296 + 15 * 1024 <= 261889 * 2149582850`) THEN
      ASM_ARITH_TAC;
      MP_TAC(ARITH_RULE `523776 * 2149582850 < 262144 * 4294967296`) THEN
      ASM_ARITH_TAC]]);;

(* ========================================================================= *)
(* Word-level to natural number connection for h32                           *)
(* ========================================================================= *)

(* h32 computes the correct rounding quotient: round(val x / 523776)
   Eliminates iword_saturate by inlining its definition and using BOUNDER_TAC
   to discharge the impossible saturation cases (consistent with mlkem-native). *)
let H32_CORRECT = prove(
  `!x:int32. val x < 8380417 ==>
    val(h32 x) = (if val x MOD 523776 * 2 <= 523776
                  then val x DIV 523776
                  else val x DIV 523776 + 1)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[h32; iword_saturate; word_INT_MIN; word_INT_MAX; DIMINDEX_32] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REPEAT(COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[] `p ==> ~p ==> q`)) THEN
    REWRITE_TAC[INT_GT; INT_NOT_LT] THEN BOUNDER_TAC[];
    ASM_REWRITE_TAC[]]) THEN
  MP_TAC(SPEC `x:int32` IVAL_EQ_VAL) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[INT_OF_NUM_MUL] THEN
  SUBGOAL_THEN `2 * val(x:int32) * 1074791425 = val x * 2149582850` SUBST1_TAC THENL [
    ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_DIV] THEN
  SUBGOAL_THEN `(val(x:int32) * 2149582850) DIV 4294967296 < 2147483648` ASSUME_TAC THENL [
    ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `~(4294967296 = 0)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ival(iword(&((val(x:int32) * 2149582850) DIV 4294967296)):int32) =
    &((val x * 2149582850) DIV 4294967296)` SUBST1_TAC THENL [
    MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN
    REWRITE_TAC[INT_OF_NUM_LT; INT_LE_NEG2; INT_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_DIV] THEN
  SUBGOAL_THEN `((val(x:int32) * 2149582850) DIV 4294967296 + 131072) DIV 262144 < 2147483648` ASSUME_TAC THENL [
    ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `~(262144 = 0)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM WORD_IWORD; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_EXP_CONV) THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 2147483648 ==> n < 4294967296`] THEN
  MATCH_MP_TAC BARRETT32_CORRECT THEN ASM_REWRITE_TAC[]);;

(* Special case: rounding quotient = 16 when val x > 8118528 *)
let ROUND32_SPECIAL = prove(
  `!n. 8118528 < n /\ n < 8380417 ==>
    (if n MOD 523776 * 2 <= 523776 then n DIV 523776 else n DIV 523776 + 1) = 16`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n < 8380416` THENL [
    SUBGOAL_THEN `n DIV 523776 = 15` ASSUME_TAC THENL [
      MATCH_MP_TAC DIV_SANDWICH THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    COND_CASES_TAC THENL [
      MP_TAC(SPECL [`n:num`; `523776`] DIVISION) THEN
      ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      STRIP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[]];
    SUBGOAL_THEN `n = 8380416` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

(* ========================================================================= *)
(* Main correctness lemmas: connect word-level to spec-level                 *)
(* ========================================================================= *)

(* decompose32_a1 computes FST(mldsa_decompose_32(val x)) *)
let DECOMPOSE32_A1_CORRECT = prove(
  `!x:int32. val x < 8380417
    ==> val(decompose32_a1 x) = FST(mldsa_decompose_32(val x))`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[DECOMPOSE32_A1_CASES; MLDSA_DECOMPOSE_32_EXPAND; LET_DEF; LET_END_DEF; FST] THEN
  COND_CASES_TAC THENL [
    (* ival x > &8118528: a1 = word 0, h = 16, FST = 0 *)
    REWRITE_TAC[VAL_WORD_0; FST] THEN
    SUBGOAL_THEN `val(x:int32) < 2 EXP 31` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `x:int32` IVAL_EQ_VAL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&(val(x:int32)):int > &8118528` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[INT_OF_NUM_GT; GT] THEN DISCH_TAC THEN
    MP_TAC(SPEC `val(x:int32)` ROUND32_SPECIAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FST];
    (* ~(ival x > &8118528): a1 = h32 x, h < 16 *)
    MP_TAC(SPEC `x:int32` H32_CORRECT) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THENL [
      (* Round-down case *)
      SUBGOAL_THEN `val(x:int32) <= 8118528` ASSUME_TAC THENL [
        SUBGOAL_THEN `val(x:int32) < 2 EXP 31` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        MP_TAC(SPEC `x:int32` IVAL_EQ_VAL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        SUBGOAL_THEN `~(&(val(x:int32)):int > &8118528)` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[INT_GT; INT_NOT_LT; INT_OF_NUM_LE]; ALL_TAC] THEN
      SUBGOAL_THEN `~(val(x:int32) DIV 523776 = 16)` ASSUME_TAC THENL [
        DISCH_TAC THEN
        MP_TAC(SPECL [`val(x:int32)`; `523776`] DIVISION) THEN
        ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        STRIP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[FST];
      (* Round-up case *)
      SUBGOAL_THEN `val(x:int32) <= 8118528` ASSUME_TAC THENL [
        SUBGOAL_THEN `val(x:int32) < 2 EXP 31` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        MP_TAC(SPEC `x:int32` IVAL_EQ_VAL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        SUBGOAL_THEN `~(&(val(x:int32)):int > &8118528)` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[INT_GT; INT_NOT_LT; INT_OF_NUM_LE]; ALL_TAC] THEN
      SUBGOAL_THEN `~(val(x:int32) DIV 523776 + 1 = 16)` ASSUME_TAC THENL [
        REWRITE_TAC[ARITH_RULE `n + 1 = 16 <=> n = 15`] THEN DISCH_TAC THEN
        MP_TAC(SPECL [`val(x:int32)`; `523776`] DIVISION) THEN
        ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        STRIP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[FST]]]);;

(* mldsa_cmod n 523776 is bounded by [-261888, 261888], well within int32 range *)
let CMOD_ABS_BOUND_523776 = prove(
  `!n. abs(mldsa_cmod n 523776) <= &261888`,
  GEN_TAC THEN REWRITE_TAC[mldsa_cmod] THEN
  SUBGOAL_THEN `n MOD 523776 < 523776` MP_TAC THENL [
    SIMP_TAC[MOD_LT_EQ; ARITH_RULE `~(523776 = 0)`]; ALL_TAC] THEN
  SPEC_TAC(`n MOD 523776`, `m:num`) THEN GEN_TAC THEN DISCH_TAC THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[INT_ABS; INT_POS; INT_OF_NUM_LE;
              INT_OF_NUM_SUB; INT_SUB_LE; INT_NEG_SUB] THEN
  ASM_ARITH_TAC);;

(* decompose32_a0 computes SND(mldsa_decompose_32(val x)) *)
let DECOMPOSE32_A0_CORRECT = prove(
  `!x:int32. val x < 8380417
    ==> ival(decompose32_a0 x) = SND(mldsa_decompose_32(val x))`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[DECOMPOSE32_A0_CASES; MLDSA_DECOMPOSE_32_EXPAND; LET_DEF; LET_END_DEF; SND] THEN
  (* Express word_sub x (word_mul (h32 x) (word 523776)) as iword(...) *)
  SUBGOAL_THEN `word_sub x (word_mul (h32 x) (word 523776)) : int32 =
    iword(ival x - ival(h32 x) * &523776)` SUBST1_TAC THENL [
    CONV_TAC WORD_RULE; ALL_TAC] THEN
  (* Convert ival x and ival(h32 x) to val-based expressions *)
  SUBGOAL_THEN `ival(x:int32) = &(val x)` SUBST1_TAC THENL [
    MATCH_MP_TAC IVAL_EQ_VAL THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ival(h32 x:int32) = &(val(h32 x))` SUBST1_TAC THENL [
    MATCH_MP_TAC IVAL_EQ_VAL THEN
    MP_TAC(SPEC `x:int32` H32_CORRECT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `~(523776 = 0)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  (* Substitute h32 value using H32_CORRECT *)
  MP_TAC(SPEC `x:int32` H32_CORRECT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[INT_OF_NUM_GT] THEN
  ABBREV_TAC `h = (if val(x:int32) MOD 523776 * 2 <= 523776
    then val x DIV 523776 else val x DIV 523776 + 1)` THEN
  (* Establish DIVISION identity in int form *)
  SUBGOAL_THEN `&(val(x:int32)):int =
    &(val x DIV 523776) * &523776 + &(val x MOD 523776)` ASSUME_TAC THENL [
    MP_TAC(SPECL [`val(x:int32)`; `523776`] DIVISION) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `int_of_num` o CONJUNCT1) THEN
    REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD]; ALL_TAC] THEN
  (* Prove key identity: val x - h * 523776 = mldsa_cmod(val x) 523776 *)
  SUBGOAL_THEN `&(val(x:int32)) - &h * &523776 = mldsa_cmod (val x) 523776`
    ASSUME_TAC THENL [
    REWRITE_TAC[mldsa_cmod] THEN
    FIRST_X_ASSUM(MP_TAC o SYM o check (fun th ->
      fst(dest_cond(fst(dest_eq(concl th)))) =
        `val (x:int32) MOD 523776 * 2 <= 523776`)) THEN
    COND_CASES_TAC THENL [
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[GSYM INT_OF_NUM_ADD;
        GSYM INT_OF_NUM_MUL] THEN INT_ARITH_TAC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* Case split on val x > 8118528 *)
  COND_CASES_TAC THENL [
    (* Special case: val x > 8118528, h = 16 *)
    SUBGOAL_THEN `h = 16` SUBST1_TAC THENL [
      MP_TAC(SPEC `val(x:int32)` ROUND32_SPECIAL) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SND] THEN
    SUBGOAL_THEN `word_sub (iword(mldsa_cmod (val(x:int32)) 523776)) (word 1) : int32 =
      iword(mldsa_cmod (val x) 523776 - &1)` SUBST1_TAC THENL [
      REWRITE_TAC[GSYM IWORD_INT_SUB; WORD_IWORD]; ALL_TAC] THEN
    MATCH_MP_TAC(INST_TYPE [`:32`,`:N`] IVAL_IWORD) THEN
    REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(SPEC `val(x:int32)` CMOD_ABS_BOUND_523776) THEN INT_ARITH_TAC;
    (* Normal case: ~(val x > 8118528), h != 16 *)
    SUBGOAL_THEN `~(h = 16)` ASSUME_TAC THENL [
      DISCH_TAC THEN
      SUBGOAL_THEN `val(x:int32) <= 8118528` ASSUME_TAC THENL [
        ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(if val(x:int32) MOD 523776 * 2 <= 523776
        then val x DIV 523776 else val x DIV 523776 + 1) = 16` MP_TAC THENL [
        ASM_MESON_TAC[]; ALL_TAC] THEN
      COND_CASES_TAC THENL [
        DISCH_TAC THEN
        MP_TAC(SPECL [`val(x:int32)`; `523776`] DIVISION) THEN
        ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        STRIP_TAC THEN ASM_ARITH_TAC;
        REWRITE_TAC[ARITH_RULE `n + 1 = 16 <=> n = 15`] THEN DISCH_TAC THEN
        MP_TAC(SPECL [`val(x:int32)`; `523776`] DIVISION) THEN
        ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
        STRIP_TAC THEN ASM_ARITH_TAC]; ALL_TAC] THEN
    ASM_REWRITE_TAC[SND] THEN
    MATCH_MP_TAC(INST_TYPE [`:32`,`:N`] IVAL_IWORD) THEN
    REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(SPEC `val(x:int32)` CMOD_ABS_BOUND_523776) THEN INT_ARITH_TAC]);;

(* ========================================================================= *)
(* Specification                                                             *)
(* ========================================================================= *)

let MLDSA_DECOMPOSE_32_CORRECT = prove(
 `!pc a r1 x.
    nonoverlapping (word pc, LENGTH mldsa_decompose_32_mc)
                   (r1, 1024) /\
    nonoverlapping (word pc, LENGTH mldsa_decompose_32_mc)
                   (a, 1024) /\
    nonoverlapping (r1, 1024) (a, 1024)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) mldsa_decompose_32_mc /\
              read PC s = word(pc + MLDSA_DECOMPOSE_32_CORE_START) /\
              C_ARGUMENTS [r1; a] s /\
              (!i. i < 256
                   ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                       x i))
         (\s. read PC s = word(pc + MLDSA_DECOMPOSE_32_CORE_END) /\
              ((!i. i < 256 ==> val(x i:int32) < 8380417)
               ==> (!i. i < 256
                        ==> val(read(memory :> bytes32
                          (word_add r1 (word(4 * i)))) s) =
                            FST(mldsa_decompose_32(val(x i)))) /\
                   (!i. i < 256
                        ==> ival(read(memory :> bytes32
                          (word_add a (word(4 * i)))) s) =
                            SND(mldsa_decompose_32(val(x i))))))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(r1, 1024)] ,,
          MAYCHANGE [memory :> bytes(a, 1024)])`,

  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  MAP_EVERY X_GEN_TAC [`pc:num`; `a:int64`; `r1:int64`; `x:num->int32`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; SOME_FLAGS;
              fst MLDSA_DECOMPOSE_32_EXEC;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  STRIP_TAC THEN

  (* Expand the quantified input condition to individual coefficients *)
  CONV_TAC(RATOR_CONV(LAND_CONV(ONCE_DEPTH_CONV
    (EXPAND_CASES_CONV THENC ONCE_DEPTH_CONV NUM_MULT_CONV)))) THEN

  ENSURES_INIT_TAC "s0" THEN

  (* Merge 4x32-bit coefficient reads into 128-bit vector reads *)
  MP_TAC(end_itlist CONJ (map (fun n -> READ_MEMORY_MERGE_CONV 2
            (subst[mk_small_numeral(16*n),`n:num`]
                  `read (memory :> bytes128(word_add a (word n))) s0`))
            (0--63))) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN
  DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
  STRIP_TAC THEN

  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN

  (* Symbolic execution with folding to decompose32_a1/a0 *)
  MAP_UNTIL_TARGET_PC (fun n ->
    ARM_STEPS_TAC MLDSA_DECOMPOSE_32_EXEC [n] THEN
    RULE_ASSUM_TAC(CONV_RULE(
      TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV THENC
      ONCE_REWRITE_CONV [GSYM h32] THENC
      REWRITE_CONV [WORD_NOT_JOIN_128; WORD_NOT_JOIN_64;
                    WORD_AND_JOIN_128; WORD_AND_JOIN_64] THENC
      ONCE_REWRITE_CONV [WORD_IGT] THENC
      DEPTH_CONV WORD_IVAL_CONV THENC
      ONCE_REWRITE_CONV [GSYM decompose32_a1] THENC
      ONCE_REWRITE_CONV [GSYM decompose32_a0]))) 1 THEN

  (* Establish postcondition *)
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (* Discharge bound premise from postcondition *)
  DISCH_TAC THEN

  (* Split bytes128 results back into bytes32 *)
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
    check (can (term_match [] `read qqq s:int128 = xxx`) o concl))) THEN

  RULE_ASSUM_TAC(CONV_RULE(RAND_CONV(
    TOP_DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV))) THEN

  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[WORD_ADD_0] THEN

  (* Apply mathematical correctness lemmas *)
  REPEAT CONJ_TAC THEN
  (MATCH_MP_TAC DECOMPOSE32_A1_CORRECT ORELSE
   MATCH_MP_TAC DECOMPOSE32_A0_CORRECT) THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ========================================================================= *)
(* Subroutine form: wraps CORRECT with RET handling                          *)
(* ========================================================================= *)

let MLDSA_DECOMPOSE_32_SUBROUTINE_CORRECT = prove(
 `!pc a r1 x returnaddress.
    nonoverlapping (word pc, LENGTH mldsa_decompose_32_mc)
                   (r1, 1024) /\
    nonoverlapping (word pc, LENGTH mldsa_decompose_32_mc)
                   (a, 1024) /\
    nonoverlapping (r1, 1024) (a, 1024)
    ==> ensures arm
         (\s. aligned_bytes_loaded s (word pc) mldsa_decompose_32_mc /\
              read PC s = word pc /\
              read X30 s = returnaddress /\
              C_ARGUMENTS [r1; a] s /\
              (!i. i < 256
                   ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                       x i))
         (\s. read PC s = returnaddress /\
              ((!i. i < 256 ==> val(x i:int32) < 8380417)
               ==> (!i. i < 256
                        ==> val(read(memory :> bytes32
                          (word_add r1 (word(4 * i)))) s) =
                            FST(mldsa_decompose_32(val(x i)))) /\
                   (!i. i < 256
                        ==> ival(read(memory :> bytes32
                          (word_add a (word(4 * i)))) s) =
                            SND(mldsa_decompose_32(val(x i)))) /\
                   (!i. i < 256
                        ==> val(read(memory :> bytes32
                          (word_add r1 (word(4 * i)))) s) <= 15) /\
                   (!i. i < 256
                        ==> --(&261888) <=
                            ival(read(memory :> bytes32
                              (word_add a (word(4 * i)))) s) /\
                            ival(read(memory :> bytes32
                              (word_add a (word(4 * i)))) s) <= &261888)))
         (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(r1, 1024)] ,,
          MAYCHANGE [memory :> bytes(a, 1024)])`,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; SOME_FLAGS;
              fst MLDSA_DECOMPOSE_32_EXEC;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN
  MP_TAC(REWRITE_RULE[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; SOME_FLAGS;
    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI]
   (SPECL [`pc:num`; `a:int64`; `r1:int64`; `x:num->int32`]
    (CONV_RULE LENGTH_SIMPLIFY_CONV MLDSA_DECOMPOSE_32_CORRECT))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ARM_BIGSTEP_TAC MLDSA_DECOMPOSE_32_EXEC "s1" THEN
  ARM_STEPS_TAC MLDSA_DECOMPOSE_32_EXEC [2] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP
    (ASSUME `!i. i < 256 ==> val((x:num->int32) i) < 8380417`)) THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC MLDSA_DECOMPOSE_32_A1_BOUND THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC MLDSA_DECOMPOSE_32_A0_BOUND THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Constant-time and memory safety proof.                                    *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    ~keep_maychanges:false
    (assoc "mldsa_decompose_32" subroutine_signatures)
    MLDSA_DECOMPOSE_32_SUBROUTINE_CORRECT
    MLDSA_DECOMPOSE_32_EXEC;;

let MLDSA_DECOMPOSE_32_SUBROUTINE_SAFE = time prove
 (`exists f_events.
       forall e pc a r1 returnaddress.
           nonoverlapping (word pc,LENGTH mldsa_decompose_32_mc) (r1,1024) /\
           nonoverlapping (word pc,LENGTH mldsa_decompose_32_mc) (a,1024) /\
           nonoverlapping (r1,1024) (a,1024)
           ==> ensures arm
               (\s.
                    aligned_bytes_loaded s (word pc)
                    mldsa_decompose_32_mc /\
                    read PC s = word pc /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r1; a] s /\
                    read events s = e)
               (\s.
                    read PC s = returnaddress /\
                    (exists e2.
                         read events s = APPEND e2 e /\
                         e2 = f_events r1 a pc returnaddress /\
                         memaccess_inbounds e2 [a,1024; r1,1024]
                         [r1,1024; a,1024]))
               (\s s'. true)`,
  ASSERT_CONCL_TAC full_spec THEN
  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars MLDSA_DECOMPOSE_32_EXEC);;
