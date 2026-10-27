(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics shared by the proofs of code compiled from the C       *)
(* implementation in mlkem-native (see arm/mlkem_native/README.md).          *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(* ------------------------------------------------------------------------- *)
(* Normalization of 32-bit arithmetic in W registers.                        *)
(* ------------------------------------------------------------------------- *)

(*** Writing and then reading a W register ***)

let WORD_ZX_ZX_32_64 = prove
 (`!x:int32. word_zx(word_zx x:int64) = x`,
  SIMP_TAC[WORD_ZX_ZX; DIMINDEX_32; DIMINDEX_64; ARITH]);;

(*** Simplify the results of 32-bit arithmetic as stored by the simulator ***)

let MLKEM_NATIVE_W_SIMP_TAC =
  REWRITE_TAC[WORD_ZX_ZX_32_64; WORD_ADD; WORD_MUL; WORD_VAL];;

(*** Truncation to 16 bits as reduction of the signed value ***)

let WORD_ZX_32_16 = prove
 (`!w:int32. (word_zx w:int16) = iword(ival w)`,
  REWRITE_TAC[GSYM word_sx] THEN BITBLAST_TAC);;

(*** Eliminate ival(iword t) when t is in range, innermost terms first ***)

let IVAL_IWORD_ELIM_TAC =
  REPEAT(W(fun (asl,w) ->
     let t = hd(sort free_in
        (find_terms (can (term_match [] `ival(iword x)`)) w)) in
     let th = PART_MATCH (lhand o rand) IVAL_IWORD t in
     MP_TAC th THEN REWRITE_TAC[DIMINDEX_16; DIMINDEX_32] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     ANTS_TAC THENL [BOUNDER_TAC[]; DISCH_THEN SUBST1_TAC]));;

(* ------------------------------------------------------------------------- *)
(* The scalar Barrett reduction mlk_barrett_reduce, as compiled using a pair *)
(* of 32-bit multiply-adds, is exactly the "barred" function used for the    *)
(* vectorized code.                                                          *)
(* ------------------------------------------------------------------------- *)

let BARRED_QUOTIENT = prove
 (`!x:int. ((&2 * x * &20159) div &65536 + &1024) div &2048 =
           (&33554432 + x * &20159) div &67108864`,
  GEN_TAC THEN
  SUBGOAL_THEN `(&2 * x * &20159) div &65536 = (x * &20159) div &32768`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_ARITH `&65536:int = &2 * &32768`] THEN
    SIMP_TAC[GSYM INT_DIV_DIV; INT_POS; GSYM INT_MUL_ASSOC] THEN
    SIMP_TAC[INT_DIV_MUL; INT_OF_NUM_EQ; ARITH_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[INT_ARITH `&33554432 + x:int = x + &1024 * &32768`;
              INT_ARITH `&67108864:int = &32768 * &2048`] THEN
  SIMP_TAC[GSYM INT_DIV_DIV; INT_POS; INT_DIV_MUL_ADD;
           INT_OF_NUM_EQ; ARITH_EQ]);;

let BARRED_SCALAR = prove
 (`!x:int16.
        word_zx(word_add (word_sx x)
                  (word_mul (word_ishr (word_add (word 33554432)
                                         (word_mul (word_sx x) (word 20159)))
                                       26)
                            (word 4294963967)):int32):int16 =
        barred x`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_ZX_32_16; WORD_ADD_IMODULAR; WORD_MUL_IMODULAR;
              imodular; word_sx; IVAL_WORD_ISHR] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN IVAL_IWORD_ELIM_TAC THEN
  REWRITE_TAC[barred; iword_saturate; word_INT_MIN; word_INT_MAX;
              DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REPEAT(COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[] `p ==> ~p ==> q`)) THEN
    REWRITE_TAC[INT_GT; INT_NOT_LT] THEN BOUNDER_TAC[];
    ASM_REWRITE_TAC[]]) THEN
  REWRITE_TAC[WORD_RULE
   `word_sub a (word_mul b (word n)) = iword(ival a - ival b * &n)`] THEN
  IVAL_IWORD_ELIM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[BARRED_QUOTIENT] THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Adding 3329 to a negative result of "barred" gives the remainder.         *)
(* ------------------------------------------------------------------------- *)

let BARRED_CONDADD_REM = prove
 (`!x:int16.
        ival(word_add (barred x)
                      (word_and (word_ishr (barred x) 15) (word 3329))) =
        ival x rem &3329`,
  let lemma = prove
   (`(y == x) (mod &3329) /\
     --(&1664) <= y /\ y <= &1664
     ==> x rem &3329 = if y < &0 then y + &3329 else y`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[INT_REM_UNIQUE] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN
    UNDISCH_TAC `(y:int == x) (mod &3329)` THEN
    SPEC_TAC(`&3329:int`,`p:int`) THEN CONV_TAC INTEGER_RULE) in
  REWRITE_TAC[MATCH_MP lemma (CONGBOUND_RULE `barred x`)] THEN
  BITBLAST_TAC);;
