(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Rounding, compression and decompression.                                   *)
(* ========================================================================= *)

needs "common/fips203/properties/ntt_formulas.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Rounding, compression and decompression.                                  *)
(* ------------------------------------------------------------------------- *)

let MLKEM_ROUND_UNIQUE = prove
 (`!a b n. &0 < b
           ==> (mlkem_round(a,b) = n <=>
                &2 * b * n <= &2 * a + b /\ &2 * a + b < &2 * b * (n + &1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_round] THEN EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(SPECL [`&2 * a + b:int`; `&2 * b:int`] INT_DIVISION) THEN
    ASM_SIMP_TAC[INT_ARITH `&0 < b ==> ~(&2 * b:int = &0)`;
                 INT_ARITH `&0 < b ==> abs(&2 * b:int) = &2 * b`] THEN
    INT_ARITH_TAC;
    STRIP_TAC THEN MATCH_MP_TAC INT_DIV_UNIQ THEN
    EXISTS_TAC `(&2 * a + b) - &2 * b * n:int` THEN
    ASM_SIMP_TAC[INT_ARITH `&0 < b ==> abs(&2 * b:int) = &2 * b`] THEN
    ASM_INT_ARITH_TAC]);;

let MLKEM_COMPRESS_DECOMPRESS = prove
 (`!d y. d < 12 /\ &0 <= y /\ y < &2 pow d
         ==> mlkem_compress d (mlkem_decompress d y) = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_compress; mlkem_decompress] THEN
  SUBGOAL_THEN `&1:int <= &2 pow d /\ &2 pow d <= &2048:int`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `~(x = 0) ==> 1 <= x`) THEN
      REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP 11` THEN
      CONJ_TAC THENL [REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
                      CONV_TAC NUM_REDUCE_CONV]];
    ALL_TAC] THEN
  ABBREV_TAC `x = mlkem_round(&3329 * y,&2 pow d)` THEN
  MP_TAC(SPECL [`&3329 * y:int`; `(&2 pow d):int`; `x:int`]
               MLKEM_ROUND_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_INT_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `mlkem_round(&2 pow d * x,&3329) = y` SUBST1_TAC THENL
   [MP_TAC(SPECL [`&2 pow d * x:int`; `&3329:int`; `y:int`]
                 MLKEM_ROUND_UNIQUE) THEN
    REWRITE_TAC[INT_ARITH `&0:int < &3329`] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_INT_ARITH_TAC;
    MATCH_MP_TAC INT_REM_LT THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Compress and Decompress as integer divisions with a rounding offset,      *)
(* and the range of mlkem_compress d.                                        *)
(* ------------------------------------------------------------------------- *)

let RQ_ROUND_DIV = prove
 (`!a:int. (&2 * a + &3329) div (&2 * &3329) = (a + &1664) div &3329`,
  GEN_TAC THEN MATCH_MP_TAC INT_DIV_UNIQ THEN
  EXISTS_TAC `&2 * ((a:int) + &1664) rem &3329 + &1` THEN
  MP_TAC(SPECL [`(a:int) + &1664`; `&3329:int`] INT_DIVISION) THEN
  REWRITE_TAC[INT_ARITH `~(&3329:int = &0)`; INT_ABS_NUM] THEN
  CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC);;

let RQ_DIV_DOUBLE = prove
 (`!x p:int. &0 < p ==> (&2 * x) div (&2 * p) = x div p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_DIV_UNIQ THEN
  EXISTS_TAC `&2 * x rem p` THEN
  MP_TAC(SPECL [`x:int`; `p:int`] INT_DIVISION) THEN
  ASM_SIMP_TAC[INT_ARITH `&0:int < p ==> ~(p = &0)`; INT_ABS] THEN
  COND_CASES_TAC THENL [INT_ARITH_TAC; ASM_INT_ARITH_TAC]);;

let RQ_COMPRESS_ARITH = prove
 (`!d x. (&2 pow d * x + &1664) div &3329 rem &2 pow d = mlkem_compress d x`,
  REWRITE_TAC[mlkem_compress; mlkem_round; RQ_ROUND_DIV] THEN
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let RQ_DECOMPRESS_ARITH = prove
 (`!e y. (&3329 * y + &2 pow e) div &2 pow (e + 1) =
         mlkem_decompress (e + 1) y`,
  REWRITE_TAC[mlkem_decompress; mlkem_round] THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `&2 * &3329 * (y:int) + &2 pow (e + 1) =
                &2 * (&3329 * y + &2 pow e)` SUBST1_TAC THENL
   [REWRITE_TAC[INT_POW_ADD] THEN INT_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(GSYM RQ_DIV_DOUBLE) THEN MATCH_MP_TAC INT_POW_LT THEN
  INT_ARITH_TAC);;

let KPKE_COMPRESS_BOUNDS = prove
 (`!d x. &0 <= mlkem_compress d x /\ mlkem_compress d x < &2 pow d`,
  REWRITE_TAC[mlkem_compress; INT_REM_POS_EQ; INT_LT_REM_EQ; INT_POW_EQ_0;
              INT_LT_POW2] THEN
  CONV_TAC INT_REDUCE_CONV);;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
