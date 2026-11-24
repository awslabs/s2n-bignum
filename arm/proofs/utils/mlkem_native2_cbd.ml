(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The coefficients of SamplePolyCBD_eta(b) of FIPS 203 as integers, which   *)
(* mlkem_cbd2 and mlkem_cbd3 compute, for the contracts of those functions   *)
(* and the proofs of the callers (utils/mlkem_native2_noise.ml).             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "common/fips203/fips203.ml";;

(* ------------------------------------------------------------------------- *)
(* The coefficients of SamplePolyCBD_eta(b) as integers in [-eta,eta], so    *)
(* that mlkem_cbd eta b is their polynomial, and as computed by mlkem_cbd2   *)
(* and mlkem_cbd3.                                                           *)
(* ------------------------------------------------------------------------- *)

let mlkem_cbd_coeff = new_definition
 `mlkem_cbd_coeff eta (b:byte list) i =
    &(nsum {j | j < eta}
           (\j. (num_of_bytelist b DIV 2 EXP (2 * eta * i + j)) MOD 2)) -
    &(nsum {j | j < eta}
           (\j. (num_of_bytelist b DIV 2 EXP (2 * eta * i + eta + j)) MOD 2)):
    int`;;

let MLKEM_CBD_COEFF = prove
 (`!eta b. mlkem_cbd eta b = mlkem_poly(mlkem_cbd_coeff eta b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlkem_cbd] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; mlkem_cbd_coeff]);;

let NSUM_LT_2 = prove
 (`!f. nsum {j | j < 2} f = f 0 + f 1`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `2 = SUC(SUC 0)`] THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; ADD_CLAUSES; ARITH_RULE `SUC 0 = 1`]);;

let NSUM_LT_3 = prove
 (`!f. nsum {j | j < 3} f = f 0 + f 1 + f 2`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `3 = SUC(SUC(SUC 0))`] THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; ADD_CLAUSES;
              ARITH_RULE `SUC 0 = 1 /\ SUC 1 = 2`; ADD_ASSOC]);;

let MLKEM_CBD_COEFF_2 = prove
 (`!b i. mlkem_cbd_coeff 2 b i =
         &((num_of_bytelist b DIV 2 EXP (4 * i)) MOD 2 +
           (num_of_bytelist b DIV 2 EXP (4 * i + 1)) MOD 2) -
         &((num_of_bytelist b DIV 2 EXP (4 * i + 2)) MOD 2 +
           (num_of_bytelist b DIV 2 EXP (4 * i + 3)) MOD 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlkem_cbd_coeff; NSUM_LT_2] THEN
  REWRITE_TAC[ARITH_RULE
   `2 * 2 * i + 0 = 4 * i /\ 2 * 2 * i + 1 = 4 * i + 1 /\
    2 * 2 * i + 2 + 0 = 4 * i + 2 /\ 2 * 2 * i + 2 + 1 = 4 * i + 3`]);;

let MLKEM_CBD_COEFF_3 = prove
 (`!b i. mlkem_cbd_coeff 3 b i =
         &((num_of_bytelist b DIV 2 EXP (6 * i)) MOD 2 +
           (num_of_bytelist b DIV 2 EXP (6 * i + 1)) MOD 2 +
           (num_of_bytelist b DIV 2 EXP (6 * i + 2)) MOD 2) -
         &((num_of_bytelist b DIV 2 EXP (6 * i + 3)) MOD 2 +
           (num_of_bytelist b DIV 2 EXP (6 * i + 4)) MOD 2 +
           (num_of_bytelist b DIV 2 EXP (6 * i + 5)) MOD 2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlkem_cbd_coeff; NSUM_LT_3] THEN
  REWRITE_TAC[ARITH_RULE
   `2 * 3 * i + 0 = 6 * i /\ 2 * 3 * i + 1 = 6 * i + 1 /\
    2 * 3 * i + 2 = 6 * i + 2 /\ 2 * 3 * i + 3 + 0 = 6 * i + 3 /\
    2 * 3 * i + 3 + 1 = 6 * i + 4 /\ 2 * 3 * i + 3 + 2 = 6 * i + 5`]);;
