(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Common specifications and tactics for ML-KEM, mainly related to the NTT.  *)
(* ========================================================================= *)

needs "Library/words.ml";;
needs "Library/isum.ml";;

(* ------------------------------------------------------------------------- *)
(* The pure forms of forward and inverse NTT with no reordering.             *)
(* ------------------------------------------------------------------------- *)

let pure_forward_ntt = define
 `pure_forward_ntt f k =
    isum (0..127) (\j. f(2 * j + k MOD 2) *
                       &17 pow ((2 * k DIV 2 + 1) * j))
    rem &3329`;;

let pure_inverse_ntt = define
 `pure_inverse_ntt f k =
    (&3303 * isum (0..127) (\j. f(2 * j + k MOD 2) *
                                &1175 pow ((2 * j + 1) * k DIV 2)))
    rem &3329`;;

let pure_forward_ntt_mldsa = define
 `pure_forward_ntt_mldsa f k =
    isum (0..127) (\j. f(2 * j + k MOD 2) *
                       &1753 pow ((2 * k DIV 2 + 1) * j))
    rem &8380417`;;

let pure_inverse_ntt_mldsa = define
 `pure_inverse_ntt_mldsa f k =
    (&8347681 * isum (0..127) (\j. f(2 * j + k MOD 2) *
                                &8347681 pow ((2 * j + 1) * k DIV 2)))
    rem &8380417`;;

(* ------------------------------------------------------------------------- *)
(* Bit-reversing order as used in the standard/default order.                *)
(* ------------------------------------------------------------------------- *)

let bitreverse7 = define
 `bitreverse7(n) = val(word_reversefields 1 (word n:7 word))`;;

let bitreverse8 = define
 `bitreverse8(n) = val(word_reversefields 1 (word n:8 word))`;;

let bitreverse_pairs = define
 `bitreverse_pairs i = 2 * bitreverse7 (i DIV 2) + i MOD 2`;;

let reorder = define
 `reorder p (a:num->int) = \i. a(p i)`;;

let avx2_ntt_order = define
 `avx2_ntt_order i =
    bitreverse7(64 * (i DIV 64) + ((i MOD 64) DIV 16) + 4 * (i MOD 16))`;;

let avx2_ntt_order' = define
 `avx2_ntt_order' i =
    let j = bitreverse7 i in
    (64 * (j DIV 64) + 16 * (j MOD 4) + (j MOD 64) DIV 4)`;;

let avx2_reorder = define
 `avx2_reorder i =
    let r = (i DIV 16) MOD 2
    and q = 16 * (i DIV 32) + i MOD 16 in
    2 * avx2_ntt_order q + r`;;

let avx2_reorder' = define
 `avx2_reorder' i =
    let r = i MOD 2
    and q = avx2_ntt_order'(i DIV 2) in
    (q DIV 16) * 32 + r * 16 + q MOD 16`;;

(* ------------------------------------------------------------------------- *)
(* The simpler ones as used on ARM are actually involutions.                 *)
(* ------------------------------------------------------------------------- *)

let BITREVERSE7_INVOLUTION = prove
 (`!n. n < 128 ==> bitreverse7(bitreverse7 n) = n`,
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC[bitreverse7] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

let BITREVERSE_PAIRS_INVOLUTION = prove
 (`!n. n < 256 ==> bitreverse_pairs(bitreverse_pairs n) = n`,
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[bitreverse_pairs; bitreverse7] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

let AVX2_NTT_ORDER_INVOLUTION = prove
 (`!n. n < 128 ==> avx2_ntt_order'(avx2_ntt_order n) = n /\
                   avx2_ntt_order(avx2_ntt_order' n) = n`,
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[avx2_ntt_order; avx2_ntt_order'; bitreverse7] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

let AVX2_REORDER_INVOLUTION = prove
 (`!n. n < 256 ==> avx2_reorder'(avx2_reorder n) = n /\
                   avx2_reorder(avx2_reorder' n) = n`,
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[avx2_reorder; avx2_reorder';
              avx2_ntt_order; avx2_ntt_order'; bitreverse7] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

(* ------------------------------------------------------------------------- *)
(* AVX2-optimized ordering for ML-DSA NTT (swaps bit fields then reverses)   *)
(* ------------------------------------------------------------------------- *)

let bitmap = define
 `bitmap [] n = 0 /\
  bitmap (CONS i t) n = bitval(numbit i n) + 2 * bitmap t n`;;

let mldsa_avx2_ntt_order = define
 `mldsa_avx2_ntt_order i =
    bitreverse8(64 * (i DIV 64) + ((i MOD 64) DIV 8) + 8 * (i MOD 8))`;;

let BITMAP_MLDSA_AVX2_NTT_ORDER = prove
 (`!n. n < 256 ==> bitmap [7;6;2;1;0;5;4;3] n = mldsa_avx2_ntt_order n`,
  REWRITE_TAC[bitmap; numbit; mldsa_avx2_ntt_order; bitreverse8; bitval] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

let mldsa_avx2_ntt_order' = define
 `mldsa_avx2_ntt_order' = bitmap [4;3;2;7;6;5;1;0]`;;

let MLDSA_AVX2_NTT_ORDER_INVOLUTION = prove
 (`!n. n < 256 ==> mldsa_avx2_ntt_order'(mldsa_avx2_ntt_order n) = n /\
                   mldsa_avx2_ntt_order(mldsa_avx2_ntt_order' n) = n`,
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[mldsa_avx2_ntt_order; mldsa_avx2_ntt_order'] THEN
  REWRITE_TAC[bitreverse8; bitmap; bitval; numbit] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV));;

(* ------------------------------------------------------------------------- *)
(* Conversion of each element of an array to Montgomery form with B = 2^16.  *)
(* ------------------------------------------------------------------------- *)

let tomont_3329 = define
 `tomont_3329 (a:num->int) = \i. (&2 pow 16 * a i) rem &3329`;;

let tomont_8380417 = define
 `tomont_8380417 (a:num->int) = \i. (&2 pow 32 * a i) rem &8380417`;;

(* ------------------------------------------------------------------------- *)
(* The multiplication cache for fast base multiplication                     *)
(* ------------------------------------------------------------------------- *)

let mulcache = define
 `mulcache f k =
   (f (2 * k + 1) * (&17 pow (2 * (bitreverse7 k) + 1))) rem &3329`;;

(* ------------------------------------------------------------------------- *)
(* The precise specs of the actual ARM code.                                 *)
(* ------------------------------------------------------------------------- *)

let inverse_ntt = define
 `inverse_ntt f k =
    (&512 * isum (0..127)
                 (\j. f(2 * bitreverse7 j + k MOD 2) *
                       &1175 pow ((2 * j + 1) * k DIV 2)))
    rem &3329`;;

let forward_ntt = define
 `forward_ntt f k =
    isum (0..127) (\j. f(2 * j + k MOD 2) *
                       &17 pow ((2 * bitreverse7 (k DIV 2) + 1) * j))
    rem &3329`;;

(* ------------------------------------------------------------------------- *)
(* The precise specs of the actual x86 code.                                 *)
(* Both inverse NTTs also map to Montgomery form, hence 2^B / N multiplier.  *)
(* ------------------------------------------------------------------------- *)

let avx2_forward_ntt = define
 `avx2_forward_ntt f k =
    let r = (k DIV 16) MOD 2
    and q = 16 * (k DIV 32) + k MOD 16 in
    isum (0..127) (\j. f(2 * j + r) *
                       &17 pow ((2 * avx2_ntt_order q + 1) * j))
    rem &3329`;;

let avx2_inverse_ntt = define
 `avx2_inverse_ntt f k =
    (&512 * isum (0..127)
                 (\j. f(avx2_ntt_order' j DIV 16 * 32 +
                        k MOD 2 * 16 +
                        avx2_ntt_order' j MOD 16) *
                      &1175 pow ((2 * j + 1) * k DIV 2)))
    rem &3329`;;

let mldsa_forward_ntt = define
 `mldsa_forward_ntt f k =
    isum (0..255) (\j. f j * &1753 pow ((2 * mldsa_avx2_ntt_order k + 1) * j))
    rem &8380417`;;

let mldsa_inverse_ntt = define
 `mldsa_inverse_ntt f k =
    (&2 pow 24 * isum (0..255)
                 (\j. f(mldsa_avx2_ntt_order' j) *
                      &731434 pow ((2 * j + 1) * k)))
    rem &8380417`;;

(* ------------------------------------------------------------------------- *)
(* Show how these relate to the "pure" ones.                                 *)
(* ------------------------------------------------------------------------- *)

let FORWARD_NTT = prove
 (`forward_ntt = reorder bitreverse_pairs o pure_forward_ntt`,
  REWRITE_TAC[FUN_EQ_THM; o_DEF; bitreverse_pairs; reorder] THEN
  REWRITE_TAC[forward_ntt; pure_forward_ntt] THEN
  REWRITE_TAC[ARITH_RULE `(2 * x + i MOD 2) DIV 2 = x`] THEN
  REWRITE_TAC[MOD_MULT_ADD; MOD_MOD_REFL]);;


let arm_mldsa_pure_forward_ntt = define
 `arm_mldsa_pure_forward_ntt f k =
    isum (0..255) (\j. f j * &1753 pow ((2 * k + 1) * j))
    rem &8380417`;;

let arm_mldsa_forward_ntt = define
 `arm_mldsa_forward_ntt f k =
    isum (0..255) (\j. f j * &1753 pow ((2 * bitreverse8 k + 1) * j))
    rem &8380417`;;

let ARM_MLDSA_FORWARD_NTT = prove
 (`arm_mldsa_forward_ntt = reorder bitreverse8 o arm_mldsa_pure_forward_ntt`,
  REWRITE_TAC[FUN_EQ_THM; o_DEF; reorder] THEN
  REWRITE_TAC[arm_mldsa_forward_ntt; arm_mldsa_pure_forward_ntt]);;

let INVERSE_NTT = prove
 (`inverse_ntt = tomont_3329 o pure_inverse_ntt o reorder bitreverse_pairs`,
  REWRITE_TAC[FUN_EQ_THM; o_DEF; bitreverse_pairs; reorder] THEN
  REWRITE_TAC[inverse_ntt; pure_inverse_ntt; tomont_3329] THEN
  REWRITE_TAC[ARITH_RULE `(2 * x + i MOD 2) DIV 2 = x`] THEN
  REWRITE_TAC[MOD_MULT_ADD; MOD_MOD_REFL] THEN
  MAP_EVERY X_GEN_TAC [`a:num->int`; `i:num`] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN CONV_TAC INT_REDUCE_CONV);;

let AVX2_FORWARD_NTT = prove
 (`avx2_forward_ntt = reorder avx2_reorder o pure_forward_ntt`,
  REWRITE_TAC[FUN_EQ_THM; o_DEF; avx2_reorder; reorder] THEN
  REWRITE_TAC[avx2_forward_ntt; pure_forward_ntt] THEN
  MAP_EVERY X_GEN_TAC [`x:num->int`; `k:num`] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ; MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `x MOD 2 DIV 2 = 0`; ADD_CLAUSES]);;

let AVX2_INVERSE_NTT = prove
 (`avx2_inverse_ntt = tomont_3329 o pure_inverse_ntt o reorder avx2_reorder'`,
  REWRITE_TAC[FUN_EQ_THM; o_DEF; avx2_reorder'; reorder] THEN
  REWRITE_TAC[avx2_inverse_ntt; pure_inverse_ntt; tomont_3329] THEN
  REWRITE_TAC[ARITH_RULE `(2 * x + i MOD 2) DIV 2 = x`] THEN
  REWRITE_TAC[MOD_MULT_ADD; MOD_MOD_REFL] THEN
  MAP_EVERY X_GEN_TAC [`x:num->int`; `k:num`] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN CONV_TAC INT_REDUCE_CONV);;

let MLDSA_FORWARD_NTT = prove
 (`mldsa_forward_ntt f k =
   isum (0..255) (\j. f j * &1753 pow ((2 * mldsa_avx2_ntt_order k + 1) * j)) rem &8380417`,
  REWRITE_TAC[mldsa_forward_ntt]);;

(* ------------------------------------------------------------------------- *)
(* Explicit computation rules to evaluate mod-3329 powers/sums less naively. *)
(* ------------------------------------------------------------------------- *)

let BITREVERSE7_CLAUSES = end_itlist CONJ (map
 (GEN_REWRITE_CONV I [bitreverse7] THENC DEPTH_CONV WORD_NUM_RED_CONV)
 (map (curry mk_comb `bitreverse7` o mk_small_numeral) (0--127)));;

let FORWARD_NTT_ALT = prove
 (`forward_ntt f k =
   isum (0..127)
        (\j. f(2 * j + k MOD 2) *
             (&17 pow ((2 * bitreverse7 (k DIV 2) + 1) * j)) rem &3329)
    rem &3329`,
  REWRITE_TAC[forward_ntt] THEN MATCH_MP_TAC
   (REWRITE_RULE[] (ISPEC
      `(\x y. x rem &3329 = y rem &3329)` ISUM_RELATED)) THEN
  REWRITE_TAC[INT_REM_EQ; FINITE_NUMSEG; INT_CONG_ADD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES;
              GSYM INT_REM_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC INT_ARITH);;

let ARM_MLDSA_FORWARD_NTT_ALT = prove
 (`arm_mldsa_forward_ntt f k =
   isum (0..255)
        (\j. f j *
             (&1753 pow ((2 * bitreverse8 k + 1) * j)) rem &8380417)
    rem &8380417`,
  REWRITE_TAC[arm_mldsa_forward_ntt] THEN MATCH_MP_TAC
   (REWRITE_RULE[] (ISPEC
      `(\x y. x rem &8380417 = y rem &8380417)` ISUM_RELATED)) THEN
  REWRITE_TAC[INT_REM_EQ; FINITE_NUMSEG; INT_CONG_ADD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES;
              GSYM INT_REM_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC INT_ARITH);;

let AVX2_FORWARD_NTT_ALT = prove
 (`avx2_forward_ntt f k =
   let r = (k DIV 16) MOD 2
   and q = 16 * (k DIV 32) + k MOD 16 in
   isum (0..127)
        (\j. f(2 * j + r) *
             (&17 pow ((2 * avx2_ntt_order q + 1) * j)) rem &3329)
    rem &3329`,
  REWRITE_TAC[avx2_forward_ntt] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN MATCH_MP_TAC
   (REWRITE_RULE[] (ISPEC
      `(\x y. x rem &3329 = y rem &3329)` ISUM_RELATED)) THEN
  REWRITE_TAC[INT_REM_EQ; FINITE_NUMSEG; INT_CONG_ADD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES;
              GSYM INT_REM_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC INT_ARITH);;

let INVERSE_NTT_ALT = prove
 (`inverse_ntt f k =
    isum (0..127)
      (\j. f(2 * bitreverse7 j + k MOD 2) *
           (&512 *
            (&1175 pow ((2 * j + 1) * k DIV 2)) rem &3329)
           rem &3329) rem &3329`,
  REWRITE_TAC[inverse_ntt; GSYM ISUM_LMUL] THEN MATCH_MP_TAC
   (REWRITE_RULE[] (ISPEC
      `(\x y. x rem &3329 = y rem &3329)` ISUM_RELATED)) THEN
  REWRITE_TAC[INT_REM_EQ; FINITE_NUMSEG; INT_CONG_ADD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES;
              GSYM INT_REM_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC INT_ARITH);;

let AVX2_INVERSE_NTT_ALT = prove
 (`avx2_inverse_ntt f k =
    isum (0..127)
      (\j. f(avx2_ntt_order' j DIV 16 * 32 +
             k MOD 2 * 16 +
             avx2_ntt_order' j MOD 16) *
           (&512 *
            (&1175 pow ((2 * j + 1) * k DIV 2)) rem &3329)
           rem &3329) rem &3329`,
  REWRITE_TAC[avx2_inverse_ntt; GSYM ISUM_LMUL] THEN
  MATCH_MP_TAC (REWRITE_RULE[] (ISPEC
      `(\x y. x rem &3329 = y rem &3329)` ISUM_RELATED)) THEN
  REWRITE_TAC[INT_REM_EQ; FINITE_NUMSEG; INT_CONG_ADD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES;
              GSYM INT_REM_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC INT_ARITH);;

let FORWARD_NTT_CONV =
  GEN_REWRITE_CONV I [FORWARD_NTT_ALT] THENC
  LAND_CONV EXPAND_ISUM_CONV THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [BITREVERSE7_CLAUSES] THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV DEPTH_CONV [INT_OF_NUM_POW; INT_OF_NUM_REM] THENC
  ONCE_DEPTH_CONV EXP_MOD_CONV THENC INT_REDUCE_CONV;;

let AVX2_NTT_ORDER_CLAUSES = end_itlist CONJ (map
 (GEN_REWRITE_CONV I [avx2_ntt_order] THENC DEPTH_CONV WORD_NUM_RED_CONV THENC
  GEN_REWRITE_CONV I [BITREVERSE7_CLAUSES])
 (map (curry mk_comb `avx2_ntt_order` o mk_small_numeral) (0--127)));;

let AVX2_NTT_ORDER_CLAUSES' = end_itlist CONJ (map
 (GEN_REWRITE_CONV I [avx2_ntt_order'] THENC DEPTH_CONV WORD_NUM_RED_CONV THENC
 DEPTH_CONV let_CONV THENC
 GEN_REWRITE_CONV ONCE_DEPTH_CONV [BITREVERSE7_CLAUSES] THENC NUM_REDUCE_CONV)
 (map (curry mk_comb `avx2_ntt_order'` o mk_small_numeral) (0--127)));;

let AVX2_FORWARD_NTT_CONV =
  GEN_REWRITE_CONV I [AVX2_FORWARD_NTT_ALT] THENC
  NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV let_CONV THENC
  LAND_CONV EXPAND_ISUM_CONV THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [AVX2_NTT_ORDER_CLAUSES] THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV DEPTH_CONV [INT_OF_NUM_POW; INT_OF_NUM_REM] THENC
  ONCE_DEPTH_CONV EXP_MOD_CONV THENC INT_REDUCE_CONV;;

let INVERSE_NTT_CONV =
  GEN_REWRITE_CONV I [INVERSE_NTT_ALT] THENC
  LAND_CONV EXPAND_ISUM_CONV THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [BITREVERSE7_CLAUSES] THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV DEPTH_CONV [INT_OF_NUM_POW; INT_OF_NUM_REM] THENC
  ONCE_DEPTH_CONV EXP_MOD_CONV THENC INT_REDUCE_CONV;;

let AVX2_INVERSE_NTT_CONV =
  GEN_REWRITE_CONV I [AVX2_INVERSE_NTT_ALT] THENC
  NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV let_CONV THENC
  LAND_CONV EXPAND_ISUM_CONV THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [AVX2_NTT_ORDER_CLAUSES'] THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV DEPTH_CONV [INT_OF_NUM_POW; INT_OF_NUM_REM] THENC
  ONCE_DEPTH_CONV EXP_MOD_CONV THENC INT_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* Explicit computation rules to evaluate mod-8380417 powers less naively.   *)
(* ------------------------------------------------------------------------- *)

let BITREVERSE8_CLAUSES = end_itlist CONJ (map
 (GEN_REWRITE_CONV I [bitreverse8] THENC DEPTH_CONV WORD_NUM_RED_CONV)
 (map (curry mk_comb `bitreverse8` o mk_small_numeral) (0--255)));;

let MLDSA_AVX2_NTT_ORDER_CLAUSES = end_itlist CONJ (map
 (GEN_REWRITE_CONV I [mldsa_avx2_ntt_order] THENC
  DEPTH_CONV WORD_NUM_RED_CONV THENC
  GEN_REWRITE_CONV I [BITREVERSE8_CLAUSES])
 (map (curry mk_comb `mldsa_avx2_ntt_order` o mk_small_numeral) (0--255)));;

let MLDSA_AVX2_NTT_ORDER_CLAUSES' = end_itlist CONJ (map
 (GEN_REWRITE_CONV RATOR_CONV [mldsa_avx2_ntt_order'] THENC
  GEN_REWRITE_CONV TOP_DEPTH_CONV [bitval; numbit; bitmap] THENC
  DEPTH_CONV WORD_NUM_RED_CONV)
 (map (curry mk_comb `mldsa_avx2_ntt_order'` o mk_small_numeral) (0--255)));;

let MLDSA_FORWARD_NTT_ALT = prove
 (`mldsa_forward_ntt f k =
   isum (0..255)
        (\j. f j *
             (&1753 pow ((2 * mldsa_avx2_ntt_order k + 1) * j)) rem &8380417)
    rem &8380417`,
  REWRITE_TAC[mldsa_forward_ntt] THEN MATCH_MP_TAC
   (REWRITE_RULE[] (ISPEC
      `(\x y. x rem &8380417 = y rem &8380417)` ISUM_RELATED)) THEN
  REWRITE_TAC[INT_REM_EQ; FINITE_NUMSEG; INT_CONG_ADD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES;
              GSYM INT_REM_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC INT_ARITH);;

let MLDSA_FORWARD_NTT_CONV =
  GEN_REWRITE_CONV I [MLDSA_FORWARD_NTT_ALT] THENC
  LAND_CONV EXPAND_ISUM_CONV THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [MLDSA_AVX2_NTT_ORDER_CLAUSES] THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV DEPTH_CONV [INT_OF_NUM_POW; INT_OF_NUM_REM] THENC
  ONCE_DEPTH_CONV EXP_MOD_CONV THENC INT_REDUCE_CONV;;


let ARM_MLDSA_FORWARD_NTT_CONV =
  GEN_REWRITE_CONV I [ARM_MLDSA_FORWARD_NTT_ALT] THENC
  LAND_CONV EXPAND_ISUM_CONV THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [BITREVERSE8_CLAUSES] THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV DEPTH_CONV [INT_OF_NUM_POW; INT_OF_NUM_REM] THENC
  ONCE_DEPTH_CONV EXP_MOD_CONV THENC INT_REDUCE_CONV;;

let arm_mldsa_inverse_ntt = define
 `arm_mldsa_inverse_ntt f k =
    (&2 pow 24 * isum (0..255)
                 (\j. f(bitreverse8 j) *
                      &731434 pow ((2 * j + 1) * k)))
    rem &8380417`;;

let ARM_MLDSA_INVERSE_NTT_ALT = prove
 (`arm_mldsa_inverse_ntt f k =
    isum (0..255)
         (\j. f(bitreverse8 j) *
              (&16777216 * (&731434 pow ((2 * j + 1) * k)) rem &8380417)
              rem &8380417)
    rem &8380417`,
  REWRITE_TAC[arm_mldsa_inverse_ntt; GSYM ISUM_LMUL] THEN
  MATCH_MP_TAC (REWRITE_RULE[] (ISPEC
      `(\x y. x rem &8380417 = y rem &8380417)` ISUM_RELATED)) THEN
  REWRITE_TAC[INT_REM_EQ; FINITE_NUMSEG; INT_CONG_ADD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES;
              GSYM INT_REM_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC INT_ARITH);;

let ARM_MLDSA_INVERSE_NTT_CONV =
  GEN_REWRITE_CONV I [ARM_MLDSA_INVERSE_NTT_ALT] THENC
  LAND_CONV EXPAND_ISUM_CONV THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [BITREVERSE8_CLAUSES] THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV DEPTH_CONV [INT_OF_NUM_POW; INT_OF_NUM_REM] THENC
  ONCE_DEPTH_CONV EXP_MOD_CONV THENC INT_REDUCE_CONV;;

let MLDSA_INVERSE_NTT_ALT = prove
 (`mldsa_inverse_ntt f k =
    isum (0..255)
         (\j. f(mldsa_avx2_ntt_order' j) *
              (&16777216 * (&731434 pow ((2 * j + 1) * k)) rem &8380417)
              rem &8380417)
    rem &8380417`,
  REWRITE_TAC[mldsa_inverse_ntt; GSYM ISUM_LMUL] THEN
  MATCH_MP_TAC (REWRITE_RULE[] (ISPEC
      `(\x y. x rem &8380417 = y rem &8380417)` ISUM_RELATED)) THEN
  REWRITE_TAC[INT_REM_EQ; FINITE_NUMSEG; INT_CONG_ADD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES;
              GSYM INT_REM_EQ] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC INT_ARITH);;

let MLDSA_INVERSE_NTT_CONV =
  GEN_REWRITE_CONV I [MLDSA_INVERSE_NTT_ALT] THENC
  LAND_CONV EXPAND_ISUM_CONV THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [MLDSA_AVX2_NTT_ORDER_CLAUSES'] THENC
  DEPTH_CONV NUM_RED_CONV THENC
  GEN_REWRITE_CONV DEPTH_CONV [INT_OF_NUM_POW; INT_OF_NUM_REM] THENC
  ONCE_DEPTH_CONV EXP_MOD_CONV THENC INT_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* Abbreviate the Barrett reduction and multiplication and Montgomery        *)
(* reduction patterns in the code.                                           *)
(* ------------------------------------------------------------------------- *)

let barred = define
 `(barred:int16->int16) x =
  word_sub x
   (word_mul
    (iword
    ((ival
      (iword_saturate((&2 * ival x * &20159) div &65536):int16) + &1024) div
     &2048))
   (word 3329))`;;

let barred_x86 = define
 `(barred_x86:int16->int16) x =
  word_sub
   (x)
   (word_mul
     (word_ishr
       (word_subword
         (word_mul ((word_sx x):int32) (word 20159))
         (16,16))
       (10))
     (word 3329))`;;

let barmul = define
 `barmul (k,b) (a:int16):int16 =
  word_sub (word_mul a b)
           (word_mul (iword_saturate((&2 * ival a * k + &32768) div &65536))
                     (word 3329))`;;

let arm_mldsa_barmul = define
 `arm_mldsa_barmul (k,b) (a:int32):int32 =
  word_sub (word_mul a b)
           (word_mul (iword_saturate((&2 * ival a * k + &2147483648) div &4294967296))
                     (word 8380417))`;;

let montred = define
   `(montred:int32->int16) x =
    word_subword
     (word_add
       (word_mul ((word_sx:int16->int32)
                    (word_mul (word_subword x (0,16)) (word 3327)))
                 (word 3329))
       x)
     (16,16)`;;

(* ------------------------------------------------------------------------- *)
(* For the x86 version of ML-KEM                                             *)
(* ------------------------------------------------------------------------- *)

let montmul_x86 = define
  `montmul_x86 (x : int16) (y :int16) =
   word_sub
     (word_subword (word_mul (word_sx y : int32) (word_sx x)) (16,16) : int16)
     (word_subword
        (word_mul (word 3329) (word_sx (word_mul y (word_mul (word 62209) x)) : int32))
        (16,16))
  `;;

let montmul_odd_x86 = prove
 (`word_neg(montmul_x86 x y) =
   word_sub
     (word_subword
        (word_mul (word 3329) (word_sx (word_mul y (word_mul (word 62209) x)) : int32))
        (16,16))
     (word_subword (word_mul (word_sx y : int32) (word_sx x)) (16,16) : int16)`,
  REWRITE_TAC[montmul_x86] THEN CONV_TAC WORD_RULE);;

let ntt_montmul = define
 `ntt_montmul (a:int32, b:int16) (x:int16) =
  word_sub
  (word_subword (word_mul (word_sx (x:int16)) a:int32) (16,16):int16)
  (word_subword
    (word_mul (word_sx
      ((word_mul (x:int16) b:int16)))
      (word 3329:int32))
    (16,16))`;;

let ntt_montmul_alt = prove
(`ntt_montmul (a:int32, b:int16) (x:int16) =
  word_sub
  (word_subword (word_mul a (word_sx (x:int16)):int32) (16,16):int16)
  (word_subword
    (word_mul
      (word 3329:int32)
      (word_sx ((word_mul b (x:int16):int16))))
    (16,16))`,
  REWRITE_TAC[ntt_montmul; WORD_MUL_SYM]);;


let ntt_montmul_add = prove
 (`word_add y (ntt_montmul (a, b) x) =
   word_sub
   (word_add
       (y)
       (word_subword (word_mul (word_sx (x:int16)) a:int32) (16,16):int16))
   (word_subword
     (word_mul (word_sx
       ((word_mul (x:int16) b:int16)))
       (word 3329:int32))
     (16,16))`,
  REWRITE_TAC[ntt_montmul] THEN CONV_TAC WORD_RULE);;

let ntt_montmul_sub = prove
 (`word_sub y (ntt_montmul (a, b) x) =
   word_add
   (word_sub
       (y)
       (word_subword (word_mul (word_sx (x:int16)) a:int32) (16,16):int16))
   (word_subword
     (word_mul (word_sx
       ((word_mul (x:int16) b:int16)))
       (word 3329:int32))
     (16,16))`,
  REWRITE_TAC[ntt_montmul] THEN CONV_TAC WORD_RULE);;


(* ------------------------------------------------------------------------- *)
(* Constants table: qinv (for Montgomery reduction) and Q (modulus)          *)
(* Both broadcasted 8 times for SIMD processing                              *)
(* ------------------------------------------------------------------------- *)

let mldsa_pointwise_consts = define
 `mldsa_pointwise_consts:int list =
   [&58728449; &58728449; &58728449; &58728449;
    &58728449; &58728449; &58728449; &58728449;
    &8380417; &8380417; &8380417; &8380417;
    &8380417; &8380417; &8380417; &8380417]`;;

let mldsa_pointwise_acc_consts = define
 `mldsa_pointwise_acc_consts:int list =
   [&8380417; &8380417; &8380417; &8380417;
    &8380417; &8380417; &8380417; &8380417;
    &58728449; &58728449; &58728449; &58728449;
    &58728449; &58728449; &58728449; &58728449]`;;



(* ------------------------------------------------------------------------- *)
(* Analogous ML-DSA idioms.                                                  *)
(* ------------------------------------------------------------------------- *)

let mldsa_barred = define
 `(mldsa_barred:int32->int32) x =
  word_sub x
   (word_mul
    (word_ishr (word_add x (word 4194304)) 23)
    (word 8380417))`;;

let mldsa_montred = define
   `(mldsa_montred:int64->int32) x =
    word_subword
     (word_add
       (word_mul ((word_sx:int32->int64)
                    (word_mul (word_subword x (0,32)) (word 4236238847)))
                 (word 8380417))
       x)
     (32,32)`;;

let mldsa_montmul = define
 `mldsa_montmul (a:int64,b:int64) (x:int32) =
  word_sub
  (word_subword (word_mul (word_sx (x:int32)) a:int64) (32,32):int32)
  (word_subword
    (word_mul (word_sx
      (word_subword (word_mul (word_sx (x:int32)) b:int64) (0,32):int32))
      (word 8380417:int64))
    (32,32))`;;

let mldsa_pointwise = define
 `mldsa_pointwise (f:num->int) (g:num->int) i =
    (f i * g i * &(inverse_mod 8380417 4294967296)) rem &8380417`;;

let mldsa_pointwise_montred = define
 `mldsa_pointwise_montred (x:int64) =
    word_subword
      (word_sub x
        (word_mul
          (word_sx (word_subword
            (word_mul (word 58728449:int64)
                      (word_sx (word_subword x (0,32):int32):int64))
            (0,32):int32):int64)
          (word 8380417:int64)))
      (32,32) : int32`;;

let arm_mldsa_pointwise_montred = define
 `arm_mldsa_pointwise_montred (x:int64) =
    word_subword
      (word_sub x
        (word_mul
          (word_sx (word_mul (word_subword x (0,32):int32)
                             (word 58728449:int32)):int64)
          (word_sx (word 8380417:int32):int64)))
      (32,32) : int32`;;

let arm_mldsa_pointwise_montred' =
  CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV WORD_REDUCE_CONV))
    arm_mldsa_pointwise_montred;;

(* Key equivalence: ARM montred = x86 montred.
   Uses WORD_ZX_MUL to show low-32 of 64-bit product = 32-bit product. *)
let ARM_MLDSA_MONTRED_EQ = prove(
 `!x:int64. arm_mldsa_pointwise_montred x = mldsa_pointwise_montred x`,
  GEN_TAC THEN
  REWRITE_TAC[arm_mldsa_pointwise_montred; mldsa_pointwise_montred] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[WORD_BLAST `word_subword (x:int64) (0,32):int32 = word_zx x`] THEN
  SIMP_TAC[WORD_ZX_MUL; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  REWRITE_TAC[WORD_BLAST `word_zx(word_sx (a:int32):int64):int32 = a`] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[WORD_MUL_SYM]);;

let mldsa_pointwise_acc_l4 = define
 `mldsa_pointwise_acc_l4 (f:num->int) (g:num->int) i =
    ((f i * g i +
      f (i + 256) * g (i + 256) +
      f (i + 512) * g (i + 512) +
      f (i + 768) * g (i + 768)) *
     &(inverse_mod 8380417 4294967296)) rem &8380417`;;

let mldsa_pointwise_acc_l5 = define
 `mldsa_pointwise_acc_l5 (f:num->int) (g:num->int) i =
    ((f i * g i +
      f (i + 256) * g (i + 256) +
      f (i + 512) * g (i + 512) +
      f (i + 768) * g (i + 768) +
      f (i + 1024) * g (i + 1024)) *
     &(inverse_mod 8380417 4294967296)) rem &8380417`;;

let mldsa_pointwise_acc_l7 = define
 `mldsa_pointwise_acc_l7 (f:num->int) (g:num->int) i =
    ((f i * g i +
      f (i + 256) * g (i + 256) +
      f (i + 512) * g (i + 512) +
      f (i + 768) * g (i + 768) +
      f (i + 1024) * g (i + 1024) +
      f (i + 1280) * g (i + 1280) +
      f (i + 1536) * g (i + 1536)) *
     &(inverse_mod 8380417 4294967296)) rem &8380417`;;

let WORD_ADD_MLDSA_MONTMUL = prove
 (`word_add y (mldsa_montmul (a,b) x) =
   word_sub (word_add
    (word_subword (word_mul (word_sx (x:int32)) a:int64) (32,32):int32)
    y)
  (word_subword
    (word_mul (word_sx
      (word_subword (word_mul (word_sx (x:int32)) b:int64) (0,32):int32))
      (word 8380417:int64))
    (32,32))`,
  REWRITE_TAC[mldsa_montmul] THEN CONV_TAC WORD_RULE);;

let WORD_SUB_MLDSA_MONTMUL = prove
 (`word_sub y (mldsa_montmul (a,b) x) =
  word_add (word_sub y
        (word_subword (word_mul (word_sx (x:int32)) a:int64) (32,32):int32))
    (word_subword
    (word_mul (word_sx
      (word_subword (word_mul (word_sx (x:int32)) b:int64) (0,32):int32))
      (word 8380417:int64))
    (32,32))`,
  REWRITE_TAC[mldsa_montmul] THEN CONV_TAC WORD_RULE);;

let WORD_ADD_MLDSA_MONTMUL_ALT = prove
 (`word_add y (mldsa_montmul (a,b) x) =
   word_sub (word_add y
    (word_subword (word_mul (word_sx (x:int32)) a:int64) (32,32):int32))
  (word_subword
    (word_mul (word_sx
      (word_subword (word_mul (word_sx (x:int32)) b:int64) (0,32):int32))
      (word 8380417:int64))
    (32,32))`,
  REWRITE_TAC[mldsa_montmul] THEN CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* Auxiliary lemmas for ML-DSA multiplication                                *)
(* ------------------------------------------------------------------------- *)

(* ival of sign-extended product equals integer product when bounded by Q-1 *)
let IVAL_WORD_MUL_SX32_64 = prove(
 `!x:int32 y:int32.
    abs(ival x) <= &75423752 /\ abs(ival y) <= &75423752
    ==> ival(word_mul (word_sx x:int64) (word_sx y:int64)) = ival x * ival y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE `word_mul a b:int64 = iword(ival a * ival b)`] THEN
  SIMP_TAC[IVAL_WORD_SX; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `abs(ival(x:int32) * ival(y:int32)) <= &5688742365757504` MP_TAC THENL
   [REWRITE_TAC[INT_ABS_MUL] THEN
    MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `&75423752 * &75423752:int` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INT_LE_MUL2 THEN ASM_REWRITE_TAC[INT_ABS_POS];
      CONV_TAC INT_REDUCE_CONV];
    REWRITE_TAC[INT_ABS_BOUNDS] THEN CONV_TAC INT_REDUCE_CONV THEN
    INT_ARITH_TAC]);;

let Q_MUL_COMM = WORD_RULE
 `word_mul (word 8380417:int64) x = word_mul x (word 8380417:int64)`;;

(* Normalization rules for VPSRLQ/VMOVSHDUP patterns *)
let USHR32_SUBWORD = WORD_BLAST
 `word_subword (word_ushr (x:int64) 32) (0,32):int32 = word_subword x (32,32)`;;

let DUP32_SUBWORD = WORD_BLAST
 `word_subword (word_duplicate (word_subword (x:int64) (32,32):int32):int64) (0,32):int32
  = word_subword x (32,32)`;;

(* Simplify word_subword(word_join ...) - needed for odd-indexed coefficients *)
let WORD_JOIN_SUBWORD = WORD_BLAST
 `word_subword (word_join (a:int32) (b:int32):int64) (32,32):int32 = a`;;

(* Distribute word_and / word_not over word_join (32/64-bit lanes) *)
let WORD_AND_JOIN_64 = WORD_BLAST
  `!a b c d : int32.
   word_and ((word_join:int32->int32->int64) a b)
            ((word_join:int32->int32->int64) c d) =
   word_join (word_and a c) (word_and b d)`;;

let WORD_AND_JOIN_128 = WORD_BLAST
  `!a b c d : int64.
   word_and ((word_join:int64->int64->int128) a b)
            ((word_join:int64->int64->int128) c d) =
   word_join (word_and a c) (word_and b d)`;;

let WORD_NOT_JOIN_64 = WORD_BLAST
  `!a b : int32.
   word_not ((word_join:int32->int32->int64) a b) =
   word_join (word_not a) (word_not b)`;;

let WORD_NOT_JOIN_128 = WORD_BLAST
  `!a b : int64.
   word_not ((word_join:int64->int64->int128) a b) =
   word_join (word_not a) (word_not b)`;;

(* ival of sign-extended product equals integer product when bounded *)
let IVAL_WORD_MUL_SX32_64 = prove(
 `!x:int32 y:int32.
    abs(ival x) <= &75423752 /\ abs(ival y) <= &75423752
    ==> ival(word_mul (word_sx x:int64) (word_sx y:int64)) = ival x * ival y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE `word_mul a b:int64 = iword(ival a * ival b)`] THEN
  SIMP_TAC[IVAL_WORD_SX; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `abs(ival(x:int32) * ival(y:int32)) <= &5688742365757504` MP_TAC THENL
   [REWRITE_TAC[INT_ABS_MUL] THEN
    MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `&75423752 * &75423752:int` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INT_LE_MUL2 THEN ASM_REWRITE_TAC[INT_ABS_POS];
      CONV_TAC INT_REDUCE_CONV];
    REWRITE_TAC[INT_ABS_BOUNDS] THEN CONV_TAC INT_REDUCE_CONV THEN
    INT_ARITH_TAC]);;

(* Merge 4 x bytes32 into bytes128 at a given base+offset *)
let MEMORY_128_FROM_32_TAC =
  let a_tm = `a:int64` and n_tm = `n:num` and i64_ty = `:int64`
  and pat = `read (memory :> bytes128(word_add a (word n))) s0` in
  fun v boff n ->
    let pat' = subst[mk_var(v,i64_ty),a_tm] pat in
    let f i =
      let itm = mk_small_numeral(boff + 16*i) in
      READ_MEMORY_MERGE_CONV 2 (subst[itm,n_tm] pat') in
    MP_TAC(end_itlist CONJ (map f (0--(n-1))));;

(* ------------------------------------------------------------------------- *)
(* Repeatedly apply the stepping tactic f, with monotonically increasing     *)
(* argument n, until the target PC (extracted from the goal) matches one of   *)
(* the PC-constraining assumptions.                                          *)
(*                                                                           *)
(* The goal must be of the form `ensures arm ...`; PC clauses must be of the  *)
(* form `read PC some_state = some_value`.                                    *)
(* ------------------------------------------------------------------------- *)

let MAP_UNTIL_TARGET_PC f n = fun (asl, w) ->
  let is_pc_condition = can (term_match [] `read PC some_state = some_value`) in
  let extract_target_pc_from_goal goal =
    let _, insts, _ = term_match [] `eventually arm (\s'. P) some_state` goal in
    insts |> rev_assoc `P: bool` |> conjuncts |> find is_pc_condition in
  let extract_pc_assumption asl =
    try Some (find (is_pc_condition o concl o snd) asl |> snd |> concl) with _ -> None in
  let has_matching_pc_assumption asl target_pc =
    match extract_pc_assumption asl with
     | None -> false
     | Some(asm) -> can (term_match [`returnaddress: 64 word`; `pc: num`] target_pc) asm in
  let target_pc = extract_target_pc_from_goal w in
  let TARGET_PC_REACHED_TAC target_pc = fun (asl, w) ->
    if has_matching_pc_assumption asl target_pc then ALL_TAC (asl, w)
    else NO_TAC (asl, w) in
  let rec core n (asl, w) =
    (TARGET_PC_REACHED_TAC target_pc ORELSE (f n THEN core (n + 1))) (asl, w)
  in core n (asl, w);;

(* ------------------------------------------------------------------------- *)
(* From |- (x == y) (mod m) /\ P   to   |- (x == y) (mod n) /\ P             *)
(* ------------------------------------------------------------------------- *)

let WEAKEN_INTCONG_RULE =
  let prule = (MATCH_MP o prove)
   (`(x:int == y) (mod m) ==> !n. m rem n = &0 ==> (x == y) (mod n)`,
    REWRITE_TAC[INT_REM_EQ_0] THEN INTEGER_TAC)
  and conv = GEN_REWRITE_CONV I [INT_REM_ZERO; INT_REM_REFL] ORELSEC
             INT_REM_CONV
  and zth = REFL `&0:int` in
  let lrule n th =
    let th1 = SPEC (mk_intconst n) (prule th) in
    let th2 = LAND_CONV conv (lhand(concl th1)) in
    MP th1 (EQ_MP (SYM th2) zth) in
  fun n th ->
    let th1,th2 = CONJ_PAIR th in
    CONJ (lrule n th1) th2;;

(* ------------------------------------------------------------------------- *)
(* Unify modulus and conjoin a pair of (x == y) (mod m) /\ P theorems.       *)
(* ------------------------------------------------------------------------- *)

let UNIFY_INTCONG_RULE th1 th2 =
  let p1 = dest_intconst (rand(rand(lhand(concl th1))))
  and p2 = dest_intconst (rand(rand(lhand(concl th2)))) in
  let d = gcd_num p1 p2 in
  CONJ (WEAKEN_INTCONG_RULE d th1) (WEAKEN_INTCONG_RULE d th2);;

(* ------------------------------------------------------------------------- *)
(* Process list of ineqequality into standard congbounds for atomic terms.   *)
(* ------------------------------------------------------------------------- *)

let DIMINDEX_INT_REDUCE_CONV =
  DEPTH_CONV(WORD_NUM_RED_CONV ORELSEC DIMINDEX_CONV) THENC
  INT_REDUCE_CONV;;

let PROCESS_BOUND_ASSUMPTIONS =
  let cth = prove
   (`(ival x <= b <=>
      --(&2 pow (dimindex(:N) - 1)) <= ival x /\ ival x <= b) /\
     (b <= ival x <=>
      b <= ival x /\ ival x <= &2 pow (dimindex(:N) - 1) - &1) /\
     (ival(x:N word) > b <=>
      b + &1 <= ival x /\ ival x <= &2 pow (dimindex(:N) - 1) - &1) /\
     (b > ival(x:N word) <=>
      --(&2 pow (dimindex(:N) - 1)) <= ival x /\ ival x <= b - &1) /\
     (ival(x:N word) >= b <=>
      b <= ival x /\ ival x <= &2 pow (dimindex(:N) - 1) - &1) /\
     (b >= ival(x:N word) <=>
      --(&2 pow (dimindex(:N) - 1)) <= ival x /\ ival x <= b) /\
     (ival(x:N word) < b <=>
      --(&2 pow (dimindex(:N) - 1)) <= ival x /\ ival x <= b - &1) /\
     (b < ival(x:N word) <=>
     b + &1 <= ival x /\ ival x <= &2 pow (dimindex(:N) - 1) - &1) /\
     (abs(ival(x:N word)) <= b <=>
      --b <= ival x /\ ival x <= b) /\
     (abs(ival(x:N word)) < b <=>
      &1 - b <= ival x /\ ival x <= b - &1)`,
    REWRITE_TAC[IVAL_BOUND; INT_ARITH `x:int <= y - &1 <=> x < y`] THEN
    INT_ARITH_TAC)
  and pth = prove
   (`!l u (x:N word).
          l <= ival x /\ ival x <= u
          ==> (ival x == ival x) (mod &0) /\ l <= ival x /\ ival x <= u`,
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN INTEGER_TAC) in
  let rule =
    MATCH_MP pth o
    CONV_RULE (BINOP2_CONV (LAND_CONV DIMINDEX_INT_REDUCE_CONV)
                           (RAND_CONV DIMINDEX_INT_REDUCE_CONV)) o
    GEN_REWRITE_RULE I [cth] in
  let rec process lfn ths =
    match ths with
      [] -> lfn
    | th::oths ->
          let lfn' =
            try let th' = rule th in
                let tm = rand(concl th') in
                if is_intconst (rand(rand tm)) && is_intconst (lhand(lhand tm))
                then (rand(lhand(rand tm)) |-> th') lfn
                else lfn
            with Failure _ -> lfn in
          process lfn' oths in
  process undefined;;

(* ------------------------------------------------------------------------- *)
(* Congruence-and-bound propagation, just recursion on the expression tree.  *)
(* ------------------------------------------------------------------------- *)

let CONGBOUND_CONST = prove
 (`!(x:N word) n.
        ival x = n
        ==> (ival x == n) (mod &0) /\ n <= ival x /\ ival x <= n`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[INT_LE_REFL] THEN INTEGER_TAC);;

let CONGBOUND_ATOM = prove
 (`!x:N word. (ival x == ival x) (mod &0) /\
              --(&2 pow (dimindex(:N) - 1)) <= ival x /\
              ival x <= &2 pow (dimindex(:N) - 1) - &1`,
  GEN_TAC THEN REWRITE_TAC[INT_ARITH `x:int <= y - &1 <=> x < y`] THEN
  REWRITE_TAC[IVAL_BOUND] THEN INTEGER_TAC);;

let CONGBOUND_ATOM_GEN = prove
 (`!x:N word. abs(ival x) <= n
              ==> (ival x == ival x) (mod &0) /\
                  --n <= ival x /\ ival x <= n`,
  REWRITE_TAC[INTEGER_RULE `(x:int == x) (mod n)`] THEN INT_ARITH_TAC);;

let CONGBOUND_IWORD = prove
 (`!x. ((x == x') (mod p) /\ l <= x /\ x <= u)
       ==> --(&2 pow (dimindex(:N) - 1)) <= l /\
           u <= &2 pow (dimindex(:N) - 1) - &1
           ==> (ival(iword x:N word) == x') (mod p) /\
               l <= ival(iword x:N word) /\ ival(iword x:N word) <= u`,
  GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN REWRITE_TAC[word_sx] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) IVAL_IWORD o
    lhand o rand o rand o snd) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[]);;

let CONGBOUND_WORD_SX = prove
 (`!x:M word.
        ((ival x == x') (mod p) /\ l <= ival x /\ ival x <= u)
        ==> --(&2 pow (dimindex(:N) - 1)) <= l /\
            u <= &2 pow (dimindex(:N) - 1) - &1
            ==> (ival(word_sx x:N word) == x') (mod p) /\
                l <= ival(word_sx x:N word) /\ ival(word_sx x:N word) <= u`,
  REWRITE_TAC[word_sx; CONGBOUND_IWORD]);;

let CONGBOUND_WORD_NEG = prove
 (`!x:N word.
        ((ival x == x') (mod p) /\ lx <= ival x /\ ival x <= ux)
        ==> --lx <= &2 pow (dimindex(:N) - 1) - &1
            ==> (ival(word_neg x) == --x') (mod p) /\
                --ux <= ival(word_neg x) /\
                ival(word_neg x) <= --lx`,
  GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ival(word_neg x:N word) = --(ival x)` SUBST1_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN WORD_ARITH_TAC;
    ASM_SIMP_TAC[INTEGER_RULE
     `(x:int == x') (mod p) ==> (--x == --x') (mod p)`] THEN
    ASM_ARITH_TAC]);;

let CONGBOUND_WORD_ADD = prove
 (`!x y:N word.
        ((ival x == x') (mod p) /\ lx <= ival x /\ ival x <= ux) /\
        ((ival y == y') (mod p) /\ ly <= ival y /\ ival y <= uy)
        ==> --(&2 pow (dimindex(:N) - 1)) <= lx + ly /\
            ux + uy <= &2 pow (dimindex(:N) - 1) - &1
            ==> (ival(word_add x y) == x' + y') (mod p) /\
                lx + ly <= ival(word_add x y) /\
                ival(word_add x y) <= ux + uy`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_ADD_IMODULAR; imodular] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] CONGBOUND_IWORD) THEN
  ASM_SIMP_TAC[INT_CONG_ADD] THEN ASM_INT_ARITH_TAC);;

let CONGBOUND_WORD_SUB = prove
 (`!x y:N word.
        ((ival x == x') (mod p) /\ lx <= ival x /\ ival x <= ux) /\
        ((ival y == y') (mod p) /\ ly <= ival y /\ ival y <= uy)
        ==> --(&2 pow (dimindex(:N) - 1)) <= lx - uy /\
            ux - ly <= &2 pow (dimindex(:N) - 1) - &1
            ==> (ival(word_sub x y) == x' - y') (mod p) /\
                lx - uy <= ival(word_sub x y) /\
                ival(word_sub x y) <= ux - ly`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_SUB_IMODULAR; imodular] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] CONGBOUND_IWORD) THEN
  ASM_SIMP_TAC[INT_CONG_SUB] THEN ASM_INT_ARITH_TAC);;

let CONGBOUND_WORD_MUL = prove
 (`!x y:N word.
        ((ival x == x') (mod p) /\ lx <= ival x /\ ival x <= ux) /\
        ((ival y == y') (mod p) /\ ly <= ival y /\ ival y <= uy)
        ==> --(&2 pow (dimindex(:N) - 1))
            <= min (lx * ly) (min (lx * uy) (min (ux * ly) (ux * uy))) /\
            max (lx * ly) (max (lx * uy) (max (ux * ly) (ux * uy)))
            <= &2 pow (dimindex(:N) - 1) - &1
            ==> (ival(word_mul x y) == x' * y') (mod p) /\
                min (lx * ly) (min (lx * uy) (min (ux * ly) (ux * uy)))
                <= ival(word_mul x y) /\
                ival(word_mul x y)
                <= max (lx * ly) (max (lx * uy) (max (ux * ly) (ux * uy)))`,
  let lemma = prove
     (`l:int <= x /\ x <= u
       ==> !a. a * l <= a * x /\ a * x <= a * u \/
               a * u <= a * x /\ a * x <= a * l`,
      MESON_TAC[INT_LE_NEGTOTAL; INT_LE_LMUL;
                INT_ARITH `a * x:int <= a * y <=> --a * y <= --a * x`]) in
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(ASSUME_TAC o SPEC `ival(x:N word)` o MATCH_MP lemma) THEN
  DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN DISCH_THEN(fun th ->
        ASSUME_TAC(SPEC `ly:int` th) THEN ASSUME_TAC(SPEC `uy:int` th)) THEN
  REWRITE_TAC[WORD_MUL_IMODULAR; imodular] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] CONGBOUND_IWORD) THEN
  ASM_SIMP_TAC[INT_CONG_MUL] THEN ASM_INT_ARITH_TAC);;

let CONGBOUND_BARRED = prove
 (`!a a' l u.
        ((ival a == a') (mod &3329) /\ l <= ival a /\ ival a <= u)
        ==> (ival(barred a) == a') (mod &3329) /\
            -- &1664 <= ival(barred a) /\ ival(barred a) <= &1664`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[barred] THEN
  REWRITE_TAC[iword_saturate; word_INT_MIN; word_INT_MAX; DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REPEAT(COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[] `p ==> ~p ==> q`)) THEN
    REWRITE_TAC[INT_GT; INT_NOT_LT] THEN BOUNDER_TAC[];
    ASM_REWRITE_TAC[]]) THEN
  REWRITE_TAC[WORD_RULE
   `word_sub a (word_mul b (word n)) = iword(ival a - ival b * &n)`] THEN
  REPEAT(W(fun (asl,w) ->
     let t = hd(sort free_in
        (find_terms (can (term_match [] `ival(iword x)`)) w)) in
     let th = PART_MATCH (lhand o rand) IVAL_IWORD t in
     MP_TAC th THEN REWRITE_TAC[DIMINDEX_16] THEN
     CONV_TAC NUM_REDUCE_CONV THEN
     ANTS_TAC THENL [BOUNDER_TAC[]; DISCH_THEN SUBST1_TAC])) THEN
  MATCH_MP_TAC(MESON[]
   `(x == k) (mod n) /\
    (a <= x /\ x <= b) /\
    (a <= x /\ x <= b ==> ival(iword x:int16) = x)
    ==> (ival(iword x:int16) == k) (mod n) /\
        a <= ival(iword x:int16) /\ ival(iword x:int16) <= b`) THEN
  ASM_REWRITE_TAC[INTEGER_RULE
   `(a - x * n:int == a') (mod n) <=> (a == a') (mod n)`] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `a:int16` IVAL_BOUND);
    REPEAT STRIP_TAC THEN MATCH_MP_TAC IVAL_IWORD] THEN
  REWRITE_TAC[DIMINDEX_16; ARITH] THEN ASM_INT_ARITH_TAC);;

let CONGBOUND_BARRED_X86 = prove
 (`!a a' l u.
        ((ival a == a') (mod &3329) /\ l <= ival a /\ ival a <= u)
        ==> (ival(barred_x86 a) == a') (mod &3329) /\
            &0 <= ival(barred_x86 a) /\ ival(barred_x86 a) <= &6657`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[barred_x86] THEN
  REWRITE_TAC[WORD_BLAST
   `word_ishr (word_subword (x:int32) (16,16):int16) 10 =
    word_sx(word_ishr x 26)`] THEN
  REWRITE_TAC[WORD_RULE
   `word_sub a (word_mul b (word n)) = iword(ival a - ival b * &n)`] THEN
  REWRITE_TAC[BITBLAST_RULE
   `ival(word_sx(word_ishr (x:int32) 26):int16) = ival(word_ishr x 26)`] THEN
  REWRITE_TAC[WORD_MUL_IMODULAR; imodular; IVAL_WORD_ISHR] THEN
  SIMP_TAC[IVAL_WORD_SX; DIMINDEX_32; DIMINDEX_16; ARITH] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  SUBGOAL_THEN
   `ival(iword(ival(a:int16) * &20159):int32) = ival a * &20159`
  SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN BOUNDER_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) IVAL_IWORD o
    lhand o rator o lhand o snd) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPEC `a:int16` IVAL_BOUND) THEN REWRITE_TAC[DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[INTEGER_RULE
   `(a - x * p:int == a') (mod p) <=> (a == a') (mod p)`] THEN
  MP_TAC(ISPEC `a:int16` IVAL_BOUND) THEN REWRITE_TAC[DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC
 );;

let CONGBOUND_BARMUL = prove
 (`!a a' l u.
        ((ival a == a') (mod &3329) /\ l <= ival a /\ ival a <= u)
        ==> !k b. abs(k) <= &32767 /\
                  (max (abs l) (abs u) *
                   abs(&65536 * ival b - &6658 * k) + &109150207) div &65536
                  <= &32767
                  ==> (ival(barmul(k,b) a) == a' * ival b) (mod &3329) /\
                      --(max (abs l) (abs u) *
                         abs(&65536 * ival b - &6658 * k) + &109084672)
                         div &65536
                      <= ival(barmul(k,b) a) /\
                      ival(barmul(k,b) a) <=
                      (max (abs l) (abs u) * abs(&65536 * ival b - &6658 * k) +
                       &109150207) div &65536`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[INT_ABS_BOUNDS] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[barmul] THEN
  REWRITE_TAC[iword_saturate; word_INT_MIN; word_INT_MAX; DIMINDEX_16] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REPEAT(COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[] `p ==> ~p ==> q`)) THEN
    REWRITE_TAC[INT_GT; INT_NOT_LT] THEN ASM BOUNDER_TAC[];
    ASM_REWRITE_TAC[]]) THEN
  REWRITE_TAC[WORD_RULE
   `word_sub (word_mul a b) (word_mul (iword k) (word c)) =
    iword(ival a * ival b - &c * k)`] THEN
  MATCH_MP_TAC(MESON[]
   `(x == k) (mod n) /\
    (a <= x /\ x <= b ==> ival(iword x:int16) = x) /\
    (a <= x /\ x <= b)
    ==> (ival(iword x:int16) == k) (mod n) /\
        a <= ival(iword x:int16) /\ ival(iword x:int16) <= b`) THEN
  ASM_SIMP_TAC[INTEGER_RULE
   `(a:int == a') (mod n) ==> (a * b - n * c == a' * b) (mod n)`] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
    REWRITE_TAC[DIMINDEX_16; ARITH] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(INT_ARITH
   `&65536 * l + &109084672 <= a * (&65536 * b - &6658 * k) /\
    a * (&65536 * b - &6658 * k) <= &65536 * u - &109084672
    ==> l <= a * b - &3329 * (&2 * a * k + &32768) div &65536 /\
        a * b - &3329 * (&2 * a * k + &32768) div &65536 <= u`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(INT_ARITH `abs(y):int <= --x ==> x <= y`);
    MATCH_MP_TAC(INT_ARITH `abs(y):int <= x ==> y <= x`)] THEN
  REWRITE_TAC[INT_ABS_MUL] THEN
  TRANS_TAC INT_LE_TRANS
   `max (abs l) (abs u) * abs(&65536 * ival(b:int16) - &6658 * k)` THEN
  ASM_SIMP_TAC[INT_LE_RMUL; INT_ABS_POS; INT_ARITH
   `l:int <= x /\ x <= u ==> abs x <= max (abs l) (abs u)`] THEN
  CONV_TAC INT_ARITH);;

let CONGBOUND_ARM_MLDSA_BARMUL = prove
 (`!a a' l u.
        ((ival a == a') (mod &8380417) /\ l <= ival a /\ ival a <= u)
        ==> !k b. abs(k) <= &2147483647 /\
                  (max (abs l) (abs u) *
                   abs(&4294967296 * ival b - &16760834 * k) + &17996812765888511) div &4294967296
                  <= &2147483647
                  ==> (ival(arm_mldsa_barmul(k,b) a) == a' * ival b) (mod &8380417) /\
                      --(max (abs l) (abs u) *
                         abs(&4294967296 * ival b - &16760834 * k) + &17996808470921216)
                         div &4294967296
                      <= ival(arm_mldsa_barmul(k,b) a) /\
                      ival(arm_mldsa_barmul(k,b) a) <=
                      (max (abs l) (abs u) * abs(&4294967296 * ival b - &16760834 * k) +
                       &17996812765888511) div &4294967296`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[INT_ABS_BOUNDS] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[arm_mldsa_barmul] THEN
  REWRITE_TAC[iword_saturate; word_INT_MIN; word_INT_MAX; DIMINDEX_32] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  REPEAT(COND_CASES_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[] `p ==> ~p ==> q`)) THEN
    REWRITE_TAC[INT_GT; INT_NOT_LT] THEN ASM BOUNDER_TAC[];
    ASM_REWRITE_TAC[]]) THEN
  REWRITE_TAC[WORD_RULE
   `word_sub (word_mul a b) (word_mul (iword k) (word c)) =
    iword(ival a * ival b - &c * k)`] THEN
  MATCH_MP_TAC(MESON[]
   `(x == k) (mod n) /\
    (a <= x /\ x <= b ==> ival(iword x:int32) = x) /\
    (a <= x /\ x <= b)
    ==> (ival(iword x:int32) == k) (mod n) /\
        a <= ival(iword x:int32) /\ ival(iword x:int32) <= b`) THEN
  ASM_SIMP_TAC[INTEGER_RULE
   `(a:int == a') (mod n) ==> (a * b - n * c == a' * b) (mod n)`] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
    REWRITE_TAC[DIMINDEX_32; ARITH] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(INT_ARITH
   `&4294967296 * l + &17996808470921216 <= a * (&4294967296 * b - &16760834 * k) /\
    a * (&4294967296 * b - &16760834 * k) <= &4294967296 * u - &17996808470921216
    ==> l <= a * b - &8380417 * (&2 * a * k + &2147483648) div &4294967296 /\
        a * b - &8380417 * (&2 * a * k + &2147483648) div &4294967296 <= u`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(INT_ARITH `abs(y):int <= --x ==> x <= y`);
    MATCH_MP_TAC(INT_ARITH `abs(y):int <= x ==> y <= x`)] THEN
  REWRITE_TAC[INT_ABS_MUL] THEN
  TRANS_TAC INT_LE_TRANS
   `max (abs l) (abs u) * abs(&4294967296 * ival(b:int32) - &16760834 * k)` THEN
  ASM_SIMP_TAC[INT_LE_RMUL; INT_ABS_POS; INT_ARITH
   `l:int <= x /\ x <= u ==> abs x <= max (abs l) (abs u)`] THEN
  CONV_TAC INT_ARITH);;

let CONGBOUND_MONTMUL_X86 = prove
 (`!x y. ((ival x == x') (mod &3329) /\ lx <= ival x /\ ival x <= ux) /\
         ((ival y == y') (mod &3329) /\ ly <= ival y /\ ival y <= uy)
         ==> (ival(montmul_x86 x y) ==
              &(inverse_mod 3329 65536) * x' * y') (mod &3329) /\
             (min (lx * ly) (min (lx * uy) (min (ux * ly) (ux * uy))) -
              &109081343) div &65536 <= ival(montmul_x86 x y) /\
             ival(montmul_x86 x y)
             <= (max (lx * ly) (max (lx * uy) (max (ux * ly) (ux * uy))) +
                 &109150207) div &65536`,
  let lemma = prove
   (`l:int <= x /\ x <= u
     ==> !a. a * l <= a * x /\ a * x <= a * u \/
             a * u <= a * x /\ a * x <= a * l`,
    MESON_TAC[INT_LE_NEGTOTAL; INT_LE_LMUL;
              INT_ARITH `a * x:int <= a * y <=> --a * y <= --a * x`])
  and ilemma = prove
   (`!x:int32. ival(word_subword x (16,16):int16) = ival x div &2 pow 16`,
    REWRITE_TAC[GSYM DIMINDEX_16; GSYM IVAL_WORD_ISHR] THEN
    GEN_TAC THEN REWRITE_TAC[DIMINDEX_16] THEN BITBLAST_TAC) in
  let mainlemma = prove
   (`!x:int32 y:int32.
          (ival x == ival y) (mod (&2 pow 16))
          ==> &2 pow 16 *
              ival(word_sub (word_subword x (16,16))
                            (word_subword y (16,16)):int16) =
              ival(word_sub x y)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(INT_ARITH
     `b rem &2 pow 16 = &0 /\ a = &2 pow 16 * b div &2 pow 16 ==> a = b`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[WORD_SUB_IMODULAR; imodular; INT_REM_EQ_0] THEN
      SIMP_TAC[INT_DIVIDES_IVAL_IWORD; DIMINDEX_32; ARITH] THEN
      POP_ASSUM MP_TAC THEN CONV_TAC INTEGER_RULE;
      AP_TERM_TAC THEN REWRITE_TAC[GSYM ilemma] THEN AP_TERM_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM INT_REM_EQ]) THEN
    SIMP_TAC[INT_REM_IVAL; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
    BITBLAST_TAC) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV INVERSE_MOD_CONV) THEN
  MP_TAC(SPECL [`&169:int`; `(&2:int) pow 16`; `&3329:int`] (INTEGER_RULE
 `!d e n:int. (e * d == &1) (mod n)
              ==> !x y. ((x == d * y) (mod n) <=> (e * x == y) (mod n))`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM INT_REM_EQ] THEN INT_ARITH_TAC;
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  ONCE_REWRITE_TAC[INT_ARITH
   `l:int <= x <=> &2 pow 16 * l <= &2 pow 16 * x`] THEN
  REWRITE_TAC[montmul_x86] THEN
  REWRITE_TAC[WORD_MUL_IMODULAR; imodular] THEN
  SIMP_TAC[IVAL_WORD_SX; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[WORD_RULE
   `!x:int16 y:int16.
        iword(ival y * ival(iword(c * ival x):int16)):int16 =
        iword(c * ival x * ival y)`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) mainlemma o
   lhand o rator o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[GSYM INT_REM_EQ; INT_REM_IVAL_IWORD; DIMINDEX_32; ARITH] THEN
    ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN
    SIMP_TAC[INT_REM_IVAL_IWORD; DIMINDEX_16; ARITH; DIMINDEX_32] THEN
    REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    REWRITE_TAC[INT_REM_EQ] THEN MATCH_MP_TAC(INTEGER_RULE
     `(a * b:int == &1) (mod p) ==> (y * x == a * b * x * y) (mod p)`) THEN
    REWRITE_TAC[GSYM INT_REM_EQ] THEN INT_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM IWORD_INT_SUB]] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) IVAL_IWORD o
    lhand o rator o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_32; ARITH] THEN BOUNDER_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ONCE_REWRITE_TAC[INT_ARITH `ival x * ival y = ival y * ival x`] THEN
  ASM_SIMP_TAC[INTEGER_RULE
   `(x:int == x') (mod p) /\ (y == y') (mod p)
    ==> (x * y - p * z == x' * y') (mod p)`] THEN
  MATCH_MP_TAC(INT_ARITH
  `(l <= p /\ p <= u) /\ (&65535 - c <= q /\ q <= b)
   ==> &2 pow 16 * (l - b) div &65536 <= p - q /\
       p - q <= &2 pow 16 * (u + c) div &65536`) THEN
  CONJ_TAC THENL [ALL_TAC; BOUNDER_TAC[]] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN(MP_TAC o CONJUNCT2)) THEN
  DISCH_THEN(ASSUME_TAC o SPEC `ival(x:int16)` o MATCH_MP lemma) THEN
  DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN DISCH_THEN(fun th ->
        ASSUME_TAC(SPEC `ly:int` th) THEN ASSUME_TAC(SPEC `uy:int` th)) THEN
  ASM_INT_ARITH_TAC);;

let MONTRED_LEMMA = prove
 (`!x. &2 pow 16 * ival(montred x) =
       ival(word_add
         (word_mul (word_sx(iword(ival x * &3327):int16)) (word 3329)) x)`,
  GEN_TAC THEN REWRITE_TAC[montred] THEN REWRITE_TAC[WORD_BLAST
   `word_subword (x:int32) (0,16):int16 = word_sx x`] THEN
  REWRITE_TAC[IWORD_INT_MUL; GSYM word_sx; GSYM WORD_IWORD] THEN
  REWRITE_TAC[WORD_BLAST `(word_sx:int32->int16) x = word_zx x`] THEN
  CONV_TAC INT_REDUCE_CONV THEN MATCH_MP_TAC(BITBLAST_RULE
   `word_and x (word 65535):int32 = word 0
    ==> &65536 * ival(word_subword x (16,16):int16) = ival x`) THEN
  REWRITE_TAC[BITBLAST_RULE
   `word_and x (word 65535):int32 = word 0 <=> word_zx x:int16 = word 0`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_ZX_ADD o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_16; DIMINDEX_32; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_ZX_MUL o lhand o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_16; DIMINDEX_32; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[WORD_BLAST `word_zx(word_sx (x:int16):int32) = x`] THEN
  REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM DIVIDES_MOD; DIMINDEX_16] THEN
  CONV_TAC WORD_REDUCE_CONV THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b + 1 == 0) (mod d) ==> d divides ((x * a) * b + x)`) THEN
  REWRITE_TAC[CONG] THEN ARITH_TAC);;

let MONTRED_MLDSA_LEMMA = prove
 (`!x. &2 pow 32 * ival(mldsa_montred x) =
       ival(word_add
         (word_mul (word_sx(iword(ival x * &4236238847):int32)) (word 8380417)) x)`,
  GEN_TAC THEN REWRITE_TAC[mldsa_montred] THEN REWRITE_TAC[WORD_BLAST
   `word_subword (x:int64) (0,32):int32 = word_sx x`] THEN
  REWRITE_TAC[IWORD_INT_MUL; GSYM word_sx; GSYM WORD_IWORD] THEN
  REWRITE_TAC[WORD_BLAST `(word_sx:int64->int32) x = word_zx x`] THEN
  CONV_TAC INT_REDUCE_CONV THEN MATCH_MP_TAC(BITBLAST_RULE
   `word_and x (word 4294967295):int64 = word 0
    ==> &4294967296 * ival(word_subword x (32,32):int32) = ival x`) THEN
  REWRITE_TAC[BITBLAST_RULE
   `word_and x (word 4294967295):int64 = word 0 <=> word_zx x:int32 = word 0`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_ZX_ADD o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_32; DIMINDEX_64; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_ZX_MUL o lhand o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_32; DIMINDEX_64; ARITH] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[WORD_BLAST `word_zx(word_sx (x:int32):int64) = x`] THEN
  REWRITE_TAC[GSYM VAL_EQ_0; VAL_WORD_ADD; VAL_WORD_MUL; VAL_WORD] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM DIVIDES_MOD; DIMINDEX_32] THEN
  CONV_TAC WORD_REDUCE_CONV THEN MATCH_MP_TAC(NUMBER_RULE
   `(a * b + 1 == 0) (mod d) ==> d divides ((x * a) * b + x)`) THEN
  REWRITE_TAC[CONG] THEN ARITH_TAC);;

let CONGBOUND_MONTRED = prove
 (`!a a' l u.
      (ival a == a') (mod &3329) /\ l <= ival a /\ ival a <= u
      ==> --(&2038398976) <= l /\ u <= &2038402304
          ==> (ival(montred a) == &(inverse_mod 3329 65536) * a') (mod &3329) /\
              (l - &109084672) div &2 pow 16 <= ival(montred a) /\
              ival(montred a) <= &1 + (u + &109081343) div &2 pow 16`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV INVERSE_MOD_CONV) THEN
  MP_TAC(SPECL [`&169:int`; `(&2:int) pow 16`; `&3329:int`] (INTEGER_RULE
 `!d e n:int. (e * d == &1) (mod n)
              ==> !x y. ((x == d * y) (mod n) <=> (e * x == y) (mod n))`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM INT_REM_EQ] THEN INT_ARITH_TAC;
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  ONCE_REWRITE_TAC[INT_ARITH
   `l:int <= x <=> &2 pow 16 * l <= &2 pow 16 * x`] THEN
  REWRITE_TAC[MONTRED_LEMMA] THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_mul a b) c = iword(ival a * ival b + ival c)`] THEN
  ASM_SIMP_TAC[IVAL_WORD_SX; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) IVAL_IWORD o
   lhand o rator o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  W(MP_TAC o C ISPEC IVAL_BOUND o
    rand o funpow 3 lhand o rand o lhand o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH] THEN STRIP_TAC THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[INTEGER_RULE
   `(a * p + x:int == y) (mod p) <=> (x == y) (mod p)`] THEN
  ASM_INT_ARITH_TAC);;

let CONGBOUND_MLDSA_MONTRED = prove
 (`!a a' l u.
      (ival a == a') (mod &8380417) /\ l <= ival a /\ ival a <= u
      ==> --(&9205375228383854592) <= l /\ u <= &9205375228392235008
          ==> (ival(mldsa_montred a) == &(inverse_mod 8380417 4294967296) * a')
              (mod &8380417) /\
              (l - &17996808470921216) div &2 pow 32 <= ival(mldsa_montred a) /\
              ival(mldsa_montred a) <= &1 + (u + &17996808462540799) div &2 pow 32`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV INVERSE_MOD_CONV) THEN
  MP_TAC(SPECL [`&(inverse_mod 8380417 4294967296):int`; `(&2:int) pow 32`; `&8380417:int`] (INTEGER_RULE
   `!d e n:int. (e * d == &1) (mod n)
                ==> !x y. ((x == d * y) (mod n) <=> (e * x == y) (mod n))`)) THEN
  CONV_TAC(ONCE_DEPTH_CONV INVERSE_MOD_CONV) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV;
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  ONCE_REWRITE_TAC[INT_ARITH
   `l:int <= x <=> &2 pow 32 * l <= &2 pow 32 * x`] THEN
  REWRITE_TAC[MONTRED_MLDSA_LEMMA] THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_mul a b) c = iword(ival a * ival b + ival c)`] THEN
  ASM_SIMP_TAC[IVAL_WORD_SX; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) IVAL_IWORD o
   lhand o rator o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN
     `--(&9205375228383854592) <= ival(a:int64) /\
      ival(a:int64) <= &9205375228392235008`
    MP_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC THEN
    ASM BOUNDER_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[INTEGER_RULE
   `(a * p + x:int == y) (mod p) <=> (x == y) (mod p)`] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `l:int <= a ==> x - l <= p ==> x <= p + a`)) THEN
    TRANS_TAC INT_LE_TRANS `--(&2 pow 31) *  &8380417:int` THEN
    CONJ_TAC THENL [ASM_INT_ARITH_TAC; BOUNDER_TAC[]];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (INT_ARITH
     `a:int <= u ==> x <= p - u ==> x + a <= p`)) THEN
    TRANS_TAC INT_LE_TRANS `(&2 pow 31 - &1) *  &8380417:int` THEN
    CONJ_TAC THENL [BOUNDER_TAC[]; ASM_INT_ARITH_TAC]]);;

let WORD_ZX_CONG_32 = prove
 (`!y:int64. (ival(word_zx y:int32) == ival y) (mod (&2 pow 32))`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INT_REM_EQ] THEN
  SIMP_TAC[INT_REM_IVAL; DIMINDEX_64; ARITH] THEN
  SIMP_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `32 = MIN 64 32`] THEN
  REWRITE_TAC[GSYM MOD_MOD_EXP_MIN; MOD_MOD_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `val(y:int64) MOD 18446744073709551616 = val y` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `y:int64` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[INT_REM_IVAL; DIMINDEX_32; ARITH] THEN
  SIMP_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32; DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `val(y:int64) MOD 18446744073709551616 = val y` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `y:int64` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_64] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MOD_MOD_REFL]);;

let IWORD_CONG_32 = prove
 (`!x:int. (&2 pow 32) divides (ival(iword x:int64) - x)`,
  GEN_TAC THEN MATCH_MP_TAC INT_DIVIDES_TRANS THEN
  EXISTS_TAC `(&2:int) pow 64` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM INT_REM_EQ_0] THEN CONV_TAC INT_REDUCE_CONV;
    REWRITE_TAC[GSYM INT_CONG_0_DIVIDES; GSYM INT_REM_EQ;
                INT_REM_IVAL_IWORD; DIMINDEX_64] THEN
    ONCE_REWRITE_TAC[GSYM INT_SUB_REM] THEN
    SIMP_TAC[INT_REM_IVAL_IWORD; DIMINDEX_64; LE_REFL] THEN
    REWRITE_TAC[INT_SUB_REFL; INT_REM_ZERO]]);;

let IVAL_WORD_SUBWORD_DIV_32 = prove
 (`!x:int64. ival(word_subword x (32,32):int32) = ival x div &2 pow 32`,
  REWRITE_TAC[GSYM DIMINDEX_16; GSYM IVAL_WORD_ISHR] THEN
  GEN_TAC THEN REWRITE_TAC[DIMINDEX_16] THEN BITBLAST_TAC);;

let MLDSA_POINTWISE_MONTRED_LEMMA = prove
 (`!x:int64. &2 pow 32 * ival(mldsa_pointwise_montred x) =
       ival(word_sub x
         (word_mul (word_sx(word_subword
           (word_mul (word 58728449:int64)
                     (word_sx (word_subword x (0,32):int32):int64))
           (0,32):int32):int64) (word 8380417:int64)))`,
  GEN_TAC THEN REWRITE_TAC[mldsa_pointwise_montred; IVAL_WORD_SUBWORD_DIV_32] THEN
  MATCH_MP_TAC(INT_ARITH
    `x rem &2 pow 32 = &0 ==> &2 pow 32 * x div &2 pow 32 = x`) THEN
  REWRITE_TAC[WORD_SUB_IMODULAR; imodular; INT_REM_EQ_0] THEN
  SIMP_TAC[INT_DIVIDES_IVAL_IWORD; DIMINDEX_64; ARITH] THEN
  REWRITE_TAC[WORD_MUL_IMODULAR; imodular] THEN
  SIMP_TAC[INT_DIVIDES_IVAL_IWORD; DIMINDEX_64; ARITH] THEN
  SIMP_TAC[IVAL_WORD_SX; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[WORD_BLAST
   `word_subword (x:int64) (0,32):int32 = word_zx x`] THEN
  ABBREV_TAC `low:int = ival(word_zx(x:int64):int32)` THEN
  ABBREV_TAC `mid:int = ival(word_zx(iword((&58728449:int) * low):int64):int32)` THEN
  SUBGOAL_THEN `((&2:int) pow 32) divides (low - ival(x:int64))` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:int64` WORD_ZX_CONG_32) THEN
    ASM_REWRITE_TAC[int_congruent; GSYM int_divides]; ALL_TAC] THEN
  MP_TAC(SPEC `(&58728449:int) * low` IWORD_CONG_32) THEN
  ABBREV_TAC `iw:int = ival(iword((&58728449:int) * low):int64)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `((&2:int) pow 32) divides (mid - iw:int)` ASSUME_TAC THENL
   [MP_TAC(SPEC `iword((&58728449:int) * low):int64` WORD_ZX_CONG_32) THEN
    ASM_REWRITE_TAC[int_congruent; GSYM int_divides]; ALL_TAC] THEN
  SUBGOAL_THEN `((&2:int) pow 32) divides ((&58728449:int) * (&8380417:int) - &1)`
    ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_REM_EQ_0] THEN CONV_TAC INT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `((&2:int) pow 32) divides (ival(x:int64) - mid * &8380417)`
    MP_TAC THENL
   [MP_TAC(SPECL [`(&2:int) pow 32`; `ival(x:int64)`; `low:int`;
                   `iw:int`; `mid:int`; `(&58728449:int)`; `(&8380417:int)`]
      (INTEGER_RULE `!(n:int) ix lo iw mid q p.
        n divides (lo - ix) /\ n divides (iw - q * lo) /\
        n divides (mid - iw) /\ n divides (q * p - &1)
        ==> n divides (ix - mid * p)`)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `mid * (&8380417:int)` IWORD_CONG_32) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  MESON_TAC[INTEGER_RULE
    `!(n:int) a b c. n divides (a - c) /\ n divides (b - c)
      ==> n divides (a - b)`]);;

let CONGBOUND_MLDSA_POINTWISE_MONTRED = prove
 (`!a a' l u.
      (ival a == a') (mod &8380417) /\ l <= ival a /\ ival a <= u
      ==> --(&9205375228383854592) <= l /\ u <= &9205375228383854591
          ==> (ival(mldsa_pointwise_montred a) ==
               &(inverse_mod 8380417 4294967296) * a')
              (mod &8380417) /\
              (l - &17996808470921216) div &2 pow 32
                <= ival(mldsa_pointwise_montred a) /\
              ival(mldsa_pointwise_montred a) <=
              &1 + (u + &17996808470921216) div &2 pow 32`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV INVERSE_MOD_CONV) THEN
  MP_TAC(SPECL [`&8265825:int`; `(&2:int) pow 32`; `&8380417:int`] (INTEGER_RULE
   `!d e n:int. (e * d == &1) (mod n)
                ==> !x y. ((x == d * y) (mod n) <=> (e * x == y) (mod n))`)) THEN
  CONV_TAC(ONCE_DEPTH_CONV INVERSE_MOD_CONV) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV;
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  ONCE_REWRITE_TAC[INT_ARITH
   `l:int <= x <=> &2 pow 32 * l <= &2 pow 32 * x`] THEN
  REWRITE_TAC[MLDSA_POINTWISE_MONTRED_LEMMA] THEN
  REWRITE_TAC[WORD_RULE
   `word_sub (a:int64) (word_mul b c) = iword(ival a - ival b * ival c)`] THEN
  SIMP_TAC[IVAL_WORD_SX; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[WORD_BLAST `word_subword (x:int64) (0,32):int32 = word_zx x`] THEN
  ABBREV_TAC `m:int = ival(word_zx(word_mul (word 58728449:int64)
                  (word_sx (word_zx (a:int64):int32):int64)):int32)` THEN
  SUBGOAL_THEN `--(&2147483648:int) <= m /\ m <= &2147483647` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `word_zx(word_mul (word 58728449:int64)
                    (word_sx (word_zx (a:int64):int32):int64)):int32` IVAL_BOUND) THEN
    ASM_REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `ival(iword(ival(a:int64) - m * &8380417):int64) = ival a - m * &8380417`
    SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
    ASM_INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[INTEGER_RULE
   `(a - m * p:int == y) (mod p) <=> (a == y) (mod p)`] THEN
  ASM_INT_ARITH_TAC);;

let CONGBOUND_MLDSA_BARRED = prove
 (`!a a' l u.
        ((ival a == a') (mod &8380417) /\ l <= ival a /\ ival a <= u)
        ==> u <= &0x7fbfffff
            ==> (ival(mldsa_barred a) == a') (mod &8380417) /\
                --(&6283009) <= ival(mldsa_barred a) /\
                ival(mldsa_barred a) <= &6283008`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `a:int32` (BITBLAST_RULE
     `!a:int32.
        let ML_DSA_Q = &8380417 in
        let t = word_ishr (word_add a (word 4194304)) 23 in
        let r = word_sub a (word_mul t (word 8380417)) in
        ival(a) < &0x7fc00000
        ==> ival(a) - ML_DSA_Q * ival t = ival r /\
            --(&6283009) <= ival r /\ ival r <= &6283008`)) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[GSYM mldsa_barred] THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  ASM_REWRITE_TAC[INTEGER_RULE
   `(x - p * q:int == y) (mod p) <=> (x == y) (mod p)`]);;

let CONGBOUND_MLDSA_MONTMUL = prove
 (`!x x' lx ux.
       ((ival x == x') (mod &8380417) /\ lx <= ival x /\ ival x <= ux)
       ==> !a b. --(&2147483648) <= ival a /\
                 ival a <= &2147483647 /\
                 (&8380417 * ival b) rem &4294967296 = ival a rem &4294967296
                 ==> (ival(mldsa_montmul (a,b) x) ==
                     &(inverse_mod 8380417 4294967296) * ival a * x')
                     (mod &8380417) /\
                     (min (ival a * lx) (ival a * ux) - &17996808462540799)
                     div &4294967296 <= ival(mldsa_montmul (a,b) x) /\
                     ival(mldsa_montmul (a,b) x) <=
                     (max (ival a * lx) (ival a * ux) + &17996812765888511)
                     div &2 pow 32`,
  let lemma = prove
   (`l:int <= x /\ x <= u
     ==> !a. a * l <= a * x /\ a * x <= a * u \/
             a * u <= a * x /\ a * x <= a * l`,
    MESON_TAC[INT_LE_NEGTOTAL; INT_LE_LMUL;
              INT_ARITH `a * x:int <= a * y <=> --a * y <= --a * x`])
  and ilemma = prove
   (`!x:int64. ival(word_subword x (32,32):int32) = ival x div &2 pow 32`,
    REWRITE_TAC[GSYM DIMINDEX_16; GSYM IVAL_WORD_ISHR] THEN
    GEN_TAC THEN REWRITE_TAC[DIMINDEX_16] THEN BITBLAST_TAC) in
  let mainlemma = prove
   (`!x:int64 y:int64.
          (ival x == ival y) (mod (&2 pow 32))
          ==> &2 pow 32 *
              ival(word_sub (word_subword x (32,32))
                            (word_subword y (32,32)):int32) =
              ival(word_sub x y)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(INT_ARITH
     `b rem &2 pow 32 = &0 /\ a = &2 pow 32 * b div &2 pow 32 ==> a = b`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[WORD_SUB_IMODULAR; imodular; INT_REM_EQ_0] THEN
      SIMP_TAC[INT_DIVIDES_IVAL_IWORD; DIMINDEX_64; ARITH] THEN
      POP_ASSUM MP_TAC THEN CONV_TAC INTEGER_RULE;
      AP_TERM_TAC THEN REWRITE_TAC[GSYM ilemma] THEN AP_TERM_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM INT_REM_EQ]) THEN
    SIMP_TAC[INT_REM_IVAL; DIMINDEX_16; DIMINDEX_64; ARITH] THEN
    BITBLAST_TAC) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV INVERSE_MOD_CONV) THEN
  MP_TAC(SPECL [`&8265825:int`; `(&2:int) pow 32`; `&8380417:int`] (INTEGER_RULE
 `!d e n:int. (e * d == &1) (mod n)
              ==> !x y. ((x == d * y) (mod n) <=> (e * x == y) (mod n))`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM INT_REM_EQ] THEN INT_ARITH_TAC;
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  ONCE_REWRITE_TAC[INT_ARITH
   `l:int <= x <=> &2 pow 32 * l <= &2 pow 32 * x`] THEN
  REWRITE_TAC[mldsa_montmul] THEN
  REWRITE_TAC[WORD_MUL_IMODULAR; imodular] THEN
  SIMP_TAC[IVAL_WORD_SX; DIMINDEX_32; DIMINDEX_64; ARITH] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  W(MP_TAC o PART_MATCH (lhand o rand) mainlemma o
   lhand o rator o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[GSYM INT_REM_EQ; INT_REM_IVAL_IWORD; DIMINDEX_64; ARITH] THEN
    ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN
    SIMP_TAC[GSYM VAL_IVAL_REM; GSYM DIMINDEX_32] THEN
    SIMP_TAC[WORD_SUBWORD_EQUAL_WORD_ZX_POS0; DIMINDEX_32; DIMINDEX_64;
             VAL_WORD_ZX_GEN; ARITH_LE; ARITH_LT] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `32 = MIN 64 32`] THEN
    REWRITE_TAC[GSYM MOD_MOD_EXP_MIN] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_REM; GSYM INT_OF_NUM_CLAUSES] THEN
    REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ; DIMINDEX_64]
     (INST_TYPE [`:64`,`:N`] VAL_IWORD_CONG)] THEN
    REWRITE_TAC[INT_REM_REM_POW_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC INT_REM_DOWN_CONV THEN
    REWRITE_TAC[GSYM INT_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN
    SIMP_TAC[GSYM VAL_IVAL_REM; GSYM DIMINDEX_32] THEN
    REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC INT_REDUCE_CONV THEN ASM_REWRITE_TAC[INT_MUL_SYM];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM IWORD_INT_SUB]] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) IVAL_IWORD o
    lhand o rator o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_64; ARITH] THEN ASM BOUNDER_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[INTEGER_RULE
   `(x:int == x') (mod p) ==> (x * a - q * p == a * x') (mod p)`] THEN
  REWRITE_TAC[GSYM(INT_REDUCE_CONV `(&2:int) pow 32`)] THEN
  MATCH_MP_TAC(INT_ARITH
  `(l <= p /\ p <= u) /\ (&4294967295 - c <= q /\ q <= b)
   ==> &2 pow 32 * (l - b) div &2 pow 32 <= p - q /\
       p - q <= &2 pow 32 * (u + c) div &2 pow 32`) THEN
  CONJ_TAC THENL [ALL_TAC; BOUNDER_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ival(a:int64)` o
    MATCH_MP lemma o CONJUNCT2) THEN
  INT_ARITH_TAC);;

let CONGBOUND_NTT_MONTMUL = prove
 (`!x x' lx ux.
       ((ival x == x') (mod &3329) /\ lx <= ival x /\ ival x <= ux)
       ==> !a b. --(&32768) <= ival a /\
                 ival a <= &32767 /\
                 (&3329 * ival b) rem &65536 = ival a rem &65536
                 ==> (ival(ntt_montmul (a,b) x) ==
                     &(inverse_mod 3329 65536) * ival a * x')
                     (mod &3329) /\
                     (min (ival a * lx) (ival a * ux) - &109081343)
                     div &65536 <= ival(ntt_montmul (a,b) x) /\
                     ival(ntt_montmul (a,b) x) <=
                     (max (ival a * lx) (ival a * ux) + &109150208)
                     div &2 pow 16`,
  let lemma = prove
   (`l:int <= x /\ x <= u
     ==> !a. a * l <= a * x /\ a * x <= a * u \/
             a * u <= a * x /\ a * x <= a * l`,
    MESON_TAC[INT_LE_NEGTOTAL; INT_LE_LMUL;
              INT_ARITH `a * x:int <= a * y <=> --a * y <= --a * x`])
  and ilemma = prove
   (`!x:int32. ival(word_subword x (16,16):int16) = ival x div &2 pow 16`,
    REWRITE_TAC[GSYM DIMINDEX_16; GSYM IVAL_WORD_ISHR] THEN
    GEN_TAC THEN REWRITE_TAC[DIMINDEX_16] THEN BITBLAST_TAC) in
  let mainlemma = prove
   (`!x:int32 y:int32.
          (ival x == ival y) (mod (&2 pow 16))
          ==> &2 pow 16 *
              ival(word_sub (word_subword x (16,16))
                            (word_subword y (16,16)):int16) =
              ival(word_sub x y)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(INT_ARITH
     `b rem &2 pow 16 = &0 /\ a = &2 pow 16 * b div &2 pow 16 ==> a = b`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[WORD_SUB_IMODULAR; imodular; INT_REM_EQ_0] THEN
      SIMP_TAC[INT_DIVIDES_IVAL_IWORD; DIMINDEX_32; ARITH] THEN
      POP_ASSUM MP_TAC THEN CONV_TAC INTEGER_RULE;
      AP_TERM_TAC THEN REWRITE_TAC[GSYM ilemma] THEN AP_TERM_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM INT_REM_EQ]) THEN
    SIMP_TAC[INT_REM_IVAL; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
    BITBLAST_TAC) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV INVERSE_MOD_CONV) THEN
  MP_TAC(SPECL [`&169:int`; `(&2:int) pow 16`; `&3329:int`] (INTEGER_RULE
 `!d e n:int. (e * d == &1) (mod n)
              ==> !x y. ((x == d * y) (mod n) <=> (e * x == y) (mod n))`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM INT_REM_EQ] THEN INT_ARITH_TAC;
    DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  ONCE_REWRITE_TAC[INT_ARITH
   `l:int <= x <=> &2 pow 16 * l <= &2 pow 16 * x`] THEN
  REWRITE_TAC[ntt_montmul] THEN
  REWRITE_TAC[WORD_MUL_IMODULAR; imodular] THEN
  SIMP_TAC[IVAL_WORD_SX; DIMINDEX_32; DIMINDEX_32; ARITH] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  W(MP_TAC o PART_MATCH (lhand o rand) mainlemma o
   lhand o rator o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[GSYM INT_REM_EQ; INT_REM_IVAL_IWORD; DIMINDEX_32; ARITH] THEN
    SIMP_TAC[IVAL_WORD_SX; DIMINDEX_16; DIMINDEX_32; ARITH_LE; ARITH_LT] THEN
    ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN
    REWRITE_TAC[REWRITE_RULE[GSYM INT_REM_EQ] IVAL_IWORD_CONG;
                GSYM DIMINDEX_16] THEN
    REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC INT_REM_DOWN_CONV THEN
    REWRITE_TAC[GSYM INT_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM INT_MUL_REM] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC INT_REDUCE_CONV THEN ASM_REWRITE_TAC[INT_MUL_SYM];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM IWORD_INT_SUB]] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) IVAL_IWORD o
    lhand o rator o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[IVAL_WORD_SX; DIMINDEX_16; DIMINDEX_32; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[DIMINDEX_32; ARITH] THEN ASM BOUNDER_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[IVAL_WORD_SX; DIMINDEX_16; DIMINDEX_32; ARITH_LE; ARITH_LT] THEN
  ASM_SIMP_TAC[INTEGER_RULE
   `(x:int == x') (mod p) ==> (x * a - q * p == a * x') (mod p)`] THEN
  REWRITE_TAC[GSYM(INT_REDUCE_CONV `(&2:int) pow 16`)] THEN
  MATCH_MP_TAC(INT_ARITH
  `(l <= p /\ p <= u) /\ (&65535 - c <= q /\ q <= b)
   ==> &2 pow 16 * (l - b) div &2 pow 16 <= p - q /\
       p - q <= &2 pow 16 * (u + c) div &2 pow 16`) THEN
  CONJ_TAC THENL [ALL_TAC; BOUNDER_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ival(a:int32)` o
    MATCH_MP lemma o CONJUNCT2) THEN
  INT_ARITH_TAC);;

let CONCL_BOUNDS_RULE =
  CONV_RULE(BINOP2_CONV
          (LAND_CONV(RAND_CONV DIMINDEX_INT_REDUCE_CONV))
          (BINOP2_CONV
           (LAND_CONV DIMINDEX_INT_REDUCE_CONV)
           (RAND_CONV DIMINDEX_INT_REDUCE_CONV)));;

let SIDE_ELIM_RULE th =
  MP th (EQT_ELIM(DIMINDEX_INT_REDUCE_CONV(lhand(concl th))));;

let rec ASM_CONGBOUND_RULE lfn tm =
    try apply lfn tm with Failure _ ->
    match tm with
      Comb(Const("word",_),n) when is_numeral n ->
        let th1 = ISPEC tm CONGBOUND_CONST in
        let th2 = WORD_RED_CONV(lhand(lhand(snd(strip_forall(concl th1))))) in
        MATCH_MP th1 th2
    | Comb(Const("iword",_),n) when is_intconst n ->
        let th0 = WORD_IWORD_CONV tm in
        let th1 = ISPEC (rand(concl th0)) CONGBOUND_CONST in
        let th2 = WORD_RED_CONV(lhand(lhand(snd(strip_forall(concl th1))))) in
        SUBS[SYM th0] (MATCH_MP th1 th2)
    | Comb(Comb(Const("barmul",_),kb),t) ->
        let ktm,btm = dest_pair kb and th0 = ASM_CONGBOUND_RULE lfn t in
        let th0' = WEAKEN_INTCONG_RULE (num 3329) th0 in
        let th1 = SPECL [ktm;btm] (MATCH_MP CONGBOUND_BARMUL th0') in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
    | Comb(Comb(Const("arm_mldsa_barmul",_),kb),t) ->
        let ktm,btm = dest_pair kb and th0 = ASM_CONGBOUND_RULE lfn t in
        let th0' = WEAKEN_INTCONG_RULE (num 8380417) th0 in
        let th1 = SPECL [ktm;btm] (MATCH_MP CONGBOUND_ARM_MLDSA_BARMUL th0') in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
    | Comb(Comb(Const("montmul_x86",_),ltm),rtm) ->
        let lth = WEAKEN_INTCONG_RULE (num 3329) (ASM_CONGBOUND_RULE lfn ltm)
        and rth = WEAKEN_INTCONG_RULE (num 3329) (ASM_CONGBOUND_RULE lfn rtm) in
        let th1 = MATCH_MP CONGBOUND_MONTMUL_X86
                   (UNIFY_INTCONG_RULE lth rth) in
        CONCL_BOUNDS_RULE(th1)
    | Comb(Const("barred",_),t) ->
        let th1 = WEAKEN_INTCONG_RULE (num 3329) (ASM_CONGBOUND_RULE lfn t) in
        MATCH_MP CONGBOUND_BARRED th1
    | Comb(Const("barred_x86",_),t) ->
        let th1 = WEAKEN_INTCONG_RULE (num 3329) (ASM_CONGBOUND_RULE lfn t) in
        MATCH_MP CONGBOUND_BARRED_X86 th1
    | Comb(Const("montred",_),t) ->
        let th1 = WEAKEN_INTCONG_RULE (num 3329) (ASM_CONGBOUND_RULE lfn t) in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE(MATCH_MP CONGBOUND_MONTRED th1))
    | Comb(Const("mldsa_montred",_),t) ->
        let th1 = WEAKEN_INTCONG_RULE (num 8380417)
                   (ASM_CONGBOUND_RULE lfn t) in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE(MATCH_MP CONGBOUND_MLDSA_MONTRED th1))
    | Comb(Const("mldsa_pointwise_montred",_),t) ->
        let th1 = WEAKEN_INTCONG_RULE (num 8380417)
                   (ASM_CONGBOUND_RULE lfn t) in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE(MATCH_MP CONGBOUND_MLDSA_POINTWISE_MONTRED th1))
    | Comb(Const("mldsa_barred",_),t) ->
        let th1 = WEAKEN_INTCONG_RULE (num 8380417)
                     (ASM_CONGBOUND_RULE lfn t) in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE(MATCH_MP CONGBOUND_MLDSA_BARRED th1))
    | Comb(Comb(Const("mldsa_montmul",_),ab),t) ->
        let atm,btm = dest_pair ab and th0 = ASM_CONGBOUND_RULE lfn t in
        let th0' = WEAKEN_INTCONG_RULE (num 8380417) th0 in
        let th1 = SPECL [atm;btm] (MATCH_MP CONGBOUND_MLDSA_MONTMUL th0') in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
    | Comb(Comb(Const("ntt_montmul",_),ab),t) ->
        let atm,btm = dest_pair ab and th0 = ASM_CONGBOUND_RULE lfn t in
        let th0' = WEAKEN_INTCONG_RULE (num 3329) th0 in
        let th1 = SPECL [atm;btm] (MATCH_MP CONGBOUND_NTT_MONTMUL th0') in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
    | Comb(Const("word_sx",_),t) ->
        let th0 = ASM_CONGBOUND_RULE lfn t in
        let tyin = type_match
         (type_of(rator(rand(lhand(funpow 4 rand (snd(dest_forall
            (concl CONGBOUND_WORD_SX)))))))) (type_of(rator tm)) [] in
        let th1 = MATCH_MP (INST_TYPE tyin CONGBOUND_WORD_SX) th0 in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
    | Comb(Const("word_neg",_),t) ->
        let th0 = ASM_CONGBOUND_RULE lfn t in
        let th1 = MATCH_MP CONGBOUND_WORD_NEG th0 in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
    | Comb(Comb(Const("word_add",_),ltm),rtm) ->
        let lth = ASM_CONGBOUND_RULE lfn ltm
        and rth = ASM_CONGBOUND_RULE lfn rtm in
        let th1 = MATCH_MP CONGBOUND_WORD_ADD (UNIFY_INTCONG_RULE lth rth) in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
    | Comb(Comb(Const("word_sub",_),ltm),rtm) ->
        let lth = ASM_CONGBOUND_RULE lfn ltm
        and rth = ASM_CONGBOUND_RULE lfn rtm in
        let th1 = MATCH_MP CONGBOUND_WORD_SUB (UNIFY_INTCONG_RULE lth rth) in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
    | Comb(Comb(Const("word_mul",_),ltm),rtm) ->
        let lth = ASM_CONGBOUND_RULE lfn ltm
        and rth = ASM_CONGBOUND_RULE lfn rtm in
        let th1 = MATCH_MP CONGBOUND_WORD_MUL (UNIFY_INTCONG_RULE lth rth) in
        CONCL_BOUNDS_RULE(SIDE_ELIM_RULE th1)
    | _ -> CONCL_BOUNDS_RULE(ISPEC tm CONGBOUND_ATOM);;

let GEN_CONGBOUND_RULE aboths =
  ASM_CONGBOUND_RULE (PROCESS_BOUND_ASSUMPTIONS aboths);;

let CONGBOUND_RULE = GEN_CONGBOUND_RULE [];;

let rec LOCAL_CONGBOUND_RULE lfn asms =
  match asms with
    [] -> lfn
  | th::ths ->
      let bod,var = dest_eq (concl th) in
      let th1 = ASM_CONGBOUND_RULE lfn bod in
      let th2 = SUBS[th] th1 in
      let lfn' = (var |-> th2) lfn in
      LOCAL_CONGBOUND_RULE lfn' ths;;

(* ------------------------------------------------------------------------- *)
(* Simplify SIMD cruft and fold relevant definitions when encountered.       *)
(* The ABBREV form also introduces abbreviations for relevant subterms.      *)
(* ------------------------------------------------------------------------- *)

let SIMD_SIMPLIFY_CONV unfold_defs =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV THENC
  REWRITE_CONV (map GSYM unfold_defs);;

let SIMD_SIMPLIFY_TAC unfold_defs =
  let arm_simdable = can (term_match [] `read X (s:armstate):int128 = whatever`) in
  let x86_simdable = can (term_match [] `read X (s:x86state):int256 = whatever`) in
  let simdable tm = arm_simdable tm || x86_simdable tm in
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o
    CONV_RULE(RAND_CONV (SIMD_SIMPLIFY_CONV unfold_defs)) o
    check (simdable o concl)));;

let is_local_definition unfold_defs =
  let pats = map (lhand o snd o strip_forall o concl) unfold_defs in
  let pam t = exists (fun p -> can(term_match [] p) t) pats in
  fun tm -> is_eq tm && is_var(rand tm) && pam(lhand tm);;

let AUTO_ABBREV_TAC tm =
  let gv = genvar(type_of tm) in
  ABBREV_TAC(mk_eq(gv,tm));;

let SIMD_SIMPLIFY_ABBREV_TAC =
  let arm_simdable =
    can (term_match [] `read X (s:armstate):int128 = whatever`)
  and x86_simdable =
    can (term_match [] `read X (s:x86state):int256 = whatever`) in
  let simdable tm = arm_simdable tm || x86_simdable tm in
  fun unfold_defs unfold_aux ->
    let pats = map (lhand o snd o strip_forall o concl) unfold_defs in
    let pam t = exists (fun p -> can(term_match [] p) t) pats in
    let ttac th (asl,w) =
      let th' = CONV_RULE(RAND_CONV
                 (SIMD_SIMPLIFY_CONV (unfold_defs @ unfold_aux))) th in
      let asms =
        map snd (filter (is_local_definition unfold_defs o concl o snd) asl) in
      let th'' = GEN_REWRITE_RULE (RAND_CONV o TOP_DEPTH_CONV) asms th' in
      let tms = sort free_in (find_terms pam (rand(concl th''))) in
      (MP_TAC th'' THEN MAP_EVERY AUTO_ABBREV_TAC tms THEN DISCH_TAC) (asl,w) in
  TRY(FIRST_X_ASSUM(ttac o check (simdable o concl)));;

(* ========================================================================= *)
(* ML-DSA use_hint shared infrastructure lemmas                              *)
(* Used by both poly_use_hint_32 and poly_use_hint_88 proofs                 *)
(* ========================================================================= *)

(* ival equals val for values in [0, Q) where Q = 8380417 < 2^31 *)
let MLDSA_IVAL_VAL = prove(
  `!a:int32. val a < 8380417 ==> ival a = &(val a)`,
  GEN_TAC THEN DISCH_TAC THEN
  SIMP_TAC[ival; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* For natural numbers, &n is never < -2^31 *)
let INT_POS_NEG_BOUND = prove(`!n. ~((&n:int) < --(&2147483648))`,
  GEN_TAC THEN REWRITE_TAC[INT_NOT_LT] THEN
  MP_TAC(SPEC `n:num` INT_POS) THEN INT_ARITH_TAC);;

(* val(iword(&n)) = n for n < 2^31 *)
let VAL_IWORD_NUM_32 = prove(
  `!n. n < 2147483648 ==> val(iword(&n):int32) = n`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`&n:int`] (INST_TYPE [`:32`,`:N`] INT_VAL_IWORD)) THEN
  REWRITE_TAC[DIMINDEX_32; INT_POS] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ANTS_TAC THENL
  [REWRITE_TAC[INT_OF_NUM_LT] THEN ASM_ARITH_TAC;
   REWRITE_TAC[INT_OF_NUM_EQ] THEN SIMP_TAC[]]);;

(* word_ile x 0 in terms of bit 31 (signed non-positive check) *)
let WORD_ILE_ZERO_32 = BITBLAST_RULE
  `!x:int32. word_ile x (word 0) <=> bit 31 x \/ x = word 0`;;

(* val(word_and x (word 15)) = val x MOD 16 *)
let VAL_WORD_AND_15_32 = BITBLAST_RULE
  `!x:int32. val(word_and x (word 15:int32)) = val x MOD 16`;;

(* word_and x all-ones = x *)
let WORD_AND_ONES_32 = prove(
  `!x:int32. word_and x (word 4294967295) = x`,
  GEN_TAC THEN SUBGOAL_THEN `(word 4294967295 : int32) = word_not(word 0)` SUBST1_TAC THENL
  [CONV_TAC WORD_REDUCE_CONV; REWRITE_TAC[WORD_AND_NOT0]]);;

(* word_mul x 1 = x *)
let WORD_MUL_1_32 = prove(
  `!x:int32. word_mul x (word 1) = x`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_MUL; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_CLAUSES] THEN
  MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `x:int32` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Bridge lemmas: derive both real_gt and int_gt from a single NUM fact.
   Needed for native mode where real_gt and int_gt are distinct types. *)
let REAL_INT_GT_BRIDGE = prove(
  `!a:num b c. a <= b * c ==>
   ~(real_gt (&a - &b * &c) (&0)) /\ ~(int_gt (&a - &b * &c) (&0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
  [REWRITE_TAC[real_gt; REAL_NOT_LT] THEN
   MP_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL] (ASSUME `a <= b * c`)) THEN REAL_ARITH_TAC;
   REWRITE_TAC[INT_GT; INT_NOT_LT] THEN
   MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_MUL] (ASSUME `a <= b * c`)) THEN INT_ARITH_TAC]);;

let REAL_INT_GT_BRIDGE_POS = prove(
  `!a:num b c. ~(a <= b * c) ==>
   real_gt (&a - &b * &c) (&0) /\ int_gt (&a - &b * &c) (&0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NOT_LE] THEN DISCH_TAC THEN CONJ_TAC THENL
  [REWRITE_TAC[real_gt] THEN
   MP_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_MUL] (ASSUME `b * c < a`)) THEN REAL_ARITH_TAC;
   REWRITE_TAC[INT_GT] THEN
   MP_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_MUL] (ASSUME `b * c < a`)) THEN INT_ARITH_TAC]);;

(* ========================================================================= *)
(* Shared helper lemmas for UseHint proofs                                   *)
(* ========================================================================= *)

let DIV_SANDWICH = prove(
  `!x d k. ~(d = 0) /\ k * d <= x /\ x < (k + 1) * d ==> x DIV d = k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `k <= x DIV d` ASSUME_TAC THENL
  [ASM_SIMP_TAC[LE_RDIV_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x DIV d < k + 1` ASSUME_TAC THENL
  [ASM_SIMP_TAC[RDIV_LT_EQ] THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let INT_MOD_RESIDUE = prove(
  `!r m. ~(m = 0) ==> (&r:int) - &(r DIV m) * &m = &(r MOD m)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`r:num`; `m:num`] (CONJUNCT1 DIVISION_SIMP)) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_ADD;
              GSYM INT_OF_NUM_EQ] THEN
  INT_ARITH_TAC);;

(* ========================================================================= *)
(* FIPS 204 UseHint definitions (Algorithms 36 and 40)                       *)
(* ========================================================================= *)

let mldsa_cmod = new_definition
  `mldsa_cmod (r:num) (m:num) : int =
   if (r MOD m) * 2 <= m then &(r MOD m) else &(r MOD m) - &m`;;

let mldsa_decompose_32 = new_definition
  `mldsa_decompose_32 (r:num) : num # int =
   let r0 = mldsa_cmod r 523776 in
   if &r - r0 = &8380416 then (0, r0 - &1)
   else (num_of_int((&r - r0) div &523776), r0)`;;

let decompose_32_r1 = new_definition
  `decompose_32_r1 (r:num) : num = FST(mldsa_decompose_32 r)`;;

let decompose_32_r0 = new_definition
  `decompose_32_r0 (r:num) : int = SND(mldsa_decompose_32 r)`;;

let mldsa_use_hint_32 = new_definition
  `mldsa_use_hint_32 (h:num) (r:num) : num =
   let (r1, r0) = mldsa_decompose_32 r in
   if h = 1 /\ r0 > &0 then (r1 + 1) MOD 16
   else if h = 1 /\ r0 <= &0 then (r1 + 15) MOD 16
   else r1`;;

let LOWER_NONWRAP_R1 = prove(
  `!r. r MOD 523776 * 2 <= 523776 /\
       ~((&r:int) - &(r MOD 523776) = &8380416) ==>
   decompose_32_r1 r = r DIV 523776`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[decompose_32_r1; mldsa_decompose_32; mldsa_cmod] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `r MOD 523776 <= r` ASSUME_TAC THENL
  [MESON_TAC[MOD_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_DIV;
               NUM_OF_INT_OF_NUM; INT_OF_NUM_EQ] THEN
  MP_TAC(SPECL [`r:num`; `523776`] (CONJUNCT1 DIVISION_SIMP)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `r - r MOD 523776 = 523776 * r DIV 523776` SUBST1_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`523776`; `r DIV 523776`] DIV_MULT) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let UPPER_NONWRAP_R1 = prove(
  `!r. ~(r MOD 523776 * 2 <= 523776) /\
       ~((&r:int) - (&(r MOD 523776) - &523776) = &8380416) ==>
   decompose_32_r1 r = r DIV 523776 + 1`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[decompose_32_r1; mldsa_decompose_32; mldsa_cmod] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `r MOD 523776 <= r` ASSUME_TAC THENL
  [MESON_TAC[MOD_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `r MOD 523776 < 523776` ASSUME_TAC THENL
  [MP_TAC(SPECL [`r:num`; `523776`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&r:int) - (&(r MOD 523776) - &523776) =
                &(r - r MOD 523776 + 523776)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; GSYM INT_OF_NUM_ADD] THEN
   INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[INT_OF_NUM_DIV; NUM_OF_INT_OF_NUM; INT_OF_NUM_EQ] THEN
  MP_TAC(SPECL [`r:num`; `523776`] (CONJUNCT1 DIVISION_SIMP)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `r - r MOD 523776 + 523776 = (r DIV 523776 + 1) * 523776`
    ASSUME_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`(r DIV 523776 + 1) * 523776`; `523776`] DIV_MULT) THEN
  ARITH_TAC);;

let MLDSA_USE_HINT_32_UNFOLD = prove(
  `!h r. mldsa_use_hint_32 h r =
   (if h = 1 /\ decompose_32_r0 r > &0 then (decompose_32_r1 r + 1) MOD 16
    else if h = 1 /\ decompose_32_r0 r <= &0
    then (decompose_32_r1 r + 15) MOD 16
    else decompose_32_r1 r)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mldsa_use_hint_32; decompose_32_r1; decompose_32_r0] THEN
  SPEC_TAC(`mldsa_decompose_32 r`, `p:num#int`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

let mldsa_decompose_88 = new_definition
  `mldsa_decompose_88 (r:num) : num # int =
   let r0 = mldsa_cmod r 190464 in
   if &r - r0 = &8380416 then (0, r0 - &1)
   else (num_of_int((&r - r0) div &190464), r0)`;;

let decompose_88_r1 = new_definition
  `decompose_88_r1 (r:num) : num = FST(mldsa_decompose_88 r)`;;

let decompose_88_r0 = new_definition
  `decompose_88_r0 (r:num) : int = SND(mldsa_decompose_88 r)`;;

(* ------------------------------------------------------------------------- *)
(* Centered-mod (cmod) helper lemmas + decompose expansion / coefficient      *)
(* bounds, shared by the decompose_32 and decompose_88 assembly proofs.        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_CMOD_SUB = prove(
 `!r m. ~(m = 0) ==>
    num_of_int(&r - mldsa_cmod r m) =
      if r MOD m * 2 <= m then r DIV m * m
      else (r DIV m + 1) * m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_cmod] THEN
  MP_TAC(SPECL [`r:num`; `m:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL
  [SUBGOAL_THEN `r MOD m <= r` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&r - &(r MOD m) = &(r - r MOD m) : int`
     (fun th -> REWRITE_TAC[th; NUM_OF_INT_OF_NUM]) THENL
   [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB]; ALL_TAC] THEN
   ASM_ARITH_TAC;
   SUBGOAL_THEN `r MOD m <= r` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&r - (&(r MOD m) - &m) = &(r - r MOD m + m) : int`
     (fun th -> REWRITE_TAC[th; NUM_OF_INT_OF_NUM]) THENL
   [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC;
    ASM_ARITH_TAC]]);;

let MLDSA_CMOD_HIGHBITS = prove(
 `!r m. ~(m = 0) ==>
    num_of_int((&r - mldsa_cmod r m) div &m) =
      (if r MOD m * 2 <= m then r DIV m else r DIV m + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &r - mldsa_cmod r m` ASSUME_TAC THENL
  [REWRITE_TAC[mldsa_cmod] THEN
   MP_TAC(SPECL [`r:num`; `m:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `r MOD m <= r` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   COND_CASES_TAC THEN
   ASM_SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_LE] THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
   `num_of_int((&r - mldsa_cmod r m) div &m) =
    num_of_int(&r - mldsa_cmod r m) DIV m` SUBST1_TAC THENL
  [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [GSYM(MATCH_MP INT_OF_NUM_OF_INT
                     (ASSUME `&0 <= &r - mldsa_cmod r m`))] THEN
   REWRITE_TAC[INT_OF_NUM_DIV; NUM_OF_INT_OF_NUM];
   ASM_SIMP_TAC[MLDSA_CMOD_SUB] THEN
   COND_CASES_TAC THEN REWRITE_TAC[MULT_SYM] THEN
   ASM_SIMP_TAC[DIV_MULT]]);;

(* --- mldsa_decompose_32 lemmas --- *)

(* Equivalence to MOD/DIV form, used in bound proofs *)
let MLDSA_DECOMPOSE_32_EXPAND = prove(
 `!r. mldsa_decompose_32 r =
    let r0 = mldsa_cmod r 523776 in
    let h = if r MOD 523776 * 2 <= 523776
            then r DIV 523776
            else r DIV 523776 + 1 in
    if h = 16 then (0, r0 - &1)
    else (h, r0)`,
  GEN_TAC THEN REWRITE_TAC[mldsa_decompose_32; LET_DEF; LET_END_DEF] THEN
  MP_TAC(SPECL [`r:num`; `523776`] MLDSA_CMOD_HIGHBITS) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`r:num`; `523776`] DIVISION) THEN
  ANTS_TAC THENL [ARITH_TAC; STRIP_TAC] THEN
  ASM_CASES_TAC `r MOD 523776 * 2 <= 523776` THEN ASM_REWRITE_TAC[] THENL
  [REWRITE_TAC[mldsa_cmod] THEN ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `r DIV 523776 = 16` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `&r - &(r MOD 523776) = &8380416 : int` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `~(&r - &(r MOD 523776) = &8380416 : int)` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_ARITH_TAC];
   REWRITE_TAC[mldsa_cmod] THEN ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `r DIV 523776 + 1 = 16` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `&r - (&(r MOD 523776) - &523776) = &8380416 : int` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `~(&r - (&(r MOD 523776) - &523776) = &8380416 : int)` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_ARITH_TAC]]);;

let MLDSA_DECOMPOSE_32_A1_BOUND = prove(
 `!r. r < 8380417 ==> FST(mldsa_decompose_32 r) <= 15`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[MLDSA_DECOMPOSE_32_EXPAND; mldsa_cmod;
              LET_DEF; LET_END_DEF; FST] THEN
  MP_TAC(SPECL [`r:num`; `523776`] DIVISION) THEN
  ANTS_TAC THENL [ARITH_TAC; STRIP_TAC] THEN
  ASM_CASES_TAC `r MOD 523776 * 2 <= 523776` THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

let MLDSA_DECOMPOSE_32_A0_BOUND = prove(
 `!r. r < 8380417 ==>
       -- &261888 <= SND(mldsa_decompose_32 r) /\
       SND(mldsa_decompose_32 r) <= &261888`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[MLDSA_DECOMPOSE_32_EXPAND; mldsa_cmod;
              LET_DEF; LET_END_DEF] THEN
  MP_TAC(SPECL [`r:num`; `523776`] DIVISION) THEN
  ANTS_TAC THENL [ARITH_TAC; STRIP_TAC] THEN
  ASM_CASES_TAC `r MOD 523776 * 2 <= 523776` THEN ASM_REWRITE_TAC[] THENL
  [(* Case 1: MOD*2 <= 523776 *)
   ASM_CASES_TAC `r DIV 523776 = 16` THEN ASM_REWRITE_TAC[SND] THENL
   [(* 1a: wrap *)
    SUBGOAL_THEN `r MOD 523776 = 0` SUBST1_TAC THENL
    [ASM_ARITH_TAC; CONV_TAC INT_REDUCE_CONV];
    (* 1b: no wrap *)
    MP_TAC(SPEC `r MOD 523776` INT_POS) THEN
    ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC];
   (* Case 2: MOD*2 > 523776 *)
   ASM_CASES_TAC `r DIV 523776 + 1 = 16` THEN ASM_REWRITE_TAC[SND] THENL
   [(* 2a: wrap *)
    SUBGOAL_THEN `&261888 < &(r MOD 523776) : int /\ &(r MOD 523776) < &523776 : int` MP_TAC THENL
    [REWRITE_TAC[INT_OF_NUM_LT] THEN ASM_ARITH_TAC; INT_ARITH_TAC];
    (* 2b: no wrap *)
    SUBGOAL_THEN `&261888 < &(r MOD 523776) : int /\ &(r MOD 523776) < &523776 : int` MP_TAC THENL
    [REWRITE_TAC[INT_OF_NUM_LT] THEN ASM_ARITH_TAC; INT_ARITH_TAC]]]);;


let MLDSA_DECOMPOSE_88_EXPAND = prove(
 `!r. mldsa_decompose_88 r =
    let r0 = mldsa_cmod r 190464 in
    let h = if r MOD 190464 * 2 <= 190464
            then r DIV 190464
            else r DIV 190464 + 1 in
    if h = 44 then (0, r0 - &1)
    else (h, r0)`,
  GEN_TAC THEN REWRITE_TAC[mldsa_decompose_88; LET_DEF; LET_END_DEF] THEN
  MP_TAC(SPECL [`r:num`; `190464`] MLDSA_CMOD_HIGHBITS) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`r:num`; `190464`] DIVISION) THEN
  ANTS_TAC THENL [ARITH_TAC; STRIP_TAC] THEN
  ASM_CASES_TAC `r MOD 190464 * 2 <= 190464` THEN ASM_REWRITE_TAC[] THENL
  [REWRITE_TAC[mldsa_cmod] THEN ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `r DIV 190464 = 44` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `&r - &(r MOD 190464) = &8380416 : int` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `~(&r - &(r MOD 190464) = &8380416 : int)` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_ARITH_TAC];
   REWRITE_TAC[mldsa_cmod] THEN ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC `r DIV 190464 + 1 = 44` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `&r - (&(r MOD 190464) - &190464) = &8380416 : int` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `~(&r - (&(r MOD 190464) - &190464) = &8380416 : int)` (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_ARITH_TAC]]);;

let MLDSA_DECOMPOSE_88_A1_BOUND = prove(
 `!r. r < 8380417 ==> FST(mldsa_decompose_88 r) <= 43`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[MLDSA_DECOMPOSE_88_EXPAND; mldsa_cmod;
              LET_DEF; LET_END_DEF; FST] THEN
  MP_TAC(SPECL [`r:num`; `190464`] DIVISION) THEN
  ANTS_TAC THENL [ARITH_TAC; STRIP_TAC] THEN
  ASM_CASES_TAC `r MOD 190464 * 2 <= 190464` THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

let MLDSA_DECOMPOSE_88_A0_BOUND = prove(
 `!r. r < 8380417 ==>
       -- &95232 <= SND(mldsa_decompose_88 r) /\
       SND(mldsa_decompose_88 r) <= &95232`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[MLDSA_DECOMPOSE_88_EXPAND; mldsa_cmod;
              LET_DEF; LET_END_DEF] THEN
  MP_TAC(SPECL [`r:num`; `190464`] DIVISION) THEN
  ANTS_TAC THENL [ARITH_TAC; STRIP_TAC] THEN
  ASM_CASES_TAC `r MOD 190464 * 2 <= 190464` THEN ASM_REWRITE_TAC[] THENL
  [(* Case 1: MOD*2 <= 190464 *)
   ASM_CASES_TAC `r DIV 190464 = 44` THEN ASM_REWRITE_TAC[SND] THENL
   [(* 1a: wrap *)
    SUBGOAL_THEN `r MOD 190464 = 0` SUBST1_TAC THENL
    [ASM_ARITH_TAC; CONV_TAC INT_REDUCE_CONV];
    (* 1b: no wrap *)
    MP_TAC(SPEC `r MOD 190464` INT_POS) THEN
    ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC];
   (* Case 2: MOD*2 > 190464 *)
   ASM_CASES_TAC `r DIV 190464 + 1 = 44` THEN ASM_REWRITE_TAC[SND] THENL
   [(* 2a: wrap *)
    SUBGOAL_THEN `&95232 < &(r MOD 190464) : int /\ &(r MOD 190464) < &190464 : int` MP_TAC THENL
    [REWRITE_TAC[INT_OF_NUM_LT] THEN ASM_ARITH_TAC; INT_ARITH_TAC];
    (* 2b: no wrap *)
    SUBGOAL_THEN `&95232 < &(r MOD 190464) : int /\ &(r MOD 190464) < &190464 : int` MP_TAC THENL
    [REWRITE_TAC[INT_OF_NUM_LT] THEN ASM_ARITH_TAC; INT_ARITH_TAC]]]);;


let mldsa_use_hint_88 = new_definition
  `mldsa_use_hint_88 (h:num) (r:num) : num =
   let (r1, r0) = mldsa_decompose_88 r in
   if h = 1 /\ r0 > &0 then if r1 = 43 then 0 else r1 + 1
   else if h = 1 /\ r0 <= &0 then if r1 = 0 then 43 else r1 - 1
   else r1`;;

let LOWER_NONWRAP_R1_88 = prove(
  `!r. r MOD 190464 * 2 <= 190464 /\
       ~((&r:int) - &(r MOD 190464) = &8380416) ==>
   decompose_88_r1 r = r DIV 190464`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[decompose_88_r1; mldsa_decompose_88; mldsa_cmod] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `r MOD 190464 <= r` ASSUME_TAC THENL
  [MESON_TAC[MOD_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[INT_OF_NUM_SUB; INT_OF_NUM_DIV;
               NUM_OF_INT_OF_NUM; INT_OF_NUM_EQ] THEN
  MP_TAC(SPECL [`r:num`; `190464`] (CONJUNCT1 DIVISION_SIMP)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `r - r MOD 190464 = 190464 * r DIV 190464` SUBST1_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`190464`; `r DIV 190464`] DIV_MULT) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let UPPER_NONWRAP_R1_88 = prove(
  `!r. ~(r MOD 190464 * 2 <= 190464) /\
       ~((&r:int) - (&(r MOD 190464) - &190464) = &8380416) ==>
   decompose_88_r1 r = r DIV 190464 + 1`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[decompose_88_r1; mldsa_decompose_88; mldsa_cmod] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `r MOD 190464 <= r` ASSUME_TAC THENL
  [MESON_TAC[MOD_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `r MOD 190464 < 190464` ASSUME_TAC THENL
  [MP_TAC(SPECL [`r:num`; `190464`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&r:int) - (&(r MOD 190464) - &190464) =
                &(r - r MOD 190464 + 190464)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; GSYM INT_OF_NUM_ADD] THEN
   INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[INT_OF_NUM_DIV; NUM_OF_INT_OF_NUM; INT_OF_NUM_EQ] THEN
  MP_TAC(SPECL [`r:num`; `190464`] (CONJUNCT1 DIVISION_SIMP)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `r - r MOD 190464 + 190464 = (r DIV 190464 + 1) * 190464`
    ASSUME_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`(r DIV 190464 + 1) * 190464`; `190464`] DIV_MULT) THEN
  ARITH_TAC);;

let MLDSA_USE_HINT_88_UNFOLD = prove(
  `!h r. mldsa_use_hint_88 h r =
   (if h = 1 /\ decompose_88_r0 r > &0
    then if decompose_88_r1 r = 43 then 0 else decompose_88_r1 r + 1
    else if h = 1 /\ decompose_88_r0 r <= &0
    then if decompose_88_r1 r = 0 then 43 else decompose_88_r1 r - 1
    else decompose_88_r1 r)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mldsa_use_hint_88; decompose_88_r1; decompose_88_r0] THEN
  SPEC_TAC(`mldsa_decompose_88 r`, `p:num#int`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* TBL shuffle-index tables consumed by the AArch64 polyz_unpack routines.    *)
(* Each is 64 bytes (16 per 128-bit lane group); 255 marks a zeroed byte.     *)
(* ------------------------------------------------------------------------- *)

let mldsa_polyz_unpack_17_indices = (REWRITE_RULE[MAP] o define)
  `mldsa_polyz_unpack_17_indices:byte list = MAP word [
    0;   1;   2; 255;   2;   3;   4; 255;
    4;   5;   6; 255;   6;   7;   8; 255;
    9;  10;  11; 255;  11;  12;  13; 255;
   13;  14;  15; 255;  15;  16;  17; 255;
    2;   3;   4; 255;   4;   5;   6; 255;
    6;   7;   8; 255;   8;   9;  10; 255;
   11;  12;  13; 255;  13;  14;  15; 255;
   15;  28;  29; 255;  29;  30;  31; 255
]`;;

let mldsa_polyz_unpack_19_indices = (REWRITE_RULE[MAP] o define)
  `mldsa_polyz_unpack_19_indices:byte list = MAP word [
    0;   1;   2; 255;   2;   3;   4; 255;
    5;   6;   7; 255;   7;   8;   9; 255;
   10;  11;  12; 255;  12;  13;  14; 255;
   15;  16;  17; 255;  17;  18;  19; 255;
    4;   5;   6; 255;   6;   7;   8; 255;
    9;  10;  11; 255;  11;  12;  13; 255;
   14;  15;  24; 255;  24;  25;  26; 255;
   27;  28;  29; 255;  29;  30;  31; 255
]`;;

(* ------------------------------------------------------------------------- *)
(* z-polynomial unpack (GAMMA1 = 2^17 / 2^19) coefficient specs + the        *)
(* SUB_LIST / num_of_wordlist splitting lemmas used by the polyz_unpack       *)
(* assembly proofs.                                                           *)
(* ------------------------------------------------------------------------- *)

let zunpack17 = new_definition
 `zunpack17 (x:(18)word) : (32)word =
  word_sub (word(2 EXP 17)) (word_zx x)`;;

let ZUNPACK17_CORRECT = prove(
  `!x:(18)word.
    word_sub (word 131072 : 32 word)
             (word_zx (x : 18 word) : 32 word) = zunpack17 x`,
  REWRITE_TAC[zunpack17] THEN CONV_TAC NUM_REDUCE_CONV);;

let ZUNPACK17_IVAL = prove(
 `!x:(18)word. ival(zunpack17 x) = &(2 EXP 17) - &(val x)`,
  GEN_TAC THEN REWRITE_TAC[zunpack17] THEN
  SUBGOAL_THEN `word_zx (x:18 word) : 32 word = word(val x)` SUBST1_TAC THENL
  [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
   CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
   MP_TAC(ISPEC `x:18 word` VAL_BOUND) THEN
   CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN SIMP_TAC[MOD_LT];
   ALL_TAC] THEN
  ONCE_REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_SUB] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `x:18 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

let ZUNPACK17_BOUND = prove(
 `!x:(18)word. --(&(2 EXP 17) - &1) <= ival(zunpack17 x) /\
               ival(zunpack17 x) <= &(2 EXP 17)`,
  GEN_TAC THEN REWRITE_TAC[ZUNPACK17_IVAL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `x:18 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

let ZUNPACK17_MAP_BOUND = prove(
 `!l:(18 word) list. !i. i < LENGTH l ==>
    --(&(2 EXP 17) - &1) <= ival(EL i (MAP zunpack17 l)) /\
    ival(EL i (MAP zunpack17 l)) <= &(2 EXP 17)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_MAP] THEN
  REWRITE_TAC[ZUNPACK17_BOUND]);;

(* --- zunpack19: GAMMA1 = 2^19, 20-bit packed coefficients --- *)

let zunpack19 = new_definition
 `zunpack19 (x:(20)word) : (32)word =
  word_sub (word(2 EXP 19)) (word_zx x)`;;

let ZUNPACK19_CORRECT = prove(
  `!x:(20)word.
    word_sub (word 524288 : 32 word)
             (word_zx (x : 20 word) : 32 word) = zunpack19 x`,
  REWRITE_TAC[zunpack19] THEN CONV_TAC NUM_REDUCE_CONV);;

let ZUNPACK19_IVAL = prove(
 `!x:(20)word. ival(zunpack19 x) = &(2 EXP 19) - &(val x)`,
  GEN_TAC THEN REWRITE_TAC[zunpack19] THEN
  SUBGOAL_THEN `word_zx (x:20 word) : 32 word = word(val x)` SUBST1_TAC THENL
  [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
   CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
   REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV THEN
   MP_TAC(ISPEC `x:20 word` VAL_BOUND) THEN
   CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN SIMP_TAC[MOD_LT];
   ALL_TAC] THEN
  ONCE_REWRITE_TAC[WORD_IWORD] THEN
  REWRITE_TAC[GSYM IWORD_INT_SUB] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `x:20 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

let ZUNPACK19_BOUND = prove(
 `!x:(20)word. --(&(2 EXP 19) - &1) <= ival(zunpack19 x) /\
               ival(zunpack19 x) <= &(2 EXP 19)`,
  GEN_TAC THEN REWRITE_TAC[ZUNPACK19_IVAL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `x:20 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC);;

let ZUNPACK19_MAP_BOUND = prove(
 `!l:(20 word) list. !i. i < LENGTH l ==>
    --(&(2 EXP 19) - &1) <= ival(EL i (MAP zunpack19 l)) /\
    ival(EL i (MAP zunpack19 l)) <= &(2 EXP 19)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[EL_MAP] THEN
  REWRITE_TAC[ZUNPACK19_BOUND]);;

(* ========================================================================= *)
(* Helper lemmas: list operations                                            *)
(* ========================================================================= *)

let EL_SUB_LIST_GEN = prove(
 `!l:'a list. !i k n. i < n /\ k + n <= LENGTH l
   ==> EL i (SUB_LIST (k, n) l) = EL (k + i) l`,
  LIST_INDUCT_TAC THENL [
    REWRITE_TAC[LENGTH; LE; ADD_EQ_0] THEN ARITH_TAC;
    REWRITE_TAC[LENGTH] THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC (SPEC `k:num` num_CASES) THEN
    STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
    REWRITE_TAC[LT; SUB_LIST_CLAUSES; ADD_CLAUSES] THENL [
      STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
      REWRITE_TAC[EL; HD; TL; ADD_CLAUSES] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [`n:num`; `0`; `n':num`]) THEN
      REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[EL; TL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [`i:num`; `n':num`; `SUC n''`]) THEN
      ASM_REWRITE_TAC[LT_SUC] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let EL_SUB_LIST_CONV len_thm tm =
  let i_tm,sublist_tm = dest_comb tm in
  let el_const,i = dest_comb i_tm in
  let sublist_pair,ls = dest_comb sublist_tm in
  let sublist_const,pair_tm = dest_comb sublist_pair in
  let base,len = dest_pair pair_tm in
  let i_num = dest_numeral i and
      len_num = dest_numeral len in
  if i_num >= len_num then failwith "EL_SUB_LIST_CONV: index out of bounds" else
  let th1 = ISPECL [ls; i; base; len] EL_SUB_LIST_GEN in
  let th2 = REWRITE_RULE[len_thm] th1 in
  let th3 = MP th2 (EQT_ELIM(NUM_REDUCE_CONV (fst(dest_imp(concl th2))))) in
  CONV_RULE (RAND_CONV (LAND_CONV NUM_ADD_CONV)) th3;;

let LENGTH_SUB_LIST_0 = prove
 (`!n (l:'a list). n <= LENGTH l ==> LENGTH (SUB_LIST (0, n) l) = n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN ASM_ARITH_TAC);;

let SUB_LIST_SUB_LIST_0 = prove(
 `!k n m (l:'a list). k + n <= m /\ m <= LENGTH l
   ==> SUB_LIST (k, n) (SUB_LIST (0, m) l) = SUB_LIST (k, n) l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_SUB_LIST; SUB_0] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n' < n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC (ISPECL [`SUB_LIST (0,m) l:'a list`; `n':num`; `k:num`; `n:num`] EL_SUB_LIST_GEN) THEN
  MP_TAC (ISPECL [`l:'a list`; `n':num`; `k:num`; `n:num`] EL_SUB_LIST_GEN) THEN
  ASM_REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN
  SUBGOAL_THEN `k + n <= LENGTH (l:'a list)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k + n <= MIN m (LENGTH (l:'a list))` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC (ISPECL [`l:'a list`; `k + n':num`; `0`; `m:num`] EL_SUB_LIST_GEN) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let SUB_LIST_SPLIT_EQ = prove
 (`!n r (l:'a list). n + r = LENGTH l
   ==> APPEND (SUB_LIST (0, n) l) (SUB_LIST (n, r) l) = l`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`l:'a list`; `n:num`] SUB_LIST_TOPSPLIT) THEN
  FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN REWRITE_TAC[ADD_SUB2]);;

let APPEND_ITLIST_APPEND_NIL = prove
 (`!(l:('a list) list) (x:'a list). APPEND (ITLIST APPEND l []) x = ITLIST APPEND l x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; APPEND] THEN
  GEN_TAC THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN ASM_REWRITE_TAC[]);;

let LIST_OF_SEQ_EQ = prove
 (`!(f:num->'a) g n. (!i. i < n ==> f i = g i) ==> list_of_seq f n = list_of_seq g n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[list_of_seq] THEN
  DISCH_TAC THEN BINOP_TAC THENL [
    FIRST_X_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[CONS_11] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC
  ]);;

let SUBLIST_PARTITION = prove
 (`!r s (l:'a list). LENGTH l = r * s ==>
       l = ITLIST APPEND (list_of_seq (\i. SUB_LIST (r * i, r) l) s) []`,
  GEN_TAC THEN INDUCT_TAC THENL [
    REWRITE_TAC[MULT_CLAUSES; list_of_seq; ITLIST; LENGTH_EQ_NIL];
    REWRITE_TAC[list_of_seq; ITLIST_EXTRA; APPEND_NIL] THEN
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `SUB_LIST (0, r * s) l =
       ITLIST APPEND (list_of_seq (\i. SUB_LIST (r * i, r) (SUB_LIST (0, r * s) l)) s) []:'a list`
      ASSUME_TAC THENL [
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC LENGTH_SUB_LIST_0 THEN ASM_ARITH_TAC;
      ALL_TAC
    ] THEN
    SUBGOAL_THEN
      `list_of_seq (\i. SUB_LIST (r * i, r) (SUB_LIST (0, r * s) l):'a list) s =
       list_of_seq (\i. SUB_LIST (r * i, r) l) s`
      ASSUME_TAC THENL [
      MATCH_MP_TAC LIST_OF_SEQ_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SUB_LIST_SUB_LIST_0 THEN CONJ_TAC THENL [
        REWRITE_TAC[ARITH_RULE `r * i + r = r * (i + 1)`] THEN
        REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC
      ];
      ALL_TAC
    ] THEN
    SUBGOAL_THEN
      `APPEND (SUB_LIST (0, r * s) l) (SUB_LIST (r * s, r) l) = l:'a list`
      ASSUME_TAC THENL [
      MATCH_MP_TAC SUB_LIST_SPLIT_EQ THEN ASM_REWRITE_TAC[MULT_SUC] THEN ARITH_TAC;
      ALL_TAC
    ] THEN
    SUBGOAL_THEN
      `SUB_LIST (0, r * s) l =
       ITLIST APPEND (list_of_seq (\i. SUB_LIST (r * i, r) l) s) []:'a list`
      ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `APPEND (SUB_LIST (0,r * s) l) (SUB_LIST (r * s,r) l) = l:'a list` THEN
    UNDISCH_TAC `SUB_LIST (0,r * s) l = ITLIST APPEND (list_of_seq (\i. SUB_LIST (r * i,r) l) s) []:'a list` THEN
    SIMP_TAC[APPEND_ITLIST_APPEND_NIL]
  ]);;

(* ========================================================================= *)
(* Helper lemmas: word arithmetic                                            *)
(* ========================================================================= *)

let VAL_WORD_EXACT = prove(
  `!n. n < 2 EXP dimindex(:N) ==> val(word n : N word) = n`,
  REWRITE_TAC[VAL_WORD] THEN SIMP_TAC[MOD_LT]);;

let WORD_PACKED_EQ = prove(
 `!(x:N word) (y:N word).
    dimindex(:N) = l * k /\ 0 < l /\ l <= dimindex(:M)
    ==> (x = y <=>
         !i. i < k
             ==> word_subword x (l*i, l) : (M) word =
                 word_subword y (l*i, l))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
  [DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
   DISCH_TAC THEN
   GEN_REWRITE_TAC I [WORD_EQ_BITS_ALT] THEN
   X_GEN_TAC `j:num` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `j DIV l`) THEN
   ANTS_TAC THENL
   [UNDISCH_TAC `j < dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `0 < l ==> ~(l = 0)`; MULT_SYM];
    DISCH_THEN(fun th ->
      MP_TAC(AP_TERM `\(w:M word). bit (j MOD l) w` th)) THEN
    REWRITE_TAC[BIT_WORD_SUBWORD] THEN
    SUBGOAL_THEN `j MOD l < MIN l (dimindex(:M))`
      (fun th -> REWRITE_TAC[th]) THENL
    [ASM_SIMP_TAC[ARITH_RULE `l <= m ==> MIN l m = l`;
                   MOD_LT_EQ; ARITH_RULE `0 < l ==> ~(l = 0)`];
     ASM_SIMP_TAC[DIVISION_SIMP; ARITH_RULE `0 < l ==> ~(l = 0)`]]]]);;

let WORD_SUBWORD_NUM_OF_WORDLIST = prove
 (`!(ls:(L word)list) k.
    dimindex(:KL) = dimindex(:L) * LENGTH ls /\
    k < LENGTH ls
    ==> word_subword (word (num_of_wordlist ls) : KL word) (dimindex(:L)*k, dimindex(:L)) : L word = EL k ls`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD] THEN
  REWRITE_TAC[ARITH_RULE `MIN n n = n`] THEN
  SUBGOAL_THEN `val (word (num_of_wordlist (ls:(L word)list)) : KL word) = num_of_wordlist ls` SUBST1_TAC THENL
  [W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_EQ o lhand o snd) THEN
   ANTS_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (dimindex(:L) * LENGTH (ls:(L word)list))` THEN
    REWRITE_TAC[NUM_OF_WORDLIST_BOUND; LE_EXP; LE_REFL] THEN ASM_ARITH_TAC;
    SIMP_TAC[]];
   MP_TAC(ISPECL [`ls:(L word)list`; `k:num`] NUM_OF_WORDLIST_EL) THEN
   ASM_REWRITE_TAC[]]);;

let NUM_OF_WORDLIST_FLATTEN = prove
 (`!(ll:((N word) list) list) k.
     ALL (\l. LENGTH l = k) ll /\
     dimindex(:N) * k = dimindex(:M)
     ==> num_of_wordlist (ITLIST APPEND ll []) =
         num_of_wordlist (MAP ((word:num->M word) o num_of_wordlist) ll)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ITLIST; MAP; num_of_wordlist; ALL] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[NUM_OF_WORDLIST_APPEND; num_of_wordlist; o_THM] THEN
  ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  IMP_REWRITE_TAC [VAL_WORD_EXACT] THEN
  TRANS_TAC LTE_TRANS `2 EXP (dimindex(:N) * LENGTH(h:(N word)list))` THEN
  REWRITE_TAC[NUM_OF_WORDLIST_BOUND_LENGTH] THEN
  ASM_REWRITE_TAC[LE_REFL]);;

(* Unique decomposition of t into low k bits + high part. *)
let NUM_BIT_DECOMPOSE_UNIQ = prove(
  `!a b t k. a < 2 EXP k
    ==> (a + 2 EXP k * b = t <=> (a = t MOD 2 EXP k /\ b = t DIV 2 EXP k))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    ASM_SIMP_TAC[MOD_LT; DIV_LT; ADD_CLAUSES];
    STRIP_TAC THEN
    MP_TAC (SPECL [`t:num`; `2 EXP k`] DIVISION) THEN
    SIMP_TAC[EXP_EQ_0; ARITH_EQ] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* Split a byte-range read at an arbitrary interior offset k. *)
let READ_BYTES_SPLIT_ANY = prove(
  `read (bytes(a : int64,k+l)) s = t <=>
   read (bytes(a,k)) s = t MOD 2 EXP (8*k) /\
   read (bytes(word_add a (word k), l)) s = t DIV 2 EXP (8*k)`,
  let bound = prove(`read (bytes (a : int64,k)) s < 2 EXP (8*k)`,
    REWRITE_TAC[READ_BYTES_BOUND]) in
  REWRITE_TAC[GSYM VAL_EQ; VAL_READ_WBYTES; READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[READ_BYTES_COMBINE] THEN
  REWRITE_TAC[MATCH_MP NUM_BIT_DECOMPOSE_UNIQ bound]);;

(* ------------------------------------------------------------------------- *)
(* Generic wordlist chunk-split / subword-extract helper builders (used to    *)
(* instantiate the SIMD lane simplifications per coefficient bit-width).       *)
(* ------------------------------------------------------------------------- *)

(* Split ncoeffs d-bit coefficients into chunks of chunk_size *)
let mk_split_theorem d ncoeffs chunk_size =
  let total = d * chunk_size in
  let nchunks = ncoeffs / chunk_size in
  let d_ty = mk_finty (Num.num_of_int d) in
  let total_ty = mk_finty (Num.num_of_int total) in
  prove(
    subst [mk_small_numeral ncoeffs, `ncoeffs:num`;
           mk_small_numeral chunk_size, `cs:num`;
           mk_small_numeral nchunks, `nc:num`]
    (inst [d_ty, `:D`; total_ty, `:T`]
      `!(l: (D word) list). LENGTH l = ncoeffs ==>
         num_of_wordlist l = num_of_wordlist (MAP ((word:num->T word) o num_of_wordlist)
           (list_of_seq (\i. SUB_LIST (cs * i, cs) l) nc))`),
    REPEAT STRIP_TAC THEN
    UNDISCH_THEN (subst [mk_small_numeral ncoeffs, `n:num`]
      (inst [d_ty, `:D`] `LENGTH (l : (D word) list) = n`)) (fun th ->
       GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
         [MATCH_MP (CONV_RULE NUM_REDUCE_CONV
           (ISPECL [mk_small_numeral chunk_size; mk_small_numeral nchunks;
                    `l:'a list`] SUBLIST_PARTITION)) th]
       THEN ASSUME_TAC th) THEN
    IMP_REWRITE_TAC [CONV_RULE (ONCE_DEPTH_CONV DIMINDEX_CONV THENC NUM_REDUCE_CONV)
      (ISPECL [inst [d_ty, `:D`] `ll: ((D word) list) list`;
               mk_small_numeral chunk_size]
        (INST_TYPE [d_ty, `:N`; total_ty, `:M`] NUM_OF_WORDLIST_FLATTEN))] THEN
    CONV_TAC(ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) THEN
    ASM_REWRITE_TAC[ALL; LENGTH_SUB_LIST] THEN
    ARITH_TAC);;

(* Extract individual d-bit coefficients from (d*chunk_size)-bit word *)
let mk_subword_cases d chunk_size =
  let total = d * chunk_size in
  let d_ty = mk_finty (Num.num_of_int d) in
  let total_ty = mk_finty (Num.num_of_int total) in
  let arith_simp =
    let lhs = mk_eq(mk_small_numeral total,
                mk_comb(mk_comb(`( * ):num->num->num`,
                  mk_small_numeral d), `n:num`)) in
    let rhs = mk_eq(`n:num`, mk_small_numeral chunk_size) in
    ARITH_RULE (mk_eq(lhs, rhs)) in
  let meson_simp =
    let n_eq = mk_eq(`n:num`, mk_small_numeral chunk_size) in
    let k_lt_n = mk_comb(mk_comb(`(<):num->num->bool`, `k:num`), `n:num`) in
    let k_lt_cs = mk_comb(mk_comb(`(<):num->num->bool`, `k:num`),
                    mk_small_numeral chunk_size) in
    MESON[] (mk_eq(mk_conj(n_eq, k_lt_n), mk_conj(n_eq, k_lt_cs))) in
  let base =
    let th = INST_TYPE [total_ty, `:KL`; d_ty, `:L`] WORD_SUBWORD_NUM_OF_WORDLIST in
    let th = CONV_RULE(DEPTH_CONV DIMINDEX_CONV) th in
    REWRITE_RULE[arith_simp; meson_simp] th in
  let mk k =
    let th = SPEC (mk_small_numeral k)
      (SPEC (inst [d_ty, `:L`] `ls:(L word)list`) base) in
    CONV_RULE NUM_REDUCE_CONV (REWRITE_RULE[ARITH] th) in
  map mk (0 -- (chunk_size - 1));;

(* ========================================================================= *)
(* Shared infrastructure for the x86 AVX2 poly_use_hint_{32,88} proofs.      *)
(* Ported from mldsa-native's x86_64/proofs/mldsa_utils.ml. These are the    *)
(* generic (arch- and parameter-independent) block/lane framework lemmas and *)
(* Barrett DIV/MOD tactics shared by BOTH the 32 and 88 use_hint ports; the  *)
(* per-function bracket lemmas stay inline in the respective proof files.    *)
(* ========================================================================= *)

(* --- 256-bit-block / 8-lane framework (loop over 32 blocks of 8 int32) --- *)

(* Eight consecutive int32 coefficients packed into one 256-bit word. *)
let pack8 = new_definition
  `pack8 (f:num->int32) (b:num) : int256 =
     word_join
       (word_join (word_join (f (8*b+7)) (f (8*b+6)):int64)
                  (word_join (f (8*b+5)) (f (8*b+4)):int64):int128)
       (word_join (word_join (f (8*b+3)) (f (8*b+2)):int64)
                  (word_join (f (8*b+1)) (f (8*b+0)):int64):int128)`;;

(* Lane k (k<8) of a packed block is coefficient 8b+k. *)
let PACK8_LANE = prove(
  `!f b. !k. k < 8 ==> word_subword (pack8 f b) (32*k,32):int32 = f(8*b+k)`,
  GEN_TAC THEN GEN_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[pack8] THEN REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(* Lane k of a SIMD8 map is the scalar map applied to the corresponding lanes. *)
let SIMD8_LANE = prove(
  `!(g:int32->int32->int32) av hv. !k. k < 8 ==>
      word_subword (simd8 g av hv) (32*k,32):int32 =
      g (word_subword av (32*k,32)) (word_subword hv (32*k,32))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[simd8;simd4;simd2;DIMINDEX_32] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN CONV_TAC(DEPTH_CONV WORD_SIMPLE_SUBWORD_CONV) THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN REFL_TAC);;

(* Coefficient address 4*(8b+k) split into block base 32*b plus lane offset. *)
let ADDR_SPLIT = prove(
  `!p:int64 b k. word_add p (word(4*(8*b+k))) =
                 word_add (word_add p (word(32*b))) (word(4*k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ARITH_RULE `4*(8*b+k) = 32*b+4*k`] THEN
  CONV_TAC WORD_RULE);;

(* BLOCK_SPLIT and PACK8_MERGE are x86-specific (typed over x86state) and are
   therefore defined inline in the x86 use_hint proof files rather than here:
   this common file is shared with the AArch64 build, where an x86state-typed
   term fails to typecheck. *)

(* Two int256 words agree if all eight 32-bit lanes agree. *)
let LANES8_EQ = prove
 (`!x y:int256. (!k. k < 8 ==> word_subword x (32*k,32):int32 = word_subword y (32*k,32)) ==> x = y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MP_TAC(CONV_RULE(EXPAND_CASES_CONV THENC NUM_REDUCE_CONV) th)) THEN
  CONV_TAC WORD_BLAST);;

(* 32-byte blocks preserve 32-byte alignment of the base pointer. *)
let ALIGNED_32I = prove
 (`!i. aligned 32 (word(32*i):int64)`,
  GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64; VAL_WORD; DIMINDEX_64] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[DIVIDES_MOD] THEN CONV_TAC NUM_REDUCE_CONV;
    MP_TAC(SPECL [`32`; `32 * i`; `2 EXP 64`] DIVIDES_MOD2) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[DIVIDES_MOD] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN NUMBER_TAC]);;

let ALIGNED_BLOCK = prove
 (`!a:int64 i. aligned 32 a ==> aligned 32 (word_add a (word(32*i)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ALIGNED_WORD_ADD THEN
  ASM_REWRITE_TAC[ALIGNED_32I]);;

(* word_join of a zero high half is just zero-extension of the low half. *)
let JOIN_ZERO_ZX = prove
 (`!lo:(16)word. word_join (word 0:(16)word) lo :int32 = word_zx lo`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* word_ile/word_igt against 0 are complementary on int32. *)
let ILE_IGT = BITBLAST_RULE
  `!a0:int32. word_ile a0 (word 0) <=> ~(word_igt a0 (word 0))`;;

let WORD_NOT_0 = WORD_RULE `!x:N word. word_and x (word_not (word 0)) = x`;;

(* Per-step state compaction during SIMD body simulation: abbreviate every large
   int256 register value to a fresh atom so it propagates compactly (essential
   for instructions like VPBLENDVB whose byte-mux otherwise duplicates the value). *)
let ABBREV_BIG_TAC : tactic = fun (asl,w) ->
  MAP_EVERY (fun (_,th) -> AUTO_ABBREV_TAC (rand(concl th)))
    (filter (fun (_,th) -> let c=concl th in is_eq c &&
       (try is_comb(lhs c) && fst(dest_const(fst(strip_comb(lhs c))))="read"
            && type_of(lhs c)=`:int256` && not(is_var(rand c)) with _->false)
       && String.length(string_of_term(rand c)) > 1500) asl) (asl,w);;

(* --- Shared scalar UseHint lemmas (arch/parameter-independent) --- *)

(* Rounding division: ((q DIV n) + 1) DIV 2 = (q + n) DIV (2 * n). *)
let ROUND_DIV = prove(`!q n. ~(n = 0) ==> (q DIV n + 1) DIV 2 = (q + n) DIV (2 * n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(q + n) DIV (2 * n) = (q + n) DIV n DIV 2` SUBST1_TAC THENL
  [REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(q + n) DIV n = q DIV n + 1` (fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[DIV_ADD; DIVIDES_REFL] THEN ASM_SIMP_TAC[DIV_REFL]);;

(* The pre-shift t = (a + 127) >>u 7 has value (val a + 127) DIV 128. *)
let VAL_T = prove(`!x:int32. val x < 8380417
   ==> val(word_ushr (word_add (word 127) x) 7 :int32) = (val x + 127) DIV 128`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD_USHR] THEN
  SUBGOAL_THEN `val(word_add (word 127:int32) x) = val x + 127` SUBST1_TAC THENL
  [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
   SUBGOAL_THEN `(127 + val(x:int32)) MOD 4294967296 = 127 + val x`
     (fun th -> REWRITE_TAC[th] THEN ARITH_TAC) THEN
   MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `x:int32` VAL_BOUND) THEN
   REWRITE_TAC[DIMINDEX_32] THEN ASM_ARITH_TAC;
   REWRITE_TAC[ARITH_RULE `2 EXP 7 = 128`]]);;

(* Bounded 16->32 sign-extension equals the value for a 16-bit lane below 2^15. *)
let VAL_WORD_SX_SMALL = prove(`!u:16 word. val u < 32768
   ==> val((word_sx u):int32) = val u`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(word_sx (u:16 word)):int32 = word_zx u` SUBST1_TAC THENL
  [REWRITE_TAC[WORD_SX_ZX_GEN; DIMINDEX_16] THEN
   CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
   SUBGOAL_THEN `bit 15 (u:16 word) = F` SUBST1_TAC THENL
   [REWRITE_TAC[BIT_VAL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[BITVAL_CLAUSES;
               WORD_REDUCE_CONV `word_shl (word_neg (word 0:int32)) 16`;
               WORD_OR_0]; ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `val(u:16 word) MOD 4294967296 = val u` (fun th->REWRITE_TAC[th]) THEN
  MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `u:16 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_16] THEN ARITH_TAC);;

(* delta encoding bridge (needs the hint bound val h <= 1). *)
let DELTA_EQ_BOUNDED = prove
 (`!a0:int32 h:int32. val h <= 1 ==>
     word_sub h (word_shl (word_and (word_not
        (if word_igt a0 (word 0) then word 4294967295 else word 0)) h) 1) =
     word_mul (word_or (word_neg (word (bitval (word_ile a0 (word 0))))) (word 1)) h`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ILE_IGT] THEN
  SUBGOAL_THEN `h:int32 = word 0 \/ h = word 1` STRIP_ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN SPEC_TAC(`h:int32`,`h:int32`) THEN
    REWRITE_TAC[GSYM VAL_EQ_0; GSYM VAL_EQ_1] THEN ARITH_TAC;
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST;
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST]);;

(* --- Barrett-quotient DIV/MOD tactics over the per-variant divisor 2*GAMMA2 --- *)
(* (523776 for use_hint_32, 190464 for use_hint_88). Each proof aliases these    *)
(* at its concrete divisor gg.                                                    *)

(* Eliminate `r MOD gg` / `r DIV gg` and abstract them for ASM_ARITH_TAC. *)
let LINEARIZE_DIV_MOD_BY_TAC gg =
  let s = subst [mk_small_numeral gg, `gg:num`] in
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    free_in (s `r MOD gg`) (concl th) || free_in (s `r DIV gg`) (concl th)))) THEN
  MP_TAC(SPECL [`r:num`; mk_small_numeral gg] (CONJUNCT1 DIVISION_SIMP)) THEN
  SPEC_TAC(s `r MOD gg`, `m:num`) THEN
  SPEC_TAC(s `r DIV gg`, `q:num`) THEN
  REPEAT GEN_TAC THEN ASM_ARITH_TAC;;

(* Replace `(r - r MOD gg) DIV gg` with `r DIV gg`. *)
let DIV_MOD_TO_DIV_BY_TAC gg =
  let s = subst [mk_small_numeral gg, `gg:num`] in
  SUBGOAL_THEN (s `(r - r MOD gg) DIV gg = r DIV gg`) SUBST1_TAC THENL
  [MP_TAC(SPECL [`r:num`; mk_small_numeral gg] (CONJUNCT1 DIVISION_SIMP)) THEN
   DISCH_TAC THEN
   SUBGOAL_THEN (s `r - r MOD gg = gg * r DIV gg`) SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [mk_small_numeral gg; s `r DIV gg`] DIV_MULT) THEN
   CONV_TAC NUM_REDUCE_CONV; ALL_TAC];;

(* Prove `r DIV gg = k` via DIV_SANDWICH + LE_MULT_RCANCEL. *)
let DIV_EQ_K_BY_TAC gg k =
  let s = subst [mk_small_numeral gg, `gg:num`] in
  let k_num = mk_small_numeral k and km1 = mk_small_numeral (k-1)
  and kp1 = mk_small_numeral (k+1)
  and q = mk_var("q",`:num`) and le = `(<=):num->num->bool`
  and lt = `(<):num->num->bool` and c = mk_small_numeral gg in
  let mk_mul a b = mk_binop (rator(rator `0*0`)) a b in
  MATCH_MP_TAC DIV_SANDWICH THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    free_in (s `r MOD gg`) (concl th) || free_in (s `r DIV gg`) (concl th)))) THEN
  MP_TAC(SPECL [`r:num`; c] (CONJUNCT1 DIVISION_SIMP)) THEN
  SPEC_TAC(s `r MOD gg`, `m:num`) THEN
  SPEC_TAC(s `r DIV gg`, q) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC(mk_comb(mk_comb(le, q), km1)) THENL
  [SUBGOAL_THEN(mk_comb(mk_comb(le, mk_mul q c), mk_mul km1 c)) ASSUME_TAC THENL
   [ASM_SIMP_TAC[LE_MULT_RCANCEL]; ALL_TAC] THEN
   CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
   SUBGOAL_THEN(mk_comb(mk_comb(le, mk_mul k_num c), mk_mul q c)) ASSUME_TAC THENL
   [ASM_SIMP_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_CASES_TAC(mk_comb(mk_comb(lt, k_num), q)) THENL
   [SUBGOAL_THEN(mk_comb(mk_comb(le, mk_mul kp1 c), mk_mul q c)) ASSUME_TAC THENL
    [ASM_SIMP_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC]];;
