(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Generic stuff about bignums. This works for x86 and ARM, but is not quite *)
(* loadable independently since it uses the "memory" component.              *)
(* ========================================================================= *)

let bigdigit = new_definition
 `bigdigit n i = (n DIV (2 EXP (64 * i))) MOD (2 EXP 64)`;;

let BIGDIGITSUM_WORKS_GEN = prove
 (`!n k. nsum {i | i < k} (\i. 2 EXP (64 * i) * bigdigit n i) =
         n MOD (2 EXP (64 * k))`,
  REWRITE_TAC[bigdigit; EXP_MULT; DIGITSUM_WORKS_GEN]);;

let BIGDIGITSUM_WORKS = prove
 (`!n k. n < 2 EXP (64 * k)
         ==> nsum {i | i < k} (\i. 2 EXP (64 * i) * bigdigit n i) = n`,
  REWRITE_TAC[bigdigit; EXP_MULT; DIGITSUM_WORKS]);;

let BIGDIGIT_BOUND = prove
 (`!n i. bigdigit n i < 2 EXP 64`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bigdigit] THEN
  REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ]);;

let VAL_WORD_BIGDIGIT = prove
 (`!n i. val(word(bigdigit n i):int64) = bigdigit n i`,
  SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND]);;

let BIGDIGIT_0 = prove
 (`!i. bigdigit 0 i = 0`,
  REWRITE_TAC[bigdigit; DIV_0; MOD_0]);;

let BIGDIGIT_ZERO = prove
 (`!n i. n < 2 EXP (64 * i) ==> bigdigit n i = 0`,
  SIMP_TAC[bigdigit; DIV_LT; MOD_0]);;

let BIGDIGIT_ADD_LEFT =
  prove(`forall a n b i.
  i < n ==> bigdigit (a + 2 EXP (64 * n) * b) i = bigdigit a i`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bigdigit] THEN
  SUBGOAL_THEN `2 EXP (64 * n) = 2 EXP (64 * i) * (2 EXP (64 * (n-i)))` SUBST_ALL_TAC THENL [
    REWRITE_TAC[GSYM EXP_ADD] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;

    REWRITE_TAC[GSYM MULT_ASSOC] THEN
    IMP_REWRITE_TAC[DIV_MULT_ADD; EXP_2_NE_0] THEN
    SUBGOAL_THEN
      `2 EXP (64*(n-i)) = 2 EXP 64 * (2 EXP (64*(n-i-1)))`
      SUBST_ALL_TAC THENL [
      REWRITE_TAC[GSYM EXP_ADD] THEN
      AP_TERM_TAC THEN ASM_ARITH_TAC;

      ALL_TAC
    ] THEN
    REWRITE_TAC[GSYM MULT_ASSOC] THEN
    IMP_REWRITE_TAC[MOD_MULT_ADD; EXP_2_NE_0]]);;

let BIGDIGIT_SUC = prove(`forall n i t.
  t < 2 EXP 64 ==> bigdigit (t + 2 EXP 64 * n) (SUC i) = bigdigit n i`,

  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bigdigit;ARITH_RULE`SUC i = 1 + i`;LEFT_ADD_DISTRIB;EXP_ADD;GSYM DIV_DIV;
              ARITH_RULE`64 * 1 = 64`] THEN
  IMP_REWRITE_TAC[DIV_MULT_ADD;EXP_2_NE_0;SPECL [`t:num`;`2 EXP 64`] DIV_LT] THEN
  REWRITE_TAC[ADD]);;

let highdigits = new_definition
 `highdigits n i = n DIV (2 EXP (64 * i))`;;

let lowdigits = new_definition
 `lowdigits n i = n MOD (2 EXP (64 * i))`;;

let HIGH_LOW_DIGITS = prove
 (`(!n i. 2 EXP (64 * i) * highdigits n i + lowdigits n i = n) /\
   (!n i. lowdigits n i + 2 EXP (64 * i) * highdigits n i = n) /\
   (!n i. highdigits n i * 2 EXP (64 * i) + lowdigits n i = n) /\
   (!n i. lowdigits n i + highdigits n i * 2 EXP (64 * i) = n)`,
  REWRITE_TAC[lowdigits; highdigits] THEN
  MESON_TAC[DIVISION_SIMP; ADD_SYM; MULT_SYM]);;

let HIGHDIGITS_CLAUSES = prove
 (`(!n. highdigits n 0 = n) /\
   (!n i. highdigits n (i + 1) = highdigits n i DIV 2 EXP 64)`,
  REWRITE_TAC[highdigits; LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
  REWRITE_TAC[EXP; DIV_1; EXP_ADD; GSYM DIV_DIV]);;

let HIGHDIGITS_STEP = prove
 (`!n i. highdigits n i = 2 EXP 64 * highdigits n (i + 1) + bigdigit n i`,
  REWRITE_TAC[highdigits; bigdigit; LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN ARITH_TAC);;

let LOWDIGITS_CLAUSES = prove
 (`(!n. lowdigits n 0 = 0) /\
   (!n i. lowdigits n (i + 1) =
          2 EXP (64 * i) * bigdigit n i + lowdigits n i)`,
  REWRITE_TAC[lowdigits; highdigits; bigdigit; EXP; MOD_1; MULT_CLAUSES] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; EXP_ADD; MOD_MULT_MOD]);;

let HIGHDIGITS_EQ_0 = prove
 (`!n i. highdigits n i = 0 <=> n < 2 EXP (64 * i)`,
  SIMP_TAC[highdigits; DIV_EQ_0; EXP_EQ_0; ARITH_EQ]);;

let HIGHDIGITS_0 = prove
 (`!n. highdigits n 0 = n`,
  REWRITE_TAC[HIGHDIGITS_CLAUSES]);;

let HIGHDIGITS_ZERO = prove
 (`!n i. n < 2 EXP (64 * i) ==> highdigits n i = 0`,
  REWRITE_TAC[HIGHDIGITS_EQ_0]);;

let HIGHDIGITS_TRIVIAL = prove
 (`!n. highdigits 0 n = 0`,
  REWRITE_TAC[highdigits; DIV_0]);;

let LOWDIGITS_0 = prove
 (`!n. lowdigits n 0 = 0`,
  REWRITE_TAC[LOWDIGITS_CLAUSES]);;

let LOWDIGITS_1 = prove
 (`!n. lowdigits n 1 = bigdigit n 0`,
  SUBST1_TAC(ARITH_RULE `1 = 0 + 1`) THEN
  REWRITE_TAC[LOWDIGITS_CLAUSES; LOWDIGITS_0] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES]);;

let HIGHDIGITS_TOP = prove
 (`!n k. n < 2 EXP (64 * k) ==> highdigits n (k - 1) = bigdigit n (k - 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[highdigits; bigdigit] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
  TRANS_TAC LTE_TRANS `2 EXP (64 * k)` THEN
  ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC);;

let LOWDIGITS_BOUND = prove
 (`!n i. lowdigits n i < 2 EXP (64 * i)`,
  REWRITE_TAC[lowdigits; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ]);;

let LOWDIGITS_EQ_SELF = prove
 (`!n i. lowdigits n i = n <=> n < 2 EXP (64 * i)`,
  SIMP_TAC[lowdigits; MOD_EQ_SELF; EXP_EQ_0; ARITH_EQ]);;

let LOWDIGITS_SELF = prove
 (`!n i. n < 2 EXP (64 * i) ==> lowdigits n i = n`,
  REWRITE_TAC[LOWDIGITS_EQ_SELF]);;

let LOWDIGITS_TRIVIAL = prove
 (`!n. lowdigits 0 n = 0`,
  REWRITE_TAC[lowdigits; MOD_0]);;

let LOWDIGITS_LE = prove
 (`!n i. lowdigits n i <= n`,
  REWRITE_TAC[lowdigits; MOD_LE]);;

let LOWDIGITS_LOWDIGITS = prove
 (`!n i j. lowdigits (lowdigits n i) j = lowdigits n (MIN i j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lowdigits; MOD_MOD_EXP_MIN] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let BIGDIGIT_HIGHDIGITS = prove
 (`!n i j. bigdigit (highdigits n i) j = bigdigit n (i + j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bigdigit; highdigits] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; DIV_DIV]);;

let HIGHDIGITS_HIGHDIGITS = prove
 (`!n i j. highdigits (highdigits n i) j = highdigits n (i + j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[highdigits] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; DIV_DIV]);;

let BIGDIGIT_LOWDIGITS = prove
 (`!n i j. bigdigit (lowdigits n i) j = if j < i then bigdigit n j else 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bigdigit; lowdigits] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `j < i ==> MIN (64 * i) (64 * j + 64) = 64 * j + 64`];
    MATCH_MP_TAC(MESON[MOD_0] `x = 0 ==> x MOD n = 0`) THEN
    SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LTE_TRANS `2 EXP (64 * i)` THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ; LE_EXP] THEN ASM_ARITH_TAC]);;

let BIGDIGIT_DIV = prove
 (`!a i e.
     e <= 64
     ==> bigdigit (a DIV 2 EXP e) i =
         2 EXP (64 - e) * bigdigit a (i + 1) MOD 2 EXP e +
         bigdigit a i DIV 2 EXP e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bigdigit] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIV_DIV] THEN
  REWRITE_TAC[GSYM DIV_DIV; EXP_ADD; ARITH_RULE
   `64 * (i + 1) = 64 * i + 64`] THEN
  SPEC_TAC(`a DIV 2 EXP (64 * i)`,`a:num`) THEN GEN_TAC THEN
  ASM_SIMP_TAC[MOD_MOD_EXP_MIN; ARITH_RULE `e <= 64 ==> MIN 64 e = e`] THEN
  GEN_REWRITE_TAC (funpow 3 LAND_CONV)
   [ARITH_RULE `a = 2 EXP 64 * a DIV 2 EXP 64 + a MOD 2 EXP 64`] THEN
  MP_TAC(ARITH_RULE `a MOD 2 EXP 64 < 2 EXP 64`) THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIV_MOD_DISJOINT_BITS; DISJOINT_BITS_CLAUSES] THEN
  BINOP_TAC THENL [ALL_TAC; ASM_MESON_TAC[MOD_LT; DIV_LE; LET_TRANS]] THEN
  REWRITE_TAC[DIV_MOD; MOD_MULT2;
              ARITH_RULE `e * 2 EXP 64 = 2 EXP 64 * e`] THEN
  ASM_SIMP_TAC[MULT_DIV; DIVIDES_EXP_LE_IMP; DIV_EXP; ARITH_EQ]);;

let WORD_BIGDIGIT_DIV = prove
 (`!a i e.
        e <= 64
        ==> word(bigdigit (a DIV 2 EXP e) i):int64 =
            word_subword ((word_join:int64->int64->int128)
                          (word (bigdigit a (i + 1))) (word (bigdigit a i)))
                         (e,64)`,
  SIMP_TAC[GSYM VAL_EQ; VAL_WORD_BIGDIGIT; VAL_WORD_SUBWORD_JOIN_64;
           DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
  REWRITE_TAC[BIGDIGIT_DIV]);;

(* ------------------------------------------------------------------------- *)
(* Mapping little-endian word list to/from natural number (general size).    *)
(* ------------------------------------------------------------------------- *)

let num_of_wordlist = define
 `num_of_wordlist ([]:(N word) list) = 0 /\
  num_of_wordlist (CONS (h:N word) t) =
     val h + 2 EXP dimindex(:N) * num_of_wordlist t`;;

let wordlist_of_num = define
 `(wordlist_of_num 0 n :(N word)list = []) /\
  (wordlist_of_num (SUC k) n =
     CONS (word(n MOD 2 EXP dimindex(:N)):N word)
          (wordlist_of_num k (n DIV 2 EXP dimindex(:N))))`;;

let NUM_OF_WORDLIST_SING = prove
 (`!h:N word. num_of_wordlist [h] = val h`,
  REWRITE_TAC[num_of_wordlist; MULT_CLAUSES; ADD_CLAUSES]);;

let NUM_OF_WORDLIST_APPEND = prove
 (`!lis1 lis2:(N word)list.
        num_of_wordlist(APPEND lis1 lis2) =
        num_of_wordlist lis1 +
        2 EXP (dimindex(:N) * LENGTH lis1) * num_of_wordlist lis2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; num_of_wordlist] THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES] THEN
  REWRITE_TAC[EXP_ADD] THEN ARITH_TAC);;

let NUM_OF_WORDLIST_BOUND_LENGTH = prove
 (`!l:(N word)list. num_of_wordlist l < 2 EXP (dimindex(:N) * LENGTH l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; num_of_wordlist] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; EXP_ADD; ARITH] THEN
  W(MP_TAC o PART_MATCH lhand VAL_BOUND o lhand o lhand o snd) THEN
  MATCH_MP_TAC(ARITH_RULE
   `n * (x + 1) <= y ==> h < n ==> h + n * x < y`) THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let NUM_OF_WORDLIST_BOUND = prove
 (`!l:(N word)list n.
        LENGTH l <= n ==> num_of_wordlist l < 2 EXP (dimindex(:N) * n)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LTE_TRANS `2 EXP (dimindex(:N) * LENGTH(l:(N word)list))` THEN
  ASM_REWRITE_TAC[NUM_OF_WORDLIST_BOUND_LENGTH; LE_EXP; LE_MULT_LCANCEL] THEN
  ASM_ARITH_TAC);;

let NUM_OF_WORDLIST_BOUND_GEN = prove
 (`!l:((N word)list) n.
        dimindex(:N) * LENGTH l <= n ==> num_of_wordlist l < 2 EXP n`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH lhand NUM_OF_WORDLIST_BOUND_LENGTH o
    lhand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LTE_TRANS) THEN
  ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC);;

let NUM_OF_WORDLIST_DIV = prove
 (`!(w:N word) ws.
        num_of_wordlist (CONS w ws) DIV 2 EXP dimindex(:N) =
        num_of_wordlist ws`,
  SIMP_TAC[num_of_wordlist; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  SIMP_TAC[DIV_LT; VAL_BOUND; ADD_CLAUSES]);;

let NUM_OF_WORDLIST_MOD = prove
 (`!(w:N word) ws.
        num_of_wordlist (CONS w ws) MOD 2 EXP dimindex(:N) = val w`,
  REWRITE_TAC[num_of_wordlist; MOD_MULT_ADD] THEN
  SIMP_TAC[MOD_LT; VAL_BOUND]);;

let NUM_OF_WORDLIST_ZAP = prove
 (`!l:(N word)list.
        2 EXP dimindex(:N) * num_of_wordlist l =
        num_of_wordlist(CONS (word 0) l)`,
  REWRITE_TAC[num_of_wordlist; VAL_WORD_0; ADD_CLAUSES]);;

let LENGTH_WORDLIST_OF_NUM = prove
 (`!k n. LENGTH(wordlist_of_num k n:(N word)list) = k`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[wordlist_of_num; LENGTH]);;

let NUM_OF_WORDLIST_BOUND = prove
 (`!l:(N word)list. num_of_wordlist l < 2 EXP (dimindex(:N) * LENGTH l)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[LENGTH; num_of_wordlist; ARITH; EXP; MULT_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`h:N word`; `t:(N word)list`] THEN DISCH_TAC THEN
  REWRITE_TAC[EXP_ADD] THEN  MATCH_MP_TAC(ARITH_RULE
     `h < n /\ n * (t + 1) <= n * e
      ==> h + n * t < n * e`) THEN
  REWRITE_TAC[VAL_BOUND; LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let WORDLIST_OF_NUM_OF_WORDLIST = prove
 (`!l:(N word)list. wordlist_of_num (LENGTH l) (num_of_wordlist l) = l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[num_of_wordlist; wordlist_of_num; LENGTH] THEN FIRST_X_ASSUM
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  SIMP_TAC[CONS_11; MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ; WORD_VAL_GALOIS;
           EXP_EQ_0; MOD_MOD_REFL; MOD_EQ_SELF] THEN
  SIMP_TAC[VAL_BOUND; DIV_LT; ADD_CLAUSES]);;

let NUM_OF_WORDLIST_OF_NUM_0 = prove
 (`!k. num_of_wordlist(wordlist_of_num k 0:(N word)list) = 0`,
  INDUCT_TAC THEN SIMP_TAC[num_of_wordlist; wordlist_of_num] THEN
  ASM_REWRITE_TAC[VAL_WORD_0; DIV_0; MOD_0; MULT_CLAUSES; ADD_CLAUSES]);;

let NUM_OF_WORDLIST_OF_NUM = prove
 (`!k n. num_of_wordlist(wordlist_of_num k n:(N word)list) =
         n MOD 2 EXP (dimindex(:N) * k)`,
  INDUCT_TAC THEN REWRITE_TAC[num_of_wordlist] THENL
   [REWRITE_TAC[wordlist_of_num; num_of_wordlist; EXP; MOD_1; MULT_CLAUSES];
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN ASM_REWRITE_TAC[wordlist_of_num; num_of_wordlist] THEN
  REWRITE_TAC[EXP_ADD; ARITH_RULE `n * SUC k = n + n * k`; MOD_MULT_MOD] THEN
  REWRITE_TAC[VAL_WORD; MOD_MOD_REFL] THEN ARITH_TAC);;

let WORDLIST_OF_NUM_MOD = prove
 (`!k n. wordlist_of_num k (n MOD 2 EXP (dimindex(:N) * k)):(N word)list =
         wordlist_of_num k n`,
  REPEAT GEN_TAC THEN REWRITE_TAC [GSYM NUM_OF_WORDLIST_OF_NUM] THEN
  REWRITE_TAC [REWRITE_RULE [LENGTH_WORDLIST_OF_NUM]
    (SPEC `wordlist_of_num k n:(N word)list` WORDLIST_OF_NUM_OF_WORDLIST)]);;

let NUM_OF_WORDLIST_OF_NUM_EQ_SELF = prove
 (`!k n. n < 2 EXP (dimindex(:N) * k)
         ==> num_of_wordlist(wordlist_of_num k n:(N word)list) = n`,
  SIMP_TAC[NUM_OF_WORDLIST_OF_NUM; MOD_LT]);;

let NUM_OF_WORDLIST_LT = prove
 (`!(m0:N word) m1 (n0:N word) n1.
        num_of_wordlist(CONS m0 m1) < num_of_wordlist(CONS n0 n1) <=>
        num_of_wordlist m1 < num_of_wordlist n1 \/
        num_of_wordlist m1 = num_of_wordlist n1 /\ val m0 < val n0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_wordlist] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_LT THEN REWRITE_TAC[VAL_BOUND]);;

let NUM_OF_WORDLIST_LE = prove
 (`!(m0:N word) m1 (n0:N word) n1.
        num_of_wordlist(CONS m0 m1) <= num_of_wordlist(CONS n0 n1) <=>
        num_of_wordlist m1 < num_of_wordlist n1 \/
        num_of_wordlist m1 = num_of_wordlist n1 /\ val m0 <= val n0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_wordlist] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_LE THEN REWRITE_TAC[VAL_BOUND]);;

let NUM_OF_WORDLIST_EQ = prove
 (`!(m0:N word) m1 (n0:N word) n1.
        num_of_wordlist(CONS m0 m1) = num_of_wordlist(CONS n0 n1) <=>
        m0 = n0 /\ num_of_wordlist m1 = num_of_wordlist n1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[num_of_wordlist] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_EQ THEN REWRITE_TAC[VAL_BOUND]);;

let NUM_OF_WORDLIST_SUB_LIST_0 = prove
 (`!(l:(N word)list) n.
        num_of_wordlist(SUB_LIST(0,n) l) =
        num_of_wordlist l MOD 2 EXP (dimindex(:N) * n)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist; DIV_0; MOD_0] THEN
  MAP_EVERY X_GEN_TAC [`h:N word`; `t:(N word)list`] THEN
  DISCH_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  ASM_REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1] THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[MOD_UNIQUE] THEN
  REWRITE_TAC[EXP_ADD] THEN CONJ_TAC THENL
   [DISJ2_TAC THEN MATCH_MP_TAC(ARITH_RULE
     `h < n /\ n * (t + 1) <= n * e
      ==> h + n * t < n * e`) THEN
    REWRITE_TAC[VAL_BOUND; LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    REWRITE_TAC[ARITH_RULE `n + 1 <= m <=> n < m`; MOD_LT_EQ] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
    MATCH_MP_TAC(NUMBER_RULE
     `(t == t') (mod d)
      ==> (h + e * t == h + e * t') (mod (e * d))`) THEN
    REWRITE_TAC[CONG_RMOD; CONG_REFL]]);;

let NUM_OF_WORDLIST_SUB_LIST = prove
 (`!(l:(N word)list) m n.
        num_of_wordlist (SUB_LIST(m,n) l) =
        (num_of_wordlist l DIV 2 EXP (dimindex(:N) * m)) MOD
        2 EXP (dimindex(:N) * n)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist; DIV_0; MOD_0] THEN
  MAP_EVERY X_GEN_TAC [`h:N word`; `t:(N word)list`] THEN
  DISCH_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST_0; GSYM(CONJUNCT2 num_of_wordlist);
              EXP; DIV_1; MULT_CLAUSES] THEN
  ASM_REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist] THEN
  X_GEN_TAC `m:num` THEN DISCH_THEN(K ALL_TAC) THEN X_GEN_TAC `n:num` THEN
  SIMP_TAC[EXP_ADD; GSYM DIV_DIV; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  SIMP_TAC[DIV_LT; VAL_BOUND; ADD_CLAUSES]);;

let NUM_OF_WORDLIST_EL = prove
 (`!(l:(N word)list) n.
        (num_of_wordlist l DIV 2 EXP (dimindex(:N) * n)) MOD
        2 EXP (dimindex(:N)) =
        if n < LENGTH l then val(EL n l) else 0`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`l:(N word)list`; `n:num`; `1`]
   NUM_OF_WORDLIST_SUB_LIST) THEN
  REWRITE_TAC[SUB_LIST_1; MULT_CLAUSES] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN COND_CASES_TAC THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SING; num_of_wordlist]);;

let EL_NUM_OF_WORDLIST = prove
 (`!(l:(N word)list) n.
        n < LENGTH l
        ==> EL n l = word(num_of_wordlist l DIV 2 EXP (dimindex(:N) * n))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`l:(N word)list`; `n:num`] NUM_OF_WORDLIST_EL) THEN
  ASM_REWRITE_TAC[WORD_VAL_GALOIS]);;

let LISTS_NUM_OF_WORDLIST_EQ = prove
 (`!l1 l2:(N word)list.
        l1 = l2 <=>
        LENGTH l1 = LENGTH l2 /\
        num_of_wordlist l1 = num_of_wordlist l2`,
  MESON_TAC[WORDLIST_OF_NUM_OF_WORDLIST]);;

let BYTES_EQ_NUM_OF_WORDLIST_EXPAND = prove
 (`!m (a:int64) len (s:S) (h:((((N)tybit0)tybit0)tybit0) word) t.
    dimindex(:N) <= len
    ==> (read (m :> bytes(a,len)) s = num_of_wordlist (CONS h t) <=>
         read (m :> wbytes a) s = h /\
         read (m :> bytes(word_add a (word(dimindex(:N))),len-dimindex(:N))) s=
         num_of_wordlist t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_READ_WBYTES; READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[num_of_wordlist; DIMINDEX_TYBIT0] THEN
  REWRITE_TAC[ARITH_RULE `2 * 2 * 2 * n = 8 * n`] THEN
  REWRITE_TAC[ARITH_RULE `(8 * n) DIV 8 = n`] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
   `d:num <= l ==> l = d + (l - d)`)) THEN
  REWRITE_TAC[READ_BYTES_COMBINE; ADD_SUB2] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_EQ THEN REWRITE_TAC[READ_BYTES_BOUND] THEN
  W(MP_TAC o PART_MATCH lhand VAL_BOUND o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_TYBIT0; ARITH_RULE `2 * 2 * 2 * n = 8 * n`]);;

let BYTES_EQ_NUM_OF_WORDLIST_APPEND = prove
 (`!m (a:int64) (s:S) lis1 (lis2:(N word)list) len1 len2.
        dimindex(:N) * LENGTH lis1 = 8 * len1
        ==>  (read (m :> bytes(a,len1+len2)) s =
              num_of_wordlist(APPEND lis1 lis2) <=>
              read (m :> bytes(a,len1)) s = num_of_wordlist lis1 /\
              read (m :> bytes(word_add a (word len1),len2)) s =
              num_of_wordlist lis2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  ASM_REWRITE_TAC[NUM_OF_WORDLIST_APPEND] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_EQ THEN REWRITE_TAC[READ_BYTES_BOUND] THEN
  MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN ASM_REWRITE_TAC[LE_REFL]);;

let BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV =
  let pth = prove
   (`!m (a:int64) len (s:S) (h:((((N)tybit0)tybit0)tybit0) word).
        dimindex(:N) = len
        ==> (read (m :> bytes(a,len)) s = num_of_wordlist [h] <=>
             read (m :> wbytes a) s = h)`,
    SIMP_TAC[BYTES_EQ_NUM_OF_WORDLIST_EXPAND; LE_REFL] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; SUB_REFL; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[num_of_wordlist]) in
  let frule = PART_MATCH (lhand o rand) pth
  and brule = PART_MATCH (lhand o rand) BYTES_EQ_NUM_OF_WORDLIST_EXPAND in
  let baseconv tm =
    let ith = frule tm in
    let sth = (LAND_CONV DIMINDEX_CONV THENC NUM_EQ_CONV)
              (lhand(concl ith)) in
    MP ith (EQT_ELIM sth) in
  let rec conv tm =
    try baseconv tm with Failure _ ->
    let ith = brule tm in
    let dth = DIMINDEX_CONV(lhand(lhand(concl ith))) in
    let ith' = SUBS[dth] ith in
    let ath = MP ith' (EQT_ELIM(NUM_LE_CONV(lhand(concl ith')))) in
    let bth = CONV_RULE(RAND_CONV(RAND_CONV(LAND_CONV(LAND_CONV(RAND_CONV
               (RAND_CONV
                 (BINOP2_CONV (TRY_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                              NUM_SUB_CONV))))))) ath in
    CONV_RULE(RAND_CONV(RAND_CONV conv)) bth in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Mapping a little-endian word list into a number (64-bit case of above).   *)
(* ------------------------------------------------------------------------- *)

let bignum_of_list = define
 `bignum_of_list [] = 0 /\
  bignum_of_list (CONS h t) = h + 2 EXP 64 * bignum_of_list t`;;

let bignum_of_wordlist = define
 `bignum_of_wordlist [] = 0 /\
  bignum_of_wordlist (CONS (h:int64) t) =
     val h + 2 EXP 64 * bignum_of_wordlist t`;;

bounder_prenorm_thms := union [bignum_of_wordlist] (!bounder_prenorm_thms);;

let BIGNUM_OF_WORDLIST_DIV = prove
 (`!w ws. bignum_of_wordlist (CONS w ws) DIV 2 EXP 64 = bignum_of_wordlist ws`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bignum_of_wordlist] THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; EQ_ADD_RCANCEL_0; DIV_EQ_0] THEN
  W(MP_TAC o PART_MATCH lhand VAL_BOUND o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_64]);;

let BIGNUM_OF_WORDLIST_SING = prove
 (`!w. bignum_of_wordlist [w] = val w`,
  REWRITE_TAC[bignum_of_wordlist] THEN ARITH_TAC);;

let BIGNUM_OF_WORDLIST_MOD = prove
 (`!w ws. bignum_of_wordlist (CONS w ws) MOD 2 EXP 64 = val w`,
  REWRITE_TAC[bignum_of_wordlist; MOD_MULT_ADD] THEN
  SIMP_TAC[MOD_LT; VAL_BOUND_64]);;

let BIGNUM_OF_WORDLIST_ZAP = prove
 (`!l. 2 EXP 64 * bignum_of_wordlist l = bignum_of_wordlist(CONS (word 0) l)`,
  REWRITE_TAC[bignum_of_wordlist; VAL_WORD_0] THEN ARITH_TAC);;

let BIGNUM_OF_WORDLIST_BOUND_LENGTH = prove
 (`!l. bignum_of_wordlist l < 2 EXP (64 * LENGTH l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; bignum_of_wordlist] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; EXP_ADD] THEN
  MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN ASM_ARITH_TAC);;

let BIGNUM_OF_WORDLIST_BOUND = prove
 (`!l n. LENGTH l <= n ==> bignum_of_wordlist l < 2 EXP (64 * n)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LTE_TRANS `2 EXP (64 * LENGTH(l:int64 list))` THEN
  ASM_REWRITE_TAC[BIGNUM_OF_WORDLIST_BOUND_LENGTH; LE_EXP] THEN
  ASM_ARITH_TAC);;

let BIGNUM_FROM_WORDLIST_BOUND_GEN = prove
 (`!l n. 64 * LENGTH l <= n ==> bignum_of_wordlist l < 2 EXP n`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH lhand BIGNUM_OF_WORDLIST_BOUND_LENGTH o
    lhand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LTE_TRANS) THEN
  ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC);;

let BIGNUM_OF_WORDLIST_APPEND = prove
 (`!l1 l2. bignum_of_wordlist (APPEND l1 l2) =
           bignum_of_wordlist l1 +
           2 EXP (64 * LENGTH l1) * bignum_of_wordlist l2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[bignum_of_wordlist; APPEND; LENGTH; MULT_CLAUSES] THEN
  REWRITE_TAC[EXP; EXP_ADD] THEN ARITH_TAC);;

let BIGNUM_OF_WORDLIST_LT = prove
 (`!m0 m1 n0 n1.
        bignum_of_wordlist(CONS m0 m1) < bignum_of_wordlist(CONS n0 n1) <=>
        bignum_of_wordlist m1 < bignum_of_wordlist n1 \/
        bignum_of_wordlist m1 = bignum_of_wordlist n1 /\ val m0 < val n0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bignum_of_wordlist] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_LT_64 THEN REWRITE_TAC[VAL_BOUND_64]);;

let BIGNUM_OF_WORDLIST_LE = prove
 (`!m0 m1 n0 n1.
        bignum_of_wordlist(CONS m0 m1) <= bignum_of_wordlist(CONS n0 n1) <=>
        bignum_of_wordlist m1 < bignum_of_wordlist n1 \/
        bignum_of_wordlist m1 = bignum_of_wordlist n1 /\ val m0 <= val n0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bignum_of_wordlist] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_LE_64 THEN REWRITE_TAC[VAL_BOUND_64]);;

let BIGNUM_OF_WORDLIST_EQ = prove
 (`!m0 m1 n0 n1.
        bignum_of_wordlist(CONS m0 m1) = bignum_of_wordlist(CONS n0 n1) <=>
        m0 = n0 /\ bignum_of_wordlist m1 = bignum_of_wordlist n1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[bignum_of_wordlist] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_EQ_64 THEN REWRITE_TAC[VAL_BOUND_64]);;

let BIGNUM_OF_WORDLIST_EQ_0 = prove
 (`!l. bignum_of_wordlist l = 0 <=> ALL (\x. x = word 0) l`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL; bignum_of_wordlist; ADD_EQ_0; MULT_EQ_0; EXP_EQ_0] THEN
  ASM_REWRITE_TAC[ARITH_EQ; VAL_EQ_0]);;

let BIGNUM_OF_WORDLIST_EQ_MAX = prove
 (`!l n. 64 * LENGTH l = n
         ==> (bignum_of_wordlist l = 2 EXP n - 1 <=>
              ALL (\x. x = word_not(word 0)) l)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_UNWIND_THM1] THEN
  MP_TAC(SPEC `MAP word_not (l:int64 list)` BIGNUM_OF_WORDLIST_EQ_0) THEN
  REWRITE_TAC[WORD_RULE `x = word_not(word 0) <=> word_not x = word 0`] THEN
  REWRITE_TAC[ALL_MAP; o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(ARITH_RULE `n = a + b + 1 ==> (a = n - 1 <=> b = 0)`) THEN
  SPEC_TAC(`l:int64 list`,`l:int64 list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[bignum_of_wordlist; MAP; LENGTH] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; EXP; EXP_ADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
  REAL_ARITH_TAC);;

let BIGNUM_OF_WORDLIST_LT_MAX = prove
 (`!l n. 64 * LENGTH l = n
         ==> (bignum_of_wordlist l < 2 EXP n - 1 <=>
              EX (\x. ~(x = word_not(word 0))) l)`,
  SIMP_TAC[GSYM NOT_ALL; GSYM BIGNUM_OF_WORDLIST_EQ_MAX] THEN
  REWRITE_TAC[ARITH_RULE `a < n - 1 <=> a < n /\ ~(a = n - 1)`] THEN
  SIMP_TAC[LT_LE; BIGNUM_FROM_WORDLIST_BOUND_GEN; LE_REFL]);;

let BIGNUM_OF_WORDLIST_DIV_CONV =
  let pth = prove
   (`64 <= n
     ==> bignum_of_wordlist (CONS w ws) DIV 2 EXP n =
         bignum_of_wordlist ws DIV 2 EXP (n - 64)`,
    REWRITE_TAC[ARITH_RULE `64 <= n <=> n = 64 + (n - 64)`] THEN
    DISCH_THEN(fun th ->
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    REWRITE_TAC[EXP_ADD; GSYM DIV_DIV; BIGNUM_OF_WORDLIST_DIV]) in
  let rule = PART_MATCH (lhand o rand) pth in
  let rec conv tm =
    try let th1 = rule tm in
        let th2 = MP th1 (EQT_ELIM(NUM_LE_CONV(lhand(concl th1)))) in
        let th3 = CONV_RULE(funpow 3 RAND_CONV NUM_SUB_CONV) th2 in
        CONV_RULE(RAND_CONV conv) th3
    with Failure _ -> REFL tm in
  let patok = can (term_match [] `bignum_of_wordlist l DIV 2 EXP n`) in
  (conv o check patok) THENC
  GEN_REWRITE_CONV (TRY_CONV o LAND_CONV)
   [BIGNUM_OF_WORDLIST_SING; CONJUNCT1 bignum_of_wordlist] THENC
  GEN_REWRITE_CONV TRY_CONV [DIV_0; ARITH_RULE `n DIV 2 EXP 0 = n`];;

let BIGDIGIT_BIGNUM_OF_WORDLIST = prove(`forall l i.
  i < LENGTH l ==> bigdigit (bignum_of_wordlist l) i = val (EL i l)`,

  LIST_INDUCT_TAC THENL [
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;

    REWRITE_TAC[LENGTH; bignum_of_wordlist] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (SPEC `i:num` num_CASES) THEN
    STRIP_TAC THENL [
      (* i = 0 *)
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[bigdigit;EL;HD] THEN
      REWRITE_TAC[MULT_0;EXP;DIV_1] THEN
      ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
      REWRITE_TAC[MOD_MULT; ADD_0; MOD_MOD_REFL] THEN
      SIMP_TAC[VAL_BOUND_64;MOD_LT];

      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[EL;TL] THEN
      IMP_REWRITE_TAC[BIGDIGIT_SUC;VAL_BOUND_64] THEN
      ASM_ARITH_TAC
    ]
  ]);;

(* ------------------------------------------------------------------------- *)
(* Reading a general word list from memory. This may be somewhat incoherent  *)
(* unless the total number of bits dimindex(:N) * n is a multiple of 8.      *)
(* ------------------------------------------------------------------------- *)

let wordlist_from_memory = define
 `wordlist_from_memory(a,n) s:(N word)list =
    wordlist_of_num n
     (read (memory :> bytes(a,(dimindex(:N) * n + 7) DIV 8)) s)`;;

let WORDLIST_FROM_MEMORY_GEN = prove
 (`!n m a s.
        dimindex(:N) * n <= 8 * m
        ==> wordlist_from_memory(a,n) s:(N word)list =
            wordlist_of_num n (read(memory :> bytes(a,m)) s)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[wordlist_from_memory] THEN
  ONCE_REWRITE_TAC[GSYM WORDLIST_OF_NUM_MOD] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `(dimindex (:N) * n + 7) DIV 8 = MIN m ((dimindex (:N) * n + 7) DIV 8)`
  SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM READ_BYTES_MOD] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `MIN a b = b <=> b <= a`] THEN ARITH_TAC);;

let WORDLIST_FROM_MEMORY = prove
 (`!a n s. wordlist_from_memory(a,n) s:((((N tybit0)tybit0)tybit0)word)list =
           wordlist_of_num n (read(memory :> bytes(a,dimindex(:N) * n)) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wordlist_from_memory] THEN
  REWRITE_TAC[DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN REPLICATE_TAC 4 AP_TERM_TAC THEN
  ARITH_TAC);;

let LENGTH_WORDLIST_FROM_MEMORY = prove
 (`!a n s. LENGTH(wordlist_from_memory(a,n) s:(N word)list) = n`,
  REWRITE_TAC[wordlist_from_memory; LENGTH_WORDLIST_OF_NUM]);;

let NUM_OF_WORDLIST_FROM_MEMORY_GEN = prove
 (`!n m a s.
        dimindex(:N) * n = 8 * m
        ==> num_of_wordlist(wordlist_from_memory(a,n) s:(N word)list) =
            read(memory :> bytes(a,m)) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wordlist_from_memory] THEN
  ASM_REWRITE_TAC[ARITH_RULE `(8 * m + 7) DIV 8 = m`] THEN
  MATCH_MP_TAC NUM_OF_WORDLIST_OF_NUM_EQ_SELF THEN
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]);;

let NUM_OF_WORDLIST_FROM_MEMORY = prove
 (`!a n s.
        num_of_wordlist
         (wordlist_from_memory(a,n) s:((((N tybit0)tybit0)tybit0)word)list) =
        read(memory :> bytes(a,dimindex(:N) * n)) s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NUM_OF_WORDLIST_FROM_MEMORY_GEN THEN
  REWRITE_TAC[DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN ARITH_TAC);;

let WORDLIST_FROM_MEMORY_EQ_ALT = prove
 (`!addr len size l s.
        dimindex(:N) * len = 8 * size
        ==> (wordlist_from_memory(addr,len) s:(N word)list = l <=>
             LENGTH l = len /\
             read (memory :> bytes(addr,size)) s = num_of_wordlist l)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `LENGTH(l:(N word)list) = len` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[LENGTH_WORDLIST_FROM_MEMORY]] THEN
  EQ_TAC THENL [ASM_MESON_TAC[NUM_OF_WORDLIST_FROM_MEMORY_GEN]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `wordlist_of_num len:num->(N word)list`) THEN
  MATCH_MP_TAC EQ_IMP THEN
  BINOP_TAC THENL [ALL_TAC; ASM_MESON_TAC[WORDLIST_OF_NUM_OF_WORDLIST]] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORDLIST_FROM_MEMORY_GEN THEN
  ASM_REWRITE_TAC[LE_REFL]);;

let WORDLIST_FROM_MEMORY_CLAUSES = prove
 (`(!a s. wordlist_from_memory(a,0) s:(N word)list = []) /\
   (!a n s.
     wordlist_from_memory(a,SUC n) s :((((N tybit0)tybit0)tybit0)word)list =
     APPEND (wordlist_from_memory(a,n) s)
            [read (memory :> wbytes(word_add a (word(dimindex(:N) * n)))) s])`,
  CONJ_TAC THENL
   [REWRITE_TAC[wordlist_from_memory; MULT_CLAUSES; ADD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[wordlist_of_num];
    REPEAT GEN_TAC] THEN
  REWRITE_TAC[LISTS_NUM_OF_WORDLIST_EQ] THEN
  REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY; LENGTH_APPEND; LENGTH; ADD_CLAUSES;
              NUM_OF_WORDLIST_FROM_MEMORY; wordlist_of_num;
              NUM_OF_WORDLIST_APPEND; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; NUM_OF_WORDLIST_SING] THEN
  REWRITE_TAC[ARITH_RULE `x * SUC y = x * y + x`; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[VAL_READ_WBYTES; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN
  REWRITE_TAC[GSYM MULT_ASSOC; ARITH_RULE `2 * 2 * 2 * x = 8 * x`] THEN
  REWRITE_TAC[ARITH_RULE `(8 * n) DIV 8 = n`]);;

let WORDLIST_FROM_MEMORY_CONV =
  let pthc = prove
   (`l:((((N tybit0)tybit0)tybit0)word)list = APPEND l [] /\
     APPEND (wordlist_from_memory(a,0) s) l = l /\
     APPEND (wordlist_from_memory(a,SUC n) s) l =
     APPEND (wordlist_from_memory(a,n) s)
     (CONS (read(memory :> wbytes(word_add a (word(dimindex(:N) * n)))) s) l)`,
    REWRITE_TAC[WORDLIST_FROM_MEMORY_CLAUSES] THEN
    REWRITE_TAC[APPEND_NIL; APPEND; GSYM APPEND_ASSOC]) in
  let pths = CONJUNCTS pthc
  and avars = sort (<) (frees(concl pthc))
  and timfn = type_match (type_of(lhand(lhand(concl pthc))))
  and prule =
       (PURE_REWRITE_RULE o map GSYM)
       [BYTES8_WBYTES; BYTES16_WBYTES; BYTES32_WBYTES; BYTES64_WBYTES;
        BYTES128_WBYTES; BYTES256_WBYTES] in
  fun tm ->
    match tm with
      Comb(Comb(Const("wordlist_from_memory",_),
                Comb(Comb(Const(",",_),_),n)),_) when is_numeral n ->
      let tyin = timfn (type_of tm) [] in
      let [a_tm;l_tm;n_tm;s_tm] = map (inst tyin) avars
      and [pth_init;pth_base;pth_step] =
        map (CONV_RULE(ONCE_DEPTH_CONV DIMINDEX_CONV) o INST_TYPE tyin) pths in
      let rule_base = GEN_REWRITE_RULE RAND_CONV [pth_base]
      and rule_step =
        CONV_RULE(RAND_CONV(LAND_CONV(LAND_CONV(RAND_CONV num_CONV)) THENC
                  GEN_REWRITE_CONV I [pth_step] THENC
                  RAND_CONV(LAND_CONV(LAND_CONV (funpow 2 RAND_CONV
                    (funpow 2 RAND_CONV NUM_MULT_CONV THENC
                     TRY_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                     GEN_REWRITE_CONV TRY_CONV
                      [WORD_RULE `word_add z (word 0):int64 = z`])))))) in
      let rec conv th =
        try rule_base th with Failure _ ->
        let th' = rule_step th in conv th' in
      prule(conv (INST [tm,l_tm] pth_init))
    | _ -> failwith "WORDLIST_FROM_MEMORY_CONV";;

(* ------------------------------------------------------------------------- *)
(* Pairing up elements of a word list, relation with above value             *)
(* ------------------------------------------------------------------------- *)

let pair_wordlist = define
 `(!hi (lo:N word) rest.
     pair_wordlist (CONS lo (CONS hi rest)) =
     CONS (word_join hi lo:((N)tybit0)word) (pair_wordlist rest)) /\
  (!w. pair_wordlist [w] = [word_join (word 0:N word) w]) /\
  pair_wordlist [] = []`;;

let LENGTH_PAIR_WORDLIST = prove
 (`!l:(N word)list. LENGTH(pair_wordlist l) = (LENGTH l + 1) DIV 2`,
  GEN_TAC THEN WF_INDUCT_TAC `LENGTH(l:(N word)list)` THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`l:(N word)list`,`l:(N word)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[pair_wordlist; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[pair_wordlist; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_SIMP_TAC[ARITH_RULE `n < SUC(SUC n)`] THEN ARITH_TAC);;

let NUM_OF_PAIR_WORDLIST = prove
 (`!l:(N word)list. num_of_wordlist (pair_wordlist l) = num_of_wordlist l`,
  GEN_TAC THEN WF_INDUCT_TAC `LENGTH(l:(N word)list)` THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`l:(N word)list`,`l:(N word)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[pair_wordlist; num_of_wordlist] THEN
  MAP_EVERY X_GEN_TAC [`lo:N word`; `med:(N word)list`] THEN
  DISCH_THEN(K ALL_TAC) THEN
  SPEC_TAC(`med:(N word)list`,`med:(N word)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[pair_wordlist; num_of_wordlist] THEN
  SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES; VAL_WORD_JOIN_SIMPLE; DIMINDEX_TYBIT0;
           VAL_WORD_0; GSYM MULT_2; LENGTH; ARITH_RULE `n < SUC(SUC n)`] THEN
  REWRITE_TAC[MULT_2; EXP_ADD] THEN ARITH_TAC);;

let WORDLIST_FROM_MEMORY_PAIR_GEN = prove
 (`!a n s. 4 divides (dimindex(:N) * n)
           ==> wordlist_from_memory(a,n) s =
               pair_wordlist(wordlist_from_memory(a,2*n) s:(N word)list)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LISTS_NUM_OF_WORDLIST_EQ] THEN
  ASM_REWRITE_TAC[LENGTH_PAIR_WORDLIST; LENGTH_WORDLIST_FROM_MEMORY] THEN
  REWRITE_TAC[NUM_OF_PAIR_WORDLIST] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `m:num` o REWRITE_RULE[divides]) THEN
  TRANS_TAC EQ_TRANS `read(memory :> bytes(a,m)) s` THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC SYM_CONV] THEN
  MATCH_MP_TAC NUM_OF_WORDLIST_FROM_MEMORY_GEN THEN
  REWRITE_TAC[DIMINDEX_TYBIT0] THEN POP_ASSUM MP_TAC THEN CONV_TAC NUM_RING);;

let WORDLIST_FROM_MEMORY_PAIR = prove
 (`!a n s. wordlist_from_memory(a,n) s =
           pair_wordlist
             (wordlist_from_memory(a,2*n) s:(((N tybit0)tybit0)word)list)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC WORDLIST_FROM_MEMORY_PAIR_GEN THEN
  REWRITE_TAC[DIMINDEX_TYBIT0; ARITH_RULE `2 * 2 * n = n * 4`] THEN
  NUMBER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Extracting a bignum from memory.                                          *)
(* ------------------------------------------------------------------------- *)

let bignum_from_memory = new_definition
 `bignum_from_memory(a,k) s =
    nsum {i | i < k}
         (\i. 2 EXP (64 * i) *
              read (memory :> bytes(word_add a (word(8 * i)),8)) s)`;;

let BIGNUM_FROM_MEMORY_BOUND = prove
 (`!k a s. bignum_from_memory(a,k) s < 2 EXP (64 * k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bignum_from_memory; EXP_MULT] THEN
  MATCH_MP_TAC DIGITSUM_BOUND THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  SUBST1_TAC(ARITH_RULE `64 = 8 * 8`) THEN REWRITE_TAC[READ_BYTES_BOUND]);;

let BIGNUM_FROM_MEMORY_TRIVIAL = prove
 (`!a s. bignum_from_memory(a,0) s = 0`,
  REPEAT GEN_TAC THEN
  W(MP_TAC o PART_MATCH lhand BIGNUM_FROM_MEMORY_BOUND o lhand o snd) THEN
  ARITH_TAC);;

let BIGNUM_FROM_MEMORY = prove
 (`!k a s.
       bignum_from_memory(a,k) s =
       nsum {i | i < k}
            (\i. 2 EXP (64 * i) *
                 val(read (memory :> bytes64(word_add a (word(8 * i)))) s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bignum_from_memory] THEN
  MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[bytes64; COMPONENT_COMPOSE_ASSOC] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[asword; through; read; VAL_WORD] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[DIMINDEX_64] THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  SUBST1_TAC(ARITH_RULE `64 = 8 * 8`) THEN REWRITE_TAC[READ_BYTES_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* Some stepping and lex comparison theorems                                 *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_FROM_MEMORY_STEP = prove
 (`!k a s. bignum_from_memory(a,k+1) s =
           bignum_from_memory(a,k) s +
           2 EXP (64 * k) *
           val(read (memory :> bytes64(word_add a (word(8 * k)))) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bignum_from_memory] THEN
  REWRITE_TAC[ARITH_RULE `i:num < k + 1 <=> i = k \/ i < k`] THEN
  REWRITE_TAC[SET_RULE `{x | x = a \/ P x} = a INSERT {x | P x}`] THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  GEN_REWRITE_TAC LAND_CONV [ADD_SYM] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE; bytes64] THEN
  REWRITE_TAC[read; through; asword] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN
  W(MP_TAC o PART_MATCH lhand READ_BYTES_BOUND o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_FROM_MEMORY_SING = prove
 (`!a s. bignum_from_memory(a,1) s = val(read (memory :> bytes64 a) s)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ARITH_RULE `1 = 0 + 1`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
  REWRITE_TAC[EXP; MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0]);;

let BIGNUM_FROM_MEMORY_MOD = prove
 (`!a k n s. (bignum_from_memory(a,k) s) MOD (2 EXP (64 * n)) =
             bignum_from_memory(a,MIN k n) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bignum_from_memory; EXP_MULT] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) DIGITSUM_MOD o lhand o snd) THEN
  REWRITE_TAC[IN_ELIM_THM; ARITH_RULE `i < MIN k n <=> i < k /\ i < n`] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; ARITH_RULE `64 = 8 * 8`] THEN
  REWRITE_TAC[READ_BYTES_BOUND]);;

let BIGNUM_FROM_MEMORY_DIV = prove
 (`!a k n s. (bignum_from_memory(a,k) s) DIV (2 EXP (64 * n)) =
             bignum_from_memory(word_add a (word(8 * n)),k - n) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bignum_from_memory; EXP_MULT] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) DIGITSUM_DIV_NUMSEG o lhand o snd) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; ARITH_RULE `64 = 8 * 8`] THEN
  REWRITE_TAC[READ_BYTES_BOUND] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; WORD_ADD] THEN REWRITE_TAC[WORD_ADD_AC]);;

let LOWDIGITS_BIGNUM_FROM_MEMORY = prove
 (`!a k n s.
        lowdigits (bignum_from_memory(a,k) s) n =
        bignum_from_memory(a,MIN k n) s`,
  REWRITE_TAC[lowdigits; BIGNUM_FROM_MEMORY_MOD]);;

let HIGHDIGITS_BIGNUM_FROM_MEMORY = prove
 (`!a k n s.
        highdigits (bignum_from_memory(a,k) s) n =
        bignum_from_memory(word_add a (word(8 * n)),k - n) s`,
  REWRITE_TAC[highdigits; BIGNUM_FROM_MEMORY_DIV]);;

let BIGNUM_FROM_MEMORY_SPLIT = prove
 (`!a m n s.
        bignum_from_memory(a,m+n) s =
        2 EXP (64 * m) * bignum_from_memory(word_add a (word(8 * m)),n) s +
        bignum_from_memory(a,m) s`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [`bignum_from_memory(a,m+n) s`; `2 EXP (64 * m)`]
        (CONJUNCT1 DIVISION_SIMP))) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_MOD; BIGNUM_FROM_MEMORY_DIV] THEN
  REWRITE_TAC[ADD_SUB2; ARITH_RULE `MIN (m + n) m = m`] THEN ARITH_TAC);;

let BIGDIGIT_BIGNUM_FROM_MEMORY = prove
 (`!k a s i.
      bigdigit (bignum_from_memory(a,k) s) i =
      if i < k then val(read (memory :> bytes64(word_add a (word(8 * i)))) s)
      else 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bigdigit; BIGNUM_FROM_MEMORY_DIV] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP (64 * 1)`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_MOD] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `i < k ==> MIN (k - i) 1 = 1`;
               ARITH_RULE `~(i < k) ==> MIN (k - i) 1 = 0`;
               BIGNUM_FROM_MEMORY_TRIVIAL] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY; ARITH_RULE `i < 1 <=> i = 0`] THEN
  REWRITE_TAC[SING_GSPEC; NSUM_SING; MULT_CLAUSES; EXP; WORD_ADD_0]);;

let BIGNUM_FROM_MEMORY_LT_STEP = prove
 (`!k a s n.
        bignum_from_memory(a,k) s < 2 EXP (64 * n) <=>
        k <= n \/
        read (memory :> bytes64(word_add a (word(8 * n)))) s = word 0 /\
        bignum_from_memory(a,k) s < 2 EXP (64 * (n + 1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY] THEN
  REWRITE_TAC[GSYM VAL_EQ_0; GSYM EXP_EXP; GSYM MULT_ASSOC] THEN
  MATCH_MP_TAC DIGITSUM_LT_STEP THEN
  REWRITE_TAC[GSYM DIMINDEX_64; VAL_BOUND] THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_FROM_MEMORY_LEXICOGRAPHIC = prove
 (`!k a b s.
        bignum_from_memory(a,k+1) s < bignum_from_memory(b,k+1) s <=>
        val(read (memory :> bytes64(word_add a (word(8 * k)))) s) <
        val(read (memory :> bytes64(word_add b (word(8 * k)))) s) \/
        val(read (memory :> bytes64(word_add a (word(8 * k)))) s) =
        val(read (memory :> bytes64(word_add b (word(8 * k)))) s) /\
        bignum_from_memory(a,k) s < bignum_from_memory(b,k) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC LEXICOGRAPHIC_LT THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BOUND]);;

let BIGNUM_FROM_MEMORY_EXPAND = prove
 (`!k a s. bignum_from_memory(a,k) s =
           if k = 0 then 0 else
           val(read (memory :> bytes64 a) s) +
           2 EXP 64 * bignum_from_memory(word_add a (word 8),k - 1) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; NSUM_CLAUSES] THEN
  SUBGOAL_THEN
   `{i | i < k} = 0 INSERT IMAGE (\i. i + 1) {i | i < k - 1}`
  SUBST1_TAC THENL
   [REWRITE_TAC[IN_INSERT; EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
    REWRITE_TAC[ARITH_RULE `x = y + 1 <=> y = x - 1 /\ ~(x = 0)`] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; ARITH_RULE `~(0 = i + 1)`] THEN
  SIMP_TAC[NSUM_IMAGE; EQ_ADD_RCANCEL] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; WORD_ADD_0] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM NSUM_LMUL] THEN MATCH_MP_TAC NSUM_EQ THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[MULT_ASSOC; GSYM(CONJUNCT2 EXP); EXP_MULT; o_DEF] THEN
  REWRITE_TAC[ADD1] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `8 + 8 * i = 8 * (i + 1)`]);;

let BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS = prove
 (`!x n a i s.
      bignum_from_memory(x,n) s = highdigits a i <=>
      if n = 0 then a < 2 EXP (64 * i) else
      read(memory :> bytes64 x) s = word(bigdigit a i) /\
      bignum_from_memory(word_add x (word 8),n - 1) s = highdigits a (i + 1)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
   [ONCE_REWRITE_RULE[ADD_SYM] BIGNUM_FROM_MEMORY_EXPAND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [MESON_TAC[HIGHDIGITS_EQ_0]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [HIGHDIGITS_STEP] THEN
  SIMP_TAC[LEXICOGRAPHIC_EQ; BIGDIGIT_BOUND; VAL_BOUND_64] THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  MESON_TAC[]);;

let BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS = prove
 (`!x n a i j s.
        bignum_from_memory(word_add x (word (8 * i)),n) s = highdigits a j <=>
        if n = 0 then a < 2 EXP (64 * j) else
        read(memory :> bytes64(word_add x (word(8 * i)))) s =
        word(bigdigit a j) /\
        bignum_from_memory(word_add x (word (8 * (i + 1))),n - 1) s =
        highdigits a (j + 1)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_add x (word (8 * i))) (word 8) =
    word_add x (word(8 * (i + 1)))`]);;

let BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS_ALT = prove
 (`!x n a i s.
      bignum_from_memory(x,n) s = highdigits a i <=>
      (if n = 0 then a < 2 EXP (64 * i) else
       read(memory :> bytes64 x) s = word(bigdigit a i)) /\
      bignum_from_memory(word_add x (word 8),n - 1) s = highdigits a (i + 1)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUB_0; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
  REWRITE_TAC[MESON[] `(p <=> p /\ a = b) <=> p ==> b = a`] THEN
  REWRITE_TAC[HIGHDIGITS_EQ_0] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LTE_TRANS) THEN
  REWRITE_TAC[LE_EXP] THEN ARITH_TAC);;

let BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS_ALT = prove
 (`!x n a i j s.
        bignum_from_memory(word_add x (word (8 * i)),n) s = highdigits a j <=>
        (if n = 0 then a < 2 EXP (64 * j) else
         read(memory :> bytes64(word_add x (word(8 * i)))) s =
         word(bigdigit a j)) /\
        bignum_from_memory(word_add x (word (8 * (i + 1))),n - 1) s =
        highdigits a (j + 1)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS_ALT] THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_add x (word (8 * i))) (word 8) =
    word_add x (word(8 * (i + 1)))`]);;

let BIGNUM_FROM_MEMORY_EQ_LOWDIGITS = prove
 (`!x a n s.
      bignum_from_memory(x,n+1) s = lowdigits a (n+1) <=>
      read (memory :> bytes64 (word_add x (word (8 * n)))) s =
      word(bigdigit a n) /\
      bignum_from_memory(x,n) s = lowdigits a n`,
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; LOWDIGITS_CLAUSES] THEN
  ONCE_REWRITE_TAC[ARITH_RULE
   `a + e * b:num = e * c + d <=> e * b + a = e * c + d`] THEN
  SIMP_TAC[LEXICOGRAPHIC_EQ; BIGNUM_FROM_MEMORY_BOUND; LOWDIGITS_BOUND] THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* Now a "packaged" version where the first word encodes the size            *)
(* ------------------------------------------------------------------------- *)

let packaged_bignum_from_memory = new_definition
 `packaged_bignum_from_memory a s =
    bignum_from_memory(word_add a (word 8),read (bytes(a,8)) s)`;;

(* ------------------------------------------------------------------------- *)
(* Thanks to little-endian encoding this is true. It's handy to use it since *)
(* we already have some orthogonality infrastructure for "bytes".            *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_FROM_MEMORY_BYTES = prove
 (`!k a. bignum_from_memory(a,k) = read (memory :> bytes(a,8 * k))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  INTRO_TAC "![s]" THEN REWRITE_TAC[bignum_from_memory] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[READ_BYTES; DIMINDEX_64] THEN
  SPEC_TAC(`read memory s`,`m:int64->byte`) THEN GEN_TAC THEN
  REWRITE_TAC[GSYM NSUM_LMUL; EXP_MULT; ARITH_RULE `2 EXP 8 = 256`] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 = 256 EXP 8`] THEN
  REWRITE_TAC[MULT_ASSOC; GSYM EXP_ADD; EXP_EXP] THEN
  SIMP_TAC[NSUM_NSUM_PRODUCT; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC NSUM_EQ_GENERAL_INVERSES THEN
  MAP_EVERY EXISTS_TAC [`\(i,j). 8 * i + j`; `\n. n DIV 8,n MOD 8`] THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM; FORALL_PAIR_THM; WORD_VAL] THEN
  REWRITE_TAC[WORD_ADD; WORD_VAL] THEN REWRITE_TAC[WORD_RULE
   `word_add (word_add x y) z = word_add x (word_add y z)`] THEN
  REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_ARITH_TAC; MATCH_MP_TAC DIVMOD_UNIQ THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Passing between alternative byte component formulations.                  *)
(* ------------------------------------------------------------------------- *)

let READ_BYTES_EQ_BYTELIST = prove
 (`!x n k s.
        read (memory :> bytes(x,k)) s = n <=>
        n < 256 EXP k /\
        read (memory :> bytelist(x,k)) s = bytelist_of_num k n`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; bytelist; through; read] THEN
  MESON_TAC[NUM_OF_BYTELIST_OF_NUM_EQ; READ_BYTES_BOUND_ALT]);;

let READ_BYTELIST_EQ_BYTES = prove
 (`!x l k s.
        read (memory :> bytelist(x,k)) s = l <=>
        LENGTH l = k /\
        read (memory :> bytes(x,k)) s = num_of_bytelist l`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; bytelist; through; read] THEN
  MESON_TAC[NUM_OF_BYTELIST_OF_NUM_EQ; BYTELIST_OF_NUM_OF_BYTELIST;
            READ_BYTES_BOUND_ALT; LENGTH_BYTELIST_OF_NUM]);;

(* ------------------------------------------------------------------------- *)
(* Conversion to expand "bytes_loaded" in 64-bit word assignments.           *)
(* ------------------------------------------------------------------------- *)

let DATA64_CONV =
  let pth = prove
   (`bytes_loaded s (word pc)
      (CONS d0 (CONS d1 (CONS d2 (CONS d3
         (CONS d4 (CONS d5 (CONS d6 (CONS d7 l)))))))) <=>
     read (memory :> bytes64 (word pc)) s =
     word(num_of_bytelist [d0;d1;d2;d3;d4;d5;d6;d7]) /\
     bytes_loaded s (word(pc + 8)) l`,
    SUBST1_TAC(SYM(ISPEC `l:byte list` (CONJUNCT1 APPEND))) THEN
    REWRITE_TAC[GSYM(CONJUNCT2 APPEND)] THEN REWRITE_TAC[CONJUNCT1 APPEND] THEN
    REWRITE_TAC[bytes_loaded_append] THEN
    CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN
    REWRITE_TAC[WORD_ADD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES] THEN
    REWRITE_TAC[bytes64; asword; READ_COMPONENT_COMPOSE; through; read] THEN
    CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC SYM_CONV THEN BINOP_TAC THEN MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[GSYM(NUM_MULT_CONV `8 * 8`); READ_BYTES_BOUND] THEN
    W(MP_TAC o PART_MATCH lhand NUM_OF_BYTELIST_BOUND o lhand o snd) THEN
    CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN ARITH_TAC) in
  let rec conv tm =
   TRY_CONV
    (GEN_REWRITE_CONV I [pth] THENC
    BINOP2_CONV
      (REWRITE_CONV[num_of_bytelist] THENC
       DEPTH_CONV WORD_NUM_RED_CONV)
      (LAND_CONV (RAND_CONV
        (GEN_REWRITE_CONV I [GSYM ADD_ASSOC] THENC
         RAND_CONV NUM_ADD_CONV)) THENC
       conv)) tm in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Bignum as a state component (little-endian only of course).               *)
(* ------------------------------------------------------------------------- *)

let bignum = define
 `bignum(a:int64,k) = bytes(a,8 * k)`;;

add_component_alias_thms [bignum];;

simulation_precanon_thms :=
  union [bignum; BIGNUM_FROM_MEMORY_BYTES] (!simulation_precanon_thms);;

let BIGNUM_FROM_MEMORY_BIGNUM = prove
 (`!k a. bignum_from_memory(a,k) = read (memory :> bignum(a,k))`,
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; bignum]);;

let READ_BIGNUM_BOUND = prove
 (`(!k a m. read (bignum(a,k)) m < 2 EXP (64 * k)) /\
   (!k a s. read (memory :> bignum(a,k)) s < 2 EXP (64 * k))`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; bignum] THEN
  SUBST1_TAC(ARITH_RULE `64 = 8 * 8`) THEN
  REWRITE_TAC[READ_BYTES_BOUND; GSYM MULT_ASSOC]);;

let READ_BIGNUM_TRIVIAL = prove
 (`(!a m. read (bignum(a,0)) m = 0) /\
   (!a s. read (memory :> bignum(a,0)) s = 0)`,
  MP_TAC READ_BIGNUM_BOUND THEN MATCH_MP_TAC MONO_AND THEN
  CONJ_TAC THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Get ranges of bignum abbreviation out of precondition.                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_TERMRANGE_TAC =
  let pth = prove
   (`!k m. m < 2 EXP (64 * k) \/ !s x. ~(bignum_from_memory (x,k) s = m)`,
    MESON_TAC[BIGNUM_FROM_MEMORY_BOUND]) in
  fun k m ->
    DISJ_CASES_THEN2
     ASSUME_TAC
     (fun th ->
        ENSURES_OR_ENSURES_N_TAC
            (REWRITE_TAC[th; ENSURES_TRIVIAL])
            (REWRITE_TAC[th; ENSURES_N_TRIVIAL]) THEN NO_TAC)
     (SPECL [k; m] pth);;

let BIGNUM_RANGE_TAC =
  let pth = prove
   (`!k m. m < 2 EXP (64 * k) \/ !s x. ~(bignum_from_memory (x,k) s = m)`,
    MESON_TAC[BIGNUM_FROM_MEMORY_BOUND])
  and nty = `:num` in
  fun k m ->
    DISJ_CASES_THEN2
     ASSUME_TAC
     (fun th -> REWRITE_TAC[th; ENSURES_TRIVIAL] THEN NO_TAC)
     (SPECL [mk_var(k,nty); mk_var(m,nty)] pth);;

(* ------------------------------------------------------------------------- *)
(* Conversion to expand `bignum_from_memory(x,n) s` for specific n           *)
(* into a reasonably naturally normalized sum of 64-bit words.               *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_EXPAND_CONV =
  let pth = prove
   (`bignum_from_memory(x,0) s = 0 /\
     bignum_from_memory(x,SUC n) s =
        nsum(0..n) (\i. 2 EXP (64 * i) *
             val(read(memory :> bytes64(word_add x (word (8 * i)))) s))`,
    REWRITE_TAC[BIGNUM_FROM_MEMORY] THEN
    REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; NSUM_CLAUSES] THEN
    REWRITE_TAC[numseg; LT_SUC_LE; LE_0])
  and tth = ARITH_RULE `2 EXP 0 * n = n`
  and address_conv =
   TRY_CONV NORMALIZE_RELATIVE_ADDRESS_CONV  THENC
   GEN_REWRITE_CONV TRY_CONV [WORD_RULE `word_add z (word 0) = z`] in
  GEN_REWRITE_CONV (TRY_CONV o RATOR_CONV)
    [GSYM BIGNUM_FROM_MEMORY_BIGNUM;
     GSYM BIGNUM_FROM_MEMORY_BYTES] THENC
  (GEN_REWRITE_CONV I [CONJUNCT1 pth] ORELSEC
   (LAND_CONV(RAND_CONV num_CONV) THENC
    GEN_REWRITE_CONV I [CONJUNCT2 pth] THENC
    EXPAND_NSUM_CONV THENC
    DEPTH_BINOP_CONV `(+):num->num->num`
     (BINOP2_CONV
        (RAND_CONV NUM_MULT_CONV)
        (RAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
          (RAND_CONV(RAND_CONV NUM_MULT_CONV) THENC
          address_conv))))) THENC
      GEN_REWRITE_CONV TRY_CONV [tth])));;

(*** Examples:

BIGNUM_EXPAND_CONV `bignum_from_memory (x,6) s`;;

BIGNUM_EXPAND_CONV `bignum_from_memory(word_add z (word 16),12) s0`;;

BIGNUM_EXPAND_CONV `read (memory :> bytes (x,8 * 6)) s0`;;

****)

(* ------------------------------------------------------------------------- *)
(* Expand a bignum and introduce abbreviations for digits                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_DIGITIZE_TAC =
  let strip_add = striplist (dest_binop `(+):num->num->num`)
  and ty64 = `:int64` in
  fun s tm ->
    let th = BIGNUM_EXPAND_CONV tm in
    let mts = strip_add(rand(concl th)) in
    let tms =
      if mts = [] then [] else map rand ((hd mts)::map rand (tl mts)) in
    let vs =
      map (fun i -> mk_var(s^string_of_int i,ty64)) (0--(length tms - 1)) in
    let abseqs = map2 (curry mk_eq) vs tms in
    SUBST_ALL_TAC th THEN MAP_EVERY ABBREV_TAC abseqs;;

(*** Example:

  BIGNUM_DIGITIZE_TAC "m_" `read(memory :> bytes(x,8 * 6)) s0`

***)

(* ------------------------------------------------------------------------- *)
(* Expansion of bignum_of_wordlist, corresponding digitization variants.     *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_OF_WORDLIST_CONV =
  let [conv_0;conv_1;conv_2;conv_base;conv_step] =
     (map (fun t -> GEN_REWRITE_CONV I [t]) o CONJUNCTS o prove)
   (`bignum_of_wordlist [] = 0 /\
     bignum_of_wordlist [h] = val h /\
     bignum_of_wordlist (CONS h t) =
     val h + 2 EXP 64 * bignum_of_wordlist t /\
     2 EXP n * bignum_of_wordlist [h] = 2 EXP n * val h /\
     2 EXP n * bignum_of_wordlist(CONS h t) =
     2 EXP n * val h + 2 EXP (n + 64) * bignum_of_wordlist t`,
    REWRITE_TAC[bignum_of_wordlist; EXP_ADD] THEN ARITH_TAC) in
    let rec coreconv tm =
      (conv_base ORELSEC
       (conv_step THENC
        RAND_CONV (LAND_CONV(RAND_CONV NUM_ADD_CONV) THENC coreconv))) tm in
    conv_0 ORELSEC conv_1 ORELSEC (conv_2 THENC RAND_CONV coreconv);;

let BIGNUM_OF_WORDLIST_SPLIT_RULE =
  let int64_ty = `:int64`
  and append_tm = `APPEND:int64 list->int64 list->int64 list` in
  fun (m,n) ->
    let vs = map (fun n -> mk_var("x"^string_of_int n,int64_ty)) (1--(m+n)) in
    let vs1,vs2 = chop_list m vs in
    let th = SPECL [mk_list(vs1,int64_ty); mk_list(vs2,int64_ty)]
                   BIGNUM_OF_WORDLIST_APPEND in
    CONV_RULE
     (BINOP2_CONV
       (GEN_REWRITE_CONV (RAND_CONV o TOP_DEPTH_CONV) [APPEND])
       (RAND_CONV(LAND_CONV(RAND_CONV
         (GEN_REWRITE_CONV (RAND_CONV o TOP_DEPTH_CONV) [LENGTH] THENC
          NUM_REDUCE_CONV))))) th;;

let BIGNUM_LEXPAND_CONV =
  let strip_add = striplist (dest_binop `(+):num->num->num`)
  and ofw_tm = `bignum_of_wordlist`
  and ty64 = `:int64` in
  fun tm ->
    let th = BIGNUM_EXPAND_CONV tm in
    let mts = strip_add(rand(concl th)) in
    let tms =
      if mts = [] then [] else map rand ((hd mts)::map rand (tl mts)) in
    let tm' = mk_comb(ofw_tm,mk_list(tms,ty64)) in
    TRANS th (SYM(BIGNUM_OF_WORDLIST_CONV tm'));;

let BIGNUM_LDIGITIZE_TAC =
  let ty64 = `:int64` in
  fun s tm ->
    let th = BIGNUM_LEXPAND_CONV tm in
    let tms = dest_list(rand(rand(concl th))) in
    let vs =
      map (fun i -> mk_var(s^string_of_int i,ty64)) (0--(length tms - 1)) in
    let abseqs = map2 (curry mk_eq) vs tms in
    SUBST_ALL_TAC th THEN MAP_EVERY ABBREV_TAC abseqs;;

(* ------------------------------------------------------------------------- *)
(* Expansion of bytes by analogy.                                            *)
(* ------------------------------------------------------------------------- *)

let BYTES_EXPAND_CONV =
  let pth = prove
   (`read (memory :> bytes(x,0)) s = 0 /\
     read (memory :> bytes(x,SUC n)) s =
        nsum(0..n) (\i. 2 EXP (8 * i) *
             val(read(memory :> bytes8(word_add x (word i))) s))`,
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES] THEN
    REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; NSUM_CLAUSES] THEN
    REWRITE_TAC[numseg; LT_SUC_LE; LE_0] THEN
    REWRITE_TAC[READ_BYTES_1; READ_COMPONENT_COMPOSE; bytes8;
                asword; through; read; WORD_VAL])
  and tth = ARITH_RULE `2 EXP 0 * n = n`
  and address_conv =
   TRY_CONV NORMALIZE_RELATIVE_ADDRESS_CONV  THENC
   GEN_REWRITE_CONV TRY_CONV [WORD_RULE `word_add z (word 0) = z`] in
  (GEN_REWRITE_CONV I [CONJUNCT1 pth] ORELSEC
   (LAND_CONV(funpow 3 RAND_CONV num_CONV) THENC
    GEN_REWRITE_CONV I [CONJUNCT2 pth] THENC
    EXPAND_NSUM_CONV THENC
    DEPTH_BINOP_CONV `(+):num->num->num`
     (BINOP2_CONV
        (RAND_CONV NUM_MULT_CONV)
        (RAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
          address_conv)))) THENC
      GEN_REWRITE_CONV TRY_CONV [tth])));;

(*** Examples:

BYTES_EXPAND_CONV `read (memory :> bytes (word_add x (word 42),8)) s0`;;

****)

let BYTES_DIGITIZE_TAC =
  let strip_add = striplist (dest_binop `(+):num->num->num`)
  and ty8 = `:byte` in
  fun s tm ->
    let th = BYTES_EXPAND_CONV tm in
    let mts = strip_add(rand(concl th)) in
    let tms =
      if mts = [] then [] else map rand ((hd mts)::map rand (tl mts)) in
    let vs =
      map (fun i -> mk_var(s^string_of_int i,ty8)) (0--(length tms - 1)) in
    let abseqs = map2 (curry mk_eq) vs tms in
    SUBST_ALL_TAC th THEN MAP_EVERY ABBREV_TAC abseqs;;

(*** Example:

  BYTES_DIGITIZE_TAC "m_" `read(memory :> bytes(x,4)) s0`

***)

(* ------------------------------------------------------------------------- *)
(* Expansion of bytelist by analogy, occasionally useful for bignums.        *)
(* ------------------------------------------------------------------------- *)

let BYTELIST_EXPAND_CONV =
  let pth = prove
   (`read (memory :> bytelist (x,0)) s = [] /\
     read (memory :> bytelist (x,SUC n)) s =
     CONS (read (memory :> bytes8 x) s)
          (read (memory :> bytelist (word_add x (word 1),n)) s)`,
    REWRITE_TAC[bytelist_clauses; READ_COMPONENT_COMPOSE;
                bytes8; READ_BYTES_1; asword; read; through; WORD_VAL]) in
  let rewr_base = GEN_REWRITE_CONV I [CONJUNCT1 pth]
  and rewr_step = GEN_REWRITE_CONV I [CONJUNCT2 pth] in
  let rec conv tm =
    (rewr_base ORELSEC
     (LAND_CONV (funpow 3 RAND_CONV num_CONV) THENC
      rewr_step THENC
      RAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV(LAND_CONV
        (TRY_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))))) THENC
      RAND_CONV conv)) tm in
  conv;;

(*** Examples:

BYTELIST_EXPAND_CONV `read (memory :> bytelist (x,1)) s0`;;

BYTELIST_EXPAND_CONV `read (memory :> bytelist (word_add x (word 7),5)) s`;;

****)

let BYTELIST_DIGITIZE_TAC =
  let ty8 = `:byte` in
  fun s tm ->
    let th = BYTELIST_EXPAND_CONV tm in
    let tms = dest_list(rand(concl th)) in
    let vs =
      map (fun i -> mk_var(s^string_of_int i,ty8)) (0--(length tms - 1)) in
    let abseqs = map2 (curry mk_eq) vs tms in
    SUBST_ALL_TAC th THEN MAP_EVERY ABBREV_TAC abseqs;;

(*** Example:

  BYTELIST_DIGITIZE_TAC
    "b_" `read (memory :> bytelist (word_add x (word 1),42)) s`;;

***)

(* ------------------------------------------------------------------------- *)
(* Some general stuff for fiddling with the chunksize for memory             *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_MERGE_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_SPLIT] THENC
    LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV))))) in
  let rec conv n tm =
    if n = 0 then REFL tm else
    (baseconv THENC BINOP_CONV (conv(n - 1))) tm in
  conv;;

let READ_MEMORY_FULLMERGE_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_SPLIT] THENC
    LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV))))) in
  let rec conv tm =
    (baseconv THENC BINOP_CONV(TRY_CONV conv)) tm in
  conv;;

let MEMORY_128_FROM_16_TAC =
  let a_tm = `a:int64` and n_tm = `n:num` and i64_ty = `:int64`
  and pat = `read (memory :> bytes128(word_add a (word n))) s0` in
  fun v n ->
    let pat' = subst[mk_var(v,i64_ty),a_tm] pat in
    let f i =
      let itm = mk_small_numeral(16*i) in
      READ_MEMORY_MERGE_CONV 3 (subst[itm,n_tm] pat') in
    MP_TAC(end_itlist CONJ (map f (0--(n-1))));;

let MEMORY_128_FROM_64_TAC =
  let a_tm = `a:int64` and n_tm = `n:num` and i64_ty = `:int64`
  and pat = `read (memory :> bytes128(word_add a (word n))) s0` in
  fun v boff n ->
    let pat' = subst[mk_var(v,i64_ty),a_tm] pat in
    let f i =
      let itm = mk_small_numeral(boff + 16*i) in
      READ_MEMORY_MERGE_CONV 1 (subst[itm,n_tm] pat') in
    MP_TAC(end_itlist CONJ (map f (0--(n-1))));;

let READ_MEMORY_SPLIT_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_UNSPLIT] THENC
    BINOP_CONV(LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV)))))) in
  let rec conv n tm =
    if n = 0 then REFL tm else
    (baseconv THENC BINOP_CONV (conv(n - 1))) tm in
  conv;;

let MEMORY_SPLIT_TAC k =
  let tac =
    STRIP_ASSUME_TAC o
    CONV_RULE (BINOP_CONV(BINOP2_CONV
       (ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) WORD_REDUCE_CONV)) o
    GEN_REWRITE_RULE I [el k (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] in
  EVERY_ASSUM (fun th -> try tac th with Failure _ -> ALL_TAC);;
