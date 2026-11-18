(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Byte strings, encoding and decoding.                                       *)
(* ========================================================================= *)

needs "common/fips203/properties/compression.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Byte strings, encoding and decoding. The first four theorems are also in  *)
(* common/words2.ml, with the same statements.                               *)
(* ------------------------------------------------------------------------- *)

let LENGTH_BYTELIST_OF_NUM = prove
 (`!k n. LENGTH(bytelist_of_num k n) = k`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[bytelist_of_num; LENGTH]);;

let NUM_OF_BYTELIST_OF_NUM = prove
 (`!k n. num_of_bytelist(bytelist_of_num k n) = n MOD 256 EXP k`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[bytelist_of_num; num_of_bytelist] THEN
  REWRITE_TAC[EXP; MOD_1] THEN GEN_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[MOD_MULT_MOD] THEN
  MP_TAC(SPECL [`n:num`; `256`] DIVISION) THEN ARITH_TAC);;

let NUM_OF_BYTELIST_BOUND = prove
 (`!l. num_of_bytelist l < 256 EXP (LENGTH l)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; num_of_bytelist; ARITH; EXP] THEN
  MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ASM_ARITH_TAC);;

let BYTELIST_OF_NUM_OF_BYTELIST = prove
 (`!l. bytelist_of_num (LENGTH l) (num_of_bytelist l) = l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[num_of_bytelist; bytelist_of_num; LENGTH] THEN FIRST_X_ASSUM
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  SIMP_TAC[CONS_11; MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ; WORD_VAL_GALOIS] THEN
  REWRITE_TAC[DIMINDEX_8; MOD_EQ_SELF; ARITH; MOD_MOD_REFL] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
  SIMP_TAC[DIV_LT; ADD_CLAUSES] THEN MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

let MLKEM_ENCODE_LENGTH = prove
 (`!d n f. LENGTH(mlkem_encode d n f) = (d * n) DIV 8`,
  REWRITE_TAC[mlkem_encode; LENGTH_BYTELIST_OF_NUM]);;

let MLKEM_ENCODE_DIGIT = prove
 (`!d (f:num->int) i. num_of_int(f i rem &2 pow d) < 2 EXP d /\
                      &(num_of_int(f i rem &2 pow d)) = f i rem &2 pow d`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `&0 <= (f:num->int) i rem &2 pow d` ASSUME_TAC THENL
   [REWRITE_TAC[INT_REM_POS_EQ; INT_POW_EQ_0] THEN CONV_TAC INT_REDUCE_CONV;
    ASM_SIMP_TAC[INT_OF_NUM_OF_INT]] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN ASM_SIMP_TAC[INT_OF_NUM_OF_INT] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_POW; INT_LT_REM_EQ; INT_LT_POW2]);;

let NUM_OF_BYTELIST_MLKEM_ENCODE = prove
 (`!d n f. 8 divides (d * n)
           ==> num_of_bytelist(mlkem_encode d n f) =
               nsum {i | i < n}
                    (\i. num_of_int(f i rem &2 pow d) * 2 EXP (d * i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_encode; NUM_OF_BYTELIST_OF_NUM] THEN
  MATCH_MP_TAC MOD_LT THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` MP_TAC o REWRITE_RULE[divides]) THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `(8 * m) DIV 8 = m`] THEN
  SUBGOAL_THEN `256 EXP m = (2 EXP d) EXP n` SUBST1_TAC THENL
   [REWRITE_TAC[EXP_EXP; ARITH_RULE `256 = 2 EXP 8`] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MESON[EXP_EXP; MULT_SYM]
   `b * 2 EXP (d * i) = (2 EXP d) EXP i * b`] THEN
  MATCH_MP_TAC DIGITSUM_BOUND THEN REWRITE_TAC[MLKEM_ENCODE_DIGIT]);;

let MLKEM_DECODE_ENCODE = prove
 (`!d n f i.
        8 divides (d * n) /\ i < n
        ==> mlkem_decode d (mlkem_encode d n f) i =
            if d = 12 then (f i rem &2 pow d) rem &3329 else f i rem &2 pow d`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[mlkem_decode; NUM_OF_BYTELIST_MLKEM_ENCODE] THEN
  REWRITE_TAC[MESON[EXP_EXP; MULT_SYM]
   `b * 2 EXP (d * i) = (2 EXP d) EXP i * b`] THEN
  REWRITE_TAC[GSYM EXP_EXP] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPECL [`2 EXP d`; `\i. num_of_int ((f:num->int) i rem &2 pow d)`;
                 `{i:num | i < n}`; `i:num`] DIGITSUM_DIV_MOD) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; MLKEM_ENCODE_DIGIT] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MLKEM_ENCODE_DIGIT] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let MLKEM_DECODE_ENCODE_SMALL = prove
 (`!d n f i.
        8 divides (d * n) /\ i < n /\ ~(d = 12) /\ &0 <= f i /\ f i < &2 pow d
        ==> mlkem_decode d (mlkem_encode d n f) i = f i`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_DECODE_ENCODE] THEN
  MATCH_MP_TAC INT_REM_LT THEN ASM_REWRITE_TAC[]);;

let MLKEM_DECODE_ENCODE_12 = prove
 (`!n f i.
        8 divides (12 * n) /\ i < n /\ &0 <= f i /\ f i < &3329
        ==> mlkem_decode 12 (mlkem_encode 12 n f) i = f i`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_DECODE_ENCODE] THEN
  SUBGOAL_THEN `(f:num->int) i rem &2 pow 12 = f i` SUBST1_TAC THEN
  MATCH_MP_TAC INT_REM_LT THEN ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* mlkem_slice a n b is the list of the n bytes of b from position a.        *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLKEM_SLICE = prove
 (`!a n (b:byte list). LENGTH (mlkem_slice a n b) = n`,
  REWRITE_TAC[mlkem_slice; LENGTH_LIST_OF_SEQ]);;

let EL_MLKEM_SLICE = prove
 (`!a n (b:byte list) i. i < n ==> EL i (mlkem_slice a n b) = EL (a + i) b`,
  SIMP_TAC[mlkem_slice; EL_LIST_OF_SEQ]);;

let MLKEM_EQ_SLICE_SLICE = prove
 (`!a n b m (l:byte list).
     b + m <= n
     ==> mlkem_slice b m (mlkem_slice a n l) = mlkem_slice (a + b) m l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_MLKEM_SLICE] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `b + i < n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MLKEM_SLICE; ADD_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Bytes and bits of num_of_bytelist b, and bytelist_of_num n v as the       *)
(* only list of n bytes whose byte m is (v DIV 2 EXP (8 * m)) MOD 256.       *)
(* ------------------------------------------------------------------------- *)

let BYTES_NUM_OF_BYTELIST_BYTE = prove
 (`!(b:byte list) i.
     i < LENGTH b ==> (num_of_bytelist b DIV 2 EXP (8 * i)) MOD 256 =
                      val (EL i b)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  INDUCT_TAC THEN
  REWRITE_TAC[num_of_bytelist; EL; HD; TL; LT_SUC; MULT_CLAUSES; EXP; DIV_1]
  THENL
   [DISCH_THEN(K ALL_TAC) THEN ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT];
    DISCH_TAC THEN
    SUBGOAL_THEN `2 EXP (8 + 8 * i) = 256 * 2 EXP (8 * i)` SUBST1_TAC THENL
     [REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[GSYM DIV_DIV] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; ARITH_EQ; DIV_LT; ADD_CLAUSES]]);;

let BYTES_BIT_DIGIT = prove
 (`!x y j. j < 8 /\ x MOD 256 = y MOD 256
           ==> (ODD (x DIV 2 EXP j) <=> ODD (y DIV 2 EXP j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP (j + 1) * 2 EXP (7 - j) = 256` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN
    SUBGOAL_THEN `(j + 1) + (7 - j) = 8` SUBST1_TAC THENL
     [ASM_ARITH_TAC; CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `x MOD 2 EXP (j + 1) = y MOD 2 EXP (j + 1)` MP_TAC THENL
   [MP_TAC(SPECL [`x:num`; `2 EXP (j + 1)`; `2 EXP (7 - j)`] MOD_MOD) THEN
    MP_TAC(SPECL [`y:num`; `2 EXP (j + 1)`; `2 EXP (7 - j)`] MOD_MOD) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ODD_MOD; DIV_MOD] THEN
  SUBGOAL_THEN `2 EXP j * 2 = 2 EXP (j + 1)` SUBST1_TAC THENL
   [REWRITE_TAC[EXP_ADD; EXP_1]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let BYTES_BYTELIST_BIT = prove
 (`!(b:byte list) i j.
     i < LENGTH b /\ j < 8
     ==> (ODD (num_of_bytelist b DIV 2 EXP (8 * i + j)) <=>
          ODD (val (EL i b) DIV 2 EXP j))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  MATCH_MP_TAC BYTES_BIT_DIGIT THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[BYTES_NUM_OF_BYTELIST_BYTE] THEN
  MP_TAC(ISPEC `EL i (b:byte list)` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT]);;

let BYTES_BYTELIST_OF_NUM_EL = prove
 (`!n v (l:byte list).
     LENGTH l = n /\
     (!m. m < n ==> val (EL m l) = (v DIV 2 EXP (8 * m)) MOD 256)
     ==> l = bytelist_of_num n v`,
  INDUCT_TAC THEN GEN_TAC THEN X_GEN_TAC `l:byte list` THEN
  STRUCT_CASES_TAC(ISPEC `l:byte list` list_CASES) THEN
  REWRITE_TAC[LENGTH; bytelist_of_num; NOT_SUC; GSYM NOT_SUC; SUC_INJ] THEN
  STRIP_TAC THEN REWRITE_TAC[CONS_11] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[LT_0; EL; HD; MULT_CLAUSES; EXP; DIV_1] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[WORD_VAL];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC m`) THEN
    ASM_REWRITE_TAC[LT_SUC; EL; TL; MULT_CLAUSES] THEN
    SUBGOAL_THEN `2 EXP (8 + 8 * m) = 256 * 2 EXP (8 * m)` SUBST1_TAC THENL
     [REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[GSYM DIV_DIV] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A slice of a byte string as a number, and decoding from a slice.          *)
(* ------------------------------------------------------------------------- *)

let BYTES_MLKEM_SLICE_BYTELIST = prove
 (`!a n (b:byte list).
     a + n <= LENGTH b
     ==> mlkem_slice a n b =
         bytelist_of_num n (num_of_bytelist b DIV 256 EXP a)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BYTES_BYTELIST_OF_NUM_EL THEN
  REWRITE_TAC[LENGTH_MLKEM_SLICE] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_MLKEM_SLICE] THEN
  MP_TAC(SPECL [`b:byte list`; `a + m`] BYTES_NUM_OF_BYTELIST_BYTE) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `(256:num) EXP a = 2 EXP (8 * a)` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP]; ALL_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `8 * a + 8 * m = 8 * (a + m)`]);;

let BYTES_NUM_OF_BYTELIST_SLICE = prove
 (`!a n (b:byte list).
     a + n <= LENGTH b
     ==> num_of_bytelist (mlkem_slice a n b) =
         (num_of_bytelist b DIV 256 EXP a) MOD 256 EXP n`,
  SIMP_TAC[BYTES_MLKEM_SLICE_BYTELIST; NUM_OF_BYTELIST_OF_NUM]);;

let BYTES_DIV_MOD_MOD = prove
 (`!x s t e. s + t <= e
             ==> ((x MOD 2 EXP e) DIV 2 EXP s) MOD 2 EXP t =
                 (x DIV 2 EXP s) MOD 2 EXP t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `2 EXP e = 2 EXP (s + t) * 2 EXP (e - (s + t))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MOD_MOD]);;

let BYTES_MLKEM_DECODE_SLICE = prove
 (`!d (b:byte list) a n q j.
     a + n <= LENGTH b /\ 8 * a = d * q /\ d * j + d <= 8 * n
     ==> mlkem_decode d (mlkem_slice a n b) j = mlkem_decode d b (q + j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_decode] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `(num_of_bytelist (mlkem_slice a n b) DIV 2 EXP (d * j)) MOD 2 EXP d =
    (num_of_bytelist b DIV 2 EXP (d * (q + j))) MOD 2 EXP d`
   (fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[BYTES_NUM_OF_BYTELIST_SLICE] THEN
  SUBGOAL_THEN `(256:num) EXP a = 2 EXP (d * q)` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(256:num) EXP n = 2 EXP (8 * n)` SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP]; ALL_TAC] THEN
  ASM_SIMP_TAC[BYTES_DIV_MOD_MOD] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `d * q + d * j = d * (q + j)`]);;

let KPKE_DECODE_SMALL = prove
 (`!d b i. ~(d = 12)
           ==> &0 <= mlkem_decode d b i /\ mlkem_decode d b i < &2 pow d`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[mlkem_decode; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[INT_POS; INT_OF_NUM_POW; INT_OF_NUM_LT] THEN
  SIMP_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* mlkem_encode of natural numbers as bytelist_of_num of a sum of digits.    *)
(* If 256 * k values are encoded together, block kv of the bytes is the      *)
(* encoding of the 256 values of that block (for d = 12, 10 and 11).         *)
(* ------------------------------------------------------------------------- *)

let BYTES_MLKEM_ENCODE_NSUM = prove
 (`!d n (g:num->num).
     mlkem_encode d n (\i. &(g i)) =
     bytelist_of_num ((d * n) DIV 8)
       (nsum {i | i < n} (\i. (g i MOD 2 EXP d) * 2 EXP (i * d)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlkem_encode] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_REM; NUM_OF_INT_OF_NUM] THEN
  REWRITE_TAC[MULT_SYM]);;

let BYTES_NSUM_LT_ADD = prove
 (`!(f:num->num) a b.
     nsum {i | i < a + b} f =
     nsum {i | i < a} f + nsum {i | i < b} (\i. f (a + i))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; NSUM_CLAUSES_NUMSEG_LT] THEN ARITH_TAC);;

let BYTES_SPLIT_SUM = prove
 (`!(w:num->num) k.
     nsum {i | i < 256 * k} (\i. w i * 2 EXP (12 * i)) =
     nsum {i | i < k}
       (\j. 2 EXP (3072 * j) *
            nsum {i | i < 256} (\i. w (256 * j + i) * 2 EXP (12 * i)))`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; NSUM_CLAUSES_NUMSEG_LT] THEN
  REWRITE_TAC[ARITH_RULE `256 + 256 * k = 256 * k + 256`] THEN
  MP_TAC(SPECL [`\i. (w:num->num) i * 2 EXP (12 * i)`; `256 * k`; `256`]
               BYTES_NSUM_LT_ADD) THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM NSUM_LMUL] THEN
  MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[MULT_ASSOC; GSYM EXP_ADD] THEN
  SUBGOAL_THEN `12 * (256 * k + i) = 12 * i + 3072 * k` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXP_ADD] THEN ARITH_TAC);;

let BYTES_SPLIT_SUM_d = prove
 (`!d (w:num->num) k.
     nsum {i | i < 256 * k} (\i. w i * 2 EXP (d * i)) =
     nsum {i | i < k}
       (\j. 2 EXP (d * 256 * j) *
            nsum {i | i < 256} (\i. w (256 * j + i) * 2 EXP (d * i)))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; NSUM_CLAUSES_NUMSEG_LT] THEN
  REWRITE_TAC[ARITH_RULE `256 + 256 * k = 256 * k + 256`] THEN
  MP_TAC(SPECL [`\i. (w:num->num) i * 2 EXP (d * i)`; `256 * k`; `256`]
               BYTES_NSUM_LT_ADD) THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM NSUM_LMUL] THEN
  MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[MULT_ASSOC; GSYM EXP_ADD] THEN
  SUBGOAL_THEN `d * (256 * k + i) = d * i + d * 256 * k` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXP_ADD; MULT_ASSOC] THEN ARITH_TAC);;

let BYTES_ENCODE_12_BLOCK_EL = prove
 (`!k (f:num->int) kv j.
     kv < k /\ j < 384
     ==> EL (384 * kv + j) (mlkem_encode 12 (256 * k) f) =
         EL j (mlkem_encode 12 256 (\i. f (256 * kv + i)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mlkem_encode] THEN
  (SUBGOAL_THEN `(12 * (256 * k)) DIV 8 = 384 * k /\ (12 * 256) DIV 8 = 384`
   STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ARITH_TAC; ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN
  (SUBGOAL_THEN `384 * kv + j < 384 * k` ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC]) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`bytelist_of_num (384 * k)
                   (nsum {i | i < 256 * k}
                     (\i. num_of_int ((f:num->int) i rem &2 pow 12) *
                          2 EXP (12 * i)))`;
                 `384 * kv + j`] BYTES_NUM_OF_BYTELIST_BYTE) THEN
  REWRITE_TAC[LENGTH_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL
   [`bytelist_of_num 384
      (nsum {i | i < 256}
        (\i. num_of_int ((f:num->int) (256 * kv + i) rem &2 pow 12) *
             2 EXP (12 * i)))`;
    `j:num`] BYTES_NUM_OF_BYTELIST_BYTE) THEN
  REWRITE_TAC[LENGTH_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  (* Transform MOD 256 EXP (384*k) and MOD 256 EXP 384 *)
  (SUBGOAL_THEN
    `!x. x MOD 256 EXP (384 * k) DIV 2 EXP (8 * (384 * kv + j)) MOD 256 =
         x DIV 2 EXP (8 * (384 * kv + j)) MOD 256`
    (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN
     SUBGOAL_THEN `(256:num) EXP (384 * k) = 2 EXP (8 * (384 * k))`
       SUBST1_TAC THENL
      [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP]; ALL_TAC] THEN
     MP_TAC(SPECL [`x:num`; `8 * (384 * kv + j)`; `8`; `8 * (384 * k)`]
                  BYTES_DIV_MOD_MOD) THEN
     ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[ARITH_RULE `(2:num) EXP 8 = 256`];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
    `!x. x MOD 256 EXP 384 DIV 2 EXP (8 * j) MOD 256 =
         x DIV 2 EXP (8 * j) MOD 256`
    (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN
     SUBGOAL_THEN `(256:num) EXP 384 = 2 EXP (8 * 384)` SUBST1_TAC THENL
      [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP]; ALL_TAC] THEN
     MP_TAC(SPECL [`x:num`; `8 * j`; `8`; `8 * 384`] BYTES_DIV_MOD_MOD) THEN
     ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[ARITH_RULE `(2:num) EXP 8 = 256`];
     ALL_TAC]) THEN
  MP_TAC(SPECL [`\i. num_of_int ((f:num->int) i rem &2 pow 12)`; `k:num`]
               BYTES_SPLIT_SUM) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  (SUBGOAL_THEN
    `nsum {i | i < k}
       (\jj. 2 EXP (3072 * jj) *
              nsum {i | i < 256}
                (\i. num_of_int ((f:num->int) (256 * jj + i) rem &2 pow 12) *
                     2 EXP (12 * i))) =
     nsum {i | i < k}
       (\j'.
           2 EXP (3072 * j') *
           nsum {i | i < 256}
             (\i. num_of_int (f (256 * j' + i) rem &2 pow 12) *
                  2 EXP (12 * i)))`
    SUBST1_TAC THENL
    [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN
     REFL_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `8 * (384 * kv + j) = 3072 * kv + 8 * j` SUBST1_TAC THENL
    [ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  (SUBGOAL_THEN
    `(nsum {i | i < k}
       (\j'. 2 EXP (3072 * j') *
              nsum {i | i < 256}
                (\i. num_of_int ((f:num->int) (256 * j' + i) rem &2 pow 12) *
                     2 EXP (12 * i))))
     DIV 2 EXP (3072 * kv) MOD 2 EXP 3072 =
     nsum {i | i < 256}
       (\i. num_of_int (f (256 * kv + i) rem &2 pow 12) * 2 EXP (12 * i))`
    MP_TAC THENL
    [ALL_TAC;
     DISCH_TAC THEN
     SUBGOAL_THEN
      `((nsum {i | i < k}
           (\j'. 2 EXP (3072 * j') *
                 nsum {i | i < 256}
                   (\i. num_of_int ((f:num->int) (256 * j' + i) rem &2 pow 12) *
                        2 EXP (12 * i))) DIV
         2 EXP (3072 * kv)) DIV
        2 EXP (8 * j)) MOD 256 =
       (nsum {i | i < 256}
         (\i. num_of_int (f (256 * kv + i) rem &2 pow 12) * 2 EXP (12 * i))
        DIV 2 EXP (8 * j)) MOD 256`
      (fun th2 -> REWRITE_TAC[th2]) THEN
     FIRST_X_ASSUM MP_TAC THEN
       SPEC_TAC(`nsum {i | i < k}
                  (\j'. 2 EXP (3072 * j') *
                    nsum {i | i < 256}
                      (\i. num_of_int
                        ((f:num->int) (256 * j' + i) rem &2 pow 12) *
                           2 EXP (12 * i))) DIV
                 2 EXP (3072 * kv)`, `A:num`) THEN
       SPEC_TAC(`nsum {i | i < 256}
                  (\i. num_of_int ((f:num->int) (256 * kv + i) rem &2 pow 12) *
                       2 EXP (12 * i))`, `B:num`) THEN
       REPEAT GEN_TAC THEN DISCH_TAC THEN
       SUBGOAL_THEN `A MOD 2 EXP 3072 = B` MP_TAC THENL
        [ASM_REWRITE_TAC[]; ALL_TAC] THEN
       DISCH_THEN(SUBST1_TAC o SYM) THEN
       MP_TAC(SPECL [`A:num`; `8 * j`; `8`; `3072`] BYTES_DIV_MOD_MOD) THEN
       ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
       REWRITE_TAC[ARITH_RULE `(2:num) EXP 8 = 256`]]) THENL
   [MP_TAC(ISPECL
      [`2 EXP 3072`;
       `\j'. nsum {i | i < 256}
               (\i. num_of_int ((f:num->int) (256 * j' + i) rem &2 pow 12) *
                    2 EXP (12 * i))`;
       `{i:num | i < k}`; `kv:num`] DIGITSUM_DIV_MOD) THEN
     REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
     (ANTS_TAC THENL
       [REPEAT STRIP_TAC THEN
        REWRITE_TAC[ARITH_RULE `3072 = 12 * 256`] THEN
        REWRITE_TAC[MESON[EXP_EXP; MULT_SYM]
         `(2 EXP (12 * 256) = (2 EXP 12) EXP 256) /\
          (b * 2 EXP (12 * i) = (2 EXP 12) EXP i * b)`] THEN
        MATCH_MP_TAC DIGITSUM_BOUND THEN
        REPEAT STRIP_TAC THEN
        REWRITE_TAC[MLKEM_ENCODE_DIGIT];
        ALL_TAC]) THEN
     (SUBGOAL_THEN
       `nsum {i | i < k}
          (\j'. 2 EXP (3072 * j') *
                 (\j'. nsum {i | i < 256}
                         (\i. num_of_int
                           ((f:num->int) (256 * j' + i) rem &2 pow 12) *
                              2 EXP (12 * i))) j') =
        nsum {i | i < k}
          (\j'. (2 EXP 3072) EXP j' *
                 (\j'. nsum {i | i < 256}
                         (\i. num_of_int
                           ((f:num->int) (256 * j' + i) rem &2 pow 12) *
                              2 EXP (12 * i))) j')`
       SUBST1_TAC THENL
       [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_EXP] THEN REFL_TAC;
        ALL_TAC]) THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[GSYM EXP_EXP];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let BYTES_ENCODE_10_BLOCK_EL = prove
 (`!k (f:num->int) kv j.
     kv < k /\ j < 320
     ==> EL (320 * kv + j) (mlkem_encode 10 (256 * k) f) =
         EL j (mlkem_encode 10 256 (\i. f (256 * kv + i)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mlkem_encode] THEN
  (SUBGOAL_THEN `(10 * (256 * k)) DIV 8 = 320 * k /\ (10 * 256) DIV 8 = 320`
   STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ARITH_TAC; ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN
  (SUBGOAL_THEN `320 * kv + j < 320 * k` ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC]) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`bytelist_of_num (320 * k)
                   (nsum {i | i < 256 * k}
                     (\i. num_of_int ((f:num->int) i rem &2 pow 10) *
                          2 EXP (10 * i)))`;
                 `320 * kv + j`] BYTES_NUM_OF_BYTELIST_BYTE) THEN
  REWRITE_TAC[LENGTH_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL
   [`bytelist_of_num 320
      (nsum {i | i < 256}
        (\i. num_of_int ((f:num->int) (256 * kv + i) rem &2 pow 10) *
             2 EXP (10 * i)))`;
    `j:num`] BYTES_NUM_OF_BYTELIST_BYTE) THEN
  REWRITE_TAC[LENGTH_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  (SUBGOAL_THEN
    `!x. x MOD 256 EXP (320 * k) DIV 2 EXP (8 * (320 * kv + j)) MOD 256 =
         x DIV 2 EXP (8 * (320 * kv + j)) MOD 256`
    (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN
     SUBGOAL_THEN `(256:num) EXP (320 * k) = 2 EXP (8 * (320 * k))`
       SUBST1_TAC THENL
      [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP]; ALL_TAC] THEN
     MP_TAC(SPECL [`x:num`; `8 * (320 * kv + j)`; `8`; `8 * (320 * k)`]
                  BYTES_DIV_MOD_MOD) THEN
     ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[ARITH_RULE `(2:num) EXP 8 = 256`];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
    `!x. x MOD 256 EXP 320 DIV 2 EXP (8 * j) MOD 256 =
         x DIV 2 EXP (8 * j) MOD 256`
    (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN
     SUBGOAL_THEN `(256:num) EXP 320 = 2 EXP (8 * 320)` SUBST1_TAC THENL
      [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP]; ALL_TAC] THEN
     MP_TAC(SPECL [`x:num`; `8 * j`; `8`; `8 * 320`] BYTES_DIV_MOD_MOD) THEN
     ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[ARITH_RULE `(2:num) EXP 8 = 256`];
     ALL_TAC]) THEN
  MP_TAC(SPECL [`10`;
                `\i. num_of_int ((f:num->int) i rem &2 pow 10)`; `k:num`]
               BYTES_SPLIT_SUM_d) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  (SUBGOAL_THEN
    `nsum {i | i < k}
       (\jj. 2 EXP (10 * 256 * jj) *
              nsum {i | i < 256}
                (\i. num_of_int ((f:num->int) (256 * jj + i) rem &2 pow 10) *
                     2 EXP (10 * i))) =
     nsum {i | i < k}
       (\j'. 2 EXP (2560 * j') *
              nsum {i | i < 256}
                (\i. num_of_int (f (256 * j' + i) rem &2 pow 10) *
                     2 EXP (10 * i)))`
    SUBST1_TAC THENL
    [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `8 * (320 * kv + j) = 2560 * kv + 8 * j` SUBST1_TAC THENL
    [ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SUBGOAL_THEN
   `(nsum {i | i < k}
      (\j'. 2 EXP (2560 * j') *
             nsum {i | i < 256}
               (\i. num_of_int ((f:num->int) (256 * j' + i) rem &2 pow 10) *
                    2 EXP (10 * i)))) DIV 2 EXP (2560 * kv) MOD 2 EXP 2560 =
    nsum {i | i < 256}
      (\i. num_of_int (f (256 * kv + i) rem &2 pow 10) * 2 EXP (10 * i))`
   (fun ab ->
      SUBGOAL_THEN
       `((nsum {i | i < k}
            (\j'. 2 EXP (2560 * j') *
                  nsum {i | i < 256}
                    (\i. num_of_int
                      ((f:num->int) (256 * j' + i) rem &2 pow 10) *
                         2 EXP (10 * i)))) DIV 2 EXP (2560 * kv)
         DIV 2 EXP (8 * j)) MOD 256 =
        (nsum {i | i < 256}
          (\i. num_of_int (f (256 * kv + i) rem &2 pow 10) * 2 EXP (10 * i))
         DIV 2 EXP (8 * j)) MOD 256`
       (fun th -> REWRITE_TAC[th]) THEN
      MP_TAC ab THEN
      SPEC_TAC
       (`nsum {i | i < k}
          (\j'. 2 EXP (2560 * j') *
                nsum {i | i < 256}
                  (\i. num_of_int ((f:num->int) (256 * j' + i) rem &2 pow 10) *
                       2 EXP (10 * i))) DIV 2 EXP (2560 * kv)`,
        `A:num`) THEN
      SPEC_TAC
       (`nsum {i | i < 256}
          (\i. num_of_int ((f:num->int) (256 * kv + i) rem &2 pow 10) *
               2 EXP (10 * i))`,
        `B:num`) THEN
      REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(SPECL [`A:num`; `8 * j`; `8`; `2560`] BYTES_DIV_MOD_MOD) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `(2:num) EXP 8 = 256`]) THENL
   [MP_TAC(ISPECL
      [`2 EXP 2560`;
       `\j'. nsum {i | i < 256}
               (\i. num_of_int ((f:num->int) (256 * j' + i) rem &2 pow 10) *
                    2 EXP (10 * i))`;
       `{i:num | i < k}`; `kv:num`] DIGITSUM_DIV_MOD) THEN
     REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
     (ANTS_TAC THENL
       [REPEAT STRIP_TAC THEN
        REWRITE_TAC[ARITH_RULE `2560 = 10 * 256`] THEN
        REWRITE_TAC[MESON[EXP_EXP; MULT_SYM]
         `(2 EXP (10 * 256) = (2 EXP 10) EXP 256) /\
          (b * 2 EXP (10 * i) = (2 EXP 10) EXP i * b)`] THEN
        MATCH_MP_TAC DIGITSUM_BOUND THEN
        REPEAT STRIP_TAC THEN
        REWRITE_TAC[MLKEM_ENCODE_DIGIT];
        ALL_TAC]) THEN
     (SUBGOAL_THEN
       `nsum {i | i < k}
          (\j'. 2 EXP (2560 * j') *
                 (\j'. nsum {i | i < 256}
                         (\i. num_of_int
                           ((f:num->int) (256 * j' + i) rem &2 pow 10) *
                              2 EXP (10 * i))) j') =
        nsum {i | i < k}
          (\j'. (2 EXP 2560) EXP j' *
                 (\j'. nsum {i | i < 256}
                         (\i. num_of_int
                           ((f:num->int) (256 * j' + i) rem &2 pow 10) *
                              2 EXP (10 * i))) j')`
       SUBST1_TAC THENL
       [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_EXP] THEN REFL_TAC;
        ALL_TAC]) THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[GSYM EXP_EXP];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let BYTES_ENCODE_11_BLOCK_EL = prove
 (`!k (f:num->int) kv j.
     kv < k /\ j < 352
     ==> EL (352 * kv + j) (mlkem_encode 11 (256 * k) f) =
         EL j (mlkem_encode 11 256 (\i. f (256 * kv + i)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mlkem_encode] THEN
  (SUBGOAL_THEN `(11 * (256 * k)) DIV 8 = 352 * k /\ (11 * 256) DIV 8 = 352`
   STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ARITH_TAC; ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN
  (SUBGOAL_THEN `352 * kv + j < 352 * k` ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC]) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`bytelist_of_num (352 * k)
                   (nsum {i | i < 256 * k}
                     (\i. num_of_int ((f:num->int) i rem &2 pow 11) *
                          2 EXP (11 * i)))`;
                 `352 * kv + j`] BYTES_NUM_OF_BYTELIST_BYTE) THEN
  REWRITE_TAC[LENGTH_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL
   [`bytelist_of_num 352
      (nsum {i | i < 256}
        (\i. num_of_int ((f:num->int) (256 * kv + i) rem &2 pow 11) *
             2 EXP (11 * i)))`;
    `j:num`] BYTES_NUM_OF_BYTELIST_BYTE) THEN
  REWRITE_TAC[LENGTH_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  (SUBGOAL_THEN
    `!x. x MOD 256 EXP (352 * k) DIV 2 EXP (8 * (352 * kv + j)) MOD 256 =
         x DIV 2 EXP (8 * (352 * kv + j)) MOD 256`
    (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN
     SUBGOAL_THEN `(256:num) EXP (352 * k) = 2 EXP (8 * (352 * k))`
       SUBST1_TAC THENL
      [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP]; ALL_TAC] THEN
     MP_TAC(SPECL [`x:num`; `8 * (352 * kv + j)`; `8`; `8 * (352 * k)`]
                  BYTES_DIV_MOD_MOD) THEN
     ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[ARITH_RULE `(2:num) EXP 8 = 256`];
     ALL_TAC]) THEN
  (SUBGOAL_THEN
    `!x. x MOD 256 EXP 352 DIV 2 EXP (8 * j) MOD 256 =
         x DIV 2 EXP (8 * j) MOD 256`
    (fun th -> REWRITE_TAC[th]) THENL
    [GEN_TAC THEN
     SUBGOAL_THEN `(256:num) EXP 352 = 2 EXP (8 * 352)` SUBST1_TAC THENL
      [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP]; ALL_TAC] THEN
     MP_TAC(SPECL [`x:num`; `8 * j`; `8`; `8 * 352`] BYTES_DIV_MOD_MOD) THEN
     ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[ARITH_RULE `(2:num) EXP 8 = 256`];
     ALL_TAC]) THEN
  MP_TAC(SPECL [`11`;
                `\i. num_of_int ((f:num->int) i rem &2 pow 11)`; `k:num`]
               BYTES_SPLIT_SUM_d) THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  (SUBGOAL_THEN
    `nsum {i | i < k}
       (\jj. 2 EXP (11 * 256 * jj) *
              nsum {i | i < 256}
                (\i. num_of_int ((f:num->int) (256 * jj + i) rem &2 pow 11) *
                     2 EXP (11 * i))) =
     nsum {i | i < k}
       (\j'. 2 EXP (2816 * j') *
              nsum {i | i < 256}
                (\i. num_of_int (f (256 * j' + i) rem &2 pow 11) *
                     2 EXP (11 * i)))`
    SUBST1_TAC THENL
    [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
     ALL_TAC]) THEN
  (SUBGOAL_THEN `8 * (352 * kv + j) = 2816 * kv + 8 * j` SUBST1_TAC THENL
    [ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SUBGOAL_THEN
   `(nsum {i | i < k}
      (\j'. 2 EXP (2816 * j') *
             nsum {i | i < 256}
               (\i. num_of_int ((f:num->int) (256 * j' + i) rem &2 pow 11) *
                    2 EXP (11 * i)))) DIV 2 EXP (2816 * kv) MOD 2 EXP 2816 =
    nsum {i | i < 256}
      (\i. num_of_int (f (256 * kv + i) rem &2 pow 11) * 2 EXP (11 * i))`
   (fun ab ->
      SUBGOAL_THEN
       `((nsum {i | i < k}
            (\j'. 2 EXP (2816 * j') *
                  nsum {i | i < 256}
                    (\i. num_of_int
                      ((f:num->int) (256 * j' + i) rem &2 pow 11) *
                         2 EXP (11 * i)))) DIV 2 EXP (2816 * kv)
         DIV 2 EXP (8 * j)) MOD 256 =
        (nsum {i | i < 256}
          (\i. num_of_int (f (256 * kv + i) rem &2 pow 11) * 2 EXP (11 * i))
         DIV 2 EXP (8 * j)) MOD 256`
       (fun th -> REWRITE_TAC[th]) THEN
      MP_TAC ab THEN
      SPEC_TAC
       (`nsum {i | i < k}
          (\j'. 2 EXP (2816 * j') *
                nsum {i | i < 256}
                  (\i. num_of_int ((f:num->int) (256 * j' + i) rem &2 pow 11) *
                       2 EXP (11 * i))) DIV 2 EXP (2816 * kv)`,
        `A:num`) THEN
      SPEC_TAC
       (`nsum {i | i < 256}
          (\i. num_of_int ((f:num->int) (256 * kv + i) rem &2 pow 11) *
               2 EXP (11 * i))`,
        `B:num`) THEN
      REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(SPECL [`A:num`; `8 * j`; `8`; `2816`] BYTES_DIV_MOD_MOD) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `(2:num) EXP 8 = 256`]) THENL
   [MP_TAC(ISPECL
      [`2 EXP 2816`;
       `\j'. nsum {i | i < 256}
               (\i. num_of_int ((f:num->int) (256 * j' + i) rem &2 pow 11) *
                    2 EXP (11 * i))`;
       `{i:num | i < k}`; `kv:num`] DIGITSUM_DIV_MOD) THEN
     REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
     (ANTS_TAC THENL
       [REPEAT STRIP_TAC THEN
        REWRITE_TAC[ARITH_RULE `2816 = 11 * 256`] THEN
        REWRITE_TAC[MESON[EXP_EXP; MULT_SYM]
         `(2 EXP (11 * 256) = (2 EXP 11) EXP 256) /\
          (b * 2 EXP (11 * i) = (2 EXP 11) EXP i * b)`] THEN
        MATCH_MP_TAC DIGITSUM_BOUND THEN
        REPEAT STRIP_TAC THEN
        REWRITE_TAC[MLKEM_ENCODE_DIGIT];
        ALL_TAC]) THEN
     (SUBGOAL_THEN
       `nsum {i | i < k}
          (\j'. 2 EXP (2816 * j') *
                 (\j'. nsum {i | i < 256}
                         (\i. num_of_int
                           ((f:num->int) (256 * j' + i) rem &2 pow 11) *
                              2 EXP (11 * i))) j') =
        nsum {i | i < k}
          (\j'. (2 EXP 2816) EXP j' *
                 (\j'. nsum {i | i < 256}
                         (\i. num_of_int
                           ((f:num->int) (256 * j' + i) rem &2 pow 11) *
                              2 EXP (11 * i))) j')`
       SUBST1_TAC THENL
       [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_EXP] THEN REFL_TAC;
        ALL_TAC]) THEN
     CONV_TAC(DEPTH_CONV BETA_CONV) THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[GSYM EXP_EXP];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
