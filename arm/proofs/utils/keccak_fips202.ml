(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas about the padding and the blocks of the padded message, as         *)
(* numbers, for keccak_absorb, and about the output of keccak_sponge, on top *)
(* of the bridge between keccak_f1600 and "keccak 24" in keccak_f1600.ml,    *)
(* which this file loads (the two used to be one file).                      *)
(* ========================================================================= *)

needs "arm/proofs/utils/keccak_f1600.ml";;
needs "common/mlkem_mldsa.ml";;
(* ------------------------------------------------------------------------- *)
(* The padding as a number. For a message of mlen bytes as a number M, the   *)
(* padded message in keccak_sponge is the number                             *)
(* M + 2 EXP (8 * mlen) * num_of_bytelist(keccak_pad r d mlen), whose blocks *)
(* are the whole blocks of M, then the rest of M with the padding.           *)
(* ------------------------------------------------------------------------- *)

let NUM_OF_BYTELIST_APPEND = prove
 (`!l1 l2. num_of_bytelist (APPEND l1 l2) =
           num_of_bytelist l1 + 2 EXP (8 * LENGTH l1) * num_of_bytelist l2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; num_of_bytelist; LENGTH; MULT_CLAUSES; EXP;
                  ADD_CLAUSES] THEN
  GEN_TAC THEN REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC NUM_RING);;

let NUM_OF_BYTELIST_REPLICATE_0 = prove
 (`!n. num_of_bytelist (REPLICATE n (word 0:byte)) = 0`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[REPLICATE; num_of_bytelist; VAL_WORD_0] THEN ARITH_TAC);;

let KECCAK_PAD_NUM = prove
 (`!r d len.
        0 < r /\ d < 128
        ==> num_of_bytelist(keccak_pad r d len) =
            if len MOD r = r - 1 then d + 128
            else d + 2 EXP (8 * (r - len MOD r - 1)) * 128`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[keccak_pad] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[num_of_bytelist; NUM_OF_BYTELIST_APPEND;
                  NUM_OF_BYTELIST_REPLICATE_0; LENGTH_REPLICATE;
                  VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `d < 128 ==> d < 256 /\ d + 128 < 256`] THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  MP_TAC(SPECL [`len:num`; `r:num`] MOD_LT_EQ) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `r - len MOD r - 1 = (r - len MOD r - 2) + 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let KECCAK_PAD_BOUND = prove
 (`!r d len.
        0 < r /\ d < 128
        ==> num_of_bytelist(keccak_pad r d len) < 2 EXP (8 * (r - len MOD r))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[KECCAK_PAD_NUM] THEN
  MP_TAC(SPECL [`len:num`; `r:num`] MOD_LT_EQ) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?k. r - len MOD r = k + 1` (X_CHOOSE_THEN `k:num`
   (fun th -> REWRITE_TAC[th; ADD_SUB] THEN ASSUME_TAC th))
  THENL [EXISTS_TAC `r - len MOD r - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `~(2 EXP (8 * k) = 0)` MP_TAC THENL
   [REWRITE_TAC[EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `k = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `d < 128` THEN ARITH_TAC;
    SPEC_TAC(`2 EXP (8 * k)`,`e:num`) THEN
    UNDISCH_TAC `d < 128` THEN ARITH_TAC]);;

let WORD_XOR_DISJOINT_ADD = prove
 (`!a b k. a < 2 EXP k
           ==> word_xor (word a:N word) (word(2 EXP k * b)) =
               word(a + 2 EXP k * b)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[WORD_ADD] THEN MATCH_MP_TAC WORD_ADD_XOR THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_WORD_0; BIT_WORD] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i < k:num` THENL
   [SUBGOAL_THEN `(2 EXP k * b) DIV 2 EXP i = 2 * 2 EXP (k - i - 1) * b`
     (fun th -> REWRITE_TAC[th; ODD_MULT; ARITH_ODD]) THEN
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[ADD_CLAUSES; EXP_EQ_0; ARITH_EQ;
                ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
    SUBGOAL_THEN `k = (k - i - 1) + 1 + i`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th])
    THENL [ASM_ARITH_TAC; REWRITE_TAC[EXP_ADD; EXP_1; MULT_AC]];
    SUBGOAL_THEN `a DIV 2 EXP i = 0` (fun th -> REWRITE_TAC[th; ARITH_ODD])
    THEN MATCH_MP_TAC DIV_LT THEN
    TRANS_TAC LTE_TRANS `2 EXP k` THEN ASM_REWRITE_TAC[LE_EXP] THEN
    ASM_ARITH_TAC]);;

let KECCAK_BLOCK_FULL = prove
 (`!M pad mlen r k.
        r * (k + 1) <= mlen
        ==> ((M + 2 EXP (8 * mlen) * pad) DIV 2 EXP (8 * r * k)) MOD
            2 EXP (8 * r) =
            (M DIV 2 EXP (8 * r * k)) MOD 2 EXP (8 * r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?e. mlen = r * k + r + e` (X_CHOOSE_THEN `e:num` SUBST1_TAC)
  THENL [EXISTS_TAC `mlen - r * (k + 1)` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD] THEN
  ONCE_REWRITE_TAC[ARITH_RULE
   `M + (a * b * c) * p = (b * c * p) * a + M`] THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `b * c * p + x = (c * p) * b + x`] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

let KECCAK_BLOCK_LAST = prove
 (`!M pad mlen r.
        0 < r /\ M < 2 EXP (8 * mlen) /\
        pad < 2 EXP (8 * (r - mlen MOD r))
        ==> ((M + 2 EXP (8 * mlen) * pad) DIV
             2 EXP (8 * r * mlen DIV r)) MOD 2 EXP (8 * r) =
            M DIV 2 EXP (8 * r * mlen DIV r) + 2 EXP (8 * mlen MOD r) * pad`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
  ASM_CASES_TAC `r = 0` THEN ASM_REWRITE_TAC[LT_REFL] THEN
  MAP_EVERY ABBREV_TAC [`q = mlen DIV r`; `t = mlen MOD r`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN STRIP_TAC THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `8 * q * r = 8 * r * q`] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `M + (a * b) * p = (b * p) * a + M`] THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ADD_SYM] THEN
  MATCH_MP_TAC MOD_LT THEN
  SUBGOAL_THEN `M DIV 2 EXP (8 * q * r) < 2 EXP (8 * t)` ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    UNDISCH_TAC `M < 2 EXP (8 * (q * r + t))` THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP (8 * r) = 2 EXP (8 * t) * 2 EXP (8 * (r - t))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `2 EXP (8 * t) + 2 EXP (8 * t) * pad` THEN
  ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN
  REWRITE_TAC[ARITH_RULE `a + a * b = a * (b + 1)`; LE_MULT_LCANCEL] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The output of keccak_sponge in terms of the state after absorbing all but *)
(* the last permutation, as for mlk_keccak_absorb_once in mlkem-native, and  *)
(* the first n bytes of it, or of any block of it, for n up to the rate.     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_KECCAK_PAD = prove
 (`!r d len. 0 < r ==> LENGTH(keccak_pad r d len) = r - len MOD r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[keccak_pad] THEN
  MP_TAC(SPECL [`len:num`; `r:num`] MOD_LT_EQ) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN DISCH_TAC THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[LENGTH; LENGTH_APPEND; LENGTH_REPLICATE] THEN
  ASM_ARITH_TAC);;

let KECCAK_SPONGE_ABSORB = prove
 (`!r d (m:byte list).
        0 < r
        ==> keccak_absorb r
             (num_of_bytelist(APPEND m (keccak_pad r d (LENGTH m))))
             (LENGTH(APPEND m (keccak_pad r d (LENGTH m))) DIV r) =
            keccak_f1600
             (word_xor
               (keccak_absorb r
                 (num_of_bytelist m +
                  2 EXP (8 * LENGTH m) *
                  num_of_bytelist(keccak_pad r d (LENGTH m)))
                 (LENGTH m DIV r))
               (word((num_of_bytelist m +
                      2 EXP (8 * LENGTH m) *
                      num_of_bytelist(keccak_pad r d (LENGTH m))) DIV
                     2 EXP (8 * r * LENGTH m DIV r) MOD 2 EXP (8 * r))))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NUM_OF_BYTELIST_APPEND; LENGTH_APPEND; LENGTH_KECCAK_PAD] THEN
  SUBGOAL_THEN
   `(LENGTH(m:byte list) + r - LENGTH m MOD r) DIV r = SUC(LENGTH m DIV r)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
    MP_TAC(SPECL [`LENGTH(m:byte list)`; `r:num`] DIVISION) THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN ARITH_TAC;
    REWRITE_TAC[keccak_absorb]]);;

let KECCAK_SQUEEZE_F1600 = prove
 (`!k S. keccak_f1600(keccak_squeeze k S) = keccak_squeeze k (keccak_f1600 S)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[keccak_squeeze]);;

let KECCAK_SPONGE_SQUEEZE = prove
 (`!c d (m:byte list) r P i.
        (1600 - c) DIV 8 = r /\ 0 < r /\
        P = num_of_bytelist m +
            2 EXP (8 * LENGTH m) * num_of_bytelist(keccak_pad r d (LENGTH m))
        ==> keccak_sponge c d m i =
            word_subword
             (keccak_squeeze (i DIV r + 1)
               (word_xor (keccak_absorb r P (LENGTH m DIV r))
                         (word((P DIV 2 EXP (8 * r * LENGTH m DIV r)) MOD
                               2 EXP (8 * r)))))
             (8 * (i MOD r),8)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[keccak_sponge] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[KECCAK_SPONGE_ABSORB] THEN
  REWRITE_TAC[GSYM ADD1; keccak_squeeze; KECCAK_SQUEEZE_F1600]);;

let NUM_OF_BYTELIST_STATE_BYTES = prove
 (`!(S:1600 word) n.
        n <= 200
        ==> num_of_bytelist(list_of_seq (\i. word_subword S (8 * i,8)) n) =
            val S MOD 2 EXP (8 * n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[list_of_seq; num_of_bytelist; MULT_CLAUSES; EXP; MOD_1];
    ALL_TAC] THEN
  DISCH_TAC THEN
  ASM_SIMP_TAC[list_of_seq; NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ;
               ARITH_RULE `SUC n <= 200 ==> n <= 200`] THEN
  REWRITE_TAC[num_of_bytelist; VAL_WORD_SUBWORD; DIMINDEX_8;
              ARITH_RULE `MIN 8 8 = 8`] THEN
  REWRITE_TAC[ARITH_RULE `8 * SUC n = 8 * n + 8`; EXP_ADD; MOD_MULT_MOD] THEN
  ARITH_TAC);;

let KECCAK_SPONGE_BYTES = prove
 (`!c d (m:byte list) r P n.
        (1600 - c) DIV 8 = r /\ 0 < r /\ n <= r /\
        P = num_of_bytelist m +
            2 EXP (8 * LENGTH m) * num_of_bytelist(keccak_pad r d (LENGTH m))
        ==> num_of_bytelist(list_of_seq (keccak_sponge c d m) n) =
            val(keccak_f1600
                 (word_xor (keccak_absorb r P (LENGTH m DIV r))
                           (word((P DIV 2 EXP (8 * r * LENGTH m DIV r)) MOD
                                 2 EXP (8 * r))))) MOD 2 EXP (8 * n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n <= 200` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(1600 - c) DIV 8 = r`; `n <= r`] THEN ARITH_TAC;
    ALL_TAC] THEN
  W(fun (_,w) ->
    let sv = rand(lhand(rand w)) in
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (mk_comb(`num_of_bytelist`,
      list_mk_comb(`list_of_seq:(num->byte)->num->byte list`,
       [mk_abs(`i:num`,
          list_mk_comb(`word_subword:1600 word->num#num->byte`,
            [sv; `8 * i,8`]));
        `n:num`])))) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:num`; `d:num`; `m:byte list`; `r:num`; `P:num`; `i:num`]
                 KECCAK_SPONGE_SQUEEZE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `i DIV r = 0 /\ i MOD r = i` (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THENL [MATCH_MP_TAC DIV_LT; MATCH_MP_TAC MOD_LT] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[ADD_CLAUSES; num_CONV `1`; keccak_squeeze]];
    MATCH_MP_TAC NUM_OF_BYTELIST_STATE_BYTES THEN ASM_REWRITE_TAC[]]);;

let NUM_OF_BYTELIST_LIST_OF_SEQ_ADD = prove
 (`!(f:num->byte) a b.
        num_of_bytelist(list_of_seq f (a + b)) =
        num_of_bytelist(list_of_seq f a) +
        2 EXP (8 * a) * num_of_bytelist(list_of_seq (\j. f(a + j)) b)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; list_of_seq; num_of_bytelist; MULT_CLAUSES] THEN
  ASM_REWRITE_TAC[NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ;
                  num_of_bytelist] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MULT_CLAUSES; ADD_CLAUSES] THEN
  ARITH_TAC);;

let KECCAK_SPONGE_BLOCK = prove
 (`!c d (m:byte list) r P k n.
        (1600 - c) DIV 8 = r /\ 0 < r /\ n <= r /\
        P = num_of_bytelist m +
            2 EXP (8 * LENGTH m) * num_of_bytelist(keccak_pad r d (LENGTH m))
        ==> num_of_bytelist
             (list_of_seq (\j. keccak_sponge c d m (r * k + j)) n) =
            val(keccak_squeeze (k + 1)
                 (word_xor (keccak_absorb r P (LENGTH m DIV r))
                           (word((P DIV 2 EXP (8 * r * LENGTH m DIV r)) MOD
                                 2 EXP (8 * r))))) MOD 2 EXP (8 * n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n <= 200` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(1600 - c) DIV 8 = r`; `n <= r`] THEN ARITH_TAC;
    ALL_TAC] THEN
  W(fun (_,w) ->
    let sv = rand(lhand(rand w)) in
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC (mk_comb(`num_of_bytelist`,
      list_mk_comb(`list_of_seq:(num->byte)->num->byte list`,
       [mk_abs(`j:num`,
          list_mk_comb(`word_subword:1600 word->num#num->byte`,
            [sv; `8 * j,8`]));
        `n:num`])))) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(SPECL [`c:num`; `d:num`; `m:byte list`; `r:num`; `P:num`;
                  `r * k + j`] KECCAK_SPONGE_SQUEEZE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(r * k + j) DIV r = k /\ (r * k + j) MOD r = j`
     (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `j:num` THEN ASM_ARITH_TAC;
        MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `k:num` THEN ASM_ARITH_TAC];
      REFL_TAC];
    MATCH_MP_TAC NUM_OF_BYTELIST_STATE_BYTES THEN ASM_REWRITE_TAC[]]);;
