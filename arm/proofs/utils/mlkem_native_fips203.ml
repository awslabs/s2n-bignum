(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas connecting the specifications of the mlkem-native functions to the *)
(* FIPS 203 specification in common/fips203.ml, for the proofs of the K-PKE  *)
(* and ML-KEM functions. The specifications of the leaf functions use plain  *)
(* arithmetic (congruences mod q = 3329 and bounds on the 16-bit             *)
(* coefficients, numbers for byte arrays, and lists of words), and these     *)
(* lemmas relate them to the definitions of FIPS 203 and to its NTT-domain   *)
(* forms of K-PKE in common/fips203_theory.ml.                               *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;
needs "common/mlkem_mldsa.ml";;
needs "common/fips203_theory.ml";;

(* ------------------------------------------------------------------------- *)
(* Byte strings, bit fields and lists of words.                              *)
(* ------------------------------------------------------------------------- *)

let FIPS203_NUM_OF_BYTELIST_APPEND = prove
 (`!(l1:byte list) l2.
        num_of_bytelist(APPEND l1 l2) =
        num_of_bytelist l1 + 2 EXP (8 * LENGTH l1) * num_of_bytelist l2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; num_of_bytelist; LENGTH; MULT_CLAUSES; EXP;
                  ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `8 * SUC n = 8 + 8 * n`; EXP_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let MOD_EXP_BITS = prove
 (`!n y. y MOD 2 EXP n =
         nsum {t | t < n} (\t. bitval(ODD(y DIV 2 EXP t)) * 2 EXP t)`,
  INDUCT_TAC THEN
  REWRITE_TAC[EXP; MOD_1; NSUM_CLAUSES_NUMSEG_LT] THEN GEN_TAC THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[bitval; ODD_MOD] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [MULT_SYM] THEN
  REWRITE_TAC[MOD_MULT_MOD] THEN
  MP_TAC(ARITH_RULE `(y DIV 2 EXP n) MOD 2 < 2`) THEN
  SPEC_TAC(`(y DIV 2 EXP n) MOD 2`,`b:num`) THEN GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `b < 2 <=> b = 0 \/ b = 1`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let ODD_NUM_OF_BYTELIST_LIST_OF_SEQ = prove
 (`!(s:num->byte) m a.
        a < 8 * m
        ==> (ODD(num_of_bytelist(list_of_seq s m) DIV 2 EXP a) <=>
             bit (a MOD 8) (s(a DIV 8)))`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT] THEN
  X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  REWRITE_TAC[list_of_seq; FIPS203_NUM_OF_BYTELIST_APPEND;
              LENGTH_LIST_OF_SEQ] THEN
  REWRITE_TAC[num_of_bytelist; MULT_CLAUSES; ADD_CLAUSES] THEN
  MP_TAC(ISPEC `list_of_seq (s:num->byte) m` NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:num`) THEN
  SPEC_TAC(`num_of_bytelist(list_of_seq (s:num->byte) m)`,`l:num`) THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `a < 8 * m` THENL
   [SUBGOAL_THEN `2 EXP (8 * m) = 2 EXP (8 * m - a) * 2 EXP a` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `l + (x * y) * z:num = (x * z) * y + l`] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ODD_ADD; ODD_MULT; ODD_EXP; ARITH_ODD] THEN
    SUBGOAL_THEN `~(8 * m - a = 0)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `a DIV 8 = m /\ a MOD 8 = a - 8 * m`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `a - 8 * m`;
      MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `m:num`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP a = 2 EXP (8 * m) * 2 EXP (a - 8 * m)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `l + x * y:num = y * x + l`] THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  SUBGOAL_THEN `l DIV 2 EXP (8 * m) = 0` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_LT THEN ASM_REWRITE_TAC[EXP_MULT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[ADD_CLAUSES; BIT_VAL]]);;

let NUM_OF_BYTELIST_LIST_OF_SEQ_SPLIT = prove
 (`!(f:num->byte) m n.
        num_of_bytelist(list_of_seq f (m + n)) =
        num_of_bytelist(list_of_seq f m) +
        2 EXP (8 * m) * num_of_bytelist(list_of_seq (\i. f(m + i)) n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; list_of_seq; num_of_bytelist; MULT_CLAUSES] THEN
  ASM_REWRITE_TAC[FIPS203_NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ;
                  num_of_bytelist; MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; MULT_AC; ADD_AC]);;

let NUM_OF_WORDLIST_LIST_OF_SEQ = prove
 (`!(f:num->N word) n.
        num_of_wordlist(list_of_seq f n) =
        nsum {i | i < n} (\i. val(f i) * 2 EXP (dimindex(:N) * i))`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[list_of_seq; num_of_wordlist; NSUM_CLAUSES_NUMSEG_LT] THEN
  ASM_REWRITE_TAC[NUM_OF_WORDLIST_APPEND; LENGTH_LIST_OF_SEQ;
                  NUM_OF_WORDLIST_SING] THEN
  ARITH_TAC);;

let EL_WORDLIST_OF_NUM = prove
 (`!n x i. i < n
           ==> EL i (wordlist_of_num n x:(N word)list) =
               word(x DIV 2 EXP (dimindex(:N) * i))`,
  INDUCT_TAC THEN REWRITE_TAC[CONJUNCT1 LT; wordlist_of_num] THEN
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
  REWRITE_TAC[EL; HD; TL; MULT_CLAUSES; EXP; DIV_1; LT_SUC] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[DIV_DIV; GSYM EXP_ADD; WORD_MOD_SIZE] THEN
  REWRITE_TAC[ADD_SYM]);;

let WORDLIST_FROM_MEMORY_BYTES16 = prove
 (`!a n s (l:int16 list).
        wordlist_from_memory(a,n) s = l
        ==> !i. i < n
                ==> read (memory :> bytes16(word_add a (word(2 * i)))) s =
                    EL i l`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_WORDLIST_FROM_MEMORY; BYTES16_WBYTES] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN REFL_TAC);;

let READ_MEMORY_BYTES16_LIST_OF_SEQ = prove
 (`!a n (f:num->int16) s:armstate.
        (!i. i < n
             ==> read (memory :> bytes16(word_add a (word(2 * i)))) s = f i)
        ==> read (memory :> bytes(a,2 * n)) s =
            num_of_wordlist(list_of_seq f n)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL;
                list_of_seq; num_of_wordlist];
    REPEAT STRIP_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC n = 2 * n + 2`; READ_COMPONENT_COMPOSE;
              READ_BYTES_COMBINE; list_of_seq] THEN
  REWRITE_TAC[NUM_OF_WORDLIST_APPEND; LENGTH_LIST_OF_SEQ;
              NUM_OF_WORDLIST_SING; DIMINDEX_16] THEN
  BINOP_TAC THENL
   [REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `8 * 2 * n = 16 * n`] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[ARITH_RULE `n < SUC n`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
                DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let READ16_OFFSET_EQ = prove
 (`!a x y s:armstate.
        x = y
        ==> read (memory :> bytes16(word_add a (word x))) s =
            read (memory :> bytes16(word_add a (word y))) s`,
  SIMP_TAC[]);;

let READ_MEMORY_BYTES_1 = prove
 (`!a s:armstate.
        read (memory :> bytes(a,1)) s = val(read (memory :> bytes8 a) s)`,
  REWRITE_TAC[BYTES8_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MLKEM_SLICE_NUM = prove
 (`!a n (l:byte list).
        a + n <= LENGTH l
        ==> num_of_bytelist(mlkem_slice a n l) =
            (num_of_bytelist l DIV 2 EXP (8 * a)) MOD 2 EXP (8 * n)`,
  INDUCT_TAC THENL
   [SIMP_TAC[ADD_CLAUSES; MLKEM_SLICE_0; NUM_OF_BYTELIST_OF_NUM] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1; EXP_MULT] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC a + n <= 0)`] THEN
  REWRITE_TAC[ARITH_RULE `SUC a + n <= SUC m <=> a + n <= m`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `mlkem_slice (SUC a) n (CONS (h:byte) t) = mlkem_slice a n t`
  SUBST1_TAC THENL
   [REWRITE_TAC[mlkem_slice; ADD_CLAUSES; EL; TL]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP th (ASSUME `a + n <= LENGTH(t:byte list)`)]) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[num_of_bytelist; ARITH_RULE `8 * SUC a = 8 + 8 * a`;
              EXP_ADD] THEN
  REWRITE_TAC[GSYM DIV_DIV] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[DIV_MULT_ADD; DIV_LT; ARITH_EQ; ADD_CLAUSES]);;

let READ_MEMORY_BYTES_SLICE = prove
 (`!a (l:byte list) k n s:armstate.
        read (memory :> bytes(a,LENGTH l)) s = num_of_bytelist l /\
        k + n <= LENGTH l
        ==> read (memory :> bytes(word_add a (word k),n)) s =
            num_of_bytelist(mlkem_slice k n l)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_SLICE_NUM] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* SampleNTT (FIPS 203 Algorithm 7) and rejection sampling. The result of    *)
(* mlkem_poly_rej_uniform is the first 256 of the 12-bit fields of the XOF   *)
(* output that are < q, which are the coefficients that SampleNTT returns.   *)
(* SampleNTT is only meaningful when the XOF output has 256 such fields,     *)
(* which is what mlkem_samplentt_terminates says; then they are all within   *)
(* some number of blocks of the output, as in the specifications of the      *)
(* rejection sampling functions.                                             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_XOF_FIELD_NUM = prove
 (`!(s:num->byte) m j.
        12 * j + 12 <= 8 * m
        ==> mlkem_xof_field s j =
            (num_of_bytelist(list_of_seq s m) DIV 2 EXP (12 * j)) MOD
            2 EXP 12`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_xof_field; MOD_EXP_BITS] THEN
  MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `t:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC ODD_NUM_OF_BYTELIST_LIST_OF_SEQ THEN
  ASM_ARITH_TAC);;

let FINITE_LT_RESTRICT = prove
 (`!n (Q:num->bool). FINITE {i | i < n /\ Q i}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{i:num | i < n}` THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  SET_TAC[]);;

let LENGTH_FILTER_LIST_OF_SEQ = prove
 (`!(P:A->bool) c n.
        LENGTH(FILTER P (list_of_seq c n)) = CARD {i | i < n /\ P(c i)}`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[list_of_seq; FILTER; LENGTH; CONJUNCT1 LT; EMPTY_GSPEC;
              CARD_CLAUSES] THEN
  ASM_REWRITE_TAC[FILTER_APPEND; LENGTH_APPEND; FILTER] THEN
  REWRITE_TAC[LT] THEN
  REWRITE_TAC[TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
  REWRITE_TAC[SET_RULE `{x:num | x = a /\ P x \/ Q x} =
                        if P a then a INSERT {x | Q x} else {x | Q x}`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ADD_CLAUSES] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_LT_RESTRICT; IN_ELIM_THM; LT_REFL] THEN
  ARITH_TAC);;

let EL_FILTER_LIST_OF_SEQ = prove
 (`!(P:A->bool) c N n.
        n < LENGTH(FILTER P (list_of_seq c N))
        ==> ?j. j < N /\ P(c j) /\ CARD {i | i < j /\ P(c i)} = n /\
                EL n (FILTER P (list_of_seq c N)) = c j`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[list_of_seq; FILTER; LENGTH; CONJUNCT1 LT] THEN
  X_GEN_TAC `n:num` THEN
  REWRITE_TAC[FILTER_APPEND; FILTER; LENGTH_APPEND] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH; APPEND_NIL; ADD_CLAUSES] THEN
  DISCH_TAC THENL
   [ASM_CASES_TAC `n < LENGTH(FILTER P (list_of_seq (c:num->A) N))` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `j:num` THEN ASM_SIMP_TAC[EL_APPEND] THEN ASM_ARITH_TAC;
      EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[ARITH_RULE `N < SUC N`] THEN
      SUBGOAL_THEN `n = LENGTH(FILTER P (list_of_seq (c:num->A) N))`
      SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[LENGTH_FILTER_LIST_OF_SEQ; EL_APPEND] THEN
      REWRITE_TAC[GSYM LENGTH_FILTER_LIST_OF_SEQ; LT_REFL; SUB_REFL] THEN
      REWRITE_TAC[EL; HD]];
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let CARD_FILTER_UNIQUE = prove
 (`!(Q:num->bool) j j'.
        Q j /\ Q j' /\
        CARD {i | i < j /\ Q i} = CARD {i | i < j' /\ Q i}
        ==> j = j'`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `~(j < j') /\ ~(j' < j) ==> j:num = j'`) THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`{i | i < j /\ (Q:num->bool) i}`;
                   `{i | i < j' /\ (Q:num->bool) i}`] CARD_PSUBSET);
    MP_TAC(ISPECL [`{i | i < j' /\ (Q:num->bool) i}`;
                   `{i | i < j /\ (Q:num->bool) i}`] CARD_PSUBSET)] THEN
  ASM_REWRITE_TAC[FINITE_LT_RESTRICT; LT_REFL] THEN
  REWRITE_TAC[PSUBSET; SUBSET; EXTENSION; IN_ELIM_THM; NOT_FORALL_THM] THEN
  (CONJ_TAC THENL [ASM_MESON_TAC[LT_TRANS]; ASM_MESON_TAC[LT_REFL]]));;

let MLKEM_SAMPLE_NTT_REJ = prove
 (`!b k n.
        256 <= LENGTH(FILTER (\x. val x < 3329)
                 (MAP (word_zx:12 word->16 word)
                   (wordlist_of_num (336 + 112 * k)
                     (num_of_bytelist
                       (list_of_seq (shake128 b) (504 + 168 * k)))))) /\
        n < 256
        ==> mlkem_sample_ntt b n =
            &(val(EL n (SUB_LIST(0,256)
                   (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                       (wordlist_of_num (336 + 112 * k)
                         (num_of_bytelist
                           (list_of_seq (shake128 b) (504 + 168 * k)))))))))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `N = 336 + 112 * k` THEN ABBREV_TAC `M = 504 + 168 * k` THEN
  SUBGOAL_THEN `12 * N = 8 * M` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["N"; "M"] THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `c = mlkem_xof_field (shake128 b)` THEN
  SUBGOAL_THEN
   `!j. j < N
        ==> c j = (num_of_bytelist(list_of_seq (shake128 b) M) DIV
                   2 EXP (12 * j)) MOD 2 EXP 12`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "c" THEN
    MATCH_MP_TAC MLKEM_XOF_FIELD_NUM THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `MAP (word_zx:12 word->16 word)
     (wordlist_of_num N (num_of_bytelist(list_of_seq (shake128 b) M))) =
    list_of_seq (\j. word(c j)) N`
  SUBST1_TAC THENL
   [REWRITE_TAC[LIST_EQ; LENGTH_MAP; LENGTH_WORDLIST_OF_NUM;
                LENGTH_LIST_OF_SEQ] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[EL_MAP; LENGTH_WORDLIST_OF_NUM; EL_WORDLIST_OF_NUM;
                 EL_LIST_OF_SEQ] THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MOD_MOD_REFL];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:int16. val x < 3329`; `\j. word((c:num->num) j):int16`;
                 `N:num`; `n:num`] EL_FILTER_LIST_OF_SEQ) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!i. i < N ==> val(word((c:num->num) i):int16) = c i`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VAL_WORD] THEN
    CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC MOD_LT THEN
    MATCH_MP_TAC(ARITH_RULE `x < 4096 ==> x < 65536`) THEN
    REWRITE_TAC[ARITH_RULE `4096 = 2 EXP 12`; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:num->num) j < 3329 /\ CARD {i | i < j /\ c i < 3329} = n`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[];
      FIRST_X_ASSUM(fun th ->
        if is_eq(concl th) && is_comb(lhs(concl th)) &&
           (try fst(dest_const(rator(lhs(concl th)))) = "CARD"
            with _ -> false)
        then SUBST1_TAC(SYM th) else NO_TAC) THEN
      AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i < j` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (is_forall o concl)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_SUB_LIST_GEN o rand o rand o
    rand o snd) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ADD_CLAUSES]; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN
   `(@j. (c:num->num) j < 3329 /\ CARD {j' | j' < j /\ c j' < 3329} = n) = j`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `y:num` THEN BETA_TAC THEN
    EQ_TAC THENL
     [STRIP_TAC THEN
      MATCH_MP_TAC(BETA_RULE(ISPEC `\i. (c:num->num) i < 3329`
                                   CARD_FILTER_UNIQUE)) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[mlkem_sample_ntt; mlkem_xof] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let mlkem_samplentt_terminates = new_definition
 `mlkem_samplentt_terminates (b:byte list) <=>
    ?J. 256 <= CARD {j | j < J /\ mlkem_xof_field (mlkem_xof b) j < 3329}`;;

let REJ_FIELDS_LIST = prove
 (`!s N M.
        12 * N <= 8 * M
        ==> MAP (word_zx:12 word->16 word)
             (wordlist_of_num N (num_of_bytelist(list_of_seq s M))) =
            list_of_seq (\j. word(mlkem_xof_field s j)) N`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_MAP; LENGTH_WORDLIST_OF_NUM;
              LENGTH_LIST_OF_SEQ] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_WORDLIST_OF_NUM; EL_WORDLIST_OF_NUM;
               EL_LIST_OF_SEQ] THEN
  MP_TAC(SPECL [`s:num->byte`; `M:num`; `j:num`] MLKEM_XOF_FIELD_NUM) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL; ARITH_RULE `65536 = 4096 * 16`; MOD_MOD]);;

let NSUM_BITVAL_BOUND = prove
 (`!n (b:num->bool). nsum {t | t < n} (\t. bitval(b t) * 2 EXP t) < 2 EXP n`,
  INDUCT_TAC THEN REWRITE_TAC[NSUM_CLAUSES_NUMSEG_LT; EXP; ARITH] THEN
  GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `b:num->bool`) THEN
  REWRITE_TAC[bitval] THEN COND_CASES_TAC THEN ARITH_TAC);;

let MLKEM_XOF_FIELD_BOUND = prove
 (`!s j. mlkem_xof_field s j < 4096`,
  REWRITE_TAC[mlkem_xof_field] THEN
  MP_TAC(SPEC `12` NSUM_BITVAL_BOUND) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[]);;

let LENGTH_REJ_FIELDS = prove
 (`!s N M.
        12 * N <= 8 * M
        ==> LENGTH(FILTER (\x. val x < 3329)
                   (MAP (word_zx:12 word->16 word)
                     (wordlist_of_num N (num_of_bytelist(list_of_seq s M))))) =
            CARD {j | j < N /\ mlkem_xof_field s j < 3329}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REJ_FIELDS_LIST] THEN
  REWRITE_TAC[LENGTH_FILTER_LIST_OF_SEQ] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; VAL_WORD] THEN GEN_TAC THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPECL [`s:num->byte`; `x:num`] MLKEM_XOF_FIELD_BOUND) THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `y < 4096 ==> y < 65536`]);;

let CARD_LT_RESTRICT_MONO = prove
 (`!(P:num->bool) m n.
        m <= n ==> CARD {j | j < m /\ P j} <= CARD {j | j < n /\ P j}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_SUBSET THEN
  REWRITE_TAC[FINITE_LT_RESTRICT; SUBSET; IN_ELIM_THM] THEN
  ASM_MESON_TAC[LTE_TRANS]);;

let MLKEM_SAMPLENTT_TERMINATES_REJ = prove
 (`!b. mlkem_samplentt_terminates b <=>
       ?k. 256 <= LENGTH(FILTER (\x. val x < 3329)
                   (MAP (word_zx:12 word->16 word)
                     (wordlist_of_num (336 + 112 * k)
                       (num_of_bytelist
                         (list_of_seq (shake128 b) (504 + 168 * k))))))`,
  GEN_TAC THEN REWRITE_TAC[mlkem_samplentt_terminates; mlkem_xof] THEN
  SIMP_TAC[LENGTH_REJ_FIELDS;
           ARITH_RULE `12 * (336 + 112 * k) <= 8 * (504 + 168 * k)`] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `J:num` THEN
    TRANS_TAC LE_TRANS
     `CARD {j | j < J /\ mlkem_xof_field (shake128 b) j < 3329}` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_LT_RESTRICT_MONO THEN
    ARITH_TAC;
    EXISTS_TAC `336 + 112 * k` THEN ASM_REWRITE_TAC[]]);;

let MLKEM_SAMPLENTT_TERMINATES_UNIFORM = prove
 (`!K (f:num->num->byte list).
     (!i j. i < K /\ j < K ==> mlkem_samplentt_terminates (f i j))
     ==> ?k. !i j. i < K /\ j < K
                   ==> 256 <= LENGTH(FILTER (\x. val x < 3329)
                               (MAP (word_zx:12 word->16 word)
                                 (wordlist_of_num (336 + 112 * k)
                                   (num_of_bytelist
                                     (list_of_seq (shake128 (f i j))
                                                  (504 + 168 * k))))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. ?J. i < K /\ j < K
              ==> 256 <= CARD {t | t < J /\
                                   mlkem_xof_field
                                    (shake128 ((f:num->num->byte list) i j)) t
                                   < 3329}`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN ASM_CASES_TAC `i < K /\ j < K` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
    ASM_REWRITE_TAC[mlkem_samplentt_terminates; mlkem_xof];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `J:num->num->num`)] THEN
  SUBGOAL_THEN `FINITE {(J:num->num->num) i j | i < K /\ j < K}` MP_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `IMAGE (\p. (J:num->num->num) (FST p) (SND p))
                      ({i | i < K} CROSS {j | j < K})` THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_CROSS; FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS] THEN
    MESON_TAC[];
    REWRITE_TAC[num_FINITE; FORALL_IN_GSPEC] THEN
    DISCH_THEN(X_CHOOSE_TAC `k:num`)] THEN
  EXISTS_TAC `k:num` THEN REPEAT STRIP_TAC THEN
  SIMP_TAC[LENGTH_REJ_FIELDS;
           ARITH_RULE `12 * (336 + 112 * k) <= 8 * (504 + 168 * k)`] THEN
  TRANS_TAC LE_TRANS
   `CARD {t | t < (J:num->num->num) i j /\
              mlkem_xof_field (shake128 ((f:num->num->byte list) i j)) t
              < 3329}` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC CARD_LT_RESTRICT_MONO THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let EL_FILTER_PROP = prove
 (`!P (l:A list) n. n < LENGTH(FILTER P l) ==> P(EL n (FILTER P l))`,
  MESON_TAC[MEM_EL; MEM_FILTER]);;

let MLKEM_SAMPLE_NTT_REJ_EL = prove
 (`!b k n.
        256 <= LENGTH(FILTER (\x. val x < 3329)
                 (MAP (word_zx:12 word->16 word)
                   (wordlist_of_num (336 + 112 * k)
                     (num_of_bytelist
                       (list_of_seq (shake128 b) (504 + 168 * k)))))) /\
        n < 256
        ==> val(EL n (SUB_LIST(0,256)
                 (FILTER (\x. val x < 3329)
                   (MAP (word_zx:12 word->16 word)
                     (wordlist_of_num (336 + 112 * k)
                       (num_of_bytelist
                         (list_of_seq (shake128 b) (504 + 168 * k))))))))
            < 3329`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`MAP (word_zx:12 word->16 word)
             (wordlist_of_num (336 + 112 * k)
               (num_of_bytelist (list_of_seq (shake128 b) (504 + 168 * k))))`,
           `l:int16 list`) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`FILTER (\x:int16. val x < 3329) l`; `n:num`; `0`; `256`]
                EL_SUB_LIST_GEN) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`\x:int16. val x < 3329`; `l:int16 list`; `n:num`]
                EL_FILTER_PROP) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let MLKEM_SAMPLE_NTT_REJ_BOUND = prove
 (`!b k n.
        256 <= LENGTH(FILTER (\x. val x < 3329)
                 (MAP (word_zx:12 word->16 word)
                   (wordlist_of_num (336 + 112 * k)
                     (num_of_bytelist
                       (list_of_seq (shake128 b) (504 + 168 * k)))))) /\
        n < 256
        ==> &0 <= mlkem_sample_ntt b n /\ mlkem_sample_ntt b n < &3329`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MLKEM_SAMPLE_NTT_POS] THEN
  ASM_SIMP_TAC[MLKEM_SAMPLE_NTT_REJ; INT_OF_NUM_LT; MLKEM_SAMPLE_NTT_REJ_EL]);;

let IVAL_VAL_SMALL = prove
 (`!x:int16. val x < 32768 ==> ival x = &(val x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ival; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let MLKEM_NATIVE_SAMPLE_COEFF = prove
 (`!a s b k n.
        256 <= LENGTH(FILTER (\x. val x < 3329)
                 (MAP (word_zx:12 word->16 word)
                   (wordlist_of_num (336 + 112 * k)
                     (num_of_bytelist
                       (list_of_seq (shake128 b) (504 + 168 * k)))))) /\
        wordlist_from_memory(a,256) s =
        SUB_LIST(0,256)
         (FILTER (\x. val x < 3329)
           (MAP (word_zx:12 word->16 word)
             (wordlist_of_num (336 + 112 * k)
               (num_of_bytelist
                 (list_of_seq (shake128 b) (504 + 168 * k)))))) /\
        n < 256
        ==> ival(read (memory :> bytes16(word_add a (word(2 * n)))) s) =
            mlkem_sample_ntt b n`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    ASM_SIMP_TAC[MATCH_MP WORDLIST_FROM_MEMORY_BYTES16 th]) THEN
  ASM_SIMP_TAC[MLKEM_SAMPLE_NTT_REJ] THEN MATCH_MP_TAC IVAL_VAL_SMALL THEN
  MATCH_MP_TAC(ARITH_RULE `x < 3329 ==> x < 32768`) THEN
  MATCH_MP_TAC MLKEM_SAMPLE_NTT_REJ_EL THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* SamplePolyCBD (FIPS 203 Algorithm 8): the coefficients of mlkem_cbd, and  *)
(* those computed by mlkem_poly_cbd2 and mlkem_poly_cbd3 (eta = 2 and 3).    *)
(* ------------------------------------------------------------------------- *)

let NSUM_LT_2 = prove
 (`!f. nsum {j | j < 2} f = f 0 + f 1`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 = SUC(SUC 0)`; NSUM_CLAUSES_NUMSEG_LT] THEN
  REWRITE_TAC[ARITH_RULE `SUC 0 = 1`; ADD_CLAUSES]);;

let NSUM_LT_3 = prove
 (`!f. nsum {j | j < 3} f = f 0 + f 1 + f 2`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `3 = SUC(SUC(SUC 0))`; NSUM_CLAUSES_NUMSEG_LT] THEN
  REWRITE_TAC[ARITH_RULE `SUC 0 = 1 /\ SUC 1 = 2`; ADD_CLAUSES] THEN
  ARITH_TAC);;

let MLKEM_CBD2_COEFF = prove
 (`!b i. i < 256
         ==> coeff i (mlkem_cbd 2 b) =
             (&((num_of_bytelist b DIV 2 EXP (4 * i)) MOD 2 +
                (num_of_bytelist b DIV 2 EXP (4 * i + 1)) MOD 2) -
              &((num_of_bytelist b DIV 2 EXP (4 * i + 2)) MOD 2 +
                (num_of_bytelist b DIV 2 EXP (4 * i + 3)) MOD 2)) rem &3329`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_cbd] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[COEFF_MLKEM_POLY] THEN
  REWRITE_TAC[NSUM_LT_2; ADD_CLAUSES; ARITH_RULE `2 * 2 * i = 4 * i`] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REFL_TAC);;

let MLKEM_CBD3_COEFF = prove
 (`!b i. i < 256
         ==> coeff i (mlkem_cbd 3 b) =
             (&((num_of_bytelist b DIV 2 EXP (6 * i)) MOD 2 +
                (num_of_bytelist b DIV 2 EXP (6 * i + 1)) MOD 2 +
                (num_of_bytelist b DIV 2 EXP (6 * i + 2)) MOD 2) -
              &((num_of_bytelist b DIV 2 EXP (6 * i + 3)) MOD 2 +
                (num_of_bytelist b DIV 2 EXP (6 * i + 4)) MOD 2 +
                (num_of_bytelist b DIV 2 EXP (6 * i + 5)) MOD 2)) rem &3329`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_cbd] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[COEFF_MLKEM_POLY] THEN
  REWRITE_TAC[NSUM_LT_3; ADD_CLAUSES; ARITH_RULE `2 * 3 * i = 6 * i`] THEN
  CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REFL_TAC);;

let MLKEM_NATIVE_CBD2_CONG = prove
 (`!b i x:int16.
        i < 256 /\
        x = iword(&((num_of_bytelist b DIV 2 EXP (4 * i)) MOD 2 +
                    (num_of_bytelist b DIV 2 EXP (4 * i + 1)) MOD 2) -
                  &((num_of_bytelist b DIV 2 EXP (4 * i + 2)) MOD 2 +
                    (num_of_bytelist b DIV 2 EXP (4 * i + 3)) MOD 2))
        ==> (ival x == coeff i (mlkem_cbd 2 b)) (mod &3329) /\
            abs(ival x) <= &2`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  ASM_SIMP_TAC[MLKEM_CBD2_COEFF] THEN
  MAP_EVERY (fun t -> MP_TAC(SPECL [t; `2`] MOD_LT_EQ))
   [`num_of_bytelist b DIV 2 EXP (4 * i + 3)`;
    `num_of_bytelist b DIV 2 EXP (4 * i + 2)`;
    `num_of_bytelist b DIV 2 EXP (4 * i + 1)`;
    `num_of_bytelist b DIV 2 EXP (4 * i)`] THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`(num_of_bytelist b DIV 2 EXP (4 * i + 3)) MOD 2`,`d:num`) THEN
  SPEC_TAC(`(num_of_bytelist b DIV 2 EXP (4 * i + 2)) MOD 2`,`c:num`) THEN
  SPEC_TAC(`(num_of_bytelist b DIV 2 EXP (4 * i + 1)) MOD 2`,`b1:num`) THEN
  SPEC_TAC(`(num_of_bytelist b DIV 2 EXP (4 * i)) MOD 2`,`a:num`) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `ival(iword(&(a + b1) - &(c + d)):int16) = &(a + b1) - &(c + d)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MESON_TAC[INT_REM_MOD_SELF; INT_CONG_SYM];
    REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN INT_ARITH_TAC]);;

let MLKEM_NATIVE_CBD3_CONG = prove
 (`!b i x:int16.
        i < 256 /\
        x = iword(&((num_of_bytelist b DIV 2 EXP (6 * i)) MOD 2 +
                    (num_of_bytelist b DIV 2 EXP (6 * i + 1)) MOD 2 +
                    (num_of_bytelist b DIV 2 EXP (6 * i + 2)) MOD 2) -
                  &((num_of_bytelist b DIV 2 EXP (6 * i + 3)) MOD 2 +
                    (num_of_bytelist b DIV 2 EXP (6 * i + 4)) MOD 2 +
                    (num_of_bytelist b DIV 2 EXP (6 * i + 5)) MOD 2))
        ==> (ival x == coeff i (mlkem_cbd 3 b)) (mod &3329) /\
            abs(ival x) <= &3`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  ASM_SIMP_TAC[MLKEM_CBD3_COEFF] THEN
  MAP_EVERY (fun t -> MP_TAC(SPECL [t; `2`] MOD_LT_EQ))
   [`num_of_bytelist b DIV 2 EXP (6 * i + 5)`;
    `num_of_bytelist b DIV 2 EXP (6 * i + 4)`;
    `num_of_bytelist b DIV 2 EXP (6 * i + 3)`;
    `num_of_bytelist b DIV 2 EXP (6 * i + 2)`;
    `num_of_bytelist b DIV 2 EXP (6 * i + 1)`;
    `num_of_bytelist b DIV 2 EXP (6 * i)`] THEN
  REWRITE_TAC[ARITH_EQ] THEN
  SPEC_TAC(`(num_of_bytelist b DIV 2 EXP (6 * i + 5)) MOD 2`,`f:num`) THEN
  SPEC_TAC(`(num_of_bytelist b DIV 2 EXP (6 * i + 4)) MOD 2`,`e:num`) THEN
  SPEC_TAC(`(num_of_bytelist b DIV 2 EXP (6 * i + 3)) MOD 2`,`d:num`) THEN
  SPEC_TAC(`(num_of_bytelist b DIV 2 EXP (6 * i + 2)) MOD 2`,`c:num`) THEN
  SPEC_TAC(`(num_of_bytelist b DIV 2 EXP (6 * i + 1)) MOD 2`,`b1:num`) THEN
  SPEC_TAC(`(num_of_bytelist b DIV 2 EXP (6 * i)) MOD 2`,`a:num`) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `ival(iword(&(a + b1 + c) - &(d + e + f)):int16) =
                &(a + b1 + c) - &(d + e + f)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MESON_TAC[INT_REM_MOD_SELF; INT_CONG_SYM];
    REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Coefficients of polynomials in R_q, and the ring operations of Z_q.       *)
(* ------------------------------------------------------------------------- *)

let MLKEM_COEFF_BOUNDS = prove
 (`!p k. p IN ring_carrier mlkem_rq
         ==> &0 <= coeff k p /\ coeff k p < &3329`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_MLKEM_RQ; GSYM IN_MLKEM_ZQ] THEN
  STRIP_TAC THEN MATCH_MP_TAC COEFF_POLY_IN_CARRIER THEN
  RULE_ASSUM_TAC(REWRITE_RULE[mlkem_zqx]) THEN ASM_REWRITE_TAC[]);;

let MLKEM_COEFF_POS = prove
 (`!p k. p IN ring_carrier mlkem_rq ==> &0 <= coeff k p`,
  MESON_TAC[MLKEM_COEFF_BOUNDS]);;

let MLKEM_ZQ_ADD = prove
 (`!a b. ring_add mlkem_zq a b = (a + b) rem &3329`,
  REWRITE_TAC[MLKEM_ZQ]);;

(* ------------------------------------------------------------------------- *)
(* The NTT and its inverse, as computed by the code up to congruence mod q,  *)
(* and MultiplyNTTs (FIPS 203 Algorithm 11) as plain arithmetic.             *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NTT_FORWARD_CONG = prove
 (`!f (a:num->int) k.
        f IN ring_carrier mlkem_rq /\
        (!m. m < 256 ==> (coeff m f == a m) (mod &3329))
        ==> (mlkem_ntt f k == forward_ntt a k) (mod &3329)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_NTT_FORWARD; forward_ntt] THEN
  REWRITE_TAC[INT_CONG_LREM; INT_CONG_RREM] THEN
  MATCH_MP_TAC INT_CONG_ISUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(x:int == y) (mod n) ==> (x * z == y * z) (mod n)`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ARITH_RULE `k MOD 2 < 2`) THEN ASM_ARITH_TAC);;

let MLKEM_NATIVE_NTT_CONG = prove
 (`!f (x:num->int16) (z:int16) i.
        f IN ring_carrier mlkem_rq /\
        (!n. n < 256 ==> (ival(x n) == coeff n f) (mod &3329)) /\
        (ival z == forward_ntt (\n. ival(x n)) i) (mod &3329)
        ==> (ival z == mlkem_ntt f i) (mod &3329)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:(1->num)->int`; `\n. ival((x:num->int16) n)`; `i:num`]
         MLKEM_NTT_FORWARD_CONG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[INT_CONG_SYM]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN MESON_TAC[INT_CONG_SYM; INT_CONG_TRANS]);;

let MLKEM_NTT_CBD_BOUNDS = prove
 (`!eta b k. &0 <= mlkem_ntt (mlkem_cbd eta b) k /\
             mlkem_ntt (mlkem_cbd eta b) k < &3329`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IN_MLKEM_ZQ] THEN
  MATCH_MP_TAC MLKEM_NTT_IN_ZQ THEN
  MESON_TAC[IN_MLKEM_RQ; MLKEM_CBD_IN_RQ]);;

let MLKEM_NTT_CBD_IN_ZQ = prove
 (`!eta b k. mlkem_ntt (mlkem_cbd eta b) k IN ring_carrier mlkem_zq`,
  REWRITE_TAC[IN_MLKEM_ZQ; MLKEM_NTT_CBD_BOUNDS]);;

let MLKEM_NTT_INV_CONG = prove
 (`!(a:num->int) (b:num->int) k.
        (!i. i < 256 ==> &0 <= a i /\ a i < &3329) /\
        (!i. i < 256 ==> (b i == a i) (mod &3329)) /\ k < 256
        ==> (inverse_ntt b k == &65536 * coeff k (mlkem_ntt_inv a))
            (mod &3329)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLKEM_NTT_INV_COEFF; inverse_ntt] THEN
  REWRITE_TAC[INT_CONG_LREM] THEN
  ABBREV_TAC `I1 = isum (0..127)
                    (\j. (b:num->int) (2 * bitreverse7 j + k MOD 2) *
                         &1175 pow ((2 * j + 1) * k DIV 2))` THEN
  ABBREV_TAC `I2 = isum (0..127)
                    (\j. (a:num->int) (2 * bitreverse7 j + k MOD 2) *
                         &1175 pow ((2 * j + 1) * k DIV 2))` THEN
  SUBGOAL_THEN `(I1:int == I2) (mod &3329)` MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["I1"; "I2"] THEN
    MATCH_MP_TAC INT_CONG_ISUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(INTEGER_RULE
     `(x:int == y) (mod n) ==> (x * z == y * z) (mod n)`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(SPEC `j:num` BITREVERSE7_BOUND) THEN
    MP_TAC(ARITH_RULE `k MOD 2 < 2`) THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&3303 * I2:int`; `&3329:int`] INT_REM_MOD_SELF) THEN
  SPEC_TAC(`(&3303 * I2:int) rem &3329`,`z:int`) THEN GEN_TAC THEN
  MP_TAC(prove(`(&512:int == &65536 * &3303) (mod &3329)`,
               REWRITE_TAC[int_congruent] THEN EXISTS_TAC `-- &65024:int` THEN
               INT_ARITH_TAC)) THEN
  SPEC_TAC(`&3329:int`,`q:int`) THEN SPEC_TAC(`&3303:int`,`c:int`) THEN
  SPEC_TAC(`&65536:int`,`r:int`) THEN SPEC_TAC(`&512:int`,`m:int`) THEN
  REPEAT GEN_TAC THEN CONV_TAC INTEGER_RULE);;

let INT_CONG_REM_MUL_LEMMA = prove
 (`!x y c n:int. (x == c * y) (mod n) ==> (x rem n == c * y rem n) (mod n)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`x:int`; `n:int`] INT_REM_MOD_SELF) THEN
  MP_TAC(SPECL [`y:int`; `n:int`] INT_REM_MOD_SELF) THEN
  CONV_TAC INTEGER_RULE);;

let INVERSE_NTT_CONG_MUL = prove
 (`!(a:num->int) (b:num->int) c k.
        (!i. i < 256 ==> (b i == c * a i) (mod &3329))
        ==> (inverse_ntt b k == c * inverse_ntt a k) (mod &3329)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inverse_ntt] THEN
  MATCH_MP_TAC INT_CONG_REM_MUL_LEMMA THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(x:int == c * y) (mod n) ==> (m * x == c * m * y) (mod n)`) THEN
  REWRITE_TAC[GSYM ISUM_LMUL] THEN MATCH_MP_TAC INT_CONG_ISUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `j:num` THEN
  STRIP_TAC THEN REWRITE_TAC[INT_MUL_ASSOC] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `(x:int == y) (mod n) ==> (x * z == y * z) (mod n)`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(SPEC `j:num` BITREVERSE7_BOUND) THEN
  MP_TAC(ARITH_RULE `k MOD 2 < 2`) THEN ARITH_TAC);;

let MLKEM_NTT_INV_CONG_MUL = prove
 (`!(a:num->int) (b:num->int) c k.
        (!i. i < 256 ==> &0 <= a i /\ a i < &3329) /\
        (!i. i < 256 ==> (b i == c * a i) (mod &3329)) /\ k < 256
        ==> (inverse_ntt b k == c * &65536 * coeff k (mlkem_ntt_inv a))
            (mod &3329)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num->int`; `a:num->int`; `k:num`] MLKEM_NTT_INV_CONG) THEN
  ASM_REWRITE_TAC[INT_CONG_REFL] THEN
  MP_TAC(SPECL [`a:num->int`; `b:num->int`; `c:int`; `k:num`]
               INVERSE_NTT_CONG_MUL) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`inverse_ntt b k`,`x:int`) THEN
  SPEC_TAC(`inverse_ntt a k`,`y:int`) THEN
  SPEC_TAC(`coeff k (mlkem_ntt_inv a)`,`z:int`) THEN
  SPEC_TAC(`&3329:int`,`q:int`) THEN SPEC_TAC(`&65536:int`,`r:int`) THEN
  CONV_TAC INTEGER_RULE);;

let MLKEM_NTT_INV_IN_RQ = prove
 (`!a. (!k. k < 256 ==> &0 <= a k /\ a k < &3329)
       ==> mlkem_ntt_inv a IN ring_carrier mlkem_rq`,
  MESON_TAC[MLKEM_NTT_INV]);;

let FIPS203_MULTIPLY_NTTS_INT = prove
 (`!a b n. fips203_multiply_ntts a b n =
           (if EVEN n
            then a n * b n +
                 a(n + 1) * b(n + 1) * &17 pow (2 * bitreverse7(n DIV 2) + 1)
            else a(n - 1) * b n + a n * b(n - 1)) rem &3329`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[fips203_multiply_ntts; mlkem_zq; INTEGER_MOD_RING_CLAUSES] THEN
  COND_CASES_TAC THEN CONV_TAC INT_REM_DOWN_CONV THEN
  REWRITE_TAC[INT_MUL_ASSOC]);;

let FIPS203_MULTIPLY_NTTS_IN_ZQ = prove
 (`!a b n. fips203_multiply_ntts a b n IN ring_carrier mlkem_zq`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FIPS203_MULTIPLY_NTTS_INT] THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[INTEGER_MOD_RING_CLAUSES; ARITH; IN_ELIM_THM] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let ISUM_LT_2 = prove
 (`!f. isum {j | j < 2} f = f 0 + f 1`,
  GEN_TAC THEN SUBGOAL_THEN `{j | j < 2} = 0..1` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
    CONV_TAC(LAND_CONV EXPAND_ISUM_CONV) THEN REWRITE_TAC[INT_ADD_ASSOC]]);;

let ISUM_LT_3 = prove
 (`!f. isum {j | j < 3} f = f 0 + f 1 + f 2`,
  GEN_TAC THEN SUBGOAL_THEN `{j | j < 3} = 0..2` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
    CONV_TAC(LAND_CONV EXPAND_ISUM_CONV) THEN REWRITE_TAC[INT_ADD_ASSOC]]);;

let ISUM_LT_4 = prove
 (`!f. isum {j | j < 4} f = f 0 + f 1 + f 2 + f 3`,
  GEN_TAC THEN SUBGOAL_THEN `{j | j < 4} = 0..3` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
    CONV_TAC(LAND_CONV EXPAND_ISUM_CONV) THEN REWRITE_TAC[INT_ADD_ASSOC]]);;

(* ------------------------------------------------------------------------- *)
(* The products of a row of a matrix by a vector in the NTT domain for k =   *)
(* 2, 3 and 4, as computed by the polyvec_basemul_acc_montgomery_cached      *)
(* functions up to the factor 169 = 2^-16 mod q, in terms of MultiplyNTTs,   *)
(* for even and odd coefficients. The entries of the row in the computation, *)
(* A', may be just congruent to those in FIPS 203, A.                        *)
(* ------------------------------------------------------------------------- *)

let INT_CONG_RMUL_REM = prove
 (`!t c y n:int. (t == c * y rem n) (mod n) <=> (t == c * y) (mod n)`,
  REPEAT GEN_TAC THEN MP_TAC(SPECL [`y:int`; `n:int`] INT_REM_MOD_SELF) THEN
  CONV_TAC INTEGER_RULE);;

let BASEMUL2_ROW_EVEN = prove
 (`!(A:num->num->int) (A':num->num->int) (Y:num->num->int) (YT:num->int)
    (SH:num->num->int) (t:int) p.
     (!j. j < 2 ==> (A' j (2 * p) == A j (2 * p)) (mod &3329) /\
                    (A' j (2 * p + 1) == A j (2 * p + 1)) (mod &3329) /\
                    (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329) /\
                    (YT j == Y j (2 * p + 1) *
                             &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (t == &169 * ((A' 1 (2 * p + 1) * YT 1 + A' 1 (2 * p) * Y 1 (2 * p)) +
                   (A' 0 (2 * p + 1) * YT 0 + A' 0 (2 * p) * Y 0 (2 * p))))
     (mod &3329)
     ==> (t == &169 * ring_sum mlkem_zq {j | j < 2}
                       (\j. fips203_multiply_ntts (A j) (SH j) (2 * p)))
         (mod &3329)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[RING_SUM_INTEGER_MOD_RING; FINITE_NUMSEG_LT; ARITH_EQ;
           REWRITE_RULE[mlkem_zq] FIPS203_MULTIPLY_NTTS_IN_ZQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; ISUM_LT_2;
              FIPS203_MULTIPLY_NTTS_INT] THEN
  REWRITE_TAC[EVEN_DOUBLE; ARITH_RULE `(2 * p) DIV 2 = p`] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_CONG_RMUL_REM] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`(&17:int) pow (2 * bitreverse7 p + 1)`,`z:int`) THEN GEN_TAC THEN
  SPEC_TAC(`&3329:int`,`q:int`) THEN SPEC_TAC(`&169:int`,`ri:int`) THEN
  REPEAT GEN_TAC THEN CONV_TAC INTEGER_RULE);;

let BASEMUL2_ROW_ODD = prove
 (`!(A:num->num->int) (A':num->num->int) (Y:num->num->int)
    (SH:num->num->int) (t:int) p.
     (!j. j < 2 ==> (A' j (2 * p) == A j (2 * p)) (mod &3329) /\
                    (A' j (2 * p + 1) == A j (2 * p + 1)) (mod &3329) /\
                    (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329)) /\
     (t == &169 *
           ((A' 1 (2 * p + 1) * Y 1 (2 * p) + A' 1 (2 * p) * Y 1 (2 * p + 1)) +
            (A' 0 (2 * p + 1) * Y 0 (2 * p) + A' 0 (2 * p) * Y 0 (2 * p + 1))))
     (mod &3329)
     ==> (t == &169 * ring_sum mlkem_zq {j | j < 2}
                       (\j. fips203_multiply_ntts (A j) (SH j) (2 * p + 1)))
         (mod &3329)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[RING_SUM_INTEGER_MOD_RING; FINITE_NUMSEG_LT; ARITH_EQ;
           REWRITE_RULE[mlkem_zq] FIPS203_MULTIPLY_NTTS_IN_ZQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; ISUM_LT_2;
              FIPS203_MULTIPLY_NTTS_INT] THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN; ADD_SUB] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_CONG_RMUL_REM] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`&3329:int`,`q:int`) THEN SPEC_TAC(`&169:int`,`ri:int`) THEN
  REPEAT GEN_TAC THEN CONV_TAC INTEGER_RULE);;

let BASEMUL3_ROW_EVEN = prove
 (`!(A:num->num->int) (A':num->num->int) (Y:num->num->int) (YT:num->int)
    (SH:num->num->int) (t:int) p.
     (!j. j < 3 ==> (A' j (2 * p) == A j (2 * p)) (mod &3329) /\
                    (A' j (2 * p + 1) == A j (2 * p + 1)) (mod &3329) /\
                    (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329) /\
                    (YT j == Y j (2 * p + 1) *
                             &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (t == &169 * ((A' 2 (2 * p + 1) * YT 2 + A' 2 (2 * p) * Y 2 (2 * p)) +
                   (A' 1 (2 * p + 1) * YT 1 + A' 1 (2 * p) * Y 1 (2 * p)) +
                   (A' 0 (2 * p + 1) * YT 0 + A' 0 (2 * p) * Y 0 (2 * p))))
     (mod &3329)
     ==> (t == &169 * ring_sum mlkem_zq {j | j < 3}
                       (\j. fips203_multiply_ntts (A j) (SH j) (2 * p)))
         (mod &3329)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[RING_SUM_INTEGER_MOD_RING; FINITE_NUMSEG_LT; ARITH_EQ;
           REWRITE_RULE[mlkem_zq] FIPS203_MULTIPLY_NTTS_IN_ZQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; ISUM_LT_3;
              FIPS203_MULTIPLY_NTTS_INT] THEN
  REWRITE_TAC[EVEN_DOUBLE; ARITH_RULE `(2 * p) DIV 2 = p`] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_CONG_RMUL_REM] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`(&17:int) pow (2 * bitreverse7 p + 1)`,`z:int`) THEN GEN_TAC THEN
  SPEC_TAC(`&3329:int`,`q:int`) THEN SPEC_TAC(`&169:int`,`ri:int`) THEN
  REPEAT GEN_TAC THEN CONV_TAC INTEGER_RULE);;

let BASEMUL3_ROW_ODD = prove
 (`!(A:num->num->int) (A':num->num->int) (Y:num->num->int)
    (SH:num->num->int) (t:int) p.
     (!j. j < 3 ==> (A' j (2 * p) == A j (2 * p)) (mod &3329) /\
                    (A' j (2 * p + 1) == A j (2 * p + 1)) (mod &3329) /\
                    (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329)) /\
     (t == &169 *
           ((A' 2 (2 * p + 1) * Y 2 (2 * p) + A' 2 (2 * p) * Y 2 (2 * p + 1)) +
            (A' 1 (2 * p + 1) * Y 1 (2 * p) + A' 1 (2 * p) * Y 1 (2 * p + 1)) +
            (A' 0 (2 * p + 1) * Y 0 (2 * p) + A' 0 (2 * p) * Y 0 (2 * p + 1))))
     (mod &3329)
     ==> (t == &169 * ring_sum mlkem_zq {j | j < 3}
                       (\j. fips203_multiply_ntts (A j) (SH j) (2 * p + 1)))
         (mod &3329)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[RING_SUM_INTEGER_MOD_RING; FINITE_NUMSEG_LT; ARITH_EQ;
           REWRITE_RULE[mlkem_zq] FIPS203_MULTIPLY_NTTS_IN_ZQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; ISUM_LT_3;
              FIPS203_MULTIPLY_NTTS_INT] THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN; ADD_SUB] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_CONG_RMUL_REM] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`&3329:int`,`q:int`) THEN SPEC_TAC(`&169:int`,`ri:int`) THEN
  REPEAT GEN_TAC THEN CONV_TAC INTEGER_RULE);;

let BASEMUL4_ROW_EVEN = prove
 (`!(A:num->num->int) (A':num->num->int) (Y:num->num->int) (YT:num->int)
    (SH:num->num->int) (t:int) p.
     (!j. j < 4 ==> (A' j (2 * p) == A j (2 * p)) (mod &3329) /\
                    (A' j (2 * p + 1) == A j (2 * p + 1)) (mod &3329) /\
                    (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329) /\
                    (YT j == Y j (2 * p + 1) *
                             &17 pow (2 * bitreverse7 p + 1)) (mod &3329)) /\
     (t == &169 * ((A' 3 (2 * p + 1) * YT 3 + A' 3 (2 * p) * Y 3 (2 * p)) +
                   (A' 2 (2 * p + 1) * YT 2 + A' 2 (2 * p) * Y 2 (2 * p)) +
                   (A' 1 (2 * p + 1) * YT 1 + A' 1 (2 * p) * Y 1 (2 * p)) +
                   (A' 0 (2 * p + 1) * YT 0 + A' 0 (2 * p) * Y 0 (2 * p))))
     (mod &3329)
     ==> (t == &169 * ring_sum mlkem_zq {j | j < 4}
                       (\j. fips203_multiply_ntts (A j) (SH j) (2 * p)))
         (mod &3329)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[RING_SUM_INTEGER_MOD_RING; FINITE_NUMSEG_LT; ARITH_EQ;
           REWRITE_RULE[mlkem_zq] FIPS203_MULTIPLY_NTTS_IN_ZQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; ISUM_LT_4;
              FIPS203_MULTIPLY_NTTS_INT] THEN
  REWRITE_TAC[EVEN_DOUBLE; ARITH_RULE `(2 * p) DIV 2 = p`] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_CONG_RMUL_REM] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`(&17:int) pow (2 * bitreverse7 p + 1)`,`z:int`) THEN GEN_TAC THEN
  SPEC_TAC(`&3329:int`,`q:int`) THEN SPEC_TAC(`&169:int`,`ri:int`) THEN
  REPEAT GEN_TAC THEN CONV_TAC INTEGER_RULE);;

let BASEMUL4_ROW_ODD = prove
 (`!(A:num->num->int) (A':num->num->int) (Y:num->num->int)
    (SH:num->num->int) (t:int) p.
     (!j. j < 4 ==> (A' j (2 * p) == A j (2 * p)) (mod &3329) /\
                    (A' j (2 * p + 1) == A j (2 * p + 1)) (mod &3329) /\
                    (Y j (2 * p) == SH j (2 * p)) (mod &3329) /\
                    (Y j (2 * p + 1) == SH j (2 * p + 1)) (mod &3329)) /\
     (t == &169 *
           ((A' 3 (2 * p + 1) * Y 3 (2 * p) + A' 3 (2 * p) * Y 3 (2 * p + 1)) +
            (A' 2 (2 * p + 1) * Y 2 (2 * p) + A' 2 (2 * p) * Y 2 (2 * p + 1)) +
            (A' 1 (2 * p + 1) * Y 1 (2 * p) + A' 1 (2 * p) * Y 1 (2 * p + 1)) +
            (A' 0 (2 * p + 1) * Y 0 (2 * p) + A' 0 (2 * p) * Y 0 (2 * p + 1))))
     (mod &3329)
     ==> (t == &169 * ring_sum mlkem_zq {j | j < 4}
                       (\j. fips203_multiply_ntts (A j) (SH j) (2 * p + 1)))
         (mod &3329)`,
  REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  REWRITE_TAC[mlkem_zq] THEN
  SIMP_TAC[RING_SUM_INTEGER_MOD_RING; FINITE_NUMSEG_LT; ARITH_EQ;
           REWRITE_RULE[mlkem_zq] FIPS203_MULTIPLY_NTTS_IN_ZQ] THEN
  REWRITE_TAC[INTEGER_MOD_RING_CLAUSES; ISUM_LT_4;
              FIPS203_MULTIPLY_NTTS_INT] THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN; ADD_SUB] THEN
  CONV_TAC INT_REM_DOWN_CONV THEN REWRITE_TAC[INT_CONG_RMUL_REM] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`&3329:int`,`q:int`) THEN SPEC_TAC(`&169:int`,`ri:int`) THEN
  REPEAT GEN_TAC THEN CONV_TAC INTEGER_RULE);;

(* ------------------------------------------------------------------------- *)
(* The hash function G, encoding of coefficients mod q, compression and      *)
(* decompression.                                                            *)
(* ------------------------------------------------------------------------- *)

let MLKEM_G_BYTES = prove
 (`!a c s:armstate.
        read (memory :> bytes(a,64)) s = num_of_bytelist(sha3_512 c)
        ==> read (memory :> bytes(a,32)) s =
            num_of_bytelist(FST(mlkem_g c)) /\
            read (memory :> bytes(word_add a (word 32),32)) s =
            num_of_bytelist(SND(mlkem_g c))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `64`; `32`; `read memory (s:armstate)`]
                READ_BYTES_MOD) THEN
  MP_TAC(ISPECL [`a:int64`; `64`; `32`; `read memory (s:armstate)`]
                READ_BYTES_DIV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 64 32 = 32 /\ 64 - 32 = 32`] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[mlkem_g; mlkem_slice; sha3_512; ADD_CLAUSES] THEN
  SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `i < 32 ==> i < 64 /\ 32 + i < 64`;
           LIST_OF_SEQ_EQ] THEN
  REWRITE_TAC[ARITH_RULE `64 = 32 + 32`;
              NUM_OF_BYTELIST_LIST_OF_SEQ_SPLIT] THEN
  MP_TAC(ISPEC `list_of_seq (keccak_sponge 1024 6 c) 32`
                NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; MOD_LT; DIV_LT; EXP_EQ_0; ARITH_EQ;
               ADD_CLAUSES] THEN
  CONJ_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
  SIMP_TAC[EL_LIST_OF_SEQ; ARITH_RULE `i < 32 ==> i < 64 /\ i + 32 < 64`] THEN
  REWRITE_TAC[ADD_SYM]);;

let LENGTH_MLKEM_G = prove
 (`!c. LENGTH(FST(mlkem_g c)) = 32 /\ LENGTH(SND(mlkem_g c)) = 32`,
  REWRITE_TAC[mlkem_g; mlkem_slice; LENGTH_LIST_OF_SEQ]);;

let MLKEM_ENCODE_12_LIST = prove
 (`!n (c:num->int).
        EVEN n /\ (!i. i < n ==> &0 <= c i /\ c i < &3329)
        ==> num_of_bytelist(mlkem_encode 12 n c) =
            num_of_wordlist(MAP (word_zx:int16->12 word)
                             (list_of_seq (\i. iword(c i)) n))`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NUM_OF_BYTELIST_MLKEM_ENCODE o
    lhand o snd) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o
      REWRITE_RULE[EVEN_EXISTS]) THEN
    REWRITE_TAC[ARITH_RULE `12 * 2 * m = 8 * 3 * m`] THEN
    MESON_TAC[DIVIDES_RMUL; DIVIDES_REFL];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MAP_LIST_OF_SEQ; o_DEF; NUM_OF_WORDLIST_LIST_OF_SEQ] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(c:num->int) i = &(num_of_int(c i))` SUBST1_TAC THENL
   [ASM_SIMP_TAC[INT_OF_NUM_OF_INT]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`num_of_int((c:num->int) i)`,`v:num`) THEN GEN_TAC THEN
  REWRITE_TAC[INT_OF_NUM_LT; GSYM WORD_IWORD] THEN DISCH_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; INT_POW; INT_OF_NUM_POW;
              INT_OF_NUM_REM; NUM_OF_INT_OF_NUM] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `65536 = 4096 * 16`; MOD_MOD]);;

let MLKEM_COMPRESS_NUM = prove
 (`!d x. mlkem_compress d (&x) =
         &(((2 EXP (d + 1) * x + 3329) DIV 6658) MOD 2 EXP d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlkem_compress; mlkem_round] THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_MUL; INT_OF_NUM_ADD] THEN
  REWRITE_TAC[INT_OF_NUM_DIV; INT_OF_NUM_REM] THEN
  REWRITE_TAC[EXP_ADD; INT_OF_NUM_EQ] THEN
  REWRITE_TAC[ARITH_RULE `2 * 3329 = 6658`; EXP_1; MULT_AC]);;

let MLKEM_COMPRESS_DIGIT = prove
 (`!d x. &0 <= x
         ==> num_of_int(mlkem_compress d x rem &2 pow d) =
             ((2 EXP (d + 1) * num_of_int x + 3329) DIV 6658) MOD 2 EXP d`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP INT_OF_NUM_OF_INT) THEN
  REWRITE_TAC[MLKEM_COMPRESS_NUM; NUM_OF_INT_OF_NUM] THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_REM; MOD_MOD_REFL;
              NUM_OF_INT_OF_NUM]);;

let MLKEM_DECOMPRESS_1 = prove
 (`!b. b < 2 ==> mlkem_decompress 1 (&b) = &((3329 * b + 1) DIV 2)`,
  REWRITE_TAC[ARITH_RULE `b < 2 <=> b = 0 \/ b = 1`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[mlkem_decompress; mlkem_round] THEN
  CONV_TAC INT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let MLKEM_DECOMPRESS_NUM = prove
 (`!d x. ~(d = 0)
         ==> mlkem_decompress d (&x) =
             &((3329 * x + 2 EXP (d - 1)) DIV 2 EXP d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_decompress; mlkem_round] THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_MUL; INT_OF_NUM_ADD;
              INT_OF_NUM_DIV; INT_OF_NUM_EQ] THEN
  SUBGOAL_THEN `2 EXP d = 2 * 2 EXP (d - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 * 3329 * x + 2 * e = 2 * (3329 * x + e)`] THEN
  SIMP_TAC[DIV_MULT2; ARITH_EQ]);;

let MLKEM_DECODE_1 = prove
 (`!m i. mlkem_decode 1 m i = &((num_of_bytelist m DIV 2 EXP i) MOD 2)`,
  REWRITE_TAC[mlkem_decode] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ARITH_EQ; MULT_CLAUSES; EXP_1]);;

let MLKEM_DECODE_SMALL = prove
 (`!d b i. d < 12
           ==> mlkem_decode d b i =
               &((num_of_bytelist b DIV 2 EXP (d * i)) MOD 2 EXP d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_decode] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let TT_DECODE_CONG = prove
 (`!ek (t:int16) idx.
        t = word((num_of_bytelist ek DIV 2 EXP (12 * idx)) MOD 2 EXP 12)
        ==> (ival t == mlkem_decode 12 ek idx) (mod &3329)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[mlkem_decode] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
  REWRITE_TAC[INT_CONG_RREM] THEN
  SUBGOAL_THEN `(num_of_bytelist ek DIV 2 EXP (12 * idx)) MOD 2 EXP 12 < 4096`
  MP_TAC THENL [REWRITE_TAC[ARITH_RULE `4096 = 2 EXP 12`; MOD_LT_EQ] THEN
                CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SPEC_TAC(`(num_of_bytelist ek DIV 2 EXP (12 * idx)) MOD 2 EXP 12`,
           `f:num`) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ival(word f:int16) = &f` SUBST1_TAC THENL
   [REWRITE_TAC[ival; VAL_WORD; DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `f < 4096 ==> f < 65536`;
                 ARITH_RULE `f < 4096 ==> f < 32768`];
    REWRITE_TAC[INT_CONG_REFL]]);;

let MU_IVAL = prove
 (`!b. b < 2
       ==> ival(word((3329 * b + 1) DIV 2):int16) = &((3329 * b + 1) DIV 2)`,
  REWRITE_TAC[ARITH_RULE `b < 2 <=> b = 0 \/ b = 1`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV);;

let LIST_OF_SEQ_REDUCED = prove
 (`!(f:num->int16) (g:num->int) n.
        (!i. i < n ==> ival(f i) = g i rem &3329)
        ==> LENGTH(list_of_seq f n) = n /\
            ALL (\x. val x < 4096) (list_of_seq f n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; GSYM ALL_EL] THEN
  SIMP_TAC[LENGTH_LIST_OF_SEQ; EL_LIST_OF_SEQ] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`(g:num->int) i`; `&3329:int`] INT_REM_POS) THEN
  MP_TAC(SPECL [`(g:num->int) i`; `&3329:int`] INT_LT_REM) THEN
  CONV_TAC INT_REDUCE_CONV THEN
  SPEC_TAC(`(g:num->int) i rem &3329`,`y:int`) THEN
  MP_TAC(ISPEC `(f:num->int16) i` VAL_BOUND) THEN
  REWRITE_TAC[ival; DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val((f:num->int16) i)`,`v:num`) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN INT_ARITH_TAC);;

let VAL_LT_OF_IVAL_REM = prove
 (`!(x:int16) y. ival x = y rem &3329 ==> val x < 3329`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`y:int`; `&3329:int`] INT_REM_POS) THEN
  MP_TAC(SPECL [`y:int`; `&3329:int`] INT_LT_REM) THEN
  CONV_TAC INT_REDUCE_CONV THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPEC `x:int16` VAL_BOUND) THEN
  REWRITE_TAC[ival; DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(x:int16)`,`v:num`) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Miscellaneous facts about arithmetic and about the frames of callees.     *)
(* ------------------------------------------------------------------------- *)

let IVAL_WORD_ADD_SMALL = prove
 (`!x y:int16. abs(ival x) <= &3328 /\ abs(ival y) <= &23594
               ==> ival(word_add x y) = ival x + ival y`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o BINOP_CONV) [GSYM IWORD_IVAL] THEN
  REWRITE_TAC[GSYM IWORD_INT_ADD] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_INT_ARITH_TAC);;

let IVAL_WORD_ADD_BOUNDED = prove
 (`!x y:int16. --(&32768) <= ival x + ival y /\ ival x + ival y < &32768
               ==> ival(word_add x y) = ival x + ival y`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o BINOP_CONV) [GSYM IWORD_IVAL] THEN
  REWRITE_TAC[GSYM IWORD_INT_ADD] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let IVAL_WORD_SUB_BOUNDED = prove
 (`!x y:int16. --(&32768) <= ival x - ival y /\ ival x - ival y < &32768
               ==> ival(word_sub x y) = ival x - ival y`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o BINOP_CONV) [GSYM IWORD_IVAL] THEN
  REWRITE_TAC[GSYM IWORD_INT_SUB] THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let IVAL_WORD_SMALL = prove
 (`!f. f < 32768 ==> ival(word f:int16) = &f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ival; VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `f < 32768 ==> f < 65536`]);;

let VAL_EQ_NUM_OF_INT_IVAL = prove
 (`!(x:int16) c. &0 <= c /\ ival x = c ==> val x = num_of_int c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ival(x:int16) = &(val x)` ASSUME_TAC THENL
   [REWRITE_TAC[ival; DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(ISPEC `x:int16` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `ival(x:int16) = c` THEN UNDISCH_TAC `&0:int <= c` THEN
    REWRITE_TAC[ival; DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT; NOT_LT; GSYM INT_OF_NUM_LE] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `ival(x:int16) = c` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[NUM_OF_INT_OF_NUM]);;

let INT_CONG_MONT_CANCEL = prove
 (`!x y c:int. (x == y) (mod &3329) /\ (y == &169 * &65536 * c) (mod &3329)
               ==> (x == c) (mod &3329)`,
  REPEAT GEN_TAC THEN
  MP_TAC(prove(`(&169 * &65536:int == &1) (mod &3329)`,
               REWRITE_TAC[int_congruent] THEN EXISTS_TAC `&3327:int` THEN
               INT_ARITH_TAC)) THEN
  SPEC_TAC(`&3329:int`,`q:int`) THEN SPEC_TAC(`&169:int`,`ri:int`) THEN
  SPEC_TAC(`&65536:int`,`r:int`) THEN REPEAT GEN_TAC THEN
  CONV_TAC INTEGER_RULE);;

let INT_CONG_ADD3_REM_ALT = prove
 (`!a b c x y z q:int.
     (a == x) (mod q) /\ (b == y) (mod q) /\ c = z
     ==> ((a + b) + c == (x + y) rem q + z) (mod q)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`x + y:int`; `q:int`] INT_REM_MOD_SELF) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN CONV_TAC INTEGER_RULE);;

let DIV_MOD_ADD_LT = prove
 (`!m r n. n < m ==> (m * r + n) DIV m = r /\ (m * r + n) MOD m = n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; DIV_LT; MOD_LT; ADD_CLAUSES]);;

let EXISTS_DIV_MOD_LT = prove
 (`!m k i. i < m * k ==> ?r n. r < k /\ n < m /\ i = m * r + n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `i < m * k` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`i DIV m`; `i MOD m`] THEN
  ASM_SIMP_TAC[MOD_LT_EQ; RDIV_LT_EQ] THEN
  MP_TAC(SPECL [`i:num`; `m:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let NONOVERLAPPING_MODULO_ZERO_LEN = prove
 (`(!n a b k. nonoverlapping_modulo n (a,0) (b,k)) /\
   (!n a b k. nonoverlapping_modulo n (b,k) (a,0))`,
  REWRITE_TAC[NONOVERLAPPING_MODULO_DIFFERENCE]);;

let NONOVERLAPPING_ZERO_NONZERO = prove
 (`!a:int64 n k.
        nonoverlapping (word 0:int64,1) (a,n) /\ k < n
        ==> ~(word_add a (word k) = word 0)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; nonoverlapping_modulo] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD; VAL_WORD_0;
              DIMINDEX_64] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`0`; `k:num`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < 1`; ADD_CLAUSES] THEN
  REWRITE_TAC[CONG] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[ADD_MOD_MOD_REFL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let ASSIGNS_MEMORY_BYTES_0 = prove
 (`!a:int64.
        ASSIGNS (memory :> bytes(a,0)) = ((=):armstate->armstate->bool)`,
  GEN_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; ASSIGNS_THM; WRITE_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[CONJUNCT1(CONJUNCT2(CONJUNCT2 bytes))] THEN
  MP_TAC(REWRITE_RULE[EXTENSIONALLY_VALID_COMPONENT]
   (EXTENSIONALLY_VALID_COMPONENT_CONV
     `extensionally_valid_component
       (memory:(armstate,int64->byte)component)`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;
