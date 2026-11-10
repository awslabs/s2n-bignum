(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas connecting the C-level specifications of the SHAKE streams and the *)
(* samplers of mldsa-native (common/mldsa_native_fips202.ml,                 *)
(* common/mldsa_native_sampling.ml and common/mldsa_native_challenge.ml) to  *)
(* the FIPS 204 specification in common/fips204.ml, for the bridge theorems  *)
(* of the API functions. The C-level SHAKE streams of a message M of inlen   *)
(* bytes, as a number, are SHAKE128 and SHAKE256 of bytelist_of_num inlen M  *)
(* when M < 2^(8 * inlen). The samplers compute RejNTTPoly and ExpandA,      *)
(* RejBoundedPoly and SampleInBall when they terminate (the _terminates      *)
(* predicates of the C-level specifications, under which the FIPS 204        *)
(* samplers are well defined), and ExpandMask in all cases.                  *)
(* ========================================================================= *)

needs "x86/proofs/utils/keccak_fips202.ml";;
needs "common/fips204_theory.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "common/mldsa_native_challenge.ml";;

type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Lists of accepted values: the i-th element of FILTER P of the first N     *)
(* values of a sequence c is c(j) for the j with P(c j) that is preceded by  *)
(* exactly i others, which is how FIPS 204 defines the rejection samplers.   *)
(* Byte strings: splitting bytelist_of_num, the bytes and bits of a byte     *)
(* string as a number, and words from their bits.                            *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SAMPLE_LENGTH_FILTER = prove
 (`!(P:A->bool) (c:num->A) n.
        LENGTH(FILTER P (list_of_seq c n)) = CARD {j | j < n /\ P(c j)}`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[list_of_seq; FILTER; LENGTH; LT; EMPTY_GSPEC; CARD_CLAUSES] THEN
  ASM_REWRITE_TAC[FILTER_APPEND; LENGTH_APPEND; FILTER] THEN
  REWRITE_TAC[TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
  REWRITE_TAC[SET_RULE `{j:num | j = n /\ Q j \/ R j} =
                        if Q n then n INSERT {j | R j} else {j | R j}`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ADD_CLAUSES] THEN
  SUBGOAL_THEN `FINITE {j | j < n /\ (P:A->bool)(c j)}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j:num | j < n}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    ASM_SIMP_TAC[CARD_CLAUSES; IN_ELIM_THM; LT_REFL]]);;

let MLD_FIPS204_SAMPLE_EL_FILTER_EXISTS = prove
 (`!(P:A->bool) (c:num->A) N i.
        i < LENGTH(FILTER P (list_of_seq c N))
        ==> ?j. j < N /\ P(c j) /\ LENGTH(FILTER P (list_of_seq c j)) = i /\
                EL i (FILTER P (list_of_seq c N)) = c j`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[list_of_seq; FILTER; LENGTH; LT] THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[FILTER_APPEND; FILTER; LENGTH_APPEND] THEN
  ASM_CASES_TAC `i < LENGTH(FILTER P (list_of_seq (c:num->A) N))` THENL
   [DISCH_THEN(K ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `j:num` THEN ASM_SIMP_TAC[EL_APPEND];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH; ADD_CLAUSES] THEN
  DISCH_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `i = LENGTH(FILTER P (list_of_seq (c:num->A) N))`
  SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD]);;

let MLD_FIPS204_SAMPLE_LENGTH_FILTER_MONO = prove
 (`!(P:A->bool) (c:num->A) m n.
        m <= n
        ==> LENGTH(FILTER P (list_of_seq c m)) <=
            LENGTH(FILTER P (list_of_seq c n))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[MLD_LIST_OF_SEQ_ADD; FILTER_APPEND; LENGTH_APPEND; LE_ADD]);;

let MLD_FIPS204_SAMPLE_EL_FILTER = prove
 (`!(P:A->bool) (c:num->A) N i.
        i < LENGTH(FILTER P (list_of_seq c N))
        ==> EL i (FILTER P (list_of_seq c N)) =
            c(@j. P(c j) /\ CARD {j' | j' < j /\ P(c j')} = i) /\
            P(c(@j. P(c j) /\ CARD {j' | j' < j /\ P(c j')} = i))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC o
    MATCH_MP MLD_FIPS204_SAMPLE_EL_FILTER_EXISTS) THEN
  SUBGOAL_THEN
   `(@j. (P:A->bool)(c j) /\ CARD {j' | j' < j /\ P(c j')} = i) = j`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `y:num` THEN
  REWRITE_TAC[GSYM MLD_FIPS204_SAMPLE_LENGTH_FILTER] THEN
  EQ_TAC THENL [ALL_TAC; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!u v. u < v /\ (P:A->bool)(c u)
          ==> LENGTH(FILTER P (list_of_seq c u)) <
              LENGTH(FILTER P (list_of_seq c v))`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    TRANS_TAC LTE_TRANS
     `LENGTH(FILTER P (list_of_seq (c:num->A) (SUC u)))` THEN
    ASM_SIMP_TAC[MLD_FIPS204_SAMPLE_LENGTH_FILTER_MONO; LE_SUC_LT] THEN
    ASM_REWRITE_TAC[list_of_seq; FILTER_APPEND; FILTER; LENGTH_APPEND;
                    LENGTH] THEN
    ARITH_TAC;
    DISCH_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `~(y < j) /\ ~(j < y) ==> y:num = j`) THEN
  CONJ_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`y:num`; `j:num`] th) THEN
                          MP_TAC(SPECL [`j:num`; `y:num`] th)) THEN
  ASM_REWRITE_TAC[LT_REFL]);;

let MLD_FIPS204_SAMPLE_BYTELIST_OF_NUM_ADD = prove
 (`!m n x. bytelist_of_num (m + n) x =
           APPEND (bytelist_of_num m x) (bytelist_of_num n (x DIV 256 EXP m))`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; bytelist_of_num; APPEND; EXP; DIV_1] THEN
  REWRITE_TAC[DIV_DIV]);;

let MLD_FIPS204_SAMPLE_BYTELIST_OF_NUM_SPLIT = prove
 (`!m n a b.
        a < 256 EXP m
        ==> bytelist_of_num (m + n) (a + 256 EXP m * b) =
            APPEND (bytelist_of_num m a) (bytelist_of_num n b)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[MLD_FIPS204_SAMPLE_BYTELIST_OF_NUM_ADD] THEN BINOP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM BYTELIST_OF_NUM_MOD] THEN
    AP_TERM_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT];
    AP_TERM_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES]]);;

let MLD_FIPS204_SAMPLE_BYTE_DIGIT = prove
 (`!(s:num->byte) m j.
        j < m
        ==> (num_of_bytelist(list_of_seq s m) DIV 2 EXP (8 * j)) MOD 256 =
            val(s j)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LT] THEN X_GEN_TAC `j:num` THEN
  REWRITE_TAC[list_of_seq; NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ;
              num_of_bytelist; MULT_CLAUSES; ADD_CLAUSES] THEN
  MP_TAC(REWRITE_RULE[LENGTH_LIST_OF_SEQ; ARITH_RULE `256 = 2 EXP 8`; EXP_EXP]
   (ISPEC `list_of_seq (s:num->byte) m` NUM_OF_BYTELIST_BOUND)) THEN
  ABBREV_TAC `x = num_of_bytelist(list_of_seq (s:num->byte) m)` THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (is_eq o concl)) THEN
    SUBGOAL_THEN `(x + 2 EXP (8 * m) * val((s:num->byte) m)) DIV
                  2 EXP (8 * m) = val(s m)` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `x:num` THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MATCH_MP_TAC MOD_LT THEN MP_TAC(ISPEC `(s:num->byte) m` VAL_BOUND) THEN
      REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC];
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `2 EXP (8 * m) * val((s:num->byte) m) =
      ((2 EXP (8 * (m - j - 1)) * val(s m)) * 256) * 2 EXP (8 * j)`
    SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `((a * b) * c) * d = (a * c * d) * b`] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; GSYM EXP_ADD] THEN
      AP_TERM_TAC THEN ASM_ARITH_TAC;
      ONCE_REWRITE_TAC[ADD_SYM] THEN
      SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; MOD_MULT_ADD]]]);;

let MLD_FIPS204_SAMPLE_ODD_DIV_MOD = prove
 (`!x n k. ODD((x MOD 2 EXP n) DIV 2 EXP k) <=> k < n /\ ODD(x DIV 2 EXP k)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `k < n:num` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[ODD_MOD; DIV_MOD] THEN
    SUBGOAL_THEN `2 EXP k * 2 = 2 EXP (k + 1)` SUBST1_TAC THENL
     [REWRITE_TAC[EXP_ADD; EXP_1]; REWRITE_TAC[MOD_MOD_EXP_MIN]] THEN
    SUBGOAL_THEN `MIN n (k + 1) = k + 1` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[]];
    SUBGOAL_THEN `(x MOD 2 EXP n) DIV 2 EXP k = 0`
     (fun th -> REWRITE_TAC[th; ODD]) THEN
    MATCH_MP_TAC DIV_LT THEN TRANS_TAC LTE_TRANS `2 EXP n` THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ; LE_EXP] THEN ASM_ARITH_TAC]);;

let MLD_FIPS204_SAMPLE_ODD_LIST = prove
 (`!(s:num->byte) m a.
        ODD(num_of_bytelist(list_of_seq s m) DIV 2 EXP a) <=>
        a < 8 * m /\ bit (a MOD 8) (s(a DIV 8))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a < 8 * m` THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPECL [`s:num->byte`; `m:num`; `a DIV 8`]
      MLD_FIPS204_SAMPLE_BYTE_DIGIT) THEN
    ANTS_TAC THENL
     [SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[BIT_VAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; MLD_FIPS204_SAMPLE_ODD_DIV_MOD] THEN
    REWRITE_TAC[DIV_DIV; GSYM EXP_ADD] THEN
    SIMP_TAC[MOD_LT_EQ; ARITH_EQ] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [`a:num`; `8`] DIVISION) THEN ARITH_TAC;
    SUBGOAL_THEN `num_of_bytelist(list_of_seq (s:num->byte) m) DIV 2 EXP a = 0`
     (fun th -> REWRITE_TAC[th; ODD]) THEN
    MATCH_MP_TAC DIV_LT THEN
    MP_TAC(ISPEC `list_of_seq (s:num->byte) m` NUM_OF_BYTELIST_BOUND) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ; ARITH_RULE `256 = 2 EXP 8`; EXP_EXP] THEN
    MATCH_MP_TAC(ARITH_RULE `b <= c ==> x < b ==> x < c`) THEN
    REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC]);;

let MLD_FIPS204_SAMPLE_VAL_BITS = prove
 (`!(w:N word) x.
        x < 2 EXP dimindex(:N) /\
        (!t. t < dimindex(:N) ==> (bit t w <=> ODD(x DIV 2 EXP t)))
        ==> val w = x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `w:N word = word x` SUBST1_TAC THENL
   [REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD] THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[VAL_WORD; MOD_LT]]);;

let MLD_FIPS204_SAMPLE_IVAL_SUB = prove
 (`!a (x:int32).
        a < 2147483648 /\ val x < 2147483648
        ==> ival(word_sub (word a) x) = &a - &(val x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ival(x:int32) = &(val x)` ASSUME_TAC THENL
   [MATCH_MP_TAC IVAL_EQ_VAL THEN REWRITE_TAC[DIMINDEX_32] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM IWORD_IVAL] THEN
  ASM_REWRITE_TAC[WORD_IWORD; GSYM IWORD_INT_SUB] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LT]) THEN ASM_INT_ARITH_TAC);;

let MLD_FIPS204_SAMPLE_MLDSA_POLY_EQ = prove
 (`!a b. (!i. i < 256 ==> a i = b i) ==> mldsa_poly a = mldsa_poly b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mldsa_poly; FUN_EQ_THM] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* SHAKE: the stream that mld_keccak_squeeze_byte gives from the state that  *)
(* mld_keccak_absorb_once leaves is keccak_sponge of the message, so the     *)
(* C-level streams mld_shake128_stream, mld_shake256_stream and              *)
(* mld_shake256_byte of a message M of inlen bytes are SHAKE128 and SHAKE256 *)
(* of bytelist_of_num inlen M. The bound M < 2^(8 * inlen) is needed, as the *)
(* C-level functions absorb all of M: for inlen = 0 and M = 1 the absorbed   *)
(* states differ. Also the messages seed || nonce of 66 bytes and rho || j   *)
(* || i of 34 bytes as byte strings.                                         *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SAMPLE_ABSORB_BLOCKS = prove
 (`!r X n. mld_keccak_absorb_blocks r (word 0) X n = keccak_absorb r X n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[mld_keccak_absorb_blocks; keccak_absorb]);;

let MLD_FIPS204_SAMPLE_KECCAK_ABSORB_EQ = prove
 (`!r P Q n.
        (!j. j < n ==> (P DIV 2 EXP (8 * r * j)) MOD 2 EXP (8 * r) =
                       (Q DIV 2 EXP (8 * r * j)) MOD 2 EXP (8 * r))
        ==> keccak_absorb r P n = keccak_absorb r Q n`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[keccak_absorb] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC);;

let MLD_FIPS204_SAMPLE_SQUEEZE_BYTE = prove
 (`!r (S:1600 word) i.
        0 < r
        ==> mld_keccak_squeeze_byte r S r i =
            word_subword (keccak_squeeze (i DIV r + 1) S) (8 * (i MOD r),8)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_keccak_squeeze_byte] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `r + i = 1 * r + i` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  REWRITE_TAC[ADD_SYM]);;

let MLD_FIPS204_SAMPLE_SPONGE = prove
 (`!c d r inlen M.
        (1600 - c) DIV 8 = r /\ 0 < r /\ M < 2 EXP (8 * inlen)
        ==> keccak_sponge c d (bytelist_of_num inlen M) =
            mld_keccak_squeeze_byte r (mld_keccak_absorb_once r d inlen M) r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  MP_TAC(SPECL [`c:num`; `d:num`; `bytelist_of_num inlen M`; `r:num`;
                `M + 2 EXP (8 * inlen) * num_of_bytelist(keccak_pad r d inlen)`;
                `i:num`] KECCAK_SPONGE_SQUEEZE) THEN
  REWRITE_TAC[LENGTH_BYTELIST_OF_NUM; NUM_OF_BYTELIST_OF_NUM] THEN
  SUBGOAL_THEN `M MOD 256 EXP inlen = M` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN
    ASM_REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[MLD_FIPS204_SAMPLE_SQUEEZE_BYTE; MLD_KECCAK_ABSORB_ONCE]);;

let MLD_FIPS204_SAMPLE_FINALIZE = prove
 (`!r p inlen M.
        0 < r /\ p < 128 /\ M < 2 EXP (8 * inlen)
        ==> mld_keccak_finalize r p
             (FST(mld_keccak_absorb r (word 0) 0 inlen M))
             (SND(mld_keccak_absorb r (word 0) 0 inlen M)) =
            mld_keccak_absorb_once r p inlen M`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mld_keccak_absorb; mld_keccak_finalize;
              MLD_KECCAK_ABSORB_ONCE] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES;
              MLD_FIPS204_SAMPLE_ABSORB_BLOCKS] THEN
  ABBREV_TAC `pad = num_of_bytelist(keccak_pad r p inlen)` THEN
  SUBGOAL_THEN `pad < 2 EXP (8 * (r - inlen MOD r))` ASSUME_TAC THENL
   [EXPAND_TAC "pad" THEN MATCH_MP_TAC KECCAK_PAD_BOUND THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(r = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `keccak_absorb r (M + 2 EXP (8 * inlen) * pad) (inlen DIV r) =
                keccak_absorb r M (inlen DIV r)` SUBST1_TAC THENL
   [MATCH_MP_TAC MLD_FIPS204_SAMPLE_KECCAK_ABSORB_EQ THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN MATCH_MP_TAC KECCAK_BLOCK_FULL THEN
    ASM_SIMP_TAC[GSYM LE_RDIV_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`M:num`; `pad:num`; `inlen:num`; `r:num`]
    KECCAK_BLOCK_LAST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`M:num`; `0`; `inlen:num`; `r:num`] KECCAK_BLOCK_LAST) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT_NZ; EXP_EQ_0; ARITH_EQ] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `M DIV 2 EXP (8 * r * inlen DIV r) < 2 EXP (8 * inlen MOD r)`
  ASSUME_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
    SUBGOAL_THEN `8 * r * inlen DIV r + 8 * inlen MOD r = 8 * inlen`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    MP_TAC(SPECL [`inlen:num`; `r:num`] DIVISION) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inlen MOD r < r` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOD_LT_EQ]; ALL_TAC] THEN
  MP_TAC(SPECL [`r:num`; `p:num`; `inlen:num`] KECCAK_PAD_NUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY ABBREV_TAC [`a = M DIV 2 EXP (8 * r * inlen DIV r)`;
                        `t = inlen MOD r`;
                        `A = keccak_absorb r M (inlen DIV r)`] THEN
  SUBGOAL_THEN
   `word_xor (word_xor (word a) (word(2 EXP (8 * t) * p)))
             (word(2 EXP (8 * (r - 1)) * 128)):1600 word =
    word(a + 2 EXP (8 * t) *
             (if t = r - 1 then p + 128
              else p + 2 EXP (8 * (r - t - 1)) * 128))`
   (fun th -> REWRITE_TAC[GSYM th; WORD_XOR_ASSOC]) THEN
  ASM_SIMP_TAC[WORD_XOR_DISJOINT_ADD] THEN
  SUBGOAL_THEN `a + 2 EXP (8 * t) * p < 2 EXP (8 * t + 7)` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (8 * t) * (p + 1)` THEN CONJ_TAC THENL
     [REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC;
      REWRITE_TAC[EXP_ADD; LE_MULT_LCANCEL] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `2 EXP (8 * (r - 1)) * 128 = 2 EXP (8 * t + 7) * 1`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[EXP_ADD] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[WORD_XOR_DISJOINT_ADD] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXP_ADD] THEN ARITH_TAC;
    SUBGOAL_THEN `8 * (r - 1) = 8 * t + 8 * (r - t - 1)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) WORD_XOR_DISJOINT_ADD
      (lhand w))) THEN
    ANTS_TAC THENL
     [TRANS_TAC LTE_TRANS `2 EXP (8 * t + 7)` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXP_ADD] THEN ARITH_TAC]]);;

let MLD_FIPS204_SHAKE128_STREAM = prove
 (`!inlen M.
        M < 2 EXP (8 * inlen)
        ==> mld_shake128_stream inlen M = shake128 (bytelist_of_num inlen M)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_shake128_stream; shake128] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MLD_FIPS204_SAMPLE_SPONGE THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let MLD_FIPS204_SHAKE256_STREAM = prove
 (`!inlen M.
        M < 2 EXP (8 * inlen)
        ==> mld_shake256_stream inlen M = shake256 (bytelist_of_num inlen M)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_shake256_stream; shake256] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MLD_FIPS204_SAMPLE_SPONGE THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let MLD_FIPS204_SHAKE256_BYTE = prove
 (`!inlen M.
        M < 2 EXP (8 * inlen)
        ==> mld_shake256_byte inlen M = shake256 (bytelist_of_num inlen M)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM MLD_FIPS204_SHAKE256_STREAM] THEN
  REWRITE_TAC[mld_shake256_byte; mld_shake256_stream; mld_shake256_state] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MLD_FIPS204_SAMPLE_FINALIZE THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let MLD_FIPS204_SHAKE256_BYTE_STREAM = prove
 (`!inlen M.
        M < 2 EXP (8 * inlen)
        ==> mld_shake256_byte inlen M = mld_shake256_stream inlen M`,
  SIMP_TAC[MLD_FIPS204_SHAKE256_BYTE; MLD_FIPS204_SHAKE256_STREAM]);;

let MLD_FIPS204_SEED_NONCE = prove
 (`!seed v.
        seed < 2 EXP 512 /\ v < 65536
        ==> seed + 2 EXP 512 * v < 2 EXP (8 * 66) /\
            bytelist_of_num 66 (seed + 2 EXP 512 * v) =
            APPEND (bytelist_of_num 64 seed) (bytelist_of_num 2 v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `8 * 66 = 512 + 16`; EXP_ADD] THEN
    TRANS_TAC LTE_TRANS `2 EXP 512 + 2 EXP 512 * v` THEN
    ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN
    REWRITE_TAC[ARITH_RULE `a + a * v = a * (v + 1)`; LE_MULT_LCANCEL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `2 EXP 512 = 256 EXP 64` SUBST1_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `66 = 64 + 2`] THEN
    MATCH_MP_TAC MLD_FIPS204_SAMPLE_BYTELIST_OF_NUM_SPLIT THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]]);;

let MLD_FIPS204_MATRIX_SEED = prove
 (`!rho i j.
        rho < 2 EXP 256 /\ i < 256 /\ j < 256
        ==> mld_matrix_seed rho i j < 2 EXP (8 * 34) /\
            bytelist_of_num 34 (mld_matrix_seed rho i j) =
            APPEND (bytelist_of_num 32 rho) [word j; word i]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mld_matrix_seed] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `8 * 34 = 256 + 16`; EXP_ADD] THEN
    TRANS_TAC LTE_TRANS `2 EXP 256 + 2 EXP 256 * (j + 256 * i)` THEN
    ASM_REWRITE_TAC[LT_ADD_RCANCEL] THEN
    REWRITE_TAC[ARITH_RULE `a + a * v = a * (v + 1)`; LE_MULT_LCANCEL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `2 EXP 256 = 256 EXP 32` SUBST1_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `34 = 32 + 2`] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      MLD_FIPS204_SAMPLE_BYTELIST_OF_NUM_SPLIT o lhand o snd) THEN
    ANTS_TAC THENL
     [RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC] THEN
    REWRITE_TAC[num_CONV `2`; num_CONV `1`; bytelist_of_num; CONS_11] THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ] THEN
    ASM_SIMP_TAC[MOD_LT; DIV_LT; ADD_CLAUSES]]);;

(* ------------------------------------------------------------------------- *)
(* RejNTTPoly (FIPS 204 Algorithm 30) and ExpandA (Algorithm 32). Candidate  *)
(* k of mld_rej_uniform_c is the 23-bit number of FIPS 204, so when the      *)
(* SHAKE128 output has 256 acceptable candidates the coefficients of         *)
(* mld_rej_uniform_poly are those of RejNTTPoly, and they are < q. The entry *)
(* (i,j) of the matrix of mld_polyvec_matrix_expand, the polynomial          *)
(* l * i + j, is that of A^ for rho || j || i, so ExpandA gives the inverse  *)
(* NTT of the C-level matrix entries. That needs k, l <= 256, so that i and  *)
(* j are bytes and the seed has 34 bytes.                                    *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SAMPLE_REJ_UNIFORM_CAND = prove
 (`!(b:num->byte) k.
        val(mld_rej_uniform_cand b k) =
        val(b(3 * k)) + 256 * val(b(3 * k + 1)) +
        65536 * (val(b(3 * k + 2)) MOD 128)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_rej_uniform_cand] THEN
  MAP_EVERY (fun (t,v) -> SPEC_TAC(t,v))
   [`(b:num->byte)(3 * k + 2)`,`x2:byte`;
    `(b:num->byte)(3 * k + 1)`,`x1:byte`;
    `(b:num->byte)(3 * k)`,`x0:byte`] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `8388607 = 2 EXP 23 - 1`; VAL_WORD_AND_MASK_WORD] THEN
  MP_TAC(WORD_BLAST
   `word_and (word_or (word_zx (x0:byte)) (word_shl (word_zx (x1:byte)) 8))
             (word_shl (word_zx (x2:byte)) 16):int32 = word 0 /\
    word_and (word_zx x0) (word_shl (word_zx x1) 8):int32 = word 0`) THEN
  SIMP_TAC[VAL_WORD_OR_DISJOINT] THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[VAL_WORD_SHL; VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32] THEN
  MAP_EVERY (fun x -> MP_TAC(ISPEC x VAL_BOUND))
   [`x0:byte`; `x1:byte`; `x2:byte`] THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(x2:byte)`,`v2:num`) THEN SPEC_TAC(`val(x1:byte)`,`v1:num`) THEN
  SPEC_TAC(`val(x0:byte)`,`v0:num`) THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `v < 256 ==> v < 4294967296`;
               ARITH_RULE `v < 256 ==> 256 * v < 4294967296`;
               ARITH_RULE `v < 256 ==> 65536 * v < 4294967296`] THEN
  MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `v2 DIV 128` THEN
  MP_TAC(SPECL [`v2:num`; `128`] DIVISION) THEN ASM_ARITH_TAC);;

let MLD_FIPS204_REJ_UNIFORM_POLY = prove
 (`!rho i.
        mld_rej_uniform_terminates (shake128 rho) /\ i < 256
        ==> &(val(mld_rej_uniform_poly (shake128 rho) i)) =
            mldsa_rej_ntt_poly rho i /\
            ival(mld_rej_uniform_poly (shake128 rho) i) =
            mldsa_rej_ntt_poly rho i /\
            mldsa_rej_ntt_poly rho i < &8380417`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `&(val(mld_rej_uniform_poly (shake128 rho) i)) = mldsa_rej_ntt_poly rho i /\
    val(mld_rej_uniform_poly (shake128 rho) i) < 8380417`
  MP_TAC THENL
   [REWRITE_TAC[mldsa_rej_ntt_poly] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    UNDISCH_TAC `mld_rej_uniform_terminates (shake128 rho)` THEN
    SPEC_TAC(`shake128 rho`,`s:num->byte`) THEN GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[mld_rej_uniform_poly] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MLD_REJ_UNIFORM_TERMINATES) THEN
    REWRITE_TAC[mld_rej_uniform_list] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\t:int32. val t < 8380417`; `mld_rej_uniform_cand s`;
                   `280 + 56 * mld_poly_uniform_nblocks s`; `i:num`]
           MLD_FIPS204_SAMPLE_EL_FILTER) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
    REWRITE_TAC[MLD_FIPS204_SAMPLE_REJ_UNIFORM_CAND] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LT] THEN MATCH_MP_TAC IVAL_EQ_VAL THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;

let MLD_FIPS204_POLY_UNIFORM = prove
 (`!seed i.
        seed < 2 EXP (8 * 34) /\
        mld_rej_uniform_terminates (mld_shake128_stream 34 seed) /\ i < 256
        ==> &(val(mld_poly_uniform seed i)) =
            mldsa_rej_ntt_poly (bytelist_of_num 34 seed) i /\
            ival(mld_poly_uniform seed i) =
            mldsa_rej_ntt_poly (bytelist_of_num 34 seed) i /\
            mldsa_rej_ntt_poly (bytelist_of_num 34 seed) i < &8380417`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
   RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP MLD_FIPS204_SHAKE128_STREAM th]) THEN
   REWRITE_TAC[mld_poly_uniform; MATCH_MP MLD_FIPS204_SHAKE128_STREAM th]) THEN
  MATCH_MP_TAC MLD_FIPS204_REJ_UNIFORM_POLY THEN ASM_REWRITE_TAC[]);;

let MLD_FIPS204_MATRIX_EXPAND = prove
 (`!k l rho i j n.
        mld_matrix_terminates k l rho /\ rho < 2 EXP 256 /\
        k <= 256 /\ l <= 256 /\ i < k /\ j < l /\ n < 256
        ==> &(val(mld_polyvec_matrix_expand l rho (256 * (l * i + j) + n))) =
            mldsa_rej_ntt_poly
             (APPEND (bytelist_of_num 32 rho) [word j; word i]) n /\
            ival(mld_polyvec_matrix_expand l rho (256 * (l * i + j) + n)) =
            mldsa_rej_ntt_poly
             (APPEND (bytelist_of_num 32 rho) [word j; word i]) n /\
            mldsa_rej_ntt_poly
             (APPEND (bytelist_of_num 32 rho) [word j; word i]) n
            < &8380417`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MLD_POLYVEC_MATRIX_EXPAND_COEFF] THEN
  SUBGOAL_THEN `~(l = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(l * i + j) DIV l = i /\ (l * i + j) MOD l = j`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; DIV_LT; MOD_LT; ADD_CLAUSES];
    ALL_TAC] THEN
  MP_TAC(SPECL [`rho:num`; `i:num`; `j:num`] MLD_FIPS204_MATRIX_SEED) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MATCH_MP_TAC MLD_FIPS204_POLY_UNIFORM THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[mld_matrix_terminates]) THEN
  ASM_REWRITE_TAC[]);;

let MLD_FIPS204_EXPAND_A = prove
 (`!k l rho i j.
        mld_matrix_terminates k l rho /\ rho < 2 EXP 256 /\
        k <= 256 /\ l <= 256 /\ i < k /\ j < l
        ==> mldsa_expand_a (bytelist_of_num 32 rho) i j =
            mldsa_ntt_inv
             (\n. &(val(mld_polyvec_matrix_expand l rho
                         (256 * (l * i + j) + n)))) /\
            !n. n < 256
                ==> mldsa_ntt (mldsa_expand_a (bytelist_of_num 32 rho) i j) n =
                    &(val(mld_polyvec_matrix_expand l rho
                           (256 * (l * i + j) + n)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[mldsa_expand_a] THEN
  SUBGOAL_THEN
   `!n. n < 256
        ==> &(val(mld_polyvec_matrix_expand l rho (256 * (l * i + j) + n))) =
            mldsa_rej_ntt_poly
             (APPEND (bytelist_of_num 32 rho) [word j; word i]) n /\
            mldsa_rej_ntt_poly
             (APPEND (bytelist_of_num 32 rho) [word j; word i]) n
            < &8380417`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`k:num`; `l:num`; `rho:num`; `i:num`; `j:num`; `n:num`]
      MLD_FIPS204_MATRIX_EXPAND) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MLDSA_NTT_INV_EQ THEN ASM_SIMP_TAC[];
    MP_TAC(ISPEC
     `mldsa_rej_ntt_poly (APPEND (bytelist_of_num 32 rho) [word j; word i])`
     MLDSA_NTT_INV) THEN
    ASM_SIMP_TAC[MLDSA_REJ_NTT_POLY_POS]]);;

(* ------------------------------------------------------------------------- *)
(* RejBoundedPoly (FIPS 204 Algorithm 31) and the samplers of s1 and s2: the *)
(* candidates of mld_rej_eta_c are the nibbles of FIPS 204, accepted and     *)
(* mapped to [-eta,eta] in the same way, so when the SHAKE256 output has 256 *)
(* acceptable nibbles the integer coefficients of mld_rej_eta_poly are those *)
(* of RejBoundedPoly, and in [-eta,eta]. Both the C code and FIPS 204 treat  *)
(* any eta other than 2 as eta = 4, so this holds for all eta (with the      *)
(* bound 4 then). The 66-byte input of mld_poly_uniform_eta is seed ||       *)
(* nonce || 0, the 64-byte seed followed by the 2-byte encoding of the       *)
(* nonce.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SAMPLE_REJ_ETA_NIBBLE = prove
 (`!(b:num->byte) t.
        val(mld_rej_eta_nibble b t) =
        (val(b(t DIV 2)) DIV 16 EXP (t MOD 2)) MOD 16`,
  REPEAT GEN_TAC THEN DISJ_CASES_TAC(SPEC `t:num` EVEN_OR_ODD) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o
    REWRITE_RULE[EVEN_EXISTS; ODD_EXISTS]) THEN
  REWRITE_TAC[ADD1; MLD_REJ_ETA_NIBBLE_BYTE] THEN
  REWRITE_TAC[ARITH_RULE `(2 * m) DIV 2 = m /\ (2 * m + 1) DIV 2 = m`] THEN
  REWRITE_TAC[prove(`!m. (2 * m) MOD 2 = 0 /\ (2 * m + 1) MOD 2 = 1`,
    REWRITE_TAC[GSYM EVEN_MOD; GSYM ODD_MOD; EVEN_MULT; ODD_ADD; ODD_MULT;
                ARITH_EVEN; ARITH_ODD])] THEN
  MP_TAC(ISPEC `(b:num->byte) m` VAL_BOUND) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val((b:num->byte) m)`,`v:num`) THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[DIV_1; MOD_MOD_REFL] THEN
  (SUBGOAL_THEN `v MOD 16 < 16 /\ v DIV 16 < 16` MP_TAC THENL
    [SIMP_TAC[MOD_LT_EQ; RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
     SIMP_TAC[MOD_LT; ARITH_RULE `x < 16 ==> x < 4294967296`]]));;

let MLD_FIPS204_SAMPLE_REJ_ETA_COEFF = prove
 (`!eta (t:int32).
        mld_rej_eta_valid eta t
        ==> ival(mld_rej_eta_coeff eta t) =
            if eta = 2 then &2 - &(val t MOD 5) else &4 - &(val t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_rej_eta_valid] THEN
  MP_TAC(prove
   (`!n. n < (if eta = 2 then 15 else 9)
         ==> ival(mld_rej_eta_coeff eta (word n:int32)) =
             if eta = 2 then &2 - &(n MOD 5) else &4 - &n`,
    REWRITE_TAC[mld_rej_eta_coeff] THEN
    ASM_CASES_TAC `eta = 2` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC WORD_REDUCE_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV)) THEN
  DISCH_THEN(MP_TAC o SPEC `val(t:int32)`) THEN REWRITE_TAC[WORD_VAL]);;

let MLD_FIPS204_SAMPLE_REJ_ETA_COEFF_BOUND = prove
 (`!eta (t:int32).
        mld_rej_eta_valid eta t
        ==> abs(ival(mld_rej_eta_coeff eta t)) <= &(if eta = 2 then 2 else 4)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MLD_FIPS204_SAMPLE_REJ_ETA_COEFF] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[mld_rej_eta_valid]) THEN
  MP_TAC(SPECL [`val(t:int32)`; `5`] MOD_LT_EQ) THEN
  COND_CASES_TAC THEN REWRITE_TAC[ARITH_EQ; GSYM INT_OF_NUM_LT] THEN
  INT_ARITH_TAC);;

let MLD_FIPS204_REJ_ETA_POLY = prove
 (`!eta rho.
        mld_rej_eta_terminates eta (shake256 rho)
        ==> mldsa_poly (\i. ival(mld_rej_eta_poly eta (shake256 rho) i)) =
            mldsa_rej_bounded_poly eta rho`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mldsa_rej_bounded_poly] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SPEC_TAC(`shake256 rho`,`s:num->byte`) THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC MLD_FIPS204_SAMPLE_MLDSA_POLY_EQ THEN X_GEN_TAC `i:num` THEN
  DISCH_TAC THEN REWRITE_TAC[mld_rej_eta_poly] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MLD_REJ_ETA_TERMINATES) THEN
  REWRITE_TAC[mld_rej_eta_list; LENGTH_MAP] THEN
  ABBREV_TAC `N = 2 * 136 * ((if eta = 2 then 1 else 2) +
                             mld_poly_uniform_eta_nblocks eta s)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `i < LENGTH(FILTER (mld_rej_eta_valid eta)
                            (list_of_seq (mld_rej_eta_nibble s) N))`
  ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MAP] THEN
  MP_TAC(ISPECL [`mld_rej_eta_valid eta`; `mld_rej_eta_nibble s`; `N:num`;
                 `i:num`] MLD_FIPS204_SAMPLE_EL_FILTER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  ASM_SIMP_TAC[MLD_FIPS204_SAMPLE_REJ_ETA_COEFF] THEN
  REWRITE_TAC[mld_rej_eta_valid; MLD_FIPS204_SAMPLE_REJ_ETA_NIBBLE] THEN
  ASM_CASES_TAC `eta = 2` THEN ASM_REWRITE_TAC[]);;

let MLD_FIPS204_REJ_ETA_POLY_BOUND = prove
 (`!eta (s:num->byte) i.
        mld_rej_eta_terminates eta s /\ i < 256
        ==> abs(ival(mld_rej_eta_poly eta s i)) <=
            &(if eta = 2 then 2 else 4)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_rej_eta_poly] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MLD_REJ_ETA_TERMINATES) THEN
  REWRITE_TAC[mld_rej_eta_list; LENGTH_MAP] THEN
  ABBREV_TAC `N = 2 * 136 * ((if eta = 2 then 1 else 2) +
                             mld_poly_uniform_eta_nblocks eta s)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `i < LENGTH(FILTER (mld_rej_eta_valid eta)
                            (list_of_seq (mld_rej_eta_nibble s) N))`
  ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_MAP] THEN
  MATCH_MP_TAC MLD_FIPS204_SAMPLE_REJ_ETA_COEFF_BOUND THEN
  MP_TAC(ISPECL [`mld_rej_eta_valid eta`; `mld_rej_eta_nibble s`; `N:num`;
                 `i:num`] MLD_FIPS204_SAMPLE_EL_FILTER) THEN
  ASM_SIMP_TAC[]);;

let MLD_FIPS204_POLY_UNIFORM_ETA = prove
 (`!eta seed nonce.
        seed < 2 EXP 512 /\
        mld_rej_eta_terminates eta
         (mld_shake256_stream 66 (seed + 2 EXP 512 * val nonce))
        ==> mldsa_poly (\i. ival(mld_poly_uniform_eta eta seed nonce i)) =
            mldsa_rej_bounded_poly eta
             (APPEND (bytelist_of_num 64 seed)
                     (bytelist_of_num 2 (val nonce)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`seed:num`; `val(nonce:byte)`] MLD_FIPS204_SEED_NONCE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `nonce:byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> let e = MATCH_MP MLD_FIPS204_SHAKE256_STREAM th in
              RULE_ASSUM_TAC(REWRITE_RULE[e]) THEN
              REWRITE_TAC[mld_poly_uniform_eta; e])
   (SUBST1_TAC o SYM)) THEN
  MATCH_MP_TAC MLD_FIPS204_REJ_ETA_POLY THEN ASM_REWRITE_TAC[]);;

let MLD_FIPS204_POLY_UNIFORM_ETA_BOUND = prove
 (`!eta seed nonce i.
        mld_rej_eta_terminates eta
         (mld_shake256_stream 66 (seed + 2 EXP 512 * val nonce)) /\
        i < 256
        ==> abs(ival(mld_poly_uniform_eta eta seed nonce i)) <=
            &(if eta = 2 then 2 else 4)`,
  REWRITE_TAC[mld_poly_uniform_eta; MLD_FIPS204_REJ_ETA_POLY_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* ExpandMask (FIPS 204 Algorithm 34) for gamma1 = 2^17 and 2^19: the        *)
(* unpacking of mld_polyz_unpack_17 and mld_polyz_unpack_19 gives gamma1     *)
(* minus the fields of 18 and 20 bits of the first 576 and 640 bytes of the  *)
(* buffer (proved bit by bit), so the polynomials of mld_poly_uniform_gamma1 *)
(* are those of ExpandMask for any counter kappa + r with that 16-bit nonce. *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SAMPLE_DIV_MOD_8 = prove
 (`!a n. (8 * a + n) DIV 8 = a + n DIV 8 /\ (8 * a + n) MOD 8 = n MOD 8`,
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_EQ]);;

let MLD_FIPS204_SAMPLE_BIT_BYTE = prove
 (`!(x:byte) i. 8 <= i ==> (bit i x <=> F)`,
  SIMP_TAC[BIT_TRIVIAL; DIMINDEX_8]);;

(* The bits of the 32-bit words of the unpacking, for each case r of the     *)
(* coefficient index and each bit t.                                         *)

let MLD_FIPS204_SAMPLE_BITS_TAC =
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[BIT_WORD_AND; BIT_WORD_OR; BIT_WORD_USHR; BIT_WORD_SHL;
              BIT_WORD_ZX; BIT_WORD; DIMINDEX_32; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MLD_FIPS204_SAMPLE_BIT_BYTE; ARITH_LE; ARITH_LT; ADD_CLAUSES];;

let MLD_FIPS204_SAMPLE_POLYZ_UNPACK_17 = prove
 (`!(b:num->byte) i.
        i < 256
        ==> ival(mld_polyz_unpack_17 b i) =
            &131072 - mldsa_field 18 (list_of_seq b 576) i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyz_unpack_17; mldsa_field] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN `18 * i = 8 * (9 * i DIV 4) + 18 * i MOD 4` SUBST1_TAC THENL
   [MP_TAC(SPECL [`i:num`; `4`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i DIV 4 < 64 /\ i MOD 4 < 4` MP_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; MOD_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`i MOD 4`,`r:num`) THEN SPEC_TAC(`i DIV 4`,`q:num`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  W(fun (asl,w) -> ABBREV_TAC (mk_eq(`X:int32`, rand(rand(lhand w))))) THEN
  ABBREV_TAC `zz = (num_of_bytelist (list_of_seq (b:num->byte) 576) DIV
                    2 EXP (8 * 9 * q + 18 * r)) MOD 2 EXP 18` THEN
  SUBGOAL_THEN `zz < 262144` ASSUME_TAC THENL
   [EXPAND_TAC "zz" THEN
    REWRITE_TAC[ARITH_RULE `262144 = 2 EXP 18`; MOD_LT_EQ; EXP_EQ_0;
                ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(X:int32) = zz` ASSUME_TAC THENL
   [MATCH_MP_TAC MLD_FIPS204_SAMPLE_VAL_BITS THEN REWRITE_TAC[DIMINDEX_32] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "zz" THEN
    REWRITE_TAC[MLD_FIPS204_SAMPLE_ODD_DIV_MOD; DIV_DIV; GSYM EXP_ADD;
                MLD_FIPS204_SAMPLE_ODD_LIST; GSYM ADD_ASSOC;
                MLD_FIPS204_SAMPLE_DIV_MOD_8] THEN
    SUBGOAL_THEN
     `!t B. (t < 18 /\ 8 * 9 * q + 18 * r + t < 8 * 576 /\ B) <=>
            t < 18 /\ B`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN ASM_CASES_TAC `t < 18` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `p ==> (p /\ q <=> q)`) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "X" THEN UNDISCH_TAC `r < 4` THEN SPEC_TAC(`r:num`,`r:num`) THEN
    MLD_FIPS204_SAMPLE_BITS_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`131072`; `X:int32`] MLD_FIPS204_SAMPLE_IVAL_SUB) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]);;

let MLD_FIPS204_SAMPLE_POLYZ_UNPACK_19 = prove
 (`!(b:num->byte) i.
        i < 256
        ==> ival(mld_polyz_unpack_19 b i) =
            &524288 - mldsa_field 20 (list_of_seq b 640) i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mld_polyz_unpack_19; mldsa_field] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN `20 * i = 8 * (5 * i DIV 2) + 20 * i MOD 2` SUBST1_TAC THENL
   [MP_TAC(SPECL [`i:num`; `2`] DIVISION) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i DIV 2 < 128 /\ i MOD 2 < 2` MP_TAC THENL
   [SIMP_TAC[RDIV_LT_EQ; MOD_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`i MOD 2`,`r:num`) THEN SPEC_TAC(`i DIV 2`,`q:num`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  W(fun (asl,w) -> ABBREV_TAC (mk_eq(`X:int32`, rand(rand(lhand w))))) THEN
  ABBREV_TAC `zz = (num_of_bytelist (list_of_seq (b:num->byte) 640) DIV
                    2 EXP (8 * 5 * q + 20 * r)) MOD 2 EXP 20` THEN
  SUBGOAL_THEN `zz < 1048576` ASSUME_TAC THENL
   [EXPAND_TAC "zz" THEN
    REWRITE_TAC[ARITH_RULE `1048576 = 2 EXP 20`; MOD_LT_EQ; EXP_EQ_0;
                ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(X:int32) = zz` ASSUME_TAC THENL
   [MATCH_MP_TAC MLD_FIPS204_SAMPLE_VAL_BITS THEN REWRITE_TAC[DIMINDEX_32] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "zz" THEN
    REWRITE_TAC[MLD_FIPS204_SAMPLE_ODD_DIV_MOD; DIV_DIV; GSYM EXP_ADD;
                MLD_FIPS204_SAMPLE_ODD_LIST; GSYM ADD_ASSOC;
                MLD_FIPS204_SAMPLE_DIV_MOD_8] THEN
    SUBGOAL_THEN
     `!t B. (t < 20 /\ 8 * 5 * q + 20 * r + t < 8 * 640 /\ B) <=>
            t < 20 /\ B`
     (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT GEN_TAC THEN ASM_CASES_TAC `t < 20` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `p ==> (p /\ q <=> q)`) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "X" THEN UNDISCH_TAC `r < 2` THEN SPEC_TAC(`r:num`,`r:num`) THEN
    MLD_FIPS204_SAMPLE_BITS_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`524288`; `X:int32`] MLD_FIPS204_SAMPLE_IVAL_SUB) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]);;

let MLD_FIPS204_POLY_UNIFORM_GAMMA1_17 = prove
 (`!seed nonce kappa r.
        seed < 2 EXP 512 /\ val nonce = (kappa + r) MOD 65536
        ==> mldsa_poly (\i. ival(mld_poly_uniform_gamma1_17 seed nonce i)) =
            mldsa_expand_mask 131072 (bytelist_of_num 64 seed) kappa r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mldsa_expand_mask; mldsa_h] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MLDSA_BITLEN_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `bytelist_of_num 2 (kappa + r) = bytelist_of_num 2 (val(nonce:int16))`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM BYTELIST_OF_NUM_MOD] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`seed:num`; `val(nonce:int16)`] MLD_FIPS204_SEED_NONCE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `nonce:int16` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_16] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> REWRITE_TAC[mld_poly_uniform_gamma1_17;
                          MATCH_MP MLD_FIPS204_SHAKE256_STREAM th])
   (SUBST1_TAC o SYM)) THEN
  MATCH_MP_TAC MLD_FIPS204_SAMPLE_MLDSA_POLY_EQ THEN
  SIMP_TAC[MLD_FIPS204_SAMPLE_POLYZ_UNPACK_17]);;

let MLD_FIPS204_POLY_UNIFORM_GAMMA1_19 = prove
 (`!seed nonce kappa r.
        seed < 2 EXP 512 /\ val nonce = (kappa + r) MOD 65536
        ==> mldsa_poly (\i. ival(mld_poly_uniform_gamma1_19 seed nonce i)) =
            mldsa_expand_mask 524288 (bytelist_of_num 64 seed) kappa r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mldsa_expand_mask; mldsa_h] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MLDSA_BITLEN_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `bytelist_of_num 2 (kappa + r) = bytelist_of_num 2 (val(nonce:int16))`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM BYTELIST_OF_NUM_MOD] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`seed:num`; `val(nonce:int16)`] MLD_FIPS204_SEED_NONCE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `nonce:int16` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_16] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> REWRITE_TAC[mld_poly_uniform_gamma1_19;
                          MATCH_MP MLD_FIPS204_SHAKE256_STREAM th])
   (SUBST1_TAC o SYM)) THEN
  MATCH_MP_TAC MLD_FIPS204_SAMPLE_MLDSA_POLY_EQ THEN
  SIMP_TAC[MLD_FIPS204_SAMPLE_POLYZ_UNPACK_19]);;

(* ------------------------------------------------------------------------- *)
(* SampleInBall (FIPS 204 Algorithm 29), for any tau: after any number n of  *)
(* bytes from position 8, the integer coefficients of the C-level state are  *)
(* mldsa_ball_coeffs after its number k of steps, the byte of the last step  *)
(* is before position 8 + n, and the bytes after it up to there were         *)
(* rejected; so the byte accepted at step k is at mldsa_ball_pos k, and the  *)
(* C loop reads the bytes up to that of the last step, mldsa_ball_pos (tau - *)
(* 1). The sign bits agree for every k (both are 0 for k >= 64). So when the *)
(* C loop terminates, mld_poly_challenge is SampleInBall of the seed.        *)
(* ------------------------------------------------------------------------- *)

let MLD_FIPS204_SAMPLE_CHALLENGE_SIGN = prove
 (`!(s:num->byte) k.
        ival(mld_poly_challenge_sign s k) =
        if ODD(num_of_bytelist(list_of_seq s 8) DIV 2 EXP k) then -- &1
        else &1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_poly_challenge_sign; mld_poly_challenge_signs; BIT_WORD;
              DIMINDEX_64] THEN
  SUBGOAL_THEN
   `k < 64 /\ ODD(num_of_bytelist(list_of_seq (s:num->byte) 8) DIV 2 EXP k) <=>
    ODD(num_of_bytelist(list_of_seq s 8) DIV 2 EXP k)`
  SUBST1_TAC THENL
   [ASM_CASES_TAC `k < 64` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `num_of_bytelist(list_of_seq (s:num->byte) 8) DIV 2 EXP k = 0`
     (fun th -> REWRITE_TAC[th; ODD]) THEN
    MATCH_MP_TAC DIV_LT THEN
    MP_TAC(ISPEC `list_of_seq (s:num->byte) 8` NUM_OF_BYTELIST_BOUND) THEN
    REWRITE_TAC[LENGTH_LIST_OF_SEQ] THEN
    MATCH_MP_TAC(ARITH_RULE `b <= c ==> x < b ==> x < c`) THEN
    SUBGOAL_THEN `256 EXP 8 = 2 EXP 64` SUBST1_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
    REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
    COND_CASES_TAC THEN CONV_TAC WORD_REDUCE_CONV]);;

let MLD_FIPS204_SAMPLE_BALL_POS = prove
 (`!tau (s:num->byte) k p.
        (if k = 0 then 8 <= p else mldsa_ball_pos tau s (k - 1) < p) /\
        val(s p) <= 256 - tau + k /\
        (!p'. p' < p /\
              (if k = 0 then 8 <= p' else mldsa_ball_pos tau s (k - 1) < p')
              ==> 256 - tau + k < val(s p'))
        ==> mldsa_ball_pos tau s k = p`,
  GEN_TAC THEN GEN_TAC THEN X_GEN_TAC `k:num` THEN
  STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN
  REWRITE_TAC[mldsa_ball_pos; NOT_SUC; SUC_SUB1; ADD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MINIMAL_UNIQUE THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  ASM_MESON_TAC[NOT_LE]);;

let MLD_FIPS204_POLY_CHALLENGE_STEP = prove
 (`!tau (s:num->byte) n.
        FST(mld_poly_challenge_step tau s n) <= tau /\
        (!t. ival(SND(mld_poly_challenge_step tau s n) t) =
             mldsa_ball_coeffs tau s (FST(mld_poly_challenge_step tau s n))
              t) /\
        (0 < FST(mld_poly_challenge_step tau s n)
         ==> mldsa_ball_pos tau s (FST(mld_poly_challenge_step tau s n) - 1)
             < 8 + n) /\
        (FST(mld_poly_challenge_step tau s n) < tau
         ==> !p. p < 8 + n /\
                 (if FST(mld_poly_challenge_step tau s n) = 0 then 8 <= p
                  else mldsa_ball_pos tau s
                        (FST(mld_poly_challenge_step tau s n) - 1) < p)
                 ==> 256 - tau + FST(mld_poly_challenge_step tau s n)
                     < val(s p))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[mld_poly_challenge_step; mldsa_ball_coeffs; LE_0; LT_REFL] THEN
    CONV_TAC WORD_REDUCE_CONV THEN ARITH_TAC;
    POP_ASSUM MP_TAC] THEN
  REWRITE_TAC[mld_poly_challenge_step; mld_poly_challenge_next] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SPEC_TAC(`mld_poly_challenge_step tau s n`,`kc:num#(num->int32)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `c:num->int32`] THEN
  REWRITE_TAC[] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `mldsa_ball_pos tau s k = 8 + n` ASSUME_TAC THENL
     [MATCH_MP_TAC MLD_FIPS204_SAMPLE_BALL_POS THEN ASM_SIMP_TAC[] THEN
      COND_CASES_TAC THEN
      ASM_SIMP_TAC[LE_ADD; ARITH_RULE `~(k = 0) ==> 0 < k`];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM ADD1; mldsa_ball_coeffs; NOT_SUC; SUC_SUB1] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      X_GEN_TAC `t:num` THEN
      REPEAT(COND_CASES_TAC THEN
             ASM_REWRITE_TAC[MLD_FIPS204_SAMPLE_CHALLENGE_SIGN]);
      ARITH_TAC;
      REPEAT STRIP_TAC THEN ASM_ARITH_TAC];
    CONJ_TAC THENL
     [ASM_MESON_TAC[ARITH_RULE `a < 8 + n ==> a < 8 + SUC n`];
      DISCH_TAC THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
      ASM_CASES_TAC `p = 8 + n` THENL
       [UNDISCH_TAC
         `~(k < tau /\ val((s:num->byte) (8 + n)) <= 256 - tau + k)` THEN
        ASM_REWRITE_TAC[NOT_LE];
        ASM_MESON_TAC[ARITH_RULE
         `p < 8 + SUC n /\ ~(p = 8 + n) ==> p < 8 + n`]]]]);;

let MLD_FIPS204_SAMPLE_CHALLENGE_STEP_FST = prove
 (`!tau (s:num->byte) n.
        FST(mld_poly_challenge_step tau s (SUC n)) =
        if mld_poly_challenge_accept tau s n
        then FST(mld_poly_challenge_step tau s n) + 1
        else FST(mld_poly_challenge_step tau s n)`,
  REWRITE_TAC[mld_poly_challenge_step; mld_poly_challenge_next;
              mld_poly_challenge_accept] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let MLD_FIPS204_POLY_CHALLENGE_ACCEPT = prove
 (`!tau (s:num->byte) n.
        mld_poly_challenge_accept tau s n
        ==> mldsa_ball_pos tau s (FST(mld_poly_challenge_step tau s n)) =
            8 + n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mld_poly_challenge_accept] THEN
  MP_TAC(SPECL [`tau:num`; `s:num->byte`; `n:num`]
    MLD_FIPS204_POLY_CHALLENGE_STEP) THEN
  SPEC_TAC(`FST(mld_poly_challenge_step tau (s:num->byte) n)`,`k:num`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MLD_FIPS204_SAMPLE_BALL_POS THEN
  ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[LE_ADD; ARITH_RULE `~(k = 0) ==> 0 < k`]);;

let MLD_FIPS204_POLY_CHALLENGE_BYTES = prove
 (`!tau (s:num->byte).
        0 < tau /\ (?n. FST(mld_poly_challenge_step tau s n) = tau)
        ==> mld_poly_challenge_bytes tau s + 7 =
            mldsa_ball_pos tau s (tau - 1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[mld_poly_challenge_bytes] THEN
  DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [MINIMAL]) THEN
  SPEC_TAC(`minimal n. FST(mld_poly_challenge_step tau (s:num->byte) n) = tau`,
           `N:num`) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[mld_poly_challenge_step] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_ARITH_TAC;
    POP_ASSUM(K ALL_TAC)] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (MP_TAC o SPEC `N:num`)) THEN
  REWRITE_TAC[ARITH_RULE `N < SUC N`;
              MLD_FIPS204_SAMPLE_CHALLENGE_STEP_FST] THEN
  COND_CASES_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MLD_FIPS204_POLY_CHALLENGE_ACCEPT) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `tau - 1 = FST(mld_poly_challenge_step tau (s:num->byte) N)`
  SUBST1_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let MLD_FIPS204_POLY_CHALLENGE_COEFFS = prove
 (`!tau ctlen c.
        c < 2 EXP (8 * ctlen) /\ mld_poly_challenge_terminates tau ctlen c
        ==> !t. ival(mld_poly_challenge tau ctlen c t) =
                mldsa_ball_coeffs tau (shake256 (bytelist_of_num ctlen c))
                 tau t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_poly_challenge_terminates; mld_poly_challenge;
              mld_poly_challenge_bytes] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (ASSUME_TAC o MATCH_MP MLD_FIPS204_SHAKE256_BYTE) MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`shake256(bytelist_of_num ctlen c)`,`s:num->byte`) THEN
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [MINIMAL]) THEN
  SPEC_TAC(`minimal n. FST(mld_poly_challenge_step tau (s:num->byte) n) = tau`,
           `N:num`) THEN
  MESON_TAC[MLD_FIPS204_POLY_CHALLENGE_STEP]);;

let MLD_FIPS204_POLY_CHALLENGE = prove
 (`!tau ctlen c.
        c < 2 EXP (8 * ctlen) /\ mld_poly_challenge_terminates tau ctlen c
        ==> mldsa_poly (\i. ival(mld_poly_challenge tau ctlen c i)) =
            mldsa_sample_in_ball tau (bytelist_of_num ctlen c)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP MLD_FIPS204_POLY_CHALLENGE_COEFFS) THEN
  ASM_REWRITE_TAC[mldsa_sample_in_ball; ETA_AX]);;

(* Restore the default setting for anything loaded later.                    *)

type_invention_error := false;;
