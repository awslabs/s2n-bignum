(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "common/fips203/properties/input_checks.ml";;
needs "common/fips202/properties/keccak_permutation.ml";;

(* ------------------------------------------------------------------------- *)
(* sample_ok b: the SHAKE128 stream of b has at least 256 12-bit values below *)
(* q, so that SampleNTT of b is determined. SAMPLE_OK_ALL below shows that it *)
(* holds for every 34-byte input, which is the form of all inputs of          *)
(* SampleNTT in ML-KEM (a 32-byte seed followed by two index bytes).          *)
(* ------------------------------------------------------------------------- *)

let sample_ok = new_definition
 `sample_ok (b:byte list) <=>
    ?N. 256 <= CARD {j | j < N /\ mlkem_xof_field (mlkem_xof b) j < 3329}`;;

(* ========================================================================= *)
(* Termination of SampleNTT: sample_ok holds for every 34-byte input.        *)
(*                                                                           *)
(* Argument of Barbosa and Schwabe, "Kyber terminates" (ePrint 2023/708).    *)
(* The padded input of SHAKE128 is one 168-byte block, so the sponge state   *)
(* after absorbing is keccak_f1600 B with B the block as a state. As         *)
(* keccak_f1600 is injective on a finite type, B is periodic: some m > 0     *)
(* has keccak_f1600^m B = B. Whenever the squeeze reaches B, the output     *)
(* block is the padded input again; its bytes 35..166 are 0, which makes a   *)
(* 12-bit field of the XOF stream equal to 0 < 3329. This happens in every   *)
(* m-th block, giving unboundedly many accepted fields.                      *)
(* ========================================================================= *)

let TERMINATE_SQUEEZE_ADD = prove
 (`!a b s. keccak_squeeze (a + b) s =
           keccak_squeeze a (keccak_squeeze b s)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; keccak_squeeze]);;

let TERMINATE_SQUEEZE_INJ = prove
 (`!t s u. keccak_squeeze t s = keccak_squeeze t u ==> s = u`,
  INDUCT_TAC THENL
   [REWRITE_TAC[keccak_squeeze];
    REWRITE_TAC[keccak_squeeze] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC KECCAK_F1600_INJ THEN ASM_REWRITE_TAC[]]);;

let TERMINATE_FINITE_WORD = prove
 (`FINITE (:N word)`,
  SUBGOAL_THEN
   `(:N word) = IMAGE (word:num->N word) {n | n < 2 EXP dimindex(:N)}`
   SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `w:N word` THEN EXISTS_TAC `val(w:N word)` THEN
    REWRITE_TAC[WORD_VAL; VAL_BOUND];
    MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG_LT]]);;

let TERMINATE_PERIOD = prove
 (`!x:1600 word. ?m. 0 < m /\ keccak_squeeze m x = x`,
  GEN_TAC THEN
  ASM_CASES_TAC `?m. 0 < m /\ keccak_squeeze m x = (x:1600 word)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!i d. 0 < d ==> ~(keccak_squeeze i x = keccak_squeeze (d + i) x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`i:num`; `x:1600 word`;
                  `keccak_squeeze d x:1600 word`] TERMINATE_SQUEEZE_INJ) THEN
    ASM_REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] TERMINATE_SQUEEZE_ADD] THEN
    DISCH_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. keccak_squeeze i x = keccak_squeeze j x ==> i = j`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM LE_ANTISYM] THEN
    CONJ_TAC THEN GEN_REWRITE_TAC I [GSYM NOT_LT] THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `i - j`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(i - j) + j = i` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j - i`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(j - i) + i = j` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {n | keccak_squeeze n (x:1600 word) IN (:1600 word)}`
  MP_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN REWRITE_TAC[TERMINATE_FINITE_WORD] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIV] THEN
  SUBGOAL_THEN `{n | T} = (:num)` SUBST1_TAC THENL
   [SET_TAC[]; REWRITE_TAC[GSYM INFINITE; num_INFINITE]]);;

let TERMINATE_MULT = prove
 (`!m x. keccak_squeeze m x = x ==> !u. keccak_squeeze (m * u) x = x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; TERMINATE_SQUEEZE_ADD; keccak_squeeze]);;

let terminate_init = new_definition
 `terminate_init (b:byte list) =
    word (num_of_bytelist (APPEND b (keccak_pad 168 0x1F 34))):1600 word`;;

let TERMINATE_PAD = prove
 (`keccak_pad 168 0x1F 34 =
   CONS (word 31) (APPEND (REPLICATE 132 (word 0)) [word 128])`,
  REWRITE_TAC[keccak_pad] THEN CONV_TAC NUM_REDUCE_CONV);;

let TERMINATE_NUM_BYTELIST_BYTE = prove
 (`!l k. k < LENGTH l
         ==> (num_of_bytelist l DIV 256 EXP k) MOD 256 = val (EL k l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH_RULE `~(k < 0)`] THEN
  INDUCT_TAC THEN REWRITE_TAC[num_of_bytelist; EL; HD; TL; EXP; DIV_1] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_MULT_ADD; MOD_LT];
    MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM DIV_DIV] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; DIV_LT; ARITH_EQ; ADD_CLAUSES] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let TERMINATE_LENGTH = prove
 (`!b. LENGTH b = 34 ==> LENGTH (APPEND b (keccak_pad 168 0x1F 34)) = 168`,
  SIMP_TAC[TERMINATE_PAD; LENGTH_APPEND; LENGTH; LENGTH_REPLICATE] THEN
  ARITH_TAC);;

let TERMINATE_INIT_BYTE = prove
 (`!b k. LENGTH b = 34 /\ k < 168
         ==> word_subword (terminate_init b) (8 * k,8):byte =
             EL k (APPEND b (keccak_pad 168 0x1F 34))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TERMINATE_LENGTH) THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; terminate_init; VAL_WORD; DIMINDEX_8;
              DIMINDEX_CONV `dimindex(:1600)`] THEN
  SUBGOAL_THEN
   `num_of_bytelist (APPEND b (keccak_pad 168 0x1F 34)) MOD 2 EXP 1600 =
    num_of_bytelist (APPEND b (keccak_pad 168 0x1F 34))` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN
    MP_TAC(SPEC `APPEND b (keccak_pad 168 0x1F 34)` NUM_OF_BYTELIST_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXP_MULT; ARITH_RULE `MIN 8 8 = 8`] THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  MATCH_MP_TAC TERMINATE_NUM_BYTELIST_BYTE THEN ASM_REWRITE_TAC[]);;

let TERMINATE_EL_REPLICATE = prove
 (`!n k (x:A). k < n ==> EL k (REPLICATE n x) = x`,
  INDUCT_TAC THEN REWRITE_TAC[REPLICATE; ARITH_RULE `~(k < 0)`] THEN
  INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; LT_SUC] THEN
  ASM_SIMP_TAC[]);;

let TERMINATE_ZERO = prove
 (`!b k. LENGTH b = 34 /\ 35 <= k /\ k < 167
         ==> EL k (APPEND b (keccak_pad 168 0x1F 34)) = word 0`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[TERMINATE_PAD; EL_APPEND] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k - 34 = SUC(k - 35)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[EL; HD; TL; EL_APPEND; LENGTH_REPLICATE]] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC TERMINATE_EL_REPLICATE THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let TERMINATE_ABSORB = prove
 (`!b. LENGTH b = 34
       ==> keccak_absorb 168
             (num_of_bytelist (APPEND b (keccak_pad 168 0x1F 34))) 1 =
           keccak_f1600 (terminate_init b)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ONE; keccak_absorb; terminate_init] THEN
  AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[WORD_XOR_0; DIV_1] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPEC `APPEND b (keccak_pad 168 0x1F 34)` NUM_OF_BYTELIST_BOUND) THEN
  ASM_SIMP_TAC[TERMINATE_LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let TERMINATE_STREAM = prove
 (`!b i. LENGTH b = 34
         ==> mlkem_xof b i =
             word_subword (keccak_squeeze (i DIV 168)
                            (keccak_f1600 (terminate_init b)))
                          (8 * (i MOD 168),8)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[mlkem_xof; shake128; keccak_sponge] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
  ASM_SIMP_TAC[TERMINATE_LENGTH; TERMINATE_ABSORB] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[TERMINATE_ABSORB]);;

let TERMINATE_BYTE_ZERO = prove
 (`!b blk k.
     LENGTH b = 34 /\ 35 <= k /\ k < 167 /\
     keccak_squeeze blk (keccak_f1600 (terminate_init b)) = terminate_init b
     ==> mlkem_xof b (168 * blk + k) = word 0`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[TERMINATE_STREAM] THEN
  SUBGOAL_THEN `(168 * blk + k) DIV 168 = blk /\ (168 * blk + k) MOD 168 = k`
   (fun th -> ASM_REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC DIVMOD_UNIQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[TERMINATE_INIT_BYTE; TERMINATE_ZERO;
               ARITH_RULE `k < 167 ==> k < 168`]);;

let TERMINATE_FIELD = prove
 (`!b blk.
     LENGTH b = 34 /\
     keccak_squeeze blk (keccak_f1600 (terminate_init b)) = terminate_init b
     ==> mlkem_xof_field (mlkem_xof b) (112 * blk + 50) = 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mlkem_xof_field] THEN
  MATCH_MP_TAC NSUM_EQ_0 THEN X_GEN_TAC `t:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(12 * (112 * blk + 50) + t) DIV 8 = 168 * blk + (75 + t DIV 8)`
  SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mlkem_xof b (168 * blk + (75 + t DIV 8)) = word 0:byte`
  SUBST1_TAC THENL
   [MATCH_MP_TAC TERMINATE_BYTE_ZERO THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[BIT_WORD_0; BITVAL_CLAUSES; MULT_CLAUSES]]);;

let SAMPLE_OK_ALL = prove(`!(b:byte list). LENGTH b = 34 ==> sample_ok b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sample_ok] THEN
  MP_TAC(SPEC `terminate_init b` TERMINATE_PERIOD) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?n. m = n + 1` (X_CHOOSE_TAC `n:num`) THENL
   [EXISTS_TAC `m - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  (* Block n + m * u of the stream starts from the initial state again. *)
  SUBGOAL_THEN
   `!u. keccak_squeeze (n + m * u) (keccak_f1600 (terminate_init b)) =
        terminate_init b`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(SPECL [`n + m * u`; `1`; `terminate_init b`]
                 TERMINATE_SQUEEZE_ADD) THEN
    REWRITE_TAC[ONE; keccak_squeeze] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `(n + m * u) + SUC 0 = m * SUC u` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[TERMINATE_MULT];
    ALL_TAC] THEN
  ABBREV_TAC `NN = 112 * (m * 256)` THEN
  ABBREV_TAC `g = \u:num. 112 * (n + m * u) + 50` THEN
  SUBGOAL_THEN
   `!x y. x IN {u | u < 256} /\ y IN {u | u < 256} /\
          (g:num->num) x = g y ==> x = y`
  ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o CONV_RULE(DEPTH_CONV BETA_CONV)) THEN
    REWRITE_TAC[EQ_ADD_RCANCEL; EQ_ADD_LCANCEL; EQ_MULT_LCANCEL;
                ARITH_EQ] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD (IMAGE (g:num->num) {u | u < 256}) = 256` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:num->num`; `{u | u < 256}`] CARD_IMAGE_INJ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FINITE_NUMSEG_LT];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CARD_NUMSEG_LT]];
    ALL_TAC] THEN
  EXISTS_TAC `NN:num` THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD (IMAGE (g:num->num) {u | u < 256})` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN
    DISCH_THEN(X_CHOOSE_THEN `u:num` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "g" THEN EXPAND_TAC "NN" THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `m * u <= m * 255` MP_TAC THENL
       [REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      ASM_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "g" THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `mlkem_xof_field (mlkem_xof b) (112 * (n + m * u) + 50) = 0`
      SUBST1_TAC THENL
       [MATCH_MP_TAC TERMINATE_FIELD THEN ASM_REWRITE_TAC[];
        ARITH_TAC]];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j | j < NN}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Counting accepted positions: if i < CARD {j | j < N /\ P j}, then some    *)
(* j < N has P j and exactly i accepted positions below it. Hence, if        *)
(* sample_ok b, every entry of mlkem_sample_ntt b lies in [0, q).            *)
(* ------------------------------------------------------------------------- *)

let SAMPLE_CARD_FINITE = prove
 (`!(P:num->bool) n. FINITE {j | j < n /\ P j}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{j:num | j < n}` THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  SET_TAC[]);;

let SAMPLE_CARD_SUC = prove
 (`!(P:num->bool) n.
     CARD {j | j < SUC n /\ P j} =
     CARD {j | j < n /\ P j} + (if P n then 1 else 0)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `{j | j < SUC n /\ P j} = n INSERT {j | j < n /\ P j}`
     SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM; LT] THEN
      ASM_MESON_TAC[];
      SIMP_TAC[CARD_CLAUSES; SAMPLE_CARD_FINITE; IN_ELIM_THM; LT_REFL] THEN
      ARITH_TAC];
    REWRITE_TAC[ADD_CLAUSES] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; LT] THEN ASM_MESON_TAC[]]);;

let SAMPLE_CARD_EXISTS = prove
 (`!(P:num->bool) N i.
     i < CARD {j | j < N /\ P j}
     ==> ?j. j < N /\ P j /\ CARD {j' | j' < j /\ P j'} = i`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LT; EMPTY_GSPEC; CARD_CLAUSES];
    REWRITE_TAC[SAMPLE_CARD_SUC] THEN GEN_TAC THEN
    ASM_CASES_TAC `i < CARD {j | j < N /\ (P:num->bool) j}` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[LT];
      COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
      EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[LT] THEN ASM_ARITH_TAC]]);;

let SAMPLE_OK_BOUND = prove
 (`!b. sample_ok b
       ==> !n. n < 256
               ==> &0 <= mlkem_sample_ntt b n /\ mlkem_sample_ntt b n < &3329`,
  REWRITE_TAC[sample_ok; mlkem_sample_ntt] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[INT_POS] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[INT_OF_NUM_LT] THEN
  ABBREV_TAC `c = mlkem_xof_field (mlkem_xof b)` THEN
  MP_TAC(ISPECL [`\j. (c:num->num) j < 3329`; `N:num`; `n:num`]
    SAMPLE_CARD_EXISTS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SELECT_RULE o
    MATCH_MP(MESON[] `(?j. j < N /\ P j) ==> (?j. P j)`)) THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* sample_ok holds for the 34-byte seeds of ML-KEM (32 bytes followed by     *)
(* two index bytes) when the 32 bytes are a slice of a byte string or        *)
(* the first half of G(c).                                                   *)
(* ------------------------------------------------------------------------- *)

let SAMPLE_OK_SLICE = prove
 (`!a (y:byte list) i j.
     sample_ok (APPEND (mlkem_slice a 32 y) [word j:byte; word i])`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SAMPLE_OK_ALL THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_MLKEM_SLICE; LENGTH] THEN ARITH_TAC);;

let SAMPLE_OK_G = prove
 (`!c i j.
     sample_ok (APPEND (FST (mlkem_g c)) [word j:byte; word i])`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SAMPLE_OK_ALL THEN
  REWRITE_TAC[mlkem_g; LENGTH_APPEND; LENGTH_MLKEM_SLICE; LENGTH] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* XOF fields 2t and 2t+1 come from bytes 3t, 3t+1 and 3t+2.                 *)
(* ------------------------------------------------------------------------- *)

let SAMPLE_DIV_MOD_8 = prove
 (`!a u. (8 * a + u) DIV 8 = a + u DIV 8 /\ (8 * a + u) MOD 8 = u MOD 8`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_EQ]);;

let SAMPLE_VAL_BYTE = prove
 (`!w:byte. val w =
      bitval(bit 0 w) + 2 * bitval(bit 1 w) + 4 * bitval(bit 2 w) +
      8 * bitval(bit 3 w) + 16 * bitval(bit 4 w) + 32 * bitval(bit 5 w) +
      64 * bitval(bit 6 w) + 128 * bitval(bit 7 w)`,
  GEN_TAC THEN REWRITE_TAC[VAL; DIMINDEX_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_SUB_CONV) THEN
  CONV_TAC(LAND_CONV EXPAND_NSUM_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let SAMPLE_VAL_BYTE_MOD_16 = prove
 (`!w:byte. val w MOD 16 =
      bitval(bit 0 w) + 2 * bitval(bit 1 w) + 4 * bitval(bit 2 w) +
      8 * bitval(bit 3 w)`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `16 = 2 EXP 4`; VAL_MOD] THEN
  REWRITE_TAC[NUMSEG_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV EXPAND_NSUM_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let SAMPLE_VAL_BYTE_DIV_16 = prove
 (`!w:byte. val w DIV 16 =
      bitval(bit 4 w) + 2 * bitval(bit 5 w) + 4 * bitval(bit 6 w) +
      8 * bitval(bit 7 w)`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `16 = 2 EXP 4`; VAL_DIV; DIMINDEX_8] THEN
  SUBGOAL_THEN `{i | 4 <= i /\ i < 8} = 4..7` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV EXPAND_NSUM_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let SAMPLE_XOF_FIELD_EVEN = prove
 (`!s t. mlkem_xof_field s (2 * t) =
         val(s(3 * t):byte) + 256 * (val(s(3 * t + 1):byte) MOD 16)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mlkem_xof_field; SAMPLE_VAL_BYTE; SAMPLE_VAL_BYTE_MOD_16;
    ARITH_RULE `12 * 2 * t + u = 8 * 3 * t + u`; SAMPLE_DIV_MOD_8] THEN
  REWRITE_TAC[NUMSEG_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV EXPAND_NSUM_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ADD_CLAUSES] THEN ARITH_TAC);;

let SAMPLE_XOF_FIELD_ODD = prove
 (`!s t. mlkem_xof_field s (2 * t + 1) =
         val(s(3 * t + 1):byte) DIV 16 + 16 * val(s(3 * t + 2):byte)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mlkem_xof_field; SAMPLE_VAL_BYTE; SAMPLE_VAL_BYTE_DIV_16;
    ARITH_RULE `12 * (2 * t + 1) + u = 8 * (3 * t + 1) + 4 + u`] THEN
  REWRITE_TAC[NUMSEG_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV EXPAND_NSUM_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SAMPLE_DIV_MOD_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `(3 * t + 1) + 1 = 3 * t + 2`] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* mlkem_prf eta s b has 64 * eta bytes, and coefficient n of                *)
(* mlkem_cbd eta b is the difference of the sums of the bits at              *)
(* positions 2 * eta * n + j and 2 * eta * n + eta + j, 0 <= j < eta,        *)
(* reduced mod q.                                                            *)
(* ------------------------------------------------------------------------- *)

let KPKE_LENGTH_PRF = prove
 (`!eta s b. LENGTH (mlkem_prf eta s b) = 64 * eta`,
  REWRITE_TAC[mlkem_prf; LENGTH_LIST_OF_SEQ]);;

let RQ_CBD_COEFF = prove
 (`!eta b n. n < 256
   ==> coeff n (mlkem_cbd eta b) =
       (&(nsum {j | j < eta}
            (\j. (num_of_bytelist b DIV 2 EXP (2 * eta * n + j)) MOD 2)) -
        &(nsum {j | j < eta}
            (\j. (num_of_bytelist b DIV 2 EXP (2 * eta * n + eta + j)) MOD 2)))
       rem &3329`,
  REWRITE_TAC[mlkem_cbd] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP_TAC[COEFF_MLKEM_POLY]);;
