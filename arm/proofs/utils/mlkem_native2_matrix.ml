(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of mlkem_gen_matrix: SampleNTT (FIPS 203, Algorithm  *)
(* 7) as the rejection sampling of the 12-bit fields of whole blocks of      *)
(* SHAKE128 output, mlkem_rej_uniform_alt_VARIABLE_TIME in the forms that    *)
(* the sampling of a matrix polynomial needs, the seed of a matrix           *)
(* polynomial as the state of a Keccak lane, the sponge by blocks for the    *)
(* hash jobs, and memory lemmas for the copies of the job structures and the *)
(* digests.                                                                  *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native2_noise.ml";;
needs "arm/proofs/utils/mlkem_native_fips203.ml";;
needs "arm/proofs/mlkem_rej_uniform_alt_VARIABLE_TIME.ml";;

(* ------------------------------------------------------------------------- *)
(* SampleNTT as the first 256 accepted 12-bit fields (those < q) of the      *)
(* first N fields of the XOF stream, when at least 256 of them are accepted, *)
(* and the fields of a later block as fields of the stream (with the fields  *)
(* of the bytes of a stream and the filters of list_of_seq of                *)
(* arm/proofs/utils/mlkem_native_fips203.ml).                                *)
(* ------------------------------------------------------------------------- *)

let CARD_RESTRICT_LT = prove
 (`!(P:num->bool) j1 j2.
        P j1 /\ j1 < j2
        ==> CARD {i | i < j1 /\ P i} < CARD {i | i < j2 /\ P i}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_PSUBSET THEN
  REWRITE_TAC[FINITE_LT_RESTRICT; PSUBSET; SUBSET; IN_ELIM_THM;
              EXTENSION] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[LT_TRANS];
    DISCH_THEN(MP_TAC o SPEC `j1:num`) THEN ASM_REWRITE_TAC[LT_REFL]]);;

let CARD_RESTRICT_UNIQUE = prove
 (`!(P:num->bool) j1 j2.
        P j1 /\ P j2 /\
        CARD {i | i < j1 /\ P i} = CARD {i | i < j2 /\ P i}
        ==> j1 = j2`,
  REPEAT STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (ARITH_RULE `j1 < j2 \/ j2 < j1 \/ j1 = j2:num`) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CARD_RESTRICT_LT; LT_REFL]);;

let LIST_OF_SEQ_APPEND_ADD = prove
 (`!(f:num->A) m n.
        list_of_seq f (m + n) =
        APPEND (list_of_seq f m) (list_of_seq (\i. f(m + i)) n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; list_of_seq; APPEND_NIL; APPEND_ASSOC]);;

let FILTER_REJ_FIELDS = prove
 (`!(s:num->byte) N.
        FILTER (\x:int16. val x < 3329)
         (list_of_seq (\j. word(mlkem_xof_field s j)) N) =
        MAP word (FILTER (\x. x < 3329) (list_of_seq (mlkem_xof_field s) N))`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[list_of_seq; FILTER; MAP; FILTER_APPEND; MAP_APPEND] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`s:num->byte`; `N:num`] MLKEM_XOF_FIELD_BOUND) THEN
  SIMP_TAC[VAL_WORD; DIMINDEX_16; MOD_LT;
           ARITH_RULE `x < 4096 ==> x < 2 EXP 16`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[MAP]);;

let REJ_SAMPLE_NTT = prove
 (`!b N M t.
        12 * N <= 8 * M /\
        256 <= CARD {j | j < N /\ mlkem_xof_field (shake128 b) j < 3329} /\
        t < 256
        ==> EL t (SUB_LIST(0,256)
                   (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                       (wordlist_of_num N
                         (num_of_bytelist(list_of_seq (shake128 b) M)))))) =
            iword(mlkem_sample_ntt b t)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REJ_FIELDS_LIST; FILTER_REJ_FIELDS] THEN
  ABBREV_TAC `c = mlkem_xof_field (shake128 b)` THEN
  MP_TAC(ISPECL [`\x:num. x < 3329`; `c:num->num`; `N:num`; `t:num`]
    EL_FILTER_LIST_OF_SEQ) THEN
  REWRITE_TAC[LENGTH_FILTER_LIST_OF_SEQ] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_SUB_LIST_GEN o lhand o snd) THEN
  REWRITE_TAC[LENGTH_MAP; LENGTH_FILTER_LIST_OF_SEQ; ADD_CLAUSES] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[EL_MAP; LENGTH_FILTER_LIST_OF_SEQ;
               ARITH_RULE `t < 256 /\ 256 <= n ==> t < n`] THEN
  REWRITE_TAC[mlkem_sample_ntt; mlkem_xof] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM WORD_IWORD] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `j':num` THEN BETA_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`\x:num. (c:num->num) x < 3329`; `j':num`; `j:num`]
      CARD_RESTRICT_UNIQUE) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let MLKEM_XOF_FIELD_SHIFT = prove
 (`!(s:num->byte) m j.
        mlkem_xof_field (\i. s(168 * m + i)) j =
        mlkem_xof_field s (112 * m + j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlkem_xof_field] THEN
  MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `t:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE
   `12 * (112 * m + j) + t = (12 * j + t) + (168 * m) * 8`] THEN
  SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ] THEN
  REWRITE_TAC[ADD_SYM]);;

(* ------------------------------------------------------------------------- *)
(* The result of the rejection sampling of the first m blocks of 168 bytes,  *)
(* mlkem_rej_out b m, its extension by one block, and the number of blocks   *)
(* needed, mlkem_rej_blocks b (at least the three that the code always       *)
(* takes), for a seed b for which SampleNTT terminates                       *)
(* (mlkem_samplentt_terminates, as in the statements of the API).            *)
(* ------------------------------------------------------------------------- *)

let mlkem_rej_out = new_definition
 `mlkem_rej_out (b:byte list) m =
    SUB_LIST(0,256)
     (FILTER (\x:int16. val x < 3329)
       (list_of_seq (\j. word(mlkem_xof_field (shake128 b) j)) (112 * m)))`;;

let MLKEM_REJ_OUT_BUF = prove
 (`!b. SUB_LIST(0,256)
        (APPEND []
          (FILTER (\x. val x < 3329)
            (MAP (word_zx:12 word->16 word)
              (wordlist_of_num 336
                (num_of_bytelist(list_of_seq (shake128 b) 504)))))) =
       mlkem_rej_out b 3`,
  GEN_TAC THEN REWRITE_TAC[APPEND; mlkem_rej_out] THEN
  SIMP_TAC[REJ_FIELDS_LIST; ARITH_RULE `12 * 336 <= 8 * 504`] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MLKEM_REJ_OUT_BLOCK = prove
 (`!b m. SUB_LIST(0,256)
          (APPEND (mlkem_rej_out b m)
            (FILTER (\x. val x < 3329)
              (MAP (word_zx:12 word->16 word)
                (wordlist_of_num 112
                  (num_of_bytelist
                    (list_of_seq (\j. shake128 b (168 * m + j)) 168)))))) =
         mlkem_rej_out b (m + 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mlkem_rej_out] THEN
  REWRITE_TAC[SUB_LIST_0_APPEND_SUB_LIST] THEN
  SIMP_TAC[REJ_FIELDS_LIST; ARITH_RULE `12 * 112 <= 8 * 168`] THEN
  REWRITE_TAC[MLKEM_XOF_FIELD_SHIFT; GSYM FILTER_APPEND] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; LIST_OF_SEQ_APPEND_ADD]);;

let mlkem_rej_blocks = new_definition
 `mlkem_rej_blocks (b:byte list) =
    minimal m. 3 <= m /\
               256 <= CARD {j | j < 112 * m /\
                                mlkem_xof_field (shake128 b) j < 3329}`;;

let MLKEM_REJ_BLOCKS = prove
 (`!b. mlkem_samplentt_terminates b
       ==> 3 <= mlkem_rej_blocks b /\
           256 <= CARD {j | j < 112 * mlkem_rej_blocks b /\
                            mlkem_xof_field (shake128 b) j < 3329} /\
           !m. m < mlkem_rej_blocks b /\ 3 <= m
               ==> CARD {j | j < 112 * m /\
                             mlkem_xof_field (shake128 b) j < 3329} < 256`,
  GEN_TAC THEN REWRITE_TAC[mlkem_samplentt_terminates; mlkem_xof] THEN
  DISCH_THEN(X_CHOOSE_TAC `J:num`) THEN REWRITE_TAC[mlkem_rej_blocks] THEN
  MP_TAC(ISPEC
   `\m. 3 <= m /\
        256 <= CARD {j | j < 112 * m /\ mlkem_xof_field (shake128 b) j < 3329}`
   MINIMAL) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [EXISTS_TAC `J + 3` THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    TRANS_TAC LE_TRANS
     `CARD {j | j < J /\ mlkem_xof_field (shake128 b) j < 3329}` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_LT_RESTRICT_MONO THEN ARITH_TAC;
    MESON_TAC[NOT_LE]]);;

let LENGTH_MLKEM_REJ_OUT = prove
 (`!b m. LENGTH(mlkem_rej_out b m) =
         MIN 256 (CARD {j | j < 112 * m /\
                            mlkem_xof_field (shake128 b) j < 3329})`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mlkem_rej_out; LENGTH_SUB_LIST; SUB_0;
              LENGTH_FILTER_LIST_OF_SEQ] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `j:num` THEN
  MP_TAC(SPECL [`shake128 b`; `j:num`] MLKEM_XOF_FIELD_BOUND) THEN
  SIMP_TAC[VAL_WORD; DIMINDEX_16; MOD_LT;
           ARITH_RULE `x < 4096 ==> x < 2 EXP 16`]);;

let LENGTH_MLKEM_REJ_OUT_LE = prove
 (`!b m. LENGTH(mlkem_rej_out b m) <= 256`,
  REWRITE_TAC[LENGTH_MLKEM_REJ_OUT] THEN ARITH_TAC);;

let LENGTH_MLKEM_REJ_OUT_LT = prove
 (`!b m. mlkem_samplentt_terminates b /\ 3 <= m /\ m < mlkem_rej_blocks b
         ==> LENGTH(mlkem_rej_out b m) < 256`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MLKEM_REJ_BLOCKS) THEN
  REWRITE_TAC[LENGTH_MLKEM_REJ_OUT] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let LENGTH_MLKEM_REJ_OUT_BLOCKS = prove
 (`!b. mlkem_samplentt_terminates b
       ==> LENGTH(mlkem_rej_out b (mlkem_rej_blocks b)) = 256`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MLKEM_REJ_BLOCKS) THEN
  REWRITE_TAC[LENGTH_MLKEM_REJ_OUT] THEN ASM_ARITH_TAC);;

let MLKEM_REJ_OUT_SAMPLE_NTT = prove
 (`!b m t.
        256 <= CARD {j | j < 112 * m /\
                         mlkem_xof_field (shake128 b) j < 3329} /\
        t < 256
        ==> EL t (mlkem_rej_out b m) = iword(mlkem_sample_ntt b t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`b:byte list`; `112 * m`; `168 * m`; `t:num`]
    REJ_SAMPLE_NTT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `12 * 112 * m <= 8 * 168 * m`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[mlkem_rej_out] THEN
  SIMP_TAC[REJ_FIELDS_LIST; ARITH_RULE `12 * 112 * m <= 8 * 168 * m`]);;

(* ------------------------------------------------------------------------- *)
(* mlkem_rej_uniform_alt_VARIABLE_TIME with its lists as bytes in memory, on *)
(* the three blocks in a buffer with no entries yet and on one more block    *)
(* with the entries so far, with the results as mlkem_rej_out; and the       *)
(* coefficients of SampleNTT from the 256 entries.                           *)
(* ------------------------------------------------------------------------- *)

let WORDLIST_FROM_MEMORY_BYTES16_NUM = prove
 (`!a (l:int16 list) s:armstate.
        wordlist_from_memory(a,LENGTH l) s = l
        ==> read (memory :> bytes(a,2 * LENGTH l)) s = num_of_wordlist l`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `LENGTH(l:int16 list)`; `2 * LENGTH(l:int16 list)`;
                 `l:int16 list`; `s:armstate`]
    (INST_TYPE [`:16`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH_RULE `16 * n = 8 * 2 * n`] THEN
  SIMP_TAC[]);;

let LENGTH_MLKEM_REJ_UNIFORM_TABLE = prove
 (`LENGTH mlkem_rej_uniform_table = 4096`,
  REWRITE_TAC[mlkem_rej_uniform_table] THEN
  CONV_TAC(LAND_CONV LENGTH_CONV) THEN
  REFL_TAC);;

let MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_CORRECT_BYTES = prove
 (`!res n buf buflen table curlist (inlist:(12 word)list) pc stackpointer
    returnaddress.
      aligned 16 stackpointer /\
      24 divides val buflen /\
      8 * val buflen = 12 * LENGTH inlist /\
      LENGTH curlist = val n /\ val n <= 256 /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x3d4); (word_sub stackpointer (word 48),48);
           (buf,val buflen); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 48),48))
          [(word pc,0x3d4); (buf,val buflen); (table,4096)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [res; n; buf; buflen; table] s /\
                read (memory :> bytes(table,4096)) s =
                num_of_wordlist mlkem_rej_uniform_table /\
                read (memory :> bytes(buf,val buflen)) s =
                num_of_wordlist inlist /\
                read (memory :> bytes(res,2 * val n)) s =
                num_of_wordlist curlist)
           (\s. read PC s = returnaddress /\
                C_RETURN s =
                word(LENGTH(SUB_LIST (0,256)
                  (APPEND curlist (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word) inlist))))) /\
                read (memory :> bytes(res,2 * LENGTH(SUB_LIST (0,256)
                  (APPEND curlist (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word) inlist)))))) s =
                num_of_wordlist(SUB_LIST (0,256)
                  (APPEND curlist (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word) inlist)))))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`res:int64`; `n:int64`; `buf:int64`; `buflen:int64`;
                `table:int64`; `curlist:int16 list`; `inlist:(12 word)list`;
                `pc:num`; `stackpointer:int64`; `returnaddress:int64`]
         MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_CORRECT) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPECL [`table:int64`; `4096`; `4096`; `mlkem_rej_uniform_table`]
    (INST_TYPE [`:8`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  REWRITE_TAC[DIMINDEX_8; LENGTH_MLKEM_REJ_UNIFORM_TABLE] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`buf:int64`; `LENGTH(inlist:(12 word)list)`;
                 `val(buflen:int64)`; `inlist:(12 word)list`]
    (INST_TYPE [`:12`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  ASM_REWRITE_TAC[DIMINDEX_CONV `dimindex(:12)`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`res:int64`; `val(n:int64)`; `2 * val(n:int64)`;
                 `curlist:int16 list`]
    (INST_TYPE [`:16`,`:N`] WORDLIST_FROM_MEMORY_EQ_ALT)) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH_RULE `16 * n = 8 * 2 * n`] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_POSTCONDITION_THM) THEN
  REWRITE_TAC[] THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match []
    `wordlist_from_memory(a,n) s = l`) o concl)) THEN
  MATCH_ACCEPT_TAC WORDLIST_FROM_MEMORY_BYTES16_NUM);;

let NUM_OF_WORDLIST_OF_NUM_BYTES = prove
 (`!(l:byte list) n.
        8 * LENGTH l = 12 * n
        ==> num_of_wordlist(wordlist_of_num n (num_of_bytelist l):
                            (12 word)list) =
            num_of_bytelist l`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NUM_OF_WORDLIST_OF_NUM; DIMINDEX_CONV `dimindex(:12)`] THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `l:byte list` NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; EXP_EXP] THEN
  ASM_REWRITE_TAC[]);;

let MLKEM_REJ_UNIFORM_BUF = prove
 (`!res buf table (l:byte list) pc stackpointer returnaddress.
      LENGTH l = 504 /\ aligned 16 stackpointer /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x3d4); (word_sub stackpointer (word 48),48);
           (buf,504); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 48),48))
          [(word pc,0x3d4); (buf,504); (table,4096)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [res; word 0; buf; word 504; table] s /\
                read (memory :> bytes(table,4096)) s =
                num_of_wordlist mlkem_rej_uniform_table /\
                read (memory :> bytes(buf,504)) s = num_of_bytelist l)
           (\s. read PC s = returnaddress /\
                C_RETURN s =
                word(LENGTH(SUB_LIST (0,256)
                  (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                      (wordlist_of_num 336 (num_of_bytelist l)))))) /\
                read (memory :> bytes(res,2 * LENGTH(SUB_LIST (0,256)
                  (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                      (wordlist_of_num 336 (num_of_bytelist l))))))) s =
                num_of_wordlist(SUB_LIST (0,256)
                  (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                      (wordlist_of_num 336 (num_of_bytelist l))))))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`res:int64`; `word 0:int64`; `buf:int64`; `word 504:int64`;
                 `table:int64`; `[]:int16 list`;
                 `wordlist_of_num 336 (num_of_bytelist(l:byte list)):
                  (12 word)list`;
                 `pc:num`; `stackpointer:int64`; `returnaddress:int64`]
         MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_CORRECT_BYTES) THEN
  ASM_REWRITE_TAC[LENGTH_WORDLIST_OF_NUM; LENGTH; APPEND] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[NUM_OF_WORDLIST_OF_NUM_BYTES;
               ARITH_RULE `8 * 504 = 12 * 336`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL; num_of_wordlist] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE]);;

let MLKEM_REJ_UNIFORM_BLOCK = prove
 (`!res buf table (curlist:int16 list) (l:byte list) pc stackpointer
    returnaddress.
      LENGTH l = 168 /\ LENGTH curlist <= 256 /\ aligned 16 stackpointer /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x3d4); (word_sub stackpointer (word 48),48);
           (buf,168); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 48),48))
          [(word pc,0x3d4); (buf,168); (table,4096)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [res; word(LENGTH curlist); buf; word 168;
                             table] s /\
                read (memory :> bytes(table,4096)) s =
                num_of_wordlist mlkem_rej_uniform_table /\
                read (memory :> bytes(buf,168)) s = num_of_bytelist l /\
                read (memory :> bytes(res,2 * LENGTH curlist)) s =
                num_of_wordlist curlist)
           (\s. read PC s = returnaddress /\
                C_RETURN s =
                word(LENGTH(SUB_LIST (0,256)
                  (APPEND curlist (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                      (wordlist_of_num 112 (num_of_bytelist l))))))) /\
                read (memory :> bytes(res,2 * LENGTH(SUB_LIST (0,256)
                  (APPEND curlist (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                      (wordlist_of_num 112 (num_of_bytelist l)))))))) s =
                num_of_wordlist(SUB_LIST (0,256)
                  (APPEND curlist (FILTER (\x. val x < 3329)
                     (MAP (word_zx:12 word->16 word)
                      (wordlist_of_num 112 (num_of_bytelist l)))))))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`res:int64`; `word(LENGTH(curlist:int16 list)):int64`;
                 `buf:int64`; `word 168:int64`;
                 `table:int64`; `curlist:int16 list`;
                 `wordlist_of_num 112 (num_of_bytelist(l:byte list)):
                  (12 word)list`;
                 `pc:num`; `stackpointer:int64`; `returnaddress:int64`]
         MLKEM_REJ_UNIFORM_ALT_SUBROUTINE_CORRECT_BYTES) THEN
  SUBGOAL_THEN `val(word(LENGTH(curlist:int16 list)):int64) = LENGTH curlist`
  SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    UNDISCH_TAC `LENGTH(curlist:int16 list) <= 256` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[LENGTH_WORDLIST_OF_NUM] THEN
  CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[NUM_OF_WORDLIST_OF_NUM_BYTES;
               ARITH_RULE `8 * 168 = 12 * 112`]);;

let MLKEM_REJ_UNIFORM_BUF_OUT = prove
 (`!res buf table b pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x3d4); (word_sub stackpointer (word 48),48);
           (buf,504); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 48),48))
          [(word pc,0x3d4); (buf,504); (table,4096)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [res; word 0; buf; word 504; table] s /\
                read (memory :> bytes(table,4096)) s =
                num_of_wordlist mlkem_rej_uniform_table /\
                read (memory :> bytes(buf,504)) s =
                num_of_bytelist(list_of_seq (shake128 b) 504))
           (\s. read PC s = returnaddress /\
                C_RETURN s = word(LENGTH(mlkem_rej_out b 3)) /\
                read (memory :> bytes(res,2 * LENGTH(mlkem_rej_out b 3))) s =
                num_of_wordlist(mlkem_rej_out b 3))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `table:int64`;
                `list_of_seq (shake128 b) 504`; `pc:num`;
                `stackpointer:int64`; `returnaddress:int64`]
         MLKEM_REJ_UNIFORM_BUF) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ; GSYM MLKEM_REJ_OUT_BUF; APPEND]);;

let MLKEM_REJ_UNIFORM_BLOCK_OUT = prove
 (`!res buf table b m pc stackpointer returnaddress.
      aligned 16 stackpointer /\
      ALL (nonoverlapping (res,512))
          [(word pc,0x3d4); (word_sub stackpointer (word 48),48);
           (buf,168); (table,4096)] /\
      ALL (nonoverlapping (word_sub stackpointer (word 48),48))
          [(word pc,0x3d4); (buf,168); (table,4096)]
      ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) mlkem_rej_uniform_alt_mc /\
                read PC s = word pc /\
                read SP s = stackpointer /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [res; word(LENGTH(mlkem_rej_out b m)); buf;
                             word 168; table] s /\
                read (memory :> bytes(table,4096)) s =
                num_of_wordlist mlkem_rej_uniform_table /\
                read (memory :> bytes(buf,168)) s =
                num_of_bytelist
                 (list_of_seq (\j. shake128 b (168 * m + j)) 168) /\
                read (memory :> bytes(res,2 * LENGTH(mlkem_rej_out b m))) s =
                num_of_wordlist(mlkem_rej_out b m))
           (\s. read PC s = returnaddress /\
                C_RETURN s = word(LENGTH(mlkem_rej_out b (m + 1))) /\
                read (memory :> bytes(res,2 * LENGTH(mlkem_rej_out b (m + 1))))
                     s =
                num_of_wordlist(mlkem_rej_out b (m + 1)))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,512);
                       memory :> bytes(word_sub stackpointer (word 48),48)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`res:int64`; `buf:int64`; `table:int64`;
                `mlkem_rej_out b m`;
                `list_of_seq (\j. shake128 b (168 * m + j)) 168`; `pc:num`;
                `stackpointer:int64`; `returnaddress:int64`]
         MLKEM_REJ_UNIFORM_BLOCK) THEN
  ASM_REWRITE_TAC[LENGTH_LIST_OF_SEQ; LENGTH_MLKEM_REJ_OUT_LE;
                  MLKEM_REJ_OUT_BLOCK]);;

let READ_MEMORY_BYTES16_EL = prove
 (`!a (l:int16 list) t s:armstate.
        read (memory :> bytes(a,2 * LENGTH l)) s = num_of_wordlist l /\
        t < LENGTH l
        ==> read (memory :> bytes16(word_add a (word(2 * t)))) s = EL t l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int64`; `2 * LENGTH(l:int16 list)`;
                `num_of_wordlist(l:int16 list)`; `2 * t`; `s:armstate`]
         READ_MEMORY_BYTES16_OF_NUM) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[EL_NUM_OF_WORDLIST; DIMINDEX_16] THEN
  REWRITE_TAC[ARITH_RULE `8 * 2 * t = 16 * t`] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_16; MOD_MOD_REFL]);;

let SAMPLEPOLY_POST = prove
 (`!a e b s:armstate.
     mlkem_samplentt_terminates b /\
     read (memory :> bytes(word_add a (word(512 * e)),
                   2 * LENGTH(mlkem_rej_out b (mlkem_rej_blocks b)))) s =
     num_of_wordlist(mlkem_rej_out b (mlkem_rej_blocks b))
     ==> !t. t < 256
             ==> read (memory :> bytes16(word_add a
                                          (word(512 * e + 2 * t)))) s =
                 iword(mlkem_sample_ntt b t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MLKEM_REJ_BLOCKS) THEN
  MP_TAC(ISPECL [`word_add a (word(512 * e)):int64`;
                 `mlkem_rej_out b (mlkem_rej_blocks b)`; `t:num`; `s:armstate`]
    READ_MEMORY_BYTES16_EL) THEN
  ASM_SIMP_TAC[LENGTH_MLKEM_REJ_OUT_BLOCKS] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MLKEM_REJ_OUT_SAMPLE_NTT THEN
  ASM_REWRITE_TAC[]);;

let READ_MEMORY_BYTES_PREFIX = prove
 (`!a n m x s:armstate.
        read (memory :> bytes(a,n)) s = x /\ m <= n
        ==> read (memory :> bytes(a,m)) s = x MOD 2 EXP (8 * m)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_ARITH_TAC);;

let NONOVERLAPPING_SHORTER = prove
 (`!(a:int64) n n2 b m.
        nonoverlapping (a,n) (b,m) /\ n2 <= n ==> nonoverlapping (a,n2) (b,m)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NONOVERLAPPING_SUBREGIONS THEN
  MAP_EVERY EXISTS_TAC [`a:int64`; `n:num`; `b:int64`; `m:num`] THEN
  ASM_REWRITE_TAC[contained; contained_modulo] THEN CONJ_TAC THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN EXISTS_TAC `i:num` THEN
  REWRITE_TAC[NUMBER_RULE `(x:num == x) (mod n)`] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The seed rho || x || y of a matrix polynomial absorbed into a lane        *)
(* (mlkem_matrix_state, one block of SHAKE128 with its padding), the lane as *)
(* the code sets it up, and the three blocks squeezed from it, as copied to  *)
(* the buffer, as the first 504 bytes of the XOF.                            *)
(* ------------------------------------------------------------------------- *)

let mlkem_matrix_state = new_definition
 `mlkem_matrix_state (rho:byte list) (x:byte) (y:byte) =
    (word(num_of_bytelist rho + 2 EXP 256 * val x + 2 EXP 264 * val y +
          2 EXP 272 * 31 + 2 EXP 1343):1600 word)`;;

let MLKEM_MATRIX_ABSORB = prove
 (`!rho:byte list x y.
     LENGTH rho = 32
     ==> word_xor
          (keccak_absorb 168
            (num_of_bytelist(APPEND rho [x; y]) +
             2 EXP (8 * LENGTH(APPEND rho [x; y])) *
             num_of_bytelist(keccak_pad 168 31 (LENGTH(APPEND rho [x; y]))))
            (LENGTH(APPEND rho [x; y]) DIV 168))
          (word(((num_of_bytelist(APPEND rho [x; y]) +
                  2 EXP (8 * LENGTH(APPEND rho [x; y])) *
                  num_of_bytelist(keccak_pad 168 31
                                   (LENGTH(APPEND rho [x; y])))) DIV
                 2 EXP (8 * 168 * LENGTH(APPEND rho [x; y]) DIV 168)) MOD
                2 EXP (8 * 168))) =
         mlkem_matrix_state rho x y`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH; NUM_OF_BYTELIST_APPEND] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[KECCAK_PAD_NUM; ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[keccak_absorb; WORD_XOR_0; num_of_bytelist; DIV_1] THEN
  REWRITE_TAC[mlkem_matrix_state] THEN AP_TERM_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_ASSOC] THEN
  MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPEC `rho:byte list` NUM_OF_BYTELIST_BOUND) THEN
  MP_TAC(ISPEC `x:byte` VAL_BOUND) THEN MP_TAC(ISPEC `y:byte` VAL_BOUND) THEN
  ASM_REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ARITH_TAC);;

let mlkem_matrix_padded_tm =
  `num_of_bytelist(APPEND (rho:byte list) [x; y]) +
   2 EXP (8 * LENGTH(APPEND rho [x; y])) *
   num_of_bytelist(keccak_pad 168 31 (LENGTH(APPEND rho [x; y])))`;;

let MLKEM_MATRIX_SPONGE_BLOCK = prove
 (`!rho:byte list x y t.
     LENGTH rho = 32
     ==> num_of_bytelist
          (list_of_seq (\j. shake128(APPEND rho [x; y]) (168 * t + j)) 168) =
         val(keccak_squeeze (t + 1) (mlkem_matrix_state rho x y)) MOD
         2 EXP 1344`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[shake128] THEN
  MP_TAC(SPECL [`256`; `31`; `APPEND (rho:byte list) [x; y]`; `168`;
                mlkem_matrix_padded_tm; `t:num`; `168`]
               KECCAK_SPONGE_BLOCK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ASM_SIMP_TAC[MLKEM_MATRIX_ABSORB] THEN CONV_TAC NUM_REDUCE_CONV]);;

let MLKEM_MATRIX_LANE = prove
 (`!a (rho:byte list) x y s:armstate.
     LENGTH rho = 32 /\ x < 256 /\ y < 256 /\
     read (memory :> bytes128 a) s =
     word(num_of_bytelist rho MOD 2 EXP 128) /\
     read (memory :> bytes128 (word_add a (word 16))) s =
     word((num_of_bytelist rho DIV 2 EXP 128) MOD 2 EXP 128) /\
     read (memory :> bytes64 (word_add a (word 32))) s =
     word(x + 256 * y + 2031616) /\
     read (memory :> bytes64 (word_add a (word 40))) s = word 0 /\
     read (memory :> bytes128 (word_add a (word 48))) s = word 0 /\
     read (memory :> bytes128 (word_add a (word 64))) s = word 0 /\
     read (memory :> bytes128 (word_add a (word 80))) s = word 0 /\
     read (memory :> bytes128 (word_add a (word 96))) s = word 0 /\
     read (memory :> bytes128 (word_add a (word 112))) s = word 0 /\
     read (memory :> bytes128 (word_add a (word 128))) s = word 0 /\
     read (memory :> bytes128 (word_add a (word 144))) s = word 0 /\
     read (memory :> bytes64 (word_add a (word 160))) s =
     word 9223372036854775808 /\
     read (memory :> bytes64 (word_add a (word 168))) s = word 0 /\
     read (memory :> bytes64 (word_add a (word 176))) s = word 0 /\
     read (memory :> bytes64 (word_add a (word 184))) s = word 0 /\
     read (memory :> bytes64 (word_add a (word 192))) s = word 0
     ==> read (memory :> wbytes a) s =
         mlkem_matrix_state rho (word x) (word y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[READ_MEMORY_WBYTES_1600; mlkem_matrix_state] THEN
  CONV_TAC(LAND_CONV(BYTES_PIECES_CONV
   [16;16;8;8;16;16;16;16;16;16;16;8;8;8;8;8])) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD; VAL_WORD_0; DIMINDEX_64; DIMINDEX_128; DIMINDEX_8;
              DIMINDEX_CONV `dimindex(:1600)`; MOD_MOD_REFL] THEN
  MP_TAC(ISPEC `rho:byte list` NUM_OF_BYTELIST_BOUND) THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
    filter (fun th -> can (term_match [] `x < 256`) (concl th))) THEN
  SPEC_TAC(`num_of_bytelist(rho:byte list)`,`r:num`) THEN
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(r DIV 2 EXP 128) MOD 2 EXP 128 = r DIV 2 EXP 128 /\
    (x MOD 2 EXP 8) = x /\ (y MOD 2 EXP 8) = y /\
    (x + 256 * y + 2031616) MOD 2 EXP 64 = x + 256 * y + 2031616`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THENL
     [SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
      UNDISCH_TAC `r < 256 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN
      ARITH_TAC;
      ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o rand o snd) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `r < 256 EXP 32` THEN
    MAP_EVERY UNDISCH_TAC [`x < 256`; `y < 256`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`r:num`; `2 EXP 128`] DIVISION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let READ_MEMORY_BYTES_168_OF_PIECES = prove
 (`!a x s:armstate.
     (!j. j < 10 ==> read (memory :> bytes128(word_add a (word(16 * j)))) s =
                     word((x DIV 2 EXP (128 * j)) MOD 2 EXP 128)) /\
     read (memory :> bytes64(word_add a (word 160))) s =
     word((x DIV 2 EXP 1280) MOD 2 EXP 64)
     ==> read (memory :> bytes(a,168)) s = x MOD 2 EXP 1344`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `168 = 16 * 10 + 8`; READ_MEMORY_BYTES_SPLIT] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP READ_MEMORY_BYTES_OF_BYTES128) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[READ_MEMORY_BYTES_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_MOD_REFL] THEN
  CONV_TAC(DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[MOD_EXP_ADD_SPLIT] THEN CONV_TAC NUM_REDUCE_CONV);;

let MLKEM_MATRIX_BUFFER = prove
 (`!rho:byte list x y a s:armstate.
     LENGTH rho = 32 /\
     read (memory :> bytes(a,168)) s =
     val(keccak_squeeze 1 (mlkem_matrix_state rho x y)) MOD 2 EXP 1344 /\
     read (memory :> bytes(word_add a (word 168),168)) s =
     val(keccak_squeeze 2 (mlkem_matrix_state rho x y)) MOD 2 EXP 1344 /\
     read (memory :> bytes(word_add a (word 336),168)) s =
     val(keccak_squeeze 3 (mlkem_matrix_state rho x y)) MOD 2 EXP 1344
     ==> read (memory :> bytes(a,504)) s =
         num_of_bytelist(list_of_seq (shake128(APPEND rho [x; y])) 504)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `504 = 168 + 168 + 168`] THEN
  REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD; READ_MEMORY_BYTES_SPLIT] THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`rho:byte list`; `x:byte`; `y:byte`]
         MLKEM_MATRIX_SPONGE_BLOCK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `0`) THEN FIRST_ASSUM(MP_TAC o SPEC `1`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `2`) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[ADD_ASSOC; ETA_AX] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The sponge by blocks, for the hash jobs: block j of a padded message as a *)
(* 1600-bit word, keccak_absorb as the permutation of the state with each    *)
(* block XORed in, and the digests of SHA3-256 and of SHAKE256 to 32 bytes   *)
(* from the state after the last block.                                      *)
(* ------------------------------------------------------------------------- *)

let keccak_absorb_block = new_definition
 `keccak_absorb_block r p j =
    (word((p DIV 2 EXP (8 * r * j)) MOD 2 EXP (8 * r)):1600 word)`;;

let KECCAK_ABSORB_BLOCK_STEP = prove
 (`!r p j. keccak_f1600(word_xor (keccak_absorb r p j)
                                 (keccak_absorb_block r p j)) =
           keccak_absorb r p (j + 1)`,
  REWRITE_TAC[keccak_absorb_block; GSYM ADD1; keccak_absorb]);;

let KECCAK_SPONGE_DIGEST = prove
 (`!c d (m:byte list) n.
      (1600 - c) DIV 8 = 136 /\ n <= 136
      ==> num_of_bytelist(list_of_seq (keccak_sponge c d m) n) =
          val(keccak_f1600
               (word_xor
                 (keccak_absorb 136 (keccak_padded 136 d m) (LENGTH m DIV 136))
                 (keccak_absorb_block 136 (keccak_padded 136 d m)
                                      (LENGTH m DIV 136)))) MOD
          2 EXP (8 * n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:num`; `d:num`; `m:byte list`; `136`;
                `keccak_padded 136 d m`; `n:num`] KECCAK_SPONGE_BYTES) THEN
  ASM_REWRITE_TAC[keccak_padded; keccak_absorb_block; ARITH]);;

let SHA3_256_DIGEST = prove
 (`!m:byte list.
      num_of_bytelist(sha3_256 m) =
      val(keccak_f1600
           (word_xor
             (keccak_absorb 136 (keccak_padded 136 6 m) (LENGTH m DIV 136))
             (keccak_absorb_block 136 (keccak_padded 136 6 m)
                                  (LENGTH m DIV 136)))) MOD 2 EXP 256`,
  GEN_TAC THEN REWRITE_TAC[sha3_256] THEN
  MP_TAC(SPECL [`512`; `6`; `m:byte list`; `32`] KECCAK_SPONGE_DIGEST) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let SHAKE256_32_DIGEST = prove
 (`!m:byte list.
      num_of_bytelist(list_of_seq (shake256 m) 32) =
      val(keccak_f1600
           (word_xor
             (keccak_absorb 136 (keccak_padded 136 31 m) (LENGTH m DIV 136))
             (keccak_absorb_block 136 (keccak_padded 136 31 m)
                                  (LENGTH m DIV 136)))) MOD 2 EXP 256`,
  GEN_TAC THEN REWRITE_TAC[shake256] THEN
  MP_TAC(SPECL [`512`; `31`; `m:byte list`; `32`] KECCAK_SPONGE_DIGEST) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Memory: 16 bytes from two 8-byte words and back, as for the copies of the *)
(* job structures, and 32 bytes from two 16-byte words, as for the digests.  *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES128_OF_BYTES64S = prove
 (`!a x y s:armstate.
     read (memory :> bytes64 a) s = x /\
     read (memory :> bytes64 (word_add a (word 8))) s = y
     ==> read (memory :> bytes128 a) s = word_join y x`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[GSYM READ_MEMORY_BYTES_16] THEN
  REWRITE_TAC[ARITH_RULE `16 = 8 + 8`; READ_MEMORY_BYTES_SPLIT] THEN
  ASM_REWRITE_TAC[READ_MEMORY_BYTES_8] THEN
  SIMP_TAC[VAL_WORD_JOIN_SIMPLE; DIMINDEX_64; DIMINDEX_128; ARITH] THEN
  ARITH_TAC);;

let READ_MEMORY_BYTES64S_OF_BYTES128 = prove
 (`!a v s:armstate.
     read (memory :> bytes128 a) s = v
     ==> read (memory :> bytes64 a) s = word_zx v /\
         read (memory :> bytes64 (word_add a (word 8))) s =
         word_subword v (64,64)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`a:int64`; `read (memory :> bytes64 a) s`;
                 `read (memory :> bytes64 (word_add a (word 8))) s`;
                 `s:armstate`] READ_MEMORY_BYTES128_OF_BYTES64S) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC WORD_BLAST);;

let WORD_JOIN_64_PARTS = prove
 (`!x y:int64. word_zx(word_join y x:int128):int64 = x /\
               word_subword (word_join y x:int128) (64,64):int64 = y`,
  CONV_TAC WORD_BLAST);;

let READ_MEMORY_BYTES_32_OF_BYTES128S = prove
 (`!a x s:armstate.
     read (memory :> bytes128 a) s = word(x MOD 2 EXP 128) /\
     read (memory :> bytes128 (word_add a (word 16))) s =
     word((x DIV 2 EXP 128) MOD 2 EXP 128)
     ==> read (memory :> bytes(a,32)) s = x MOD 2 EXP 256`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `32 = 16 + 16`; READ_MEMORY_BYTES_SPLIT] THEN
  ASM_REWRITE_TAC[READ_MEMORY_BYTES_16; VAL_WORD; DIMINDEX_128;
                  MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `8 * 16 = 128`; ARITH_RULE `256 = 128 + 128`;
              MOD_EXP_ADD_SPLIT]);;
