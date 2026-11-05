(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of a polynomial from a seed by rejection. In the gcc 12  *)
(* -O2 monolithic build, which compiles all of mlkem-native as one           *)
(* translation unit, mlkem_poly_rej_uniform has no code of its own: it is    *)
(* inlined into mlkem768_gen_matrix, for the last of the nine entries of the *)
(* matrix (the others are sampled four at a time by                          *)
(* mlkem_poly_rej_uniform_x4). This file only has the lemmas about the       *)
(* samples, as in the gcc 12 -O2 build, which this build's proofs of         *)
(* mlkem_poly_rej_uniform_x4 and of mlkem768_gen_matrix use. The inlined     *)
(* code itself is to be proved in mlkem768_gen_matrix's proof.               *)
(* ========================================================================= *)

needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/rej_uniform.ml";;
needs "arm/proofs/utils/keccak_fips202.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2_mono/libmlkem.ml";;

(* ------------------------------------------------------------------------- *)
(* The bytes of SHAKE128 in blocks of 168, the rate, in terms of the         *)
(* absorbed state, as for mlkem_shake256 and mlkem_shake256x4.               *)
(* ------------------------------------------------------------------------- *)

let REJ_SPONGE = prove
 (`!(m:byte list) k n.
        n <= 168
        ==> num_of_bytelist(list_of_seq (\j. shake128 m (168 * k + j)) n) =
            val(keccak_squeeze (k + 1)
                 (word_xor
                   (keccak_absorb 168
                     (num_of_bytelist m +
                      2 EXP (8 * LENGTH m) *
                      num_of_bytelist(keccak_pad 168 0x1F (LENGTH m)))
                     (LENGTH m DIV 168))
                   (word((num_of_bytelist m +
                          2 EXP (8 * LENGTH m) *
                          num_of_bytelist(keccak_pad 168 0x1F (LENGTH m))) DIV
                         2 EXP (8 * 168 * LENGTH m DIV 168) MOD
                         2 EXP (8 * 168))))) MOD 2 EXP (8 * n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[shake128] THEN
  MATCH_MP_TAC KECCAK_SPONGE_BLOCK THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let REJ_XOF_BLOCKS = prove
 (`!(f:num->byte) n.
        num_of_bytelist(list_of_seq f (168 * n)) =
        nsum {i | i < n}
         (\i. 2 EXP (8 * 168 * i) *
              num_of_bytelist(list_of_seq (\j. f(168 * i + j)) 168))`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; list_of_seq; num_of_bytelist;
                NSUM_CLAUSES_NUMSEG_LT];
    ASM_REWRITE_TAC[ARITH_RULE `168 * SUC n = 168 * n + 168`;
                    NUM_OF_BYTELIST_LIST_OF_SEQ_ADD;
                    NSUM_CLAUSES_NUMSEG_LT]]);;

let REJ_SHAKE128_BLOCKS = prove
 (`!(m:byte list) b.
        num_of_bytelist(list_of_seq (shake128 m) (168 * b)) =
        nsum {i | i < b}
         (\i. 2 EXP (8 * 168 * i) *
              val(keccak_squeeze (i + 1)
                   (word_xor
                     (keccak_absorb 168
                       (num_of_bytelist m +
                        2 EXP (8 * LENGTH m) *
                        num_of_bytelist(keccak_pad 168 0x1F (LENGTH m)))
                       (LENGTH m DIV 168))
                     (word((num_of_bytelist m +
                            2 EXP (8 * LENGTH m) *
                            num_of_bytelist(keccak_pad 168 0x1F (LENGTH m)))
                           DIV 2 EXP (8 * 168 * LENGTH m DIV 168) MOD
                           2 EXP (8 * 168))))) MOD 2 EXP (8 * 168))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REJ_XOF_BLOCKS] THEN
  MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC REJ_SPONGE THEN
  REWRITE_TAC[LE_REFL]);;

let KECCAK_SQUEEZE_ADD = prove
 (`!m n (S:1600 word).
        keccak_squeeze m (keccak_squeeze n S) = keccak_squeeze (m + n) S`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[keccak_squeeze; ADD_CLAUSES]);;

let REJ_NSUM_1 = prove
 (`!f. nsum {j | j < 1} f = f 0`,
  REWRITE_TAC[num_CONV `1`; NSUM_CLAUSES_NUMSEG_LT; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* The 12-bit fields of the first 504 + 168 * j bytes, those of three blocks *)
(* and j more, and the samples from them as in the specification of          *)
(* mlk_rej_uniform_c, with REJ_SAMPLE as there.                              *)
(* ------------------------------------------------------------------------- *)

let REJ_WORDLIST_OF_NUM_ADD = prove
 (`!m n x. wordlist_of_num (m + n) x:(N word)list =
           APPEND (wordlist_of_num m x)
                  (wordlist_of_num n (x DIV 2 EXP (dimindex(:N) * m)))`,
  INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; wordlist_of_num; APPEND; MULT_CLAUSES; EXP;
              DIV_1] THEN
  ASM_REWRITE_TAC[CONS_11; DIV_DIV; GSYM EXP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `d + d * m = d * SUC m`]);;

let REJ_WORDLIST_APPEND = prove
 (`!(f:num->byte) m n.
        8 * m = 12 * n
        ==> wordlist_of_num (n + 112)
             (num_of_bytelist(list_of_seq f (m + 168))):(12 word)list =
            APPEND (wordlist_of_num n (num_of_bytelist(list_of_seq f m)))
                   (wordlist_of_num 112
                     (num_of_bytelist(list_of_seq (\i. f(m + i)) 168)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD; REJ_WORDLIST_OF_NUM_ADD] THEN
  REWRITE_TAC[DIMINDEX_12] THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPEC `list_of_seq (f:num->byte) m` NUM_OF_BYTELIST_BOUND) THEN
  REWRITE_TAC[LENGTH_LIST_OF_SEQ; GSYM(NUM_REDUCE_CONV `2 EXP 8`);
              GSYM EXP_MULT] THEN
  SPEC_TAC(`num_of_bytelist(list_of_seq (f:num->byte) m)`,`x:num`) THEN
  SPEC_TAC(`num_of_bytelist(list_of_seq (\i. (f:num->byte)(m + i)) 168)`,
           `y:num`) THEN
  REPEAT STRIP_TAC THEN BINOP_TAC THENL
   [GEN_REWRITE_TAC BINOP_CONV [GSYM WORDLIST_OF_NUM_MOD] THEN
    REWRITE_TAC[DIMINDEX_12] THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[ARITH_RULE `x + n * y:num = y * n + x`] THEN
    REWRITE_TAC[MOD_MULT_ADD];
    AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[ARITH_RULE `x + n * y:num = y * n + x`] THEN
    SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
    ASM_SIMP_TAC[DIV_LT; ADD_CLAUSES]]);;

let REJ_FIELDS_SUC = prove
 (`!(f:num->byte) j.
        wordlist_of_num (336 + 112 * (j + 1))
         (num_of_bytelist(list_of_seq f (504 + 168 * (j + 1)))):(12 word)list =
        APPEND
         (wordlist_of_num (336 + 112 * j)
           (num_of_bytelist(list_of_seq f (504 + 168 * j))))
         (wordlist_of_num 112
           (num_of_bytelist(list_of_seq (\i. f((504 + 168 * j) + i)) 168)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `504 + 168 * (j + 1) = (504 + 168 * j) + 168`;
              ARITH_RULE `336 + 112 * (j + 1) = (336 + 112 * j) + 112`] THEN
  MATCH_MP_TAC REJ_WORDLIST_APPEND THEN ARITH_TAC);;

let REJ_FIELDS_PREFIX = prove
 (`!(f:num->byte) j k.
        j <= k
        ==> ?t. wordlist_of_num (336 + 112 * k)
                 (num_of_bytelist(list_of_seq f (504 + 168 * k))):
                (12 word)list =
                APPEND (wordlist_of_num (336 + 112 * j)
                         (num_of_bytelist(list_of_seq f (504 + 168 * j)))) t`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [REWRITE_TAC[LE] THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `[]:(12 word)list` THEN REWRITE_TAC[APPEND_NIL];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[LE] THEN
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXISTS_TAC `[]:(12 word)list` THEN
      REWRITE_TAC[APPEND_NIL];
      FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_TAC `t:(12 word)list`) THEN
      REWRITE_TAC[ADD1; REJ_FIELDS_SUC] THEN
      ASM_REWRITE_TAC[GSYM APPEND_ASSOC] THEN MESON_TAC[]]]);;

let REJ_COUNT_MONO = prove
 (`!(f:num->byte) j k.
        j <= k
        ==> LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                     (num_of_bytelist(list_of_seq f (504 + 168 * j))))) <=
            LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * k)
                     (num_of_bytelist(list_of_seq f (504 + 168 * k)))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(12 word)list` SUBST1_TAC o
             MATCH_MP(SPEC `f:num->byte` REJ_FIELDS_PREFIX)) THEN
  REWRITE_TAC[REJ_SAMPLE_APPEND; LENGTH_APPEND; LE_ADD]);;

let REJ_SAMPLE_FINAL = prove
 (`!(f:num->byte) j k.
        j <= k /\
        256 <= LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                       (num_of_bytelist(list_of_seq f (504 + 168 * j)))))
        ==> SUB_LIST(0,256)
             (REJ_SAMPLE(wordlist_of_num (336 + 112 * k)
                (num_of_bytelist(list_of_seq f (504 + 168 * k))))) =
            SUB_LIST(0,256)
             (REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                (num_of_bytelist(list_of_seq f (504 + 168 * j)))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `t:(12 word)list` SUBST1_TAC o
    MATCH_MP(SPEC `f:num->byte` REJ_FIELDS_PREFIX))
   ASSUME_TAC) THEN
  REWRITE_TAC[REJ_SAMPLE_APPEND] THEN
  MATCH_MP_TAC SUB_LIST_APPEND_LEFT THEN ASM_REWRITE_TAC[]);;

let REJ_SAMPLE_SUC = prove
 (`!(f:num->byte) j.
        LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                 (num_of_bytelist(list_of_seq f (504 + 168 * j))))) <= 256
        ==> SUB_LIST(0,256)
             (REJ_SAMPLE(wordlist_of_num (336 + 112 * (j + 1))
                (num_of_bytelist(list_of_seq f (504 + 168 * (j + 1)))))) =
            APPEND
             (SUB_LIST(0,256)
               (REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                  (num_of_bytelist(list_of_seq f (504 + 168 * j))))))
             (SUB_LIST(0,256 -
                       LENGTH(REJ_SAMPLE(wordlist_of_num (336 + 112 * j)
                         (num_of_bytelist(list_of_seq f (504 + 168 * j))))))
               (REJ_SAMPLE(wordlist_of_num 112
                  (num_of_bytelist
                    (list_of_seq (\i. f((504 + 168 * j) + i)) 168)))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REJ_FIELDS_SUC; REJ_SAMPLE_APPEND] THEN
  ASM_SIMP_TAC[SUB_LIST_APPEND_RIGHT; SUB_LIST_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Lists of 12-bit fields and of 16-bit samples in memory.                   *)
(* ------------------------------------------------------------------------- *)

let REJ_WORDLIST_FROM_BYTES = prove
 (`!a m n x s:armstate.
        12 * n = 8 * m /\ read (memory :> bytes(a,m)) s = x
        ==> wordlist_from_memory(a,n) s = (wordlist_of_num n x:(12 word)list)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[wordlist_from_memory; DIMINDEX_12] THEN
  SUBGOAL_THEN `(12 * n + 7) DIV 8 = m` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `7` THEN ASM_ARITH_TAC);;

let REJ_BYTES16_OF_WORDLIST = prove
 (`!a n (l:int16 list) s:armstate.
        wordlist_from_memory(a,n) s = l
        ==> read (memory :> bytes(a,2 * n)) s = num_of_wordlist l`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `n:num`; `2 * n`; `l:int16 list`; `s:armstate`]
         WORDLIST_FROM_MEMORY_EQ_ALT) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH_RULE `16 * n = 8 * 2 * n`] THEN
  DISCH_THEN SUBST1_TAC THEN SIMP_TAC[]);;

let REJ_WORDLIST_OF_BYTES16 = prove
 (`!a (l:int16 list) s:armstate.
        read (memory :> bytes(a,2 * LENGTH l)) s = num_of_wordlist l
        ==> wordlist_from_memory(a,LENGTH l) s = l`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `LENGTH(l:int16 list)`; `2 * LENGTH(l:int16 list)`;
                 `l:int16 list`; `s:armstate`]
                WORDLIST_FROM_MEMORY_EQ_ALT) THEN
  REWRITE_TAC[DIMINDEX_16; ARITH_RULE `16 * n = 8 * 2 * n`] THEN
  DISCH_THEN SUBST1_TAC THEN SIMP_TAC[]);;

let REJ_BYTES16_APPEND_N = prove
 (`!a n (l1:int16 list) (l2:int16 list) s:armstate.
        LENGTH l1 = n /\
        read (memory :> bytes(a,2 * n)) s = num_of_wordlist l1 /\
        read (memory :> bytes(word_add a (word(2 * n)),2 * LENGTH l2)) s =
        num_of_wordlist l2
        ==> read (memory :> bytes(a,2 * (n + LENGTH l2))) s =
            num_of_wordlist(APPEND l1 l2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check
   (fun th -> concl th = `LENGTH(l1:int16 list) = n`)) THEN
  REWRITE_TAC[GSYM LENGTH_APPEND] THEN
  MATCH_MP_TAC READ_BYTES16_APPEND THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The comparison of the number of samples with 255, as 32-bit words.        *)
(* ------------------------------------------------------------------------- *)

let REJ_HI_LEMMA = prove
 (`!c. c < 2 EXP 32
       ==> ((&c - &255:int =
             &(val(word_sub (word_zx (word c:int64):int32) (word 255))) /\
             ~(val(word_sub (word_zx (word c:int64):int32) (word 255)) =
               0)) <=>
            255 < c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word_zx(word c:int64):int32) = c` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
    POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[MOD_LT; ARITH_RULE
     `c < 4294967296 ==> c < 18446744073709551616`];
    ALL_TAC] THEN
  REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
  ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THENL
   [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC(TAUT `~a /\ ~b ==> ((a /\ c) <=> b)`) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC(INT_ARITH `x < &255 /\ &0 <= y ==> ~(x - &255:int = y)`) THEN
    REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The buffer for three blocks, followed by the state, is aligned to 32      *)
(* bytes within the stack frame, so its address depends on whether the stack *)
(* pointer is a multiple of 32 or just of 16.                                *)
(* ------------------------------------------------------------------------- *)

let REJ_ALIGNED_16_32 = prove
 (`(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`,
  CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`x:int64`; `4`] (CONJUNCT1 WORD_AND_MASK_WORD));
    MP_TAC(ISPECL [`x:int64`; `5`] (CONJUNCT1 WORD_AND_MASK_WORD))] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 16 < 16`; ARITH_RULE `x MOD 32 < 32`;
           ARITH_RULE `x < 16 ==> x < 2 EXP 64`;
           ARITH_RULE `x < 32 ==> x < 2 EXP 64`]);;

(* ------------------------------------------------------------------------- *)
(* The absorbed state of a seed of 34 bytes, and the facts from a call of    *)
(* mlk_rej_uniform_c.                                                        *)
(* ------------------------------------------------------------------------- *)

(*** The absorbed state as S0, and the minimal number k0 of blocks ***)

let REJ_ABSORBED =
 `word_xor
   (keccak_absorb 168
     (num_of_bytelist inp +
      2 EXP (8 * 34) * num_of_bytelist(keccak_pad 168 0x1F 34))
     (34 DIV 168))
   (word((num_of_bytelist inp +
          2 EXP (8 * 34) * num_of_bytelist(keccak_pad 168 0x1F 34)) DIV
         2 EXP (8 * 168 * 34 DIV 168) MOD 2 EXP (8 * 168))):1600 word`;;

let REJ_POST_TAC =
  FIRST_X_ASSUM(fun th ->
    if is_let(concl th) then
      STRIP_ASSUME_TAC(REWRITE_RULE[GSYM REJ_SAMPLE]
        (CONV_RULE(TOP_DEPTH_CONV let_CONV) th))
    else NO_TAC);;
