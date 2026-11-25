(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Word-level facts that relate the compiled compressors to the models of    *)
(* snappy_compress.ml: the input fragment and the output as byte regions,    *)
(* the uint16_t hash tables as numbers, the hash functions as the code       *)
(* computes them, and FindMatchLengthPlain's 8-byte comparisons.             *)
(* ========================================================================= *)

needs "common/snappy/snappy_roundtrip.ml";;
needs "common/snappy/snappy_words.ml";;

(* ------------------------------------------------------------------------- *)
(* Byte lists and their numbers.                                             *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_BYTE_DIVMOD = prove
 (`!(h:byte) n. (val h + 256 * n) DIV 256 = n /\ (val h + 256 * n) MOD 256 = val h`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `val(h:byte)`;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `n:num`] THEN
  ASM_ARITH_TAC);;

let SNAPPY_MOD_CONS = prove
 (`!a b m. a < 256 ==> (a + 256 * b) MOD (256 * m) = a + 256 * (b MOD m)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `m = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; MOD_ZERO] THEN
  MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `b DIV m` THEN
  MP_TAC(SPECL [`b:num`; `m:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = b DIV m` THEN ABBREV_TAC `r = b MOD m` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  CONJ_TAC THENL [CONV_TAC NUM_RING; ASM_ARITH_TAC]);;

let SNAPPY_NUM_OF_BYTELIST_SUB_LIST = prove
 (`!(l:byte list) p k.
     num_of_bytelist(SUB_LIST(p,k) l) =
     (num_of_bytelist l DIV 2 EXP (8 * p)) MOD 2 EXP (8 * k)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[SUB_LIST_CLAUSES; num_of_bytelist; DIV_0; MOD_0]; ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "ih") THEN
  X_GEN_TAC `p:num` THEN X_GEN_TAC `k:num` THEN
  STRUCT_CASES_TAC(SPEC `p:num` num_CASES) THENL
   [STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN
    REWRITE_TAC[SUB_LIST_CLAUSES; num_of_bytelist] THENL
     [REWRITE_TAC[ARITH_RULE `8 * 0 = 0`; EXP; MOD_1]; ALL_TAC] THEN
    USE_THEN "ih" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[ARITH_RULE `8 * 0 = 0`; EXP; DIV_1] THEN
    REWRITE_TAC[ARITH_RULE `8 * SUC k = 8 + 8 * k`; EXP_ADD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SNAPPY_MOD_CONS THEN
    MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    REWRITE_TAC[SUB_LIST_CLAUSES; num_of_bytelist] THEN
    USE_THEN "ih" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[ARITH_RULE `8 * SUC p = 8 + 8 * p`; EXP_ADD; GSYM DIV_DIV] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[SNAPPY_BYTE_DIVMOD]]);;

(* The model's loads from the input region.                                 *)

let SNAPPY_LOAD_SUB_LIST = prove
 (`!(src:byte list) p.
     snappy_load32 src p = num_of_bytelist(SUB_LIST(p,4) src) /\
     snappy_load64 src p = num_of_bytelist(SUB_LIST(p,8) src)`,
  REWRITE_TAC[snappy_load32; snappy_load64]);;

let SNAPPY_LOAD64_MOD32 = prove
 (`!(src:byte list) p. snappy_load64 src p MOD 2 EXP 32 = snappy_load32 src p`,
  REWRITE_TAC[snappy_load32; snappy_load64; SNAPPY_NUM_OF_BYTELIST_SUB_LIST] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

let SNAPPY_LOAD32_BOUND = prove
 (`!(src:byte list) p. snappy_load32 src p < 2 EXP 32`,
  REWRITE_TAC[snappy_load32; SNAPPY_NUM_OF_BYTELIST_SUB_LIST] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_LT_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let SNAPPY_LOAD64_BOUND = prove
 (`!(src:byte list) p. snappy_load64 src p < 2 EXP 64`,
  REWRITE_TAC[snappy_load64; SNAPPY_NUM_OF_BYTELIST_SUB_LIST] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_LT_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let SNAPPY_NUM_OF_BYTELIST_SUB_LIST_1 = prove
 (`!(l:byte list) p. p < LENGTH l
                     ==> num_of_bytelist(SUB_LIST(p,1) l) = val(EL p l)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SUB_LIST_1] THEN
  REWRITE_TAC[num_of_bytelist] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A hash table of ts uint16_t entries holding t j at index j < ts, as the   *)
(* number that its 2 * ts bytes hold.                                        *)
(* ------------------------------------------------------------------------- *)

let snappy_tval = new_recursive_definition num_RECURSION
 `(snappy_tval 0 (t:num->num) = 0) /\
  (snappy_tval (SUC k) t = snappy_tval k t + 2 EXP (16 * k) * t k)`;;

let SNAPPY_TVAL_ZERO = prove
 (`!k. snappy_tval k (\j. 0) = 0`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[snappy_tval; MULT_CLAUSES; ADD_CLAUSES]);;

let SNAPPY_TVAL_EXT = prove
 (`!k t t'. (!j. j < k ==> t' j = t j) ==> snappy_tval k t' = snappy_tval k t`,
  INDUCT_TAC THEN REWRITE_TAC[snappy_tval] THEN REPEAT STRIP_TAC THEN
  BINOP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[ARITH_RULE `j < k ==> j < SUC k`];
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

let SNAPPY_TVAL_BOUND = prove
 (`!k t. (!j. j < k ==> t j < 65536) ==> snappy_tval k t < 2 EXP (16 * k)`,
  INDUCT_TAC THEN REWRITE_TAC[snappy_tval] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `snappy_tval k t < 2 EXP (16 * k) /\ t k < 65536`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `16 * SUC k = 16 * k + 16`; EXP_ADD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    TRANS_TAC LTE_TRANS `2 EXP (16 * k) + 2 EXP (16 * k) * 65535` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `a < b /\ c <= d ==> a + c < b + d`) THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      ARITH_TAC]]);;

(* The table split at an entry e < k: the entries below e, the entry e and  *)
(* the k - e - 1 entries above it.                                          *)

let SNAPPY_TVAL_ADD = prove
 (`!a b t. snappy_tval (a + b) t =
           snappy_tval a t + 2 EXP (16 * a) * snappy_tval b (\j. t(a + j))`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; snappy_tval; MULT_CLAUSES] THEN
  GEN_TAC THEN BETA_TAC THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; ADD_ASSOC; MULT_ASSOC; GSYM EXP_ADD]);;

let SNAPPY_TVAL_1 = prove
 (`!t. snappy_tval 1 t = t 0`,
  REWRITE_TAC[ONE; snappy_tval; MULT_CLAUSES; EXP; ADD_CLAUSES]);;

let SNAPPY_TVAL_SPLIT = prove
 (`!k t e. e < k
           ==> snappy_tval k t =
               snappy_tval e t + 2 EXP (16 * e) *
               (t e + 2 EXP 16 * snappy_tval (k - e - 1) (\j. t(e + 1 + j)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `k = e + (1 + (k - e - 1))`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SNAPPY_TVAL_ADD; SNAPPY_TVAL_1] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

(* Uniqueness of the digits of a number in base N.                          *)

let SNAPPY_DIGIT_UNIQ = prove
 (`!N a b c d. a < N /\ c < N /\ a + N * b = c + N * d ==> a = c /\ b = d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(AP_TERM `\x. x MOD N` th) THEN
                          MP_TAC(AP_TERM `\x. x DIV N` th)) THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; DIV_LT; MOD_LT; ADD_CLAUSES]);;

(* The three parts of a table region at an entry.                           *)

let SNAPPY_TABLE_SPLIT = prove
 (`!(m:(S,int64->byte)component) a k t e s.
     read (m :> bytes(a,2 * k)) s = snappy_tval k t /\ e < k /\
     (!j. j < k ==> t j < 65536)
     ==> read (m :> bytes(a,2 * e)) s = snappy_tval e t /\
         read (m :> bytes16 (word_add a (word(2 * e)))) s = word(t e) /\
         read (m :> bytes(word_add a (word(2 * e + 2)),2 * (k - e - 1))) s =
         snappy_tval (k - e - 1) (\j. t(e + 1 + j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `snappy_tval e t < 2 EXP (16 * e) /\ t e < 65536 /\
    snappy_tval (k - e - 1) (\j. t(e + 1 + j)) < 2 EXP (16 * (k - e - 1))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC) THEN
    MATCH_MP_TAC SNAPPY_TVAL_BOUND THEN REPEAT STRIP_TAC THEN
    TRY BETA_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 * k = 2 * e + (2 + 2 * (k - e - 1))` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o
    check (fun th -> is_eq(concl th) && is_comb(lhs(concl th))) o
    ONCE_REWRITE_RULE[th])) THEN
  ASM_SIMP_TAC[SNAPPY_TVAL_SPLIT] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `8 * 2 * e = 16 * e`; ARITH_RULE `8 * 2 = 16`] THEN
  ABBREV_TAC `L = read (bytes(a:int64,2 * e))
                       (read (m:(S,int64->byte)component) (s:S))` THEN
  ABBREV_TAC `E = read (bytes(word_add (a:int64) (word(2 * e)),2))
                       (read (m:(S,int64->byte)component) (s:S))` THEN
  ABBREV_TAC `H = read (bytes(word_add (a:int64) (word(2 * e + 2)),
                              2 * (k - e - 1)))
                       (read (m:(S,int64->byte)component) (s:S))` THEN
  SUBGOAL_THEN `L < 2 EXP (16 * e) /\ E < 2 EXP 16` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["L"; "E"] THEN
    REWRITE_TAC[ARITH_RULE `16 * e = 8 * (2 * e)`; ARITH_RULE `16 = 8 * 2`] THEN
    REWRITE_TAC[READ_BYTES_BOUND];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`2 EXP (16 * e)`; `L:num`; `E + 2 EXP 16 * H`;
                `snappy_tval e t`;
                `t e + 2 EXP 16 * snappy_tval (k - e - 1) (\j. t(e + 1 + j))`]
         SNAPPY_DIGIT_UNIQ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`2 EXP 16`; `E:num`; `H:num`; `(t:num->num) e`;
                `snappy_tval (k - e - 1) (\j. t(e + 1 + j))`]
         SNAPPY_DIGIT_UNIQ) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM VAL_EQ; BYTES16_WBYTES; VAL_READ_WBYTES; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT]);;

(* The parts put together again after a store of v at the entry e.          *)

let SNAPPY_TABLE_JOIN = prove
 (`!(m:(S,int64->byte)component) a k t e v s.
     e < k /\ v < 65536 /\
     read (m :> bytes(a,2 * e)) s = snappy_tval e t /\
     read (m :> bytes16 (word_add a (word(2 * e)))) s = word v /\
     read (m :> bytes(word_add a (word(2 * e + 2)),2 * (k - e - 1))) s =
     snappy_tval (k - e - 1) (\j. t(e + 1 + j))
     ==> read (m :> bytes(a,2 * k)) s = snappy_tval k (snappy_tupd t e v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SNAPPY_TVAL_SPLIT] THEN
  SUBGOAL_THEN `2 * k = 2 * e + (2 + 2 * (k - e - 1))` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (term_match [] `read (m :> bytes16 x) y = word v`) (concl th))) THEN
  REWRITE_TAC[GSYM VAL_EQ; BYTES16_WBYTES; READ_COMPONENT_COMPOSE;
              VAL_READ_WBYTES; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOD_LT] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `8 * 2 * e = 16 * e`; ARITH_RULE `8 * 2 = 16`] THEN
  REWRITE_TAC[snappy_tupd] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC SNAPPY_TVAL_EXT THEN SIMP_TAC[ARITH_RULE `j < e ==> ~(j = e)`];
    AP_TERM_TAC] THEN
  BINOP_TAC THENL
   [REWRITE_TAC[];
    AP_TERM_TAC THEN MATCH_MP_TAC SNAPPY_TVAL_EXT THEN
    SIMP_TAC[ARITH_RULE `~(e + 1 + j = e)`]]);;

(* ------------------------------------------------------------------------- *)
(* The states that a run of CompressFragmentDoubleHash's model reaches, and  *)
(* the induction that relates a run of the code to it: the code is proved to *)
(* go, from a point that corresponds to a reachable state of the model, to   *)
(* the end, or to a point that corresponds to a later state, whose potential *)
(* is smaller.                                                               *)
(* ------------------------------------------------------------------------- *)

let snappy_cf2_reach = new_definition
 `snappy_cf2_reach (src:byte list) st <=>
    ?k. st = snappy_crun (snappy_cf2_step src) k (snappy_cf2_init src)`;;

let SNAPPY_CRUN_SUC_STEP = prove
 (`!step k s. snappy_crun step (SUC k) s = step(snappy_crun step k s)`,
  REWRITE_TAC[ADD1; SNAPPY_CRUN_ADD] THEN
  REWRITE_TAC[num_CONV `1`; snappy_crun]);;

let SNAPPY_CF2_REACH_INIT = prove
 (`!src:byte list. snappy_cf2_reach src (snappy_cf2_init src)`,
  GEN_TAC THEN REWRITE_TAC[snappy_cf2_reach] THEN EXISTS_TAC `0` THEN
  REWRITE_TAC[snappy_crun]);;

let SNAPPY_CF2_REACH_STEP = prove
 (`!(src:byte list) st.
     snappy_cf2_reach src st ==> snappy_cf2_reach src (snappy_cf2_step src st)`,
  REWRITE_TAC[snappy_cf2_reach] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `SUC k` THEN ASM_REWRITE_TAC[SNAPPY_CRUN_SUC_STEP]);;

let SNAPPY_CF2_REACH_INV = prove
 (`!(src:byte list) st.
     LENGTH src <= 65536 /\ snappy_cf2_reach src st ==> snappy_cf2_inv src st`,
  REWRITE_TAC[snappy_cf2_reach] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (is_var o lhs o concl)) THEN
  SPEC_TAC(`k:num`,`k:num`) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[snappy_crun; SNAPPY_CF2_INIT] THEN
  REWRITE_TAC[GSYM snappy_crun; SNAPPY_CRUN_SUC_STEP] THEN
  ASM_CASES_TAC
   `snappy_phase(snappy_crun (snappy_cf2_step src) k (snappy_cf2_init src)) = 0`
  THENL [ASM_SIMP_TAC[SNAPPY_CF2_FIX]; ASM_SIMP_TAC[SNAPPY_CF2_STEP]]);;

let SNAPPY_CF2_REACH_DONE = prove
 (`!(src:byte list) st.
     LENGTH src <= 65536 /\ snappy_cf2_reach src st /\ snappy_phase st = 0
     ==> snappy_compress_fragment 2 src = snappy_out st`,
  REWRITE_TAC[snappy_cf2_reach] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  MATCH_MP_TAC SNAPPY_COMPRESS_FRAGMENT_2 THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The hash functions as the code computes them: the product, shifted right  *)
(* and masked with mask = 2 * (ts - 1), the byte offset of the entry.        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_MASK_SHIFTED_64 = BITBLAST_RULE
 `word_and (word_shl m 1) y:int64 = word_shl (word_and m (word_ushr y 1)) 1`;;

let SNAPPY_MASK_SHIFTED_32 = BITBLAST_RULE
 `word_and (word_shl m 1) y:int32 = word_shl (word_and m (word_ushr y 1)) 1`;;

let SNAPPY_TABLE_MASK = prove
 (`(!k (y:int64). word_and (word (2 * (2 EXP k - 1))) y =
                  word(2 * ((val y DIV 2) MOD 2 EXP k))) /\
   (!k (y:int32). word_and (word (2 * (2 EXP k - 1))) y =
                  word(2 * ((val y DIV 2) MOD 2 EXP k)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 * x = 2 EXP 1 * x`; GSYM WORD_SHL_WORD] THEN
  REWRITE_TAC[SNAPPY_MASK_SHIFTED_64; SNAPPY_MASK_SHIFTED_32;
              WORD_AND_MASK_WORD] THEN
  REWRITE_TAC[VAL_WORD_USHR; EXP_1]);;

let snappy_pow2 = new_definition
 `snappy_pow2 ts <=> ?k. ts = 2 EXP k`;;

let SNAPPY_POW2_TABLE_SIZE = prove
 (`!n. snappy_pow2(snappy_table_size n DIV 2) /\
       128 <= snappy_table_size n DIV 2 /\ snappy_table_size n DIV 2 <= 16384`,
  GEN_TAC THEN REWRITE_TAC[snappy_pow2; snappy_table_size] THEN
  REPEAT COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  FIRST (map (fun k -> EXISTS_TAC (mk_small_numeral k) THEN
                       CONV_TAC NUM_REDUCE_CONV THEN NO_TAC) (7--14)));;

let SNAPPY_HASH8_WORD = prove
 (`!ts d. snappy_pow2 ts /\ d < 2 EXP 64
          ==> word_and (word (2 * (ts - 1)))
               (word_ushr (word (0 + val (word d:int64) * 58295818150454627))
                          49):int64 =
              word(2 * snappy_hash8 ts d)`,
  REWRITE_TAC[snappy_pow2] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[SNAPPY_TABLE_MASK; snappy_hash8] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[VAL_WORD_USHR; VAL_WORD; DIMINDEX_64; DIV_DIV; ADD_CLAUSES] THEN
  ASM_SIMP_TAC[MOD_LT; GSYM EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MULT_SYM]);;

(* ------------------------------------------------------------------------- *)
(* FindMatchLengthPlain: 8 bytes compared at a time, then the first          *)
(* difference found from the lowest set bit of the exclusive or, or the     *)
(* bytes compared one at a time at the end of the input.                     *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_MOD_DIV_MOD_EXP = prove
 (`!x p q r. q + r <= p
             ==> ((x MOD 2 EXP p) DIV 2 EXP q) MOD 2 EXP r =
                 (x DIV 2 EXP q) MOD 2 EXP r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `q + r <= p ==> MIN p (q + r) = q + r`]);;

let SNAPPY_LOAD64_BYTE = prove
 (`!(src:byte list) a i.
     i < 8 /\ a + i < LENGTH src
     ==> (snappy_load64 src a DIV 2 EXP (8 * i)) MOD 2 EXP 8 =
         val(EL (a + i) src)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SNAPPY_EL_NUM_OF_BYTELIST] THEN
  REWRITE_TAC[snappy_load64; SNAPPY_NUM_OF_BYTELIST_SUB_LIST] THEN
  ASM_SIMP_TAC[SNAPPY_MOD_DIV_MOD_EXP; ARITH_RULE
   `i < 8 ==> 8 * i + 8 <= 8 * 8`] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8; SNAPPY_EXP_256] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; LEFT_ADD_DISTRIB] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL]);;

(* Two numbers agree below 2^(8 * j) iff their first j bytes do.          *)

let SNAPPY_DIGIT_UNIQ_ALT = prove
 (`!N a b c d. a < N /\ c < N ==> (N * b + a = N * d + c <=> a = c /\ b = d)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC SNAPPY_DIGIT_UNIQ THEN EXISTS_TAC `N:num` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[];
    SIMP_TAC[]]);;

let SNAPPY_MOD_BYTES_EQ = prove
 (`!x y j. x MOD 2 EXP (8 * j) = y MOD 2 EXP (8 * j) <=>
           !i. i < j ==> (x DIV 2 EXP (8 * i)) MOD 2 EXP 8 =
                         (y DIV 2 EXP (8 * i)) MOD 2 EXP 8`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1; LT]; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `8 * SUC j = 8 * j + 8`; EXP_ADD; MOD_MULT_MOD] THEN
  MP_TAC(SPECL [`2 EXP (8 * j)`; `x MOD 2 EXP (8 * j)`;
                `(x DIV 2 EXP (8 * j)) MOD 2 EXP 8`; `y MOD 2 EXP (8 * j)`;
                `(y DIV 2 EXP (8 * j)) MOD 2 EXP 8`] SNAPPY_DIGIT_UNIQ_ALT) THEN
  REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `i < SUC j <=> i < j \/ i = j`] THEN MESON_TAC[]);;

let SNAPPY_MLEN_SHIFT = prove
 (`!j (src:byte list) a b k.
     (!i. i < j ==> EL (a + i) src = EL (b + i) src)
     ==> snappy_mlen (j + k) src a b = j + snappy_mlen k src (a + j) (b + j)`,
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[snappy_mlen] THEN
  FIRST_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[ADD_CLAUSES; LT_0] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SUC_INJ] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`src:byte list`; `a + 1`; `b + 1`; `k:num`]) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i + 1`) THEN
    ASM_REWRITE_TAC[ARITH_RULE `i + 1 < SUC j <=> i < j`] THEN
    REWRITE_TAC[ARITH_RULE `x + i + 1 = (x + 1) + i`];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ARITH_RULE `(x + 1) + j = SUC(x + j)`]]);;

(* The bytes of the 64-bit loads at a and b agree for i < 8.               *)

let SNAPPY_LOAD64_EQ_BYTES = prove
 (`!(src:byte list) a b.
     a + 8 <= LENGTH src /\ b + 8 <= LENGTH src
     ==> (snappy_load64 src a = snappy_load64 src b <=>
          !i. i < 8 ==> EL (a + i) src = EL (b + i) src)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`snappy_load64 src a`; `snappy_load64 src b`; `8`]
         SNAPPY_MOD_BYTES_EQ) THEN
  REWRITE_TAC[ARITH_RULE `8 * 8 = 64`] THEN
  SIMP_TAC[MOD_LT; SNAPPY_LOAD64_BOUND] THEN
  DISCH_THEN SUBST1_TAC THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SNAPPY_LOAD64_BYTE; ARITH_RULE
   `x + 8 <= n /\ i < 8 ==> x + i < n`] THEN
  REWRITE_TAC[VAL_EQ]);;

let SNAPPY_MATCH_LENGTH_EQ8 = prove
 (`!(src:byte list) a b.
     a + 8 <= LENGTH src /\ b + 8 <= LENGTH src /\
     snappy_load64 src a = snappy_load64 src b
     ==> snappy_match_length src a b =
         8 + snappy_match_length src (a + 8) (b + 8)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[SNAPPY_LOAD64_EQ_BYTES] THEN DISCH_TAC THEN
  REWRITE_TAC[snappy_match_length] THEN
  SUBGOAL_THEN `LENGTH(src:byte list) - b = 8 + (LENGTH src - (b + 8))`
   SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SNAPPY_MLEN_SHIFT THEN ASM_REWRITE_TAC[]);;

(* Exclusive or and the low bits.                                           *)

let SNAPPY_VAL_MOD_EQ_BITS = prove
 (`!(x:int64) (y:int64) k. val x MOD 2 EXP k = val y MOD 2 EXP k <=>
                   !i. i < k ==> (bit i x <=> bit i y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_WORD_AND_MASK_WORD; VAL_EQ] THEN
  REWRITE_TAC[WORD_EQ_BITS_ALT; BIT_WORD_AND; BIT_MASK_WORD; DIMINDEX_64] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  ASM_CASES_TAC `i < 64` THEN ASM_CASES_TAC `i < k` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[BIT_TRIVIAL; DIMINDEX_64; GSYM NOT_LT]);;

let SNAPPY_XOR_MOD_EQ_0 = prove
 (`!(x:int64) (y:int64) k. val(word_xor x y) MOD 2 EXP k = 0 <=>
                   val x MOD 2 EXP k = val y MOD 2 EXP k`,
  REWRITE_TAC[SNAPPY_VAL_MOD_EQ_BITS; GSYM LOWER_BITS_ZERO;
              BIT_WORD_XOR_ALT; NOT_CLAUSES]);;

(* The case of a difference in the 8 bytes is proved with the copies of    *)
(* FindMatchLengthPlain (compress_fragment_double_hash_fml_proof.ml).      *)

(* ------------------------------------------------------------------------- *)
(* Steps of the model in the proofs of the pieces of code.                   *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_CSTATE_INJ = injectivity "snappy_cstate";;

let SNAPPY_CF2_REACH_STEP_EQ = prove
 (`!(src:byte list) st st'.
     snappy_cf2_reach src st /\ snappy_cf2_step src st = st'
     ==> snappy_cf2_reach src st'`,
  MESON_TAC[SNAPPY_CF2_REACH_STEP]);;

let SNAPPY_TBOUND_16 = prove
 (`!t b k. snappy_tbound t b /\ b < 65536 ==> !j. j < k ==> t j < 65536`,
  REWRITE_TAC[snappy_tbound] THEN MESON_TAC[LET_TRANS]);;

let SNAPPY_HASH4_LT = prove
 (`!ts v. ~(ts = 0) ==> snappy_hash4 ts v < ts`,
  SIMP_TAC[snappy_hash4; MOD_LT_EQ]);;

let SNAPPY_HASH8_LT = prove
 (`!ts v. ~(ts = 0) ==> snappy_hash8 ts v < ts`,
  SIMP_TAC[snappy_hash8; MOD_LT_EQ]);;

let SNAPPY_HASH4_WORD = prove
 (`!ts d. snappy_pow2 ts /\ ts <= 16384 /\ d < 2 EXP 64
          ==> word_zx (word_and (word_zx (word (2 * (ts - 1)):int64):int32)
                (word_ushr (word (0 + 2654435761 *
                                      val (word_zx (word d:int64):int32)))
                           17)):int64 =
              word(2 * snappy_hash4 ts (d MOD 2 EXP 32))`,
  REWRITE_TAC[snappy_pow2] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `word_zx (word (2 * (2 EXP k - 1)):int64):int32 =
                word (2 * (2 EXP k - 1))` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
                DIMINDEX_64; MOD_MOD_EXP_MIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SNAPPY_TABLE_MASK] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_USHR;
              DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[snappy_hash4; ADD_CLAUSES; DIV_DIV] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `!y. 2 * y MOD 2 EXP k < 4294967296`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT (SPEC_ALL th)]) THEN
  GEN_TAC THEN MATCH_MP_TAC(ARITH_RULE
   `x < 2 EXP k /\ 2 EXP k <= 16384 ==> 2 * x < 4294967296`) THEN
  ASM_REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* The output region: bytes appended after the bytes emitted so far.         *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_NUM_OF_BYTELIST_APPEND = prove
 (`!(l1:byte list) l2.
     num_of_bytelist(APPEND l1 l2) =
     num_of_bytelist l1 + 2 EXP (8 * LENGTH l1) * num_of_bytelist l2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; num_of_bytelist; LENGTH; MULT_CLAUSES; EXP;
                  ADD_CLAUSES] THEN
  REWRITE_TAC[EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC NUM_RING);;

let SNAPPY_OUT_APPEND = prove
 (`!(m:(S,int64->byte)component) op (out:byte list) d s.
     read (m :> bytes(op,LENGTH out)) s = num_of_bytelist out /\
     read (m :> bytes(word_add op (word(LENGTH out)),LENGTH d)) s =
     num_of_bytelist d
     ==> read (m :> bytes(op,LENGTH(APPEND out d))) s =
         num_of_bytelist(APPEND out d)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; SNAPPY_NUM_OF_BYTELIST_APPEND;
                  READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXP_MULT] THEN
  CONV_TAC NUM_REDUCE_CONV);;
