(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The top-level properties of the compressor models: for inputs of fewer    *)
(* than 2^32 bytes and levels 1 and 2, the output decodes to the input       *)
(* (SNAPPY_COMPRESS_ROUNDTRIP) and is no longer than MaxCompressedLength     *)
(* (SNAPPY_COMPRESS_LENGTH).                                                 *)
(*                                                                           *)
(* The round trip is factored through snappy_encodes tags d: "the complete   *)
(* tags tags decode to the bytes d, after any output and before any further  *)
(* input". The compressors' invariants only say that the bytes emitted so   *)
(* far encode the input consumed so far, with candidate matches that really *)
(* match; the heuristics (skipping, hash tables, backtracking) only matter   *)
(* through the facts that table entries are earlier positions.              *)
(* ========================================================================= *)

needs "common/snappy/snappy_compress.ml";;

(* ------------------------------------------------------------------------- *)
(* List lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_SUB_LIST_APPEND_LEFT = prove
 (`!(x:A list) r n. n <= LENGTH x ==> SUB_LIST(0,n) (APPEND x r) = SUB_LIST(0,n) x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; LENGTH] THENL
   [SIMP_TAC[ARITH_RULE `n <= 0 <=> n = 0`; SUB_LIST_CLAUSES]; ALL_TAC] THEN
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[SUB_LIST_CLAUSES; LE_SUC]);;

let SNAPPY_SUB_LIST_APPEND_RIGHT = prove
 (`!(x:A list) r n. SUB_LIST(LENGTH x,n) (APPEND x r) = SUB_LIST(0,n) r`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; LENGTH; SUB_LIST_CLAUSES]);;

let SNAPPY_SUB_LIST_LENGTH_APPEND = prove
 (`!(x:A list) r. SUB_LIST(0,LENGTH x) (APPEND x r) = x /\
                  SUB_LIST(LENGTH x,LENGTH(APPEND x r) - LENGTH x) (APPEND x r) = r`,
  SIMP_TAC[SNAPPY_SUB_LIST_APPEND_LEFT; LE_REFL; SUB_LIST_LENGTH;
           SNAPPY_SUB_LIST_APPEND_RIGHT; LENGTH_APPEND; ADD_SUB2]);;

let SNAPPY_SUB_LIST_SNOC = prove
 (`!(l:A list) p. p < LENGTH l
                  ==> SUB_LIST(0,p + 1) l = APPEND (SUB_LIST(0,p) l) [EL p l]`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM ADD1]) THEN
  INDUCT_TAC THEN
  REWRITE_TAC[GSYM ADD1; SUB_LIST_CLAUSES; APPEND; EL; HD; TL; LT_SUC;
              LENGTH] THEN
  ASM_SIMP_TAC[]);;

let SNAPPY_SUB_LIST_TRANS = prove
 (`!(l:A list) a b c. a <= b /\ b <= c
        ==> SUB_LIST(0,c) l = APPEND (SUB_LIST(0,b) l) (SUB_LIST(b,c - b) l)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c = b + (c - b)` (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th])
  THENL [ASM_ARITH_TAC; REWRITE_TAC[SUB_LIST_SPLIT; ADD_CLAUSES]]);;

(* ------------------------------------------------------------------------- *)
(* Composition of tag steps.                                                 *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_STEPS_ADD = prove
 (`!j k m s. snappy_steps (j + k) m s =
             snappy_bind (snappy_steps j m s) (snappy_steps k m)`,
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; snappy_steps; snappy_bind] THEN
  REPEAT GEN_TAC THEN
  SPEC_TAC(`snappy_tag_step m (FST(s:byte list#byte list)) (SND s)`,
           `r:(byte list#byte list)option`) THEN
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:(byte list#byte list)option` (cases "option")) THEN
  ASM_REWRITE_TAC[snappy_bind]);;

let SNAPPY_STEPS_1 = prove
 (`!m (inp:byte list) out. snappy_steps 1 m (inp,out) = snappy_tag_step m inp out`,
  REPEAT GEN_TAC THEN REWRITE_TAC[num_CONV `1`; snappy_steps; FST; SND] THEN
  SPEC_TAC(`snappy_tag_step m inp out`,`r:(byte list#byte list)option`) THEN
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:(byte list#byte list)option` (cases "option")) THEN
  REWRITE_TAC[snappy_bind; snappy_steps]);;

let SNAPPY_STEPS_TRANS = prove
 (`!m s1 s2 s3. (?j. snappy_steps j m s1 = SOME s2) /\
                (?k. snappy_steps k m s2 = SOME s3)
                ==> ?k. snappy_steps k m s1 = SOME s3`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `j + k:num` THEN
  ASM_REWRITE_TAC[SNAPPY_STEPS_ADD; snappy_bind]);;

(* ------------------------------------------------------------------------- *)
(* The emitted tags decode as intended.                                      *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_VAL_WORD_BYTE = prove
 (`!n. n < 256 ==> val(word n:byte) = n`,
  SIMP_TAC[VAL_WORD; DIMINDEX_8; MOD_LT; ARITH_RULE `2 EXP 8 = 256`]);;

let SNAPPY_DIVMOD_TAC =
  REPEAT GEN_TAC THEN TRY DISCH_TAC THEN MATCH_MP_TAC DIVMOD_UNIQ THEN
  ASM_ARITH_TAC;;

let SNAPPY_DIVMOD_4 = prove
 (`!n. (4 * n) DIV 4 = n /\ (4 * n) MOD 4 = 0`, SNAPPY_DIVMOD_TAC);;

let SNAPPY_DIVMOD_COPY1 = prove
 (`!a b. (1 + 4 * b + 32 * a) DIV 4 = b + 8 * a /\
         (1 + 4 * b + 32 * a) MOD 4 = 1`, SNAPPY_DIVMOD_TAC);;

let SNAPPY_DIVMOD_8 = prove
 (`!a b. b < 8 ==> (b + 8 * a) DIV 8 = a /\ (b + 8 * a) MOD 8 = b`,
  SNAPPY_DIVMOD_TAC);;

let SNAPPY_DIVMOD_COPY2 = prove
 (`!b. (2 + 4 * b) DIV 4 = b /\ (2 + 4 * b) MOD 4 = 2`, SNAPPY_DIVMOD_TAC);;

let SNAPPY_DIV_MOD_256 = prove
 (`!x. 256 * (x DIV 256) + x MOD 256 = x /\ x MOD 256 + 256 * (x DIV 256) = x`,
  GEN_TAC THEN MP_TAC(SPECL [`x:num`; `256`] DIVISION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let SNAPPY_SUB_LIST_PAIR = prove
 (`!(a:A) b r. SUB_LIST(0,2) (APPEND [a;b] r) = [a;b] /\
               SUB_LIST(2,LENGTH(APPEND [a;b] r) - 2) (APPEND [a;b] r) = r /\
               LENGTH(APPEND [a;b] r) = LENGTH r + 2`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`[a:A;b]`; `r:A list`] SNAPPY_SUB_LIST_LENGTH_APPEND) THEN
  REWRITE_TAC[LENGTH; LENGTH_APPEND; ARITH_RULE `SUC(SUC 0) = 2`] THEN
  SIMP_TAC[] THEN ARITH_TAC);;

let SNAPPY_LITERAL_APPEND = prove
 (`!m (d:byte list) rest out.
        LENGTH out + LENGTH d <= m
        ==> snappy_literal m (LENGTH d) (APPEND d rest) out =
            SOME(rest,APPEND out d)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[snappy_literal; SNAPPY_SUB_LIST_LENGTH_APPEND] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LE_ADD]);;

let SNAPPY_TAG_STEP_EMIT_LITERAL = prove
 (`!m (d:byte list) rest out.
        1 <= LENGTH d /\ LENGTH d <= 2 EXP 32 /\ LENGTH out + LENGTH d <= m
        ==> snappy_tag_step m (APPEND (snappy_emit_literal d) rest) out =
            SOME(rest,APPEND out d)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[snappy_emit_literal] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `n = LENGTH(d:byte list) - 1` THEN
  SUBGOAL_THEN `LENGTH(d:byte list) = n + 1` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[APPEND; snappy_tag_step] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_SIMP_TAC[SNAPPY_VAL_WORD_BYTE; ARITH_RULE `n < 60 ==> 4 * n < 256`] THEN
    REWRITE_TAC[SNAPPY_DIVMOD_4] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> lhand(concl th) = `LENGTH(d:byte list)`)) THEN
    MATCH_MP_TAC SNAPPY_LITERAL_APPEND THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c = if n < 256 then 1 else if n < 65536 then 2
                  else if n < 2 EXP 24 then 3 else 4` THEN
  SUBGOAL_THEN `1 <= c /\ c <= 4 /\ n < 256 EXP c` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN
    REPEAT(COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
           ASM_REWRITE_TAC[]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `LENGTH(d:byte list) = n + 1`)) THEN
  REWRITE_TAC[APPEND; snappy_tag_step] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[SNAPPY_VAL_WORD_BYTE; ARITH_RULE `c <= 4 ==> 4 * (59 + c) < 256`] THEN
  REWRITE_TAC[SNAPPY_DIVMOD_4] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= c ==> ~(59 + c < 60)`; ADD_SUB2] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  MP_TAC(ISPECL [`bytelist_of_num c n:byte list`; `APPEND (d:byte list) rest`]
    SNAPPY_SUB_LIST_LENGTH_APPEND) THEN
  REWRITE_TAC[LENGTH_BYTELIST_OF_NUM] THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_BYTELIST_OF_NUM;
              ARITH_RULE `~(c + x < c)`] THEN
  ASM_SIMP_TAC[NUM_OF_BYTELIST_OF_NUM; MOD_LT] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SNAPPY_LITERAL_APPEND THEN ASM_REWRITE_TAC[]);;

let SNAPPY_TAG_STEP_EMIT_COPY64 = prove
 (`!m off len (rest:byte list) out.
        4 <= len /\ len <= 64 /\ 1 <= off /\ off <= LENGTH out /\ off < 65536 /\
        LENGTH out + len <= m
        ==> snappy_tag_step m (APPEND (snappy_emit_copy64 off len) rest) out =
            SOME(rest,snappy_copy off len out)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[snappy_emit_copy64] THEN
  COND_CASES_TAC THEN FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THENL
   [SUBGOAL_THEN `off DIV 256 < 8 /\ len - 4 < 8` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[APPEND; snappy_tag_step] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    ASM_SIMP_TAC[SNAPPY_VAL_WORD_BYTE; MOD_LT_EQ; ARITH_EQ;
      ARITH_RULE `a < 8 /\ b < 8 ==> 1 + 4 * b + 32 * a < 256`] THEN
    ASM_SIMP_TAC[SNAPPY_DIVMOD_COPY1; SNAPPY_DIVMOD_8; ARITH_EQ] THEN
    REWRITE_TAC[LENGTH; HD; TL; ARITH_RULE `~(SUC n < 1)`] THEN
    ASM_SIMP_TAC[SNAPPY_VAL_WORD_BYTE; MOD_LT_EQ; ARITH_EQ] THEN
    REWRITE_TAC[SNAPPY_DIV_MOD_256; snappy_copy_tag] THEN
    ASM_SIMP_TAC[ARITH_RULE `4 <= len ==> len - 4 + 4 = len`];
    ALL_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[APPEND] THEN REWRITE_TAC[snappy_tag_step] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[SNAPPY_VAL_WORD_BYTE; ARITH_RULE `len <= 64 ==> 2 + 4 * (len - 1) < 256`] THEN
  REWRITE_TAC[SNAPPY_DIVMOD_COPY2; ARITH_EQ; SNAPPY_SUB_LIST_PAIR] THEN
  REWRITE_TAC[ARITH_RULE `~(n + 2 < 2)`; num_of_bytelist] THEN
  ASM_SIMP_TAC[VAL_WORD; DIMINDEX_8; ARITH_RULE `2 EXP 8 = 256`; MOD_MOD_REFL;
               ARITH_RULE `off < 65536 ==> off DIV 256 < 256`; MOD_LT] THEN
  REWRITE_TAC[snappy_copy_tag; MULT_CLAUSES; ADD_CLAUSES; SNAPPY_DIV_MOD_256] THEN
  ASM_SIMP_TAC[ARITH_RULE `4 <= len ==> len - 1 + 1 = len`]);;

let SNAPPY_STEPS_EMIT_COPY = prove
 (`!m off len (rest:byte list) out.
        4 <= len /\ 1 <= off /\ off <= LENGTH out /\ off < 65536 /\
        LENGTH out + len <= m
        ==> ?k. snappy_steps k m (APPEND (snappy_emit_copy off len) rest,out) =
                SOME(rest,snappy_copy off len out)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `len:num` THEN
  DISCH_TAC THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[snappy_emit_copy] THEN
  ASM_CASES_TAC `68 <= len` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `len - 64`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`rest:byte list`; `snappy_copy off 64 (out:byte list)`]) THEN
    REWRITE_TAC[LENGTH_SNAPPY_COPY] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN EXISTS_TAC `1 + k` THEN
    ASM_SIMP_TAC[SNAPPY_STEPS_ADD; SNAPPY_STEPS_1; GSYM APPEND_ASSOC;
                 SNAPPY_TAG_STEP_EMIT_COPY64; LE_REFL;
                 ARITH_RULE `4 <= 64 /\ 64 <= 64`;
                 ARITH_RULE `68 <= len /\ a + len <= m ==> a + 64 <= m`] THEN
    ASM_REWRITE_TAC[snappy_bind; GSYM SNAPPY_COPY_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `68 <= len ==> 64 + len - 64 = len`];
    ALL_TAC] THEN
  ASM_CASES_TAC `64 < len` THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `1 + 1` THEN
    ASM_SIMP_TAC[SNAPPY_STEPS_ADD; SNAPPY_STEPS_1; GSYM APPEND_ASSOC;
                 SNAPPY_TAG_STEP_EMIT_COPY64; LE_REFL;
                 ARITH_RULE `4 <= 60 /\ 60 <= 64`;
                 ARITH_RULE `64 < len /\ a + len <= m ==> a + 60 <= m`] THEN
    REWRITE_TAC[snappy_bind; SNAPPY_STEPS_1] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SNAPPY_TAG_STEP_EMIT_COPY64 o lhand o snd) THEN
    REWRITE_TAC[LENGTH_SNAPPY_COPY] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM SNAPPY_COPY_ADD] THEN
    ASM_SIMP_TAC[ARITH_RULE `64 < len ==> 60 + len - 60 = len`];
    EXISTS_TAC `1` THEN REWRITE_TAC[SNAPPY_STEPS_1] THEN
    MATCH_MP_TAC SNAPPY_TAG_STEP_EMIT_COPY64 THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* snappy_encodes tags d: the tags are complete and decode to d, after any   *)
(* output o0 (the copies refer only to d) and before any further input.      *)
(* ------------------------------------------------------------------------- *)

let snappy_encodes = new_definition
 `snappy_encodes (tags:byte list) (d:byte list) <=>
    !m o0 rest. LENGTH o0 + LENGTH d <= m
                ==> ?k. snappy_steps k m (APPEND tags rest,o0) =
                        SOME(rest,APPEND o0 d)`;;

let SNAPPY_ENCODES_NIL = prove
 (`snappy_encodes [] []`,
  REWRITE_TAC[snappy_encodes; APPEND; APPEND_NIL] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[snappy_steps]);;

let SNAPPY_ENCODES_APPEND = prove
 (`!t1 d1 t2 d2. snappy_encodes t1 d1 /\ snappy_encodes t2 d2
                 ==> snappy_encodes (APPEND t1 t2) (APPEND d1 d2)`,
  REWRITE_TAC[snappy_encodes; LENGTH_APPEND] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `APPEND (o0:byte list) d1`; `rest:byte list`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `o0:byte list`; `APPEND (t2:byte list) rest`]) THEN
  REWRITE_TAC[LENGTH_APPEND] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `j:num`)] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `k:num`)] THEN
  EXISTS_TAC `j + k:num` THEN
  ASM_REWRITE_TAC[SNAPPY_STEPS_ADD; GSYM APPEND_ASSOC; snappy_bind]);;

let SNAPPY_ENCODES_LITERAL = prove
 (`!d:byte list. 1 <= LENGTH d /\ LENGTH d <= 2 EXP 32
                 ==> snappy_encodes (snappy_emit_literal d) d`,
  REWRITE_TAC[snappy_encodes] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `1` THEN ASM_SIMP_TAC[SNAPPY_STEPS_1; SNAPPY_TAG_STEP_EMIT_LITERAL]);;

let SNAPPY_COPY_APPEND = prove
 (`!off n (o0:byte list) d.
        off <= LENGTH d
        ==> snappy_copy off n (APPEND o0 d) = APPEND o0 (snappy_copy off n d)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[snappy_copy] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `EL (LENGTH(APPEND o0 d) - off) (APPEND o0 d) =
                EL (LENGTH d - off) (d:byte list)` SUBST1_TAC THENL
   [REWRITE_TAC[EL_APPEND; LENGTH_APPEND] THEN
    ASM_SIMP_TAC[ARITH_RULE `off <= d ==> ~((a + d) - off < a)`] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[GSYM APPEND_ASSOC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC]);;

let SNAPPY_ENCODES_COPY = prove
 (`!t d off len.
        snappy_encodes t d /\ 4 <= len /\ 1 <= off /\ off <= LENGTH d /\
        off < 65536
        ==> snappy_encodes (APPEND t (snappy_emit_copy off len))
                           (snappy_copy off len d)`,
  REWRITE_TAC[snappy_encodes; LENGTH_SNAPPY_COPY] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `o0:byte list`;
    `APPEND (snappy_emit_copy off len) rest`]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `j:num`)] THEN
  MP_TAC(SPECL [`m:num`; `off:num`; `len:num`; `rest:byte list`;
                `APPEND (o0:byte list) d`] SNAPPY_STEPS_EMIT_COPY) THEN
  REWRITE_TAC[LENGTH_APPEND] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `k:num`)] THEN
  EXISTS_TAC `j + k:num` THEN
  ASM_REWRITE_TAC[SNAPPY_STEPS_ADD; GSYM APPEND_ASSOC; snappy_bind] THEN
  ASM_SIMP_TAC[SNAPPY_COPY_APPEND]);;

(* A copy whose source really matches extends the decoded prefix.            *)

let SNAPPY_COPY_FROM_SOURCE = prove
 (`!(src:byte list) len ip cand.
        cand < ip /\ ip + len <= LENGTH src /\
        (!t. t < len ==> EL (cand + t) src = EL (ip + t) src)
        ==> snappy_copy (ip - cand) len (SUB_LIST(0,ip) src) =
            SUB_LIST(0,ip + len) src`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[snappy_copy; ADD_CLAUSES]; ALL_TAC] THEN
  REWRITE_TAC[snappy_copy] THEN MAP_EVERY X_GEN_TAC [`ip:num`; `cand:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "m"))) THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(0,ip) (src:byte list)) = ip` SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `APPEND (SUB_LIST(0,ip) src) [EL (ip - (ip - cand)) (SUB_LIST(0,ip) src)] =
                SUB_LIST(0,ip + 1) (src:byte list)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SNAPPY_SUB_LIST_SNOC; ARITH_RULE `ip + SUC len <= n ==> ip < n`] THEN
    REWRITE_TAC[APPEND_LCANCEL; CONS_11] THEN
    ASM_SIMP_TAC[ARITH_RULE `cand < ip ==> ip - (ip - cand) = cand`] THEN
    MP_TAC(ISPECL [`src:byte list`; `0`; `ip:num`; `cand:num`] SNAPPY_EL_SUB_LIST) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "m" (MP_TAC o SPEC `0`) THEN REWRITE_TAC[ADD_CLAUSES; LT_0];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ip + 1`; `cand + 1`]) THEN
  ASM_SIMP_TAC[ARITH_RULE `cand < ip ==> (ip + 1) - (cand + 1) = ip - cand`] THEN
  REWRITE_TAC[ARITH_RULE `(x + 1) + t = x + SUC t`] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  USE_THEN "m" MATCH_MP_TAC THEN ASM_REWRITE_TAC[LT_SUC]);;

(* The varint header.                                                        *)

let SNAPPY_VARINT_FROM_ENCODE = prove
 (`!k n (r:byte list).
        1 <= k /\ n < 2 EXP (7 * k - 3)
        ==> snappy_varint_from k (APPEND (snappy_varint_encode n) r) = SOME(n,r)`,
  INDUCT_TAC THEN REWRITE_TAC[ARITH_RULE `~(1 <= 0)`] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[snappy_varint_encode] THEN
  ASM_CASES_TAC `k = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
    ASM_SIMP_TAC[ARITH_RULE `n < 16 ==> n < 128`; APPEND; snappy_varint_from;
                 SNAPPY_VAL_WORD_BYTE; ARITH_RULE `n < 16 ==> n < 256`];
    ALL_TAC] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[APPEND; snappy_varint_from; SNAPPY_VAL_WORD_BYTE;
               ARITH_RULE `n < 128 ==> n < 256`] THEN
  SUBGOAL_THEN `n MOD 128 + 128 < 256` ASSUME_TAC THENL
   [MP_TAC(SPECL [`n:num`; `128`] MOD_LT_EQ) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SNAPPY_VAL_WORD_BYTE; ARITH_RULE `~(x + 128 < 128)`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n DIV 128`; `r:byte list`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    UNDISCH_TAC `n < 2 EXP (7 * SUC k - 3)` THEN
    SUBGOAL_THEN `7 * SUC k - 3 = (7 * k - 3) + 7` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[EXP_ADD] THEN ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[snappy_bind; ADD_SUB; option_INJ; PAIR_EQ] THEN
  MP_TAC(SPECL [`n:num`; `128`] DIVISION) THEN ARITH_TAC);;

let SNAPPY_VARINT_ENCODE = prove
 (`!n (r:byte list).
        n < 2 EXP 32
        ==> snappy_varint (APPEND (snappy_varint_encode n) r) = SOME(n,r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[snappy_varint] THEN
  MATCH_MP_TAC SNAPPY_VARINT_FROM_ENCODE THEN
  ASM_REWRITE_TAC[ARITH_RULE `7 * 5 - 3 = 32`] THEN ARITH_TAC);;

let LENGTH_SNAPPY_VARINT_ENCODE = prove
 (`!n. n < 2 EXP 32 ==> LENGTH(snappy_varint_encode n) <= 5`,
  SUBGOAL_THEN
   `!k n. n < 2 EXP (7 * SUC k) ==> LENGTH(snappy_varint_encode n) <= SUC k`
   (fun th -> GEN_TAC THEN DISCH_TAC THEN
              MP_TAC(SPECL [`4`; `n:num`] th) THEN
              ANTS_TAC THENL
               [UNDISCH_TAC `n < 2 EXP 32` THEN CONV_TAC NUM_REDUCE_CONV THEN
                ARITH_TAC;
                CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]]) THEN
  INDUCT_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[snappy_varint_encode] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN TRY ARITH_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[LE_SUC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
  UNDISCH_TAC `n < 2 EXP (7 * SUC(SUC k))` THEN
  REWRITE_TAC[ARITH_RULE `7 * SUC(SUC k) = 7 * SUC k + 7`; EXP_ADD] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Facts about the helpers of the models.                                    *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_LOAD32_EQ = prove
 (`!(src:byte list) a b.
        a + 4 <= LENGTH src /\ b + 4 <= LENGTH src /\
        snappy_load32 src a = snappy_load32 src b
        ==> !t. t < 4 ==> EL (a + t) src = EL (b + t) src`,
  REPEAT GEN_TAC THEN REWRITE_TAC[snappy_load32] THEN STRIP_TAC THEN
  SUBGOAL_THEN `SUB_LIST(a,4) (src:byte list) = SUB_LIST(b,4) src` ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `bytelist_of_num 4 (num_of_bytelist(SUB_LIST(a,4) (src:byte list)))` THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN
      MP_TAC(ISPEC `SUB_LIST(a,4) (src:byte list)` BYTELIST_OF_NUM_OF_BYTELIST) THEN
      REWRITE_TAC[LENGTH_SUB_LIST] THEN
      ASM_SIMP_TAC[ARITH_RULE `a + 4 <= n ==> MIN 4 (n - a) = 4`];
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `SUB_LIST(b,4) (src:byte list)` BYTELIST_OF_NUM_OF_BYTELIST) THEN
      REWRITE_TAC[LENGTH_SUB_LIST] THEN
      ASM_SIMP_TAC[ARITH_RULE `a + 4 <= n ==> MIN 4 (n - a) = 4`]];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`src:byte list`; `a:num`; `4`; `t:num`] SNAPPY_EL_SUB_LIST) THEN
    MP_TAC(ISPECL [`src:byte list`; `b:num`; `4`; `t:num`] SNAPPY_EL_SUB_LIST) THEN
    ASM_SIMP_TAC[ARITH_RULE `t < 4 /\ a + 4 <= n ==> a + t < n`]]);;

let SNAPPY_MLEN_MATCH = prove
 (`!k (src:byte list) a b t.
        t < snappy_mlen k src a b ==> EL (a + t) src = EL (b + t) src`,
  INDUCT_TAC THEN REWRITE_TAC[snappy_mlen; CONJUNCT1 LT] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[CONJUNCT1 LT] THEN
  STRUCT_CASES_TAC(SPEC `t:num` num_CASES) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; LT_SUC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`src:byte list`; `a + 1`; `b + 1`; `n:num`]) THEN
  ASM_REWRITE_TAC[ARITH_RULE `(a + 1) + n = SUC(a + n)`]);;

let SNAPPY_MLEN_LE = prove
 (`!k (src:byte list) a b. snappy_mlen k src a b <= k`,
  INDUCT_TAC THEN REWRITE_TAC[snappy_mlen; LE_REFL] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LE_SUC; LE_0]);;

let SNAPPY_MATCH_LENGTH = prove
 (`!(src:byte list) a b.
        b + snappy_match_length src a b <= LENGTH src \/ LENGTH src < b`,
  REWRITE_TAC[snappy_match_length] THEN REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`LENGTH(src:byte list) - b`; `src:byte list`; `a:num`; `b:num`]
    SNAPPY_MLEN_LE) THEN ARITH_TAC);;

let SNAPPY_MATCH_LENGTH_MATCH = prove
 (`!(src:byte list) a b t.
        t < snappy_match_length src a b ==> EL (a + t) src = EL (b + t) src`,
  REWRITE_TAC[snappy_match_length; SNAPPY_MLEN_MATCH]);;

let LENGTH_SNAPPY_EMIT_LITERAL = prove
 (`!d:byte list.
        1 <= LENGTH d /\ LENGTH d <= 2 EXP 32
        ==> LENGTH(snappy_emit_literal d) <= LENGTH d + 1 + LENGTH d DIV 30`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[snappy_emit_literal] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[LENGTH; LENGTH_APPEND; LENGTH_BYTELIST_OF_NUM] THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[LENGTH; LENGTH_APPEND;
                                         LENGTH_BYTELIST_OF_NUM]) THEN
  ASM_ARITH_TAC);;

let LENGTH_SNAPPY_EMIT_COPY = prove
 (`!off len. 4 <= len ==> LENGTH(snappy_emit_copy off len) + 1 <= len`,
  GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `len:num` THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[snappy_emit_copy] THEN
  REWRITE_TAC[snappy_emit_copy64] THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[LENGTH; LENGTH_APPEND]) THEN
  TRY ARITH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `len - 64`) THEN ASM_ARITH_TAC);;

let SNAPPY_CRUN_ADD = prove
 (`!step a b s. snappy_crun step (a + b) s = snappy_crun step b (snappy_crun step a s)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[snappy_crun; ADD_CLAUSES]);;

let SNAPPY_CRUN_FIX = prove
 (`!step k s. step s = s ==> snappy_crun step k s = s`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[snappy_crun]);;

(* An invariant and a potential give the result of a run: once the state is  *)
(* final (a fixed point of step), any longer run gives the same state.      *)

let SNAPPY_CRUN_TERMINATES = prove
 (`!step (inv:snappy_cstate->bool) pot fin.
        (!s. inv s /\ fin s ==> step s = s) /\
        (!s. inv s /\ ~fin s ==> inv(step s) /\ pot(step s) < pot s)
        ==> !k s. inv s /\ pot s <= k
                  ==> inv(snappy_crun step k s) /\ fin(snappy_crun step k s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fix") (LABEL_TAC "dec")) THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[snappy_crun] THEN
  ASM_CASES_TAC `(fin:snappy_cstate->bool) s` THEN ASM_REWRITE_TAC[] THENL
   [USE_THEN "dec" (MP_TAC o SPEC `s:snappy_cstate`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(pot:snappy_cstate->num) s <= 0` THEN ARITH_TAC;
    USE_THEN "fix" (MP_TAC o SPEC `s:snappy_cstate`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SIMP_TAC[SNAPPY_CRUN_FIX] THEN ASM_REWRITE_TAC[];
    USE_THEN "dec" (MP_TAC o SPEC `s:snappy_cstate`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(pot:snappy_cstate->num) s <= SUC k` THEN
    UNDISCH_TAC `(pot:snappy_cstate->num) (step s) < pot s` THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The steps of the invariants shared by both levels.                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_LIT_STEP = prove
 (`!(src:byte list) out ne ip.
        snappy_encodes out (SUB_LIST(0,ne) src) /\
        LENGTH out <= ne + ne DIV 30 /\
        ne < ip /\ ip <= LENGTH src /\ LENGTH src <= 2 EXP 32
        ==> snappy_encodes (APPEND out (snappy_emit_literal (SUB_LIST(ne,ip - ne) src)))
                           (SUB_LIST(0,ip) src) /\
            LENGTH(APPEND out (snappy_emit_literal (SUB_LIST(ne,ip - ne) src)))
            <= ip + ip DIV 30 + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(ne,ip - ne) (src:byte list)) = ip - ne` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`src:byte list`; `0`; `ne:num`; `ip:num`] SNAPPY_SUB_LIST_TRANS) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC SNAPPY_ENCODES_APPEND THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SNAPPY_ENCODES_LITERAL THEN ASM_ARITH_TAC;
    REWRITE_TAC[LENGTH_APPEND] THEN
    MP_TAC(ISPEC `SUB_LIST(ne,ip - ne) (src:byte list)` LENGTH_SNAPPY_EMIT_LITERAL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ARITH_RULE `ne DIV 30 + (ip - ne) DIV 30 <= (ne + (ip - ne)) DIV 30`) THEN
    REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ARITH_RULE `ne < ip ==> ne + (ip - ne) = ip`] THEN ASM_ARITH_TAC]);;

let SNAPPY_COPY_STEP = prove
 (`!(src:byte list) out ip c m.
        snappy_encodes out (SUB_LIST(0,ip) src) /\
        LENGTH out <= ip + ip DIV 30 + 1 /\
        c < ip /\ ip + m <= LENGTH src /\ LENGTH src <= 65536 /\ 4 <= m /\
        (!t. t < m ==> EL (c + t) src = EL (ip + t) src)
        ==> snappy_encodes (APPEND out (snappy_emit_copy (ip - c) m))
                           (SUB_LIST(0,ip + m) src) /\
            LENGTH(APPEND out (snappy_emit_copy (ip - c) m))
            <= (ip + m) + (ip + m) DIV 30`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`src:byte list`; `m:num`; `ip:num`; `c:num`]
      SNAPPY_COPY_FROM_SOURCE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SNAPPY_ENCODES_COPY THEN ASM_REWRITE_TAC[LENGTH_SUB_LIST] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[LENGTH_APPEND] THEN
    MP_TAC(SPECL [`ip - c:num`; `m:num`] LENGTH_SNAPPY_EMIT_COPY) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ARITH_RULE `ip DIV 30 <= (ip + m) DIV 30`) THEN
    ASM_ARITH_TAC]);;

let SNAPPY_MATCH4 = prove
 (`!(src:byte list) c ip.
        c < ip /\ ip + 4 <= LENGTH src /\
        snappy_load32 src c = snappy_load32 src ip
        ==> ip + 4 + snappy_match_length src (c + 4) (ip + 4) <= LENGTH src /\
            !t. t < 4 + snappy_match_length src (c + 4) (ip + 4)
                ==> EL (c + t) src = EL (ip + t) src`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`src:byte list`; `c + 4`; `ip + 4`] SNAPPY_MATCH_LENGTH) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `t:num` THEN DISCH_TAC THEN ASM_CASES_TAC `t < 4` THENL
   [MP_TAC(ISPECL [`src:byte list`; `c:num`; `ip:num`] SNAPPY_LOAD32_EQ) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`src:byte list`; `c + 4`; `ip + 4`; `t - 4`]
      SNAPPY_MATCH_LENGTH_MATCH) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(t < 4) ==> (a + 4) + t - 4 = a + t`]]);;

(* ------------------------------------------------------------------------- *)
(* Bounds on hash table entries.                                             *)
(* ------------------------------------------------------------------------- *)

let snappy_tbound = new_definition
 `snappy_tbound (t:num->num) b <=> !j. t j <= b`;;

let SNAPPY_TBOUND_ZERO = prove
 (`!b. snappy_tbound (\j. 0) b`,
  REWRITE_TAC[snappy_tbound; LE_0]);;

let SNAPPY_TBOUND_MONO = prove
 (`!t a b. snappy_tbound t a /\ a <= b ==> snappy_tbound t b`,
  REWRITE_TAC[snappy_tbound] THEN MESON_TAC[LE_TRANS]);;

let SNAPPY_TBOUND_TUPD = prove
 (`!t e v b. snappy_tbound t b /\ v <= b ==> snappy_tbound (snappy_tupd t e v) b`,
  REWRITE_TAC[snappy_tbound; snappy_tupd] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let SNAPPY_TBOUND_TUPD_MONO = prove
 (`!t e v a b. snappy_tbound t a /\ a <= b /\ v <= b
               ==> snappy_tbound (snappy_tupd t e v) b`,
  REWRITE_TAC[snappy_tbound; snappy_tupd] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LE_TRANS]);;

let SNAPPY_TBOUND_LOOKUP = prove
 (`!t b e. snappy_tbound t b ==> t e <= b`,
  SIMP_TAC[snappy_tbound]);;

let SNAPPY_DIV32_POS = prove
 (`!sk. 32 <= sk ==> 1 <= sk DIV 32`,
  SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* CompressFragment: invariant and potential.                                *)
(* ------------------------------------------------------------------------- *)

let snappy_cf1_inv = define
 `snappy_cf1_inv (src:byte list) (SnappyCState ph ip ne sk c x t1 t2 out) <=>
   LENGTH src <= 65536 /\
   (ph = 0 /\ snappy_encodes out src /\
    LENGTH out <= LENGTH src + LENGTH src DIV 30 + 1 \/
    ph = 5 /\ ip <= LENGTH src /\ snappy_encodes out (SUB_LIST(0,ip) src) /\
    LENGTH out <= ip + ip DIV 30 \/
    ph = 1 /\ 15 <= LENGTH src /\ ip <= LENGTH src - 15 /\ snappy_tbound t1 ip /\
    snappy_encodes out (SUB_LIST(0,ip) src) /\ LENGTH out <= ip + ip DIV 30 \/
    ph = 6 /\ 15 <= LENGTH src /\ ne + 1 = ip /\ x <= 15 /\
    ip + 16 <= LENGTH src - 15 /\ snappy_tbound t1 ((ip + x) - 1) /\
    snappy_encodes out (SUB_LIST(0,ne) src) /\ LENGTH out <= ne + ne DIV 30 \/
    ph = 2 /\ 15 <= LENGTH src /\ ne < ip /\ ip <= LENGTH src - 14 /\ 32 <= sk /\
    snappy_tbound t1 (ip - 1) /\
    snappy_encodes out (SUB_LIST(0,ne) src) /\ LENGTH out <= ne + ne DIV 30 \/
    ph = 3 /\ 15 <= LENGTH src /\ ne < ip /\ ip <= LENGTH src - 15 /\ c < ip /\
    snappy_load32 src c = snappy_load32 src ip /\ snappy_tbound t1 ip /\
    snappy_encodes out (SUB_LIST(0,ne) src) /\ LENGTH out <= ne + ne DIV 30 \/
    ph = 4 /\ 15 <= LENGTH src /\ ip <= LENGTH src - 15 /\ c < ip /\
    snappy_load32 src c = snappy_load32 src ip /\ snappy_tbound t1 ip /\
    snappy_encodes out (SUB_LIST(0,ip) src) /\
    LENGTH out <= ip + ip DIV 30 + 1)`;;

let snappy_cf1_pot = define
 `snappy_cf1_pot (src:byte list) (SnappyCState ph ip ne sk c x t1 t2 out) =
   if ph = 0 then 0 else if ph = 5 then 1
   else 8 * ((LENGTH src + 17) - (if ph = 6 then ip + x else ip)) +
        (if ph = 1 then 6 else if ph = 6 then 5 else if ph = 2 then 4
         else if ph = 3 then 3 else 2)`;;

let SNAPPY_CF1_INIT = prove
 (`!src:byte list. LENGTH src <= 65536
                   ==> snappy_cf1_inv src (snappy_cf1_init src) /\
                       snappy_cf1_pot src (snappy_cf1_init src) <=
                       snappy_cf_steps_bound (LENGTH src)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[snappy_cf1_init; snappy_cf1_inv; snappy_cf1_pot;
              snappy_cf_steps_bound] THEN
  COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[SUB_LIST_CLAUSES; SNAPPY_ENCODES_NIL; LENGTH; LE_0;
                  SNAPPY_TBOUND_ZERO] THEN
  ASM_ARITH_TAC);;

let SNAPPY_CF1_UNFOLD_TAC =
  REWRITE_TAC[snappy_cf1_step] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV;;

let SNAPPY_CF1_GOAL_TAC =
  REWRITE_TAC[snappy_cf1_inv; snappy_cf1_pot] THEN CONV_TAC NUM_REDUCE_CONV;;

let SNAPPY_CF1_STEP_1 = prove
 (`!(src:byte list) ip ne sk c x t1 t2 out.
     LENGTH src <= 65536 /\ 15 <= LENGTH src /\ ip <= LENGTH src - 15 /\
     snappy_tbound t1 ip /\ snappy_encodes out (SUB_LIST(0,ip) src) /\
     LENGTH out <= ip + ip DIV 30
     ==> let s = SnappyCState 1 ip ne sk c x t1 t2 out in
         snappy_cf1_inv src (snappy_cf1_step src s) /\
         snappy_cf1_pot src (snappy_cf1_step src s) < snappy_cf1_pot src s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SNAPPY_CF1_UNFOLD_TAC THEN COND_CASES_TAC THEN SNAPPY_CF1_GOAL_TAC THEN
  ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC]) THEN
  REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
  MATCH_MP_TAC SNAPPY_TBOUND_MONO THEN EXISTS_TAC `ip:num` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let SNAPPY_CF1_STEP_6 = prove
 (`!(src:byte list) ip ne sk c x t1 t2 out.
     LENGTH src <= 65536 /\ 15 <= LENGTH src /\ ne + 1 = ip /\ x <= 15 /\
     ip + 16 <= LENGTH src - 15 /\ snappy_tbound t1 ((ip + x) - 1) /\
     snappy_encodes out (SUB_LIST(0,ne) src) /\ LENGTH out <= ne + ne DIV 30
     ==> let s = SnappyCState 6 ip ne sk c x t1 t2 out in
         snappy_cf1_inv src (snappy_cf1_step src s) /\
         snappy_cf1_pot src (snappy_cf1_step src s) < snappy_cf1_pot src s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SNAPPY_CF1_UNFOLD_TAC THEN
  ABBREV_TAC `e = snappy_hash1 (snappy_table_size (LENGTH(src:byte list)))
                               (snappy_load32 src (ip + x))` THEN
  SUBGOAL_THEN `(t1:num->num) e <= (ip + x) - 1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SNAPPY_TBOUND_LOOKUP]; ALL_TAC] THEN
  REPEAT(COND_CASES_TAC THEN SNAPPY_CF1_GOAL_TAC THEN ASM_REWRITE_TAC[]) THEN
  (CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC]) THEN
  REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
  MATCH_MP_TAC SNAPPY_TBOUND_TUPD_MONO THEN EXISTS_TAC `(ip + x) - 1` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let SNAPPY_CF1_STEP_2 = prove
 (`!(src:byte list) ip ne sk c x t1 t2 out.
     LENGTH src <= 65536 /\ 15 <= LENGTH src /\ ne < ip /\
     ip <= LENGTH src - 14 /\ 32 <= sk /\ snappy_tbound t1 (ip - 1) /\
     snappy_encodes out (SUB_LIST(0,ne) src) /\ LENGTH out <= ne + ne DIV 30
     ==> let s = SnappyCState 2 ip ne sk c x t1 t2 out in
         snappy_cf1_inv src (snappy_cf1_step src s) /\
         snappy_cf1_pot src (snappy_cf1_step src s) < snappy_cf1_pot src s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SNAPPY_CF1_UNFOLD_TAC THEN
  ABBREV_TAC `e = snappy_hash1 (snappy_table_size (LENGTH(src:byte list)))
                               (snappy_load32 src ip)` THEN
  SUBGOAL_THEN `(t1:num->num) e <= ip - 1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SNAPPY_TBOUND_LOOKUP]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SNAPPY_DIV32_POS) THEN
  REPEAT(COND_CASES_TAC THEN SNAPPY_CF1_GOAL_TAC THEN ASM_REWRITE_TAC[]) THEN
  (CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC]) THEN
  REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
  MATCH_MP_TAC SNAPPY_TBOUND_TUPD_MONO THEN EXISTS_TAC `ip - 1` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let SNAPPY_CF1_STEP_3 = prove
 (`!(src:byte list) ip ne sk c x t1 t2 out.
     LENGTH src <= 65536 /\ 15 <= LENGTH src /\ ne < ip /\
     ip <= LENGTH src - 15 /\ c < ip /\
     snappy_load32 src c = snappy_load32 src ip /\ snappy_tbound t1 ip /\
     snappy_encodes out (SUB_LIST(0,ne) src) /\ LENGTH out <= ne + ne DIV 30
     ==> let s = SnappyCState 3 ip ne sk c x t1 t2 out in
         snappy_cf1_inv src (snappy_cf1_step src s) /\
         snappy_cf1_pot src (snappy_cf1_step src s) < snappy_cf1_pot src s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SNAPPY_CF1_UNFOLD_TAC THEN SNAPPY_CF1_GOAL_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`src:byte list`; `out:byte list`; `ne:num`; `ip:num`]
    SNAPPY_LIT_STEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]] THEN
  ARITH_TAC);;

let SNAPPY_CF1_STEP_4 = prove
 (`!(src:byte list) ip ne sk c x t1 t2 out.
     LENGTH src <= 65536 /\ 15 <= LENGTH src /\ ip <= LENGTH src - 15 /\
     c < ip /\ snappy_load32 src c = snappy_load32 src ip /\
     snappy_tbound t1 ip /\ snappy_encodes out (SUB_LIST(0,ip) src) /\
     LENGTH out <= ip + ip DIV 30 + 1
     ==> let s = SnappyCState 4 ip ne sk c x t1 t2 out in
         snappy_cf1_inv src (snappy_cf1_step src s) /\
         snappy_cf1_pot src (snappy_cf1_step src s) < snappy_cf1_pot src s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SNAPPY_CF1_UNFOLD_TAC THEN
  MP_TAC(ISPECL [`src:byte list`; `c:num`; `ip:num`] SNAPPY_MATCH4) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `m = 4 + snappy_match_length src (c + 4) (ip + 4)` THEN
  REWRITE_TAC[ADD_ASSOC] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`src:byte list`; `out:byte list`; `ip:num`; `c:num`; `m:num`]
    SNAPPY_COPY_STEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `out' = APPEND out (snappy_emit_copy (ip - c) m)` THEN
  ABBREV_TAC `t1' = snappy_tupd t1
      (snappy_hash1 (snappy_table_size (LENGTH(src:byte list)))
                    (snappy_load32 src ((ip + m) - 1))) ((ip + m) - 1)` THEN
  SUBGOAL_THEN `snappy_tbound t1' ((ip + m) - 1)` ASSUME_TAC THENL
   [EXPAND_TAC "t1'" THEN MATCH_MP_TAC SNAPPY_TBOUND_TUPD THEN
    REWRITE_TAC[LE_REFL] THEN MATCH_MP_TAC SNAPPY_TBOUND_MONO THEN
    EXISTS_TAC `ip:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `e = snappy_hash1 (snappy_table_size (LENGTH(src:byte list)))
                               (snappy_load32 src (ip + m))` THEN
  SUBGOAL_THEN `(t1':num->num) e <= (ip + m) - 1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SNAPPY_TBOUND_LOOKUP]; ALL_TAC] THEN
  SUBGOAL_THEN `snappy_tbound (snappy_tupd t1' e (ip + m)) (ip + m)` ASSUME_TAC THENL
   [MATCH_MP_TAC SNAPPY_TBOUND_TUPD THEN REWRITE_TAC[LE_REFL] THEN
    MATCH_MP_TAC SNAPPY_TBOUND_MONO THEN EXISTS_TAC `(ip + m) - 1` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(COND_CASES_TAC THEN SNAPPY_CF1_GOAL_TAC THEN ASM_REWRITE_TAC[]) THEN
  REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
  TRY(CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC));;

let SNAPPY_CF1_STEP_5 = prove
 (`!(src:byte list) ip ne sk c x t1 t2 out.
     LENGTH src <= 65536 /\ ip <= LENGTH src /\
     snappy_encodes out (SUB_LIST(0,ip) src) /\ LENGTH out <= ip + ip DIV 30
     ==> let s = SnappyCState 5 ip ne sk c x t1 t2 out in
         snappy_cf1_inv src (snappy_cf1_step src s) /\
         snappy_cf1_pot src (snappy_cf1_step src s) < snappy_cf1_pot src s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SNAPPY_CF1_UNFOLD_TAC THEN SNAPPY_CF1_GOAL_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [MP_TAC(ISPECL [`src:byte list`; `out:byte list`; `ip:num`;
                   `LENGTH(src:byte list)`] SNAPPY_LIT_STEP) THEN
    REWRITE_TAC[SUB_LIST_LENGTH] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]];
    SUBGOAL_THEN `ip = LENGTH(src:byte list)` SUBST_ALL_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUB_LIST_LENGTH]) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let SNAPPY_CF1_STEP = prove
 (`!(src:byte list) s.
        snappy_cf1_inv src s /\ ~(snappy_phase s = 0)
        ==> snappy_cf1_inv src (snappy_cf1_step src s) /\
            snappy_cf1_pot src (snappy_cf1_step src s) < snappy_cf1_pot src s`,
  GEN_TAC THEN MATCH_MP_TAC snappy_cstate_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`ph:num`; `ip:num`; `ne:num`; `sk:num`; `c:num`; `x:num`;
                       `t1:num->num`; `t2:num->num`; `out:byte list`] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [snappy_cf1_inv] THEN
  REWRITE_TAC[snappy_phase] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) ASSUME_TAC) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
                                                 lhs(concl th) = `ph:num`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_EQ]) THEN
  TRY(FIRST_X_ASSUM CONTR_TAC) THEN
  FIRST(map (fun th -> MATCH_MP_TAC(CONV_RULE(ONCE_DEPTH_CONV let_CONV) th) THEN
                       ASM_REWRITE_TAC[])
            [SNAPPY_CF1_STEP_1; SNAPPY_CF1_STEP_2; SNAPPY_CF1_STEP_3;
             SNAPPY_CF1_STEP_4; SNAPPY_CF1_STEP_5; SNAPPY_CF1_STEP_6]));;

let SNAPPY_CF1_FIX = prove
 (`!(src:byte list) s.
        snappy_phase s = 0 ==> snappy_cf1_step src s = s`,
  GEN_TAC THEN MATCH_MP_TAC snappy_cstate_INDUCT THEN
  REWRITE_TAC[snappy_phase] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN SNAPPY_CF1_UNFOLD_TAC);;

let SNAPPY_CF1_RUN = prove
 (`!(src:byte list) k.
        LENGTH src <= 65536 /\ snappy_cf_steps_bound (LENGTH src) <= k
        ==> snappy_cf1_inv src (snappy_crun (snappy_cf1_step src) k (snappy_cf1_init src)) /\
            snappy_phase (snappy_crun (snappy_cf1_step src) k (snappy_cf1_init src)) = 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`snappy_cf1_step src`; `snappy_cf1_inv src`; `snappy_cf1_pot src`;
                 `\s. snappy_phase s = 0`] SNAPPY_CRUN_TERMINATES) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [SIMP_TAC[SNAPPY_CF1_FIX; SNAPPY_CF1_STEP]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(SPEC `src:byte list` SNAPPY_CF1_INIT) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC LE_TRANS `snappy_cf_steps_bound (LENGTH(src:byte list))` THEN
  ASM_REWRITE_TAC[]);;

let SNAPPY_CF1_DONE = prove
 (`!(src:byte list) s. snappy_cf1_inv src s /\ snappy_phase s = 0
                       ==> snappy_encodes (snappy_out s) src /\
                           LENGTH(snappy_out s) <= LENGTH src + LENGTH src DIV 30 + 1`,
  GEN_TAC THEN MATCH_MP_TAC snappy_cstate_INDUCT THEN
  REWRITE_TAC[snappy_phase; snappy_out; snappy_cf1_inv] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST_ALL_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let SNAPPY_CF1_CORRECT = prove
 (`!src:byte list.
        LENGTH src <= 65536
        ==> snappy_encodes (snappy_compress_fragment 1 src) src /\
            LENGTH(snappy_compress_fragment 1 src)
            <= LENGTH src + LENGTH src DIV 30 + 1`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[snappy_compress_fragment] THEN
  MATCH_MP_TAC SNAPPY_CF1_DONE THEN MATCH_MP_TAC SNAPPY_CF1_RUN THEN
  ASM_REWRITE_TAC[LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* CompressFragmentDoubleHash: invariant and potential.                      *)
(* ------------------------------------------------------------------------- *)

let snappy_matches = new_definition
 `snappy_matches (src:byte list) c ip x <=>
    !t. t < x ==> EL (c + t) src = EL (ip + t) src`;;

let SNAPPY_MATCHES_BACK = prove
 (`!(src:byte list) c ip x.
        snappy_matches src c ip x /\ 0 < c /\ 0 < ip /\
        EL (ip - 1) src = EL (c - 1) src
        ==> snappy_matches src (c - 1) (ip - 1) (x + 1)`,
  REWRITE_TAC[snappy_matches] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `t = 0` THENL
   [ASM_REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < c /\ ~(t = 0) ==> (c - 1) + t = c + (t - 1)`]);;

let SNAPPY_MATCH4_MATCHES = prove
 (`!(src:byte list) c ip.
        c < ip /\ ip + 4 <= LENGTH src /\
        snappy_load32 src c = snappy_load32 src ip
        ==> ip + snappy_match_length src (c + 4) (ip + 4) + 4 <= LENGTH src /\
            snappy_matches src c ip (snappy_match_length src (c + 4) (ip + 4) + 4)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SNAPPY_MATCH4) THEN
  STRIP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[snappy_matches] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `t < a + 4 <=> t < 4 + a`] THEN
  ASM_REWRITE_TAC[]);;

let SNAPPY_MATCH_LENGTH_MATCHES = prove
 (`!(src:byte list) c ip.
        ip <= LENGTH src
        ==> ip + snappy_match_length src c ip <= LENGTH src /\
            snappy_matches src c ip (snappy_match_length src c ip)`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`src:byte list`; `c:num`; `ip:num`] SNAPPY_MATCH_LENGTH) THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[snappy_matches; SNAPPY_MATCH_LENGTH_MATCH]]);;

let SNAPPY_COPY_STEP_MATCHES = prove
 (`!(src:byte list) out ip c m.
        snappy_encodes out (SUB_LIST(0,ip) src) /\
        LENGTH out <= ip + ip DIV 30 + 1 /\
        c < ip /\ ip + m <= LENGTH src /\ LENGTH src <= 65536 /\ 4 <= m /\
        snappy_matches src c ip m
        ==> snappy_encodes (APPEND out (snappy_emit_copy (ip - c) m))
                           (SUB_LIST(0,ip + m) src) /\
            LENGTH(APPEND out (snappy_emit_copy (ip - c) m))
            <= (ip + m) + (ip + m) DIV 30`,
  REWRITE_TAC[snappy_matches; SNAPPY_COPY_STEP]);;

let snappy_cf2_inv = define
 `snappy_cf2_inv (src:byte list) (SnappyCState ph ip ne sk c x t1 t2 out) <=>
   LENGTH src <= 65536 /\
   (ph = 0 /\ snappy_encodes out src /\
    LENGTH out <= LENGTH src + LENGTH src DIV 30 + 1 \/
    ph = 5 /\ ip <= LENGTH src /\ snappy_encodes out (SUB_LIST(0,ip) src) /\
    LENGTH out <= ip + ip DIV 30 \/
    ph = 1 /\ 15 <= LENGTH src /\ ip <= LENGTH src - 15 /\
    snappy_tbound t1 ip /\ snappy_tbound t2 ip /\
    snappy_encodes out (SUB_LIST(0,ip) src) /\ LENGTH out <= ip + ip DIV 30 \/
    ph = 2 /\ 15 <= LENGTH src /\ ne < ip /\ ip <= LENGTH src - 14 /\
    512 <= sk /\ snappy_tbound t1 (ip - 1) /\ snappy_tbound t2 (ip - 1) /\
    snappy_encodes out (SUB_LIST(0,ne) src) /\ LENGTH out <= ne + ne DIV 30 \/
    (ph = 7 \/ ph = 3) /\ 15 <= LENGTH src /\ ne <= ip /\ c < ip /\ 4 <= x /\
    ip + x <= LENGTH src /\ snappy_matches src c ip x /\
    snappy_tbound t1 ((ip + x) - 4) /\ snappy_tbound t2 ((ip + x) - 4) /\
    snappy_encodes out (SUB_LIST(0,ne) src) /\ LENGTH out <= ne + ne DIV 30 \/
    ph = 4 /\ 15 <= LENGTH src /\ c < ip /\ 4 <= x /\
    ip + x <= LENGTH src /\ snappy_matches src c ip x /\
    snappy_tbound t1 ((ip + x) - 1) /\ snappy_tbound t2 ((ip + x) - 1) /\
    snappy_encodes out (SUB_LIST(0,ip) src) /\
    LENGTH out <= ip + ip DIV 30 + 1)`;;

let snappy_cf2_pot = define
 `snappy_cf2_pot (src:byte list) (SnappyCState ph ip ne sk c x t1 t2 out) =
   if ph = 0 then 0 else if ph = 5 then 1
   else if ph = 1 then 16 * ((LENGTH src + 17) - ip) + 3
   else if ph = 2 then 16 * ((LENGTH src + 17) - ip) + (ip - ne) + 2
   else if ph = 7 then 16 * ((LENGTH src + 17) - (ip + x)) + (ip - ne) + 6
   else if ph = 3 then 16 * ((LENGTH src + 17) - (ip + x)) + 5
   else 16 * ((LENGTH src + 17) - (ip + x)) + 4`;;

let SNAPPY_CF2_INIT = prove
 (`!src:byte list. LENGTH src <= 65536
                   ==> snappy_cf2_inv src (snappy_cf2_init src) /\
                       snappy_cf2_pot src (snappy_cf2_init src) <=
                       snappy_cf_steps_bound (LENGTH src)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[snappy_cf2_init; snappy_cf2_inv; snappy_cf2_pot;
              snappy_cf_steps_bound] THEN
  COND_CASES_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[SUB_LIST_CLAUSES; SNAPPY_ENCODES_NIL; LENGTH; LE_0;
                  SNAPPY_TBOUND_ZERO] THEN
  ASM_ARITH_TAC);;

let SNAPPY_CF2_UNFOLD_TAC =
  REWRITE_TAC[snappy_cf2_step] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV;;

let SNAPPY_CF2_GOAL_TAC =
  REWRITE_TAC[snappy_cf2_inv; snappy_cf2_pot] THEN CONV_TAC NUM_REDUCE_CONV;;

(* Proves snappy_tbound t b from an assumption snappy_tbound t a with a <= b, *)
(* or, for t = snappy_tupd t0 e v, from one about t0 and v <= b.             *)

let SNAPPY_TB_TAC : tactic = fun (asl,w as g) ->
  let tb = `snappy_tbound` in
  let is_tb_of t th =
    let c = concl th in
    is_comb c && is_comb(rator c) && rator(rator c) = tb && rand(rator c) = t in
  let t = rand(rator w) in
  try let th = snd(find (fun (_,th) -> is_tb_of t th) asl) in
      (MATCH_MP_TAC SNAPPY_TBOUND_MONO THEN EXISTS_TAC (rand(concl th)) THEN
       CONJ_TAC THENL [ACCEPT_TAC th; ASM_ARITH_TAC]) g
  with Failure _ ->
    let t0 = rand(rator(rator t)) in
    let th = snd(find (fun (_,th) -> is_tb_of t0 th) asl) in
    (MATCH_MP_TAC SNAPPY_TBOUND_TUPD_MONO THEN EXISTS_TAC (rand(concl th)) THEN
     REPEAT CONJ_TAC THENL [ACCEPT_TAC th; ASM_ARITH_TAC; ASM_ARITH_TAC]) g;;

let SNAPPY_CF2_FINISH_TAC =
  SNAPPY_CF2_GOAL_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY SNAPPY_TB_TAC;;

let SNAPPY_CF2_STEP_1 = prove
 (`!(src:byte list) ip ne sk c x t1 t2 out.
     LENGTH src <= 65536 /\ 15 <= LENGTH src /\ ip <= LENGTH src - 15 /\
     snappy_tbound t1 ip /\ snappy_tbound t2 ip /\
     snappy_encodes out (SUB_LIST(0,ip) src) /\ LENGTH out <= ip + ip DIV 30
     ==> let s = SnappyCState 1 ip ne sk c x t1 t2 out in
         snappy_cf2_inv src (snappy_cf2_step src s) /\
         snappy_cf2_pot src (snappy_cf2_step src s) < snappy_cf2_pot src s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SNAPPY_CF2_UNFOLD_TAC THEN SNAPPY_CF2_GOAL_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ADD_SUB] THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let SNAPPY_CF2_STEP_7 = prove
 (`!(src:byte list) ip ne sk c x t1 t2 out.
     LENGTH src <= 65536 /\ 15 <= LENGTH src /\ ne <= ip /\ c < ip /\ 4 <= x /\
     ip + x <= LENGTH src /\ snappy_matches src c ip x /\
     snappy_tbound t1 ((ip + x) - 4) /\ snappy_tbound t2 ((ip + x) - 4) /\
     snappy_encodes out (SUB_LIST(0,ne) src) /\ LENGTH out <= ne + ne DIV 30
     ==> let s = SnappyCState 7 ip ne sk c x t1 t2 out in
         snappy_cf2_inv src (snappy_cf2_step src s) /\
         snappy_cf2_pot src (snappy_cf2_step src s) < snappy_cf2_pot src s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SNAPPY_CF2_UNFOLD_TAC THEN COND_CASES_TAC THEN SNAPPY_CF2_GOAL_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
    SUBGOAL_THEN `(ip - 1) + (x + 1) = ip + x` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
    MATCH_MP_TAC SNAPPY_MATCHES_BACK THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let SNAPPY_CF2_STEP_3 = prove
 (`!(src:byte list) ip ne sk c x t1 t2 out.
     LENGTH src <= 65536 /\ 15 <= LENGTH src /\ ne <= ip /\ c < ip /\ 4 <= x /\
     ip + x <= LENGTH src /\ snappy_matches src c ip x /\
     snappy_tbound t1 ((ip + x) - 4) /\ snappy_tbound t2 ((ip + x) - 4) /\
     snappy_encodes out (SUB_LIST(0,ne) src) /\ LENGTH out <= ne + ne DIV 30
     ==> let s = SnappyCState 3 ip ne sk c x t1 t2 out in
         snappy_cf2_inv src (snappy_cf2_step src s) /\
         snappy_cf2_pot src (snappy_cf2_step src s) < snappy_cf2_pot src s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SNAPPY_CF2_UNFOLD_TAC THEN SNAPPY_CF2_GOAL_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THENL
   [REPEAT(MATCH_MP_TAC SNAPPY_TBOUND_TUPD THEN
           CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC]) THEN
    MATCH_MP_TAC SNAPPY_TBOUND_MONO THEN EXISTS_TAC `(ip + x) - 4` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    REPEAT(MATCH_MP_TAC SNAPPY_TBOUND_TUPD THEN
           CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC]) THEN
    MATCH_MP_TAC SNAPPY_TBOUND_MONO THEN EXISTS_TAC `(ip + x) - 4` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    COND_CASES_TAC THENL
     [MP_TAC(ISPECL [`src:byte list`; `out:byte list`; `ne:num`; `ip:num`]
        SNAPPY_LIT_STEP) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]];
      SUBGOAL_THEN `ne:num = ip` (SUBST_ALL_TAC o SYM) THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]];
    COND_CASES_TAC THENL
     [MP_TAC(ISPECL [`src:byte list`; `out:byte list`; `ne:num`; `ip:num`]
        SNAPPY_LIT_STEP) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]];
      SUBGOAL_THEN `ne:num = ip` (SUBST_ALL_TAC o SYM) THENL
       [ASM_ARITH_TAC; ASM_ARITH_TAC]]]);;

let SNAPPY_CF2_STEP_2 = prove
 (`!(src:byte list) ip ne sk c x t1 t2 out.
     LENGTH src <= 65536 /\ 15 <= LENGTH src /\ ne < ip /\
     ip <= LENGTH src - 14 /\ 512 <= sk /\
     snappy_tbound t1 (ip - 1) /\ snappy_tbound t2 (ip - 1) /\
     snappy_encodes out (SUB_LIST(0,ne) src) /\ LENGTH out <= ne + ne DIV 30
     ==> let s = SnappyCState 2 ip ne sk c x t1 t2 out in
         snappy_cf2_inv src (snappy_cf2_step src s) /\
         snappy_cf2_pot src (snappy_cf2_step src s) < snappy_cf2_pot src s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SNAPPY_CF2_UNFOLD_TAC THEN
  SUBGOAL_THEN `1 <= sk DIV 512` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `b = sk DIV 512` THEN
  ABBREV_TAC `e2 = snappy_hash8 (snappy_table_size (LENGTH(src:byte list)) DIV 2)
                                (snappy_load64 src ip)` THEN
  COND_CASES_TAC THENL [SNAPPY_CF2_FINISH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(t2:num->num) e2 <= ip - 1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SNAPPY_TBOUND_LOOKUP]; ALL_TAC] THEN
  ABBREV_TAC `c2 = (t2:num->num) e2` THEN
  SUBGOAL_THEN `snappy_tbound (snappy_tupd t2 e2 ip) ip` ASSUME_TAC THENL
   [SNAPPY_TB_TAC; ALL_TAC] THEN
  ABBREV_TAC `t2' = snappy_tupd t2 e2 ip` THEN
  COND_CASES_TAC THENL
   [MP_TAC(ISPECL [`src:byte list`; `c2:num`; `ip:num`] SNAPPY_MATCH4_MATCHES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
    SNAPPY_CF2_FINISH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `e1 = snappy_hash4 (snappy_table_size (LENGTH(src:byte list)) DIV 2)
                                (snappy_load32 src ip)` THEN
  SUBGOAL_THEN `(t1:num->num) e1 <= ip - 1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SNAPPY_TBOUND_LOOKUP]; ALL_TAC] THEN
  ABBREV_TAC `c1 = (t1:num->num) e1` THEN
  SUBGOAL_THEN `snappy_tbound (snappy_tupd t1 e1 ip) ip` ASSUME_TAC THENL
   [SNAPPY_TB_TAC; ALL_TAC] THEN
  ABBREV_TAC `t1' = snappy_tupd t1 e1 ip` THEN
  COND_CASES_TAC THENL [ALL_TAC; SNAPPY_CF2_FINISH_TAC] THEN
  MP_TAC(ISPECL [`src:byte list`; `c1:num`; `ip:num`] SNAPPY_MATCH4_MATCHES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  ABBREV_TAC `e2b = snappy_hash8 (snappy_table_size (LENGTH(src:byte list)) DIV 2)
                                 (snappy_load64 src (ip + 1))` THEN
  SUBGOAL_THEN `(t2':num->num) e2b <= ip` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SNAPPY_TBOUND_LOOKUP]; ALL_TAC] THEN
  ABBREV_TAC `c3 = (t2':num->num) e2b` THEN
  MP_TAC(ISPECL [`src:byte list`; `c3:num`; `ip + 1`] SNAPPY_MATCH_LENGTH_MATCHES) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  COND_CASES_TAC THEN SNAPPY_CF2_FINISH_TAC);;

let SNAPPY_CF2_STEP_4 = prove
 (`!(src:byte list) ip ne sk c x t1 t2 out.
     LENGTH src <= 65536 /\ 15 <= LENGTH src /\ c < ip /\ 4 <= x /\
     ip + x <= LENGTH src /\ snappy_matches src c ip x /\
     snappy_tbound t1 ((ip + x) - 1) /\ snappy_tbound t2 ((ip + x) - 1) /\
     snappy_encodes out (SUB_LIST(0,ip) src) /\ LENGTH out <= ip + ip DIV 30 + 1
     ==> let s = SnappyCState 4 ip ne sk c x t1 t2 out in
         snappy_cf2_inv src (snappy_cf2_step src s) /\
         snappy_cf2_pot src (snappy_cf2_step src s) < snappy_cf2_pot src s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SNAPPY_CF2_UNFOLD_TAC THEN
  MP_TAC(ISPECL [`src:byte list`; `out:byte list`; `ip:num`; `c:num`; `x:num`]
    SNAPPY_COPY_STEP_MATCHES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `out' = APPEND out (snappy_emit_copy (ip - c) x)` THEN
  SUBGOAL_THEN `ip + 4 <= ip + x` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `q = ip + x` THEN
  COND_CASES_TAC THENL [SNAPPY_CF2_FINISH_TAC; ALL_TAC] THEN
  ABBREV_TAC `ts = snappy_table_size (LENGTH(src:byte list)) DIV 2` THEN
  SUBGOAL_THEN
   `snappy_tbound
     (if 7 < q
      then snappy_tupd (snappy_tupd t2 (snappy_hash8 ts (snappy_load64 src (q - 7)))
                                    (q - 7))
                       (snappy_hash8 ts (snappy_load64 src (q - 4))) (q - 4)
      else t2) (q - 1)`
  ASSUME_TAC THENL
   [COND_CASES_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC SNAPPY_TBOUND_TUPD THEN (CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC]) THEN
    MATCH_MP_TAC SNAPPY_TBOUND_TUPD THEN (CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC]) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `t2a = if 7 < q
          then snappy_tupd (snappy_tupd t2 (snappy_hash8 ts (snappy_load64 src (q - 7)))
                                        (q - 7))
                           (snappy_hash8 ts (snappy_load64 src (q - 4))) (q - 4)
          else t2` THEN
  SUBGOAL_THEN
   `snappy_tbound
      (snappy_tupd (snappy_tupd t2a (snappy_hash8 ts (snappy_load64 src (q - 3)))
                                (q - 3))
                   (snappy_hash8 ts (snappy_load64 src (q - 2))) (q - 2)) (q - 1) /\
    snappy_tbound
      (snappy_tupd (snappy_tupd t1 (snappy_hash4 ts (snappy_load32 src (q - 2)))
                                (q - 2))
                   (snappy_hash4 ts (snappy_load32 src (q - 1))) (q - 1)) (q - 1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC SNAPPY_TBOUND_TUPD THEN (CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC]) THEN
    MATCH_MP_TAC SNAPPY_TBOUND_TUPD THEN (CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC]) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `t2b = snappy_tupd (snappy_tupd t2a (snappy_hash8 ts (snappy_load64 src (q - 3)))
                                   (q - 3))
                      (snappy_hash8 ts (snappy_load64 src (q - 2))) (q - 2)` THEN
  ABBREV_TAC
   `t1a = snappy_tupd (snappy_tupd t1 (snappy_hash4 ts (snappy_load32 src (q - 2)))
                                   (q - 2))
                      (snappy_hash4 ts (snappy_load32 src (q - 1))) (q - 1)` THEN
  ABBREV_TAC `e2 = snappy_hash8 ts (snappy_load64 src q)` THEN
  SUBGOAL_THEN `(t2b:num->num) e2 <= q - 1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SNAPPY_TBOUND_LOOKUP]; ALL_TAC] THEN
  ABBREV_TAC `c2 = (t2b:num->num) e2` THEN
  SUBGOAL_THEN `snappy_tbound (snappy_tupd t2b e2 q) q` ASSUME_TAC THENL
   [SNAPPY_TB_TAC; ALL_TAC] THEN
  ABBREV_TAC `t2c = snappy_tupd t2b e2 q` THEN
  COND_CASES_TAC THENL
   [MP_TAC(ISPECL [`src:byte list`; `c2:num`; `q:num`] SNAPPY_MATCH4_MATCHES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
    SNAPPY_CF2_FINISH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `e1 = snappy_hash4 ts (snappy_load32 src q)` THEN
  SUBGOAL_THEN `(t1a:num->num) e1 <= q - 1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SNAPPY_TBOUND_LOOKUP]; ALL_TAC] THEN
  ABBREV_TAC `c1 = (t1a:num->num) e1` THEN
  SUBGOAL_THEN `snappy_tbound (snappy_tupd t1a e1 q) q` ASSUME_TAC THENL
   [SNAPPY_TB_TAC; ALL_TAC] THEN
  ABBREV_TAC `t1b = snappy_tupd t1a e1 q` THEN
  COND_CASES_TAC THENL
   [MP_TAC(ISPECL [`src:byte list`; `c1:num`; `q:num`] SNAPPY_MATCH4_MATCHES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
    SNAPPY_CF2_FINISH_TAC;
    SNAPPY_CF2_FINISH_TAC]);;

let SNAPPY_CF2_STEP_5 = prove
 (`!(src:byte list) ip ne sk c x t1 t2 out.
     LENGTH src <= 65536 /\ ip <= LENGTH src /\
     snappy_encodes out (SUB_LIST(0,ip) src) /\ LENGTH out <= ip + ip DIV 30
     ==> let s = SnappyCState 5 ip ne sk c x t1 t2 out in
         snappy_cf2_inv src (snappy_cf2_step src s) /\
         snappy_cf2_pot src (snappy_cf2_step src s) < snappy_cf2_pot src s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SNAPPY_CF2_UNFOLD_TAC THEN SNAPPY_CF2_GOAL_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [MP_TAC(ISPECL [`src:byte list`; `out:byte list`; `ip:num`;
                   `LENGTH(src:byte list)`] SNAPPY_LIT_STEP) THEN
    REWRITE_TAC[SUB_LIST_LENGTH] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]];
    SUBGOAL_THEN `ip = LENGTH(src:byte list)` SUBST_ALL_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUB_LIST_LENGTH]) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let SNAPPY_CF2_STEP = prove
 (`!(src:byte list) s.
        snappy_cf2_inv src s /\ ~(snappy_phase s = 0)
        ==> snappy_cf2_inv src (snappy_cf2_step src s) /\
            snappy_cf2_pot src (snappy_cf2_step src s) < snappy_cf2_pot src s`,
  GEN_TAC THEN MATCH_MP_TAC snappy_cstate_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`ph:num`; `ip:num`; `ne:num`; `sk:num`; `c:num`; `x:num`;
                       `t1:num->num`; `t2:num->num`; `out:byte list`] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [snappy_cf2_inv] THEN
  REWRITE_TAC[snappy_phase] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) ASSUME_TAC) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
                                                 lhs(concl th) = `ph:num`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_EQ]) THEN
  TRY(FIRST_X_ASSUM CONTR_TAC) THEN
  FIRST(map (fun th -> MATCH_MP_TAC(CONV_RULE(ONCE_DEPTH_CONV let_CONV) th) THEN
                       ASM_REWRITE_TAC[])
            [SNAPPY_CF2_STEP_1; SNAPPY_CF2_STEP_2; SNAPPY_CF2_STEP_3;
             SNAPPY_CF2_STEP_4; SNAPPY_CF2_STEP_5; SNAPPY_CF2_STEP_7]));;

let SNAPPY_CF2_FIX = prove
 (`!(src:byte list) s.
        snappy_phase s = 0 ==> snappy_cf2_step src s = s`,
  GEN_TAC THEN MATCH_MP_TAC snappy_cstate_INDUCT THEN
  REWRITE_TAC[snappy_phase] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN SNAPPY_CF2_UNFOLD_TAC);;

let SNAPPY_CF2_RUN = prove
 (`!(src:byte list) k.
        LENGTH src <= 65536 /\ snappy_cf_steps_bound (LENGTH src) <= k
        ==> snappy_cf2_inv src (snappy_crun (snappy_cf2_step src) k (snappy_cf2_init src)) /\
            snappy_phase (snappy_crun (snappy_cf2_step src) k (snappy_cf2_init src)) = 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`snappy_cf2_step src`; `snappy_cf2_inv src`; `snappy_cf2_pot src`;
                 `\s. snappy_phase s = 0`] SNAPPY_CRUN_TERMINATES) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [SIMP_TAC[SNAPPY_CF2_FIX; SNAPPY_CF2_STEP]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(SPEC `src:byte list` SNAPPY_CF2_INIT) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC LE_TRANS `snappy_cf_steps_bound (LENGTH(src:byte list))` THEN
  ASM_REWRITE_TAC[]);;

let SNAPPY_CF2_DONE = prove
 (`!(src:byte list) s. snappy_cf2_inv src s /\ snappy_phase s = 0
                       ==> snappy_encodes (snappy_out s) src /\
                           LENGTH(snappy_out s) <= LENGTH src + LENGTH src DIV 30 + 1`,
  GEN_TAC THEN MATCH_MP_TAC snappy_cstate_INDUCT THEN
  REWRITE_TAC[snappy_phase; snappy_out; snappy_cf2_inv] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC SUBST_ALL_TAC) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let SNAPPY_CF2_CORRECT = prove
 (`!src:byte list.
        LENGTH src <= 65536
        ==> snappy_encodes (snappy_compress_fragment 2 src) src /\
            LENGTH(snappy_compress_fragment 2 src)
            <= LENGTH src + LENGTH src DIV 30 + 1`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[snappy_compress_fragment; ARITH_EQ] THEN
  MATCH_MP_TAC SNAPPY_CF2_DONE THEN MATCH_MP_TAC SNAPPY_CF2_RUN THEN
  ASM_REWRITE_TAC[LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Results of the fragment machines, for the machine-code proofs: any run    *)
(* that has reached phase 0 has produced snappy_compress_fragment.           *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_CRUN_FINAL = prove
 (`!step s0 k b.
        step(snappy_crun step k s0) = snappy_crun step k s0 /\
        step(snappy_crun step b s0) = snappy_crun step b s0
        ==> snappy_crun step k s0 = snappy_crun step b s0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC(ARITH_RULE `k <= b \/ b <= k:num`) THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST_ALL_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[SNAPPY_CRUN_ADD] THEN ASM_SIMP_TAC[SNAPPY_CRUN_FIX] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  ASM_SIMP_TAC[SNAPPY_CRUN_ADD; SNAPPY_CRUN_FIX]);;

let SNAPPY_COMPRESS_FRAGMENT_1 = prove
 (`!(src:byte list) k.
        LENGTH src <= 65536 /\
        snappy_phase(snappy_crun (snappy_cf1_step src) k (snappy_cf1_init src)) = 0
        ==> snappy_compress_fragment 1 src =
            snappy_out(snappy_crun (snappy_cf1_step src) k (snappy_cf1_init src))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[snappy_compress_fragment] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SNAPPY_CRUN_FINAL THEN
  ASM_SIMP_TAC[SNAPPY_CF1_FIX; SNAPPY_CF1_RUN; LE_REFL]);;

let SNAPPY_COMPRESS_FRAGMENT_2 = prove
 (`!(src:byte list) k.
        LENGTH src <= 65536 /\
        snappy_phase(snappy_crun (snappy_cf2_step src) k (snappy_cf2_init src)) = 0
        ==> snappy_compress_fragment 2 src =
            snappy_out(snappy_crun (snappy_cf2_step src) k (snappy_cf2_init src))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[snappy_compress_fragment; ARITH_EQ] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SNAPPY_CRUN_FINAL THEN
  ASM_SIMP_TAC[SNAPPY_CF2_FIX; SNAPPY_CF2_RUN; LE_REFL]);;

let SNAPPY_FRAGMENT_CORRECT = prove
 (`!level (src:byte list).
        (level = 1 \/ level = 2) /\ LENGTH src <= 65536
        ==> snappy_encodes (snappy_compress_fragment level src) src /\
            LENGTH(snappy_compress_fragment level src)
            <= LENGTH src + LENGTH src DIV 30 + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[SNAPPY_CF1_CORRECT; SNAPPY_CF2_CORRECT]);;

(* ------------------------------------------------------------------------- *)
(* The block loop.                                                           *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_BLOCKS_FUEL_NIL = prove
 (`!k level. snappy_blocks_fuel k level ([]:byte list) = []`,
  INDUCT_TAC THEN REWRITE_TAC[snappy_blocks_fuel]);;

let SNAPPY_BLOCKS_FUEL = prove
 (`!k k' level (src:byte list).
        LENGTH src <= 65536 * k /\ LENGTH src <= 65536 * k'
        ==> snappy_blocks_fuel k level src = snappy_blocks_fuel k' level src`,
  INDUCT_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[snappy_blocks_fuel; MULT_CLAUSES; ARITH_RULE `x <= 0 <=> x = 0`;
              LENGTH_EQ_NIL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[snappy_blocks_fuel; SNAPPY_BLOCKS_FUEL_NIL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[SNAPPY_LENGTH_SUB_LIST_SUFFIX] THEN
  ASM_ARITH_TAC);;

let SNAPPY_COMPRESS_BLOCKS = prove
 (`!level (src:byte list).
        snappy_compress_blocks level src =
        if src = [] then []
        else APPEND (snappy_compress_fragment level (SUB_LIST(0,65536) src))
                    (snappy_compress_blocks level
                       (SUB_LIST(65536,LENGTH src - 65536) src))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[snappy_compress_blocks] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; snappy_blocks_fuel] THEN
  SUBGOAL_THEN `?n. LENGTH(src:byte list) = SUC n` (CHOOSE_THEN ASSUME_TAC) THENL
   [EXISTS_TAC `LENGTH(src:byte list) - 1` THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM LENGTH_EQ_NIL]) THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[snappy_blocks_fuel] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC SNAPPY_BLOCKS_FUEL THEN
  ASM_REWRITE_TAC[LENGTH_SUB_LIST; MIN] THEN ARITH_TAC);;

let SNAPPY_BLOCKS_CORRECT = prove
 (`!level (src:byte list).
        (level = 1 \/ level = 2)
        ==> snappy_encodes (snappy_compress_blocks level src) src /\
            LENGTH(snappy_compress_blocks level src)
            <= LENGTH src + LENGTH src DIV 6 + 1`,
  GEN_TAC THEN REWRITE_TAC[snappy_compress_blocks] THEN
  SUBGOAL_THEN
   `!k (src:byte list).
        (level = 1 \/ level = 2) /\ LENGTH src <= 65536 * k
        ==> snappy_encodes (snappy_blocks_fuel k level src) src /\
            LENGTH(snappy_blocks_fuel k level src)
            <= LENGTH src + LENGTH src DIV 6 + 1`
   (fun th -> GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC th THEN
              ASM_REWRITE_TAC[] THEN ARITH_TAC) THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THENL
   [FIRST_X_ASSUM(MP_TAC o check (is_binary "<=" o concl)) THEN
    REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `x <= 0 <=> x = 0`; LENGTH_EQ_NIL] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[snappy_blocks_fuel; SNAPPY_ENCODES_NIL; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[snappy_blocks_fuel] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[SNAPPY_ENCODES_NIL; LENGTH; LE_0] THEN
  ABBREV_TAC `a = SUB_LIST(0,65536) (src:byte list)` THEN
  ABBREV_TAC `r = SUB_LIST(65536,LENGTH src - 65536) (src:byte list)` THEN
  SUBGOAL_THEN `APPEND a r = src:byte list` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "r"] THEN REWRITE_TAC[SUB_LIST_TOPSPLIT];
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(a:byte list) = MIN 65536 (LENGTH(src:byte list)) /\
                LENGTH(r:byte list) = LENGTH src - 65536` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "r"] THEN
    REWRITE_TAC[LENGTH_SUB_LIST; SNAPPY_LENGTH_SUB_LIST_SUFFIX] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`level:num`; `a:byte list`] SNAPPY_FRAGMENT_CORRECT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:byte list`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC SNAPPY_ENCODES_APPEND THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LENGTH_APPEND] THEN
  ASM_CASES_TAC `LENGTH(src:byte list) <= 65536` THENL
   [SUBGOAL_THEN `r:byte list = []` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SNAPPY_BLOCKS_FUEL_NIL; LENGTH] THEN
    SUBGOAL_THEN `LENGTH(a:byte list) = LENGTH(src:byte list)` SUBST_ALL_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`30`; `LENGTH(src:byte list)`; `6`] DIV_MONO2) THEN
    ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(a:byte list) = 65536` SUBST_ALL_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN
  SUBGOAL_THEN `(LENGTH(src:byte list) - 65536) DIV 6 + 10922 <=
                LENGTH(src:byte list) DIV 6` MP_TAC THENL
   [SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN
    MP_TAC(SPECL [`LENGTH(src:byte list) - 65536`; `6`] DIVISION) THEN
    ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The top-level properties.                                                 *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_COMPRESS_ROUNDTRIP = prove
 (`!level (src:byte list).
        (level = 1 \/ level = 2) /\ LENGTH src < 2 EXP 32
        ==> snappy_decode (snappy_compress level src) = SOME src`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[snappy_compress; GSYM NOT_LT; snappy_decode] THEN
  ASM_SIMP_TAC[SNAPPY_VARINT_ENCODE; snappy_bind] THEN
  MP_TAC(SPECL [`level:num`; `src:byte list`] SNAPPY_BLOCKS_CORRECT) THEN
  ASM_REWRITE_TAC[snappy_encodes] THEN
  DISCH_THEN(MP_TAC o SPECL [`LENGTH(src:byte list)`; `[]:byte list`;
                             `[]:byte list`] o CONJUNCT1) THEN
  REWRITE_TAC[LENGTH; ADD_CLAUSES; LE_REFL; APPEND_NIL; APPEND] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (MP_TAC o MATCH_MP SNAPPY_STEPS_DECODE_TAGS)) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SNAPPY_DECODE_TAGS_NIL]);;

let SNAPPY_COMPRESS_LENGTH = prove
 (`!level (src:byte list).
        (level = 1 \/ level = 2)
        ==> LENGTH(snappy_compress level src)
            <= snappy_max_compressed_length (LENGTH src)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[snappy_compress] THEN
  COND_CASES_TAC THEN REWRITE_TAC[LENGTH; LE_0] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
  ASM_SIMP_TAC[SNAPPY_MAX_COMPRESSED_LENGTH_32; LENGTH_APPEND] THEN
  MP_TAC(SPECL [`level:num`; `src:byte list`] SNAPPY_BLOCKS_CORRECT) THEN
  MP_TAC(SPEC `LENGTH(src:byte list)` LENGTH_SNAPPY_VARINT_ENCODE) THEN
  ASM_SIMP_TAC[] THEN ARITH_TAC);;
