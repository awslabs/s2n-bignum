(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The validator (SnappyDecompressionValidator in snappy.cc) and the format  *)
(* model of snappy_format.ml: the lemmas that the machine-code proofs of     *)
(* IsValidCompressedBuffer use.                                              *)
(*                                                                           *)
(* The validator does not keep the output, only the number of bytes          *)
(* produced; a model output out of that length is a ghost of the proofs.     *)
(* Its fast path, DecompressBranchless<size_t>, does not bound the output by *)
(* the length m of the header (FINDINGS F2): it decodes tags as              *)
(* snappy_tag_step M does for a bound M = 2^63 that it never reaches. So     *)
(* after the fast path the output may be longer than m, and then the stream  *)
(* is invalid (SNAPPY_DECODE_TAGS_LONG); SNAPPY_STEPS_BOUND_NONE says that   *)
(* steps with any bound M >= m keep whether the decode with m fails. The     *)
(* output stays below 2^63 since every tag appends at most 22 bytes per byte *)
(* of the stream that it consumes (SNAPPY_TAG_STEP_RATIO: 64 bytes for the   *)
(* 3 bytes of a copy with a 2-byte offset is the largest ratio), and the     *)
(* stream is shorter than 2^58 bytes.                                        *)
(* ========================================================================= *)

needs "common/snappy/snappy_decompressor.ml";;
needs "common/snappy/snappy_decompress.ml";;

(* ------------------------------------------------------------------------- *)
(* An output longer than m cannot be completed.                              *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_DECODE_TAGS_LONG = prove
 (`!m (inp:byte list) out.
        m < LENGTH out ==> snappy_decode_tags m inp out = NONE`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[SNAPPY_DECODE_TAGS] THEN
  COND_CASES_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `inp:byte list`; `out:byte list`]
    SNAPPY_TAG_STEP_LENGTH) THEN
  SPEC_TAC(`snappy_tag_step m inp out`,`r:(byte list#byte list)option`) THEN
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:(byte list#byte list)option` (cases "option")) THEN
  REWRITE_TAC[snappy_bind] THEN
  DISCH_THEN(MP_TAC o SPECL [`FST(a:byte list#byte list)`;
                             `SND(a:byte list#byte list)`]) THEN
  REWRITE_TAC[PAIR] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A tag with a bound m <= M: as with M, if the output stays within m.       *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_TAG_STEP_BOUND = prove
 (`!m M (inp:byte list) out.
        m <= M
        ==> snappy_tag_step m inp out =
            snappy_bind (snappy_tag_step M inp out)
              (\s. if LENGTH(SND s) <= m then SOME s else NONE)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  STRUCT_CASES_TAC(ISPEC `inp:byte list` list_CASES) THEN
  REWRITE_TAC[snappy_tag_step; snappy_bind] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[snappy_literal; snappy_copy_tag] THEN
  REPEAT(COND_CASES_TAC THEN
         ASM_REWRITE_TAC[snappy_bind; LENGTH_APPEND; LENGTH_SUB_LIST;
                         LENGTH_SNAPPY_COPY; SUB_0]) THEN
  REWRITE_TAC[MIN] THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* At most 22 bytes of output per byte of the stream.                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_TAG_STEP_RATIO = prove
 (`!m (inp:byte list) out inp' out'.
        snappy_tag_step m inp out = SOME(inp',out')
        ==> LENGTH out' + 22 * LENGTH inp' <= LENGTH out + 22 * LENGTH inp`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[snappy_tag_step; option_DISTINCT] THEN
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `val(h:byte) DIV 4 < 64` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(val(h:byte) DIV 4) DIV 8 < 8 /\ (val h DIV 4) MOD 8 < 8`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RDIV_LT_EQ; MOD_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[snappy_literal; snappy_copy_tag; LENGTH] THEN
  REPEAT(COND_CASES_TAC THEN
         ASM_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ]) THEN
  DISCH_THEN(CONJUNCTS_THEN(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_SUB_LIST; LENGTH_SNAPPY_COPY; SUB_0] THEN
  TRY(SUBGOAL_THEN `~(t:byte list = [])` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[LENGTH_TL]) THEN
  REWRITE_TAC[MIN] THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_ARITH_TAC);;

let SNAPPY_STEPS_RATIO = prove
 (`!k m (inp:byte list) out inp' out'.
        snappy_steps k m (inp,out) = SOME(inp',out')
        ==> LENGTH out' + 22 * LENGTH inp' <= LENGTH out + 22 * LENGTH inp`,
  INDUCT_TAC THEN REWRITE_TAC[snappy_steps; option_INJ; PAIR_EQ] THENL
   [MESON_TAC[LE_REFL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[SNAPPY_BIND_EQ_SOME; EXISTS_PAIR_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `i1:byte list` (X_CHOOSE_THEN `o1:byte list`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SNAPPY_TAG_STEP_RATIO) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ASSUME
   `!m (inp:byte list) out inp' out'.
        snappy_steps k m (inp,out) = SOME(inp',out')
        ==> LENGTH out' + 22 * LENGTH inp' <= LENGTH out + 22 * LENGTH inp`))
  THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Steps with a bound M >= m keep whether the decode with m fails.           *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_STEPS_BOUND_NONE = prove
 (`!k m M (inp:byte list) out inp' out'.
        m <= M /\ snappy_steps k M (inp,out) = SOME(inp',out')
        ==> (snappy_decode_tags m inp out = NONE <=>
             snappy_decode_tags m inp' out' = NONE)`,
  INDUCT_TAC THEN REWRITE_TAC[snappy_steps; option_INJ; PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[SNAPPY_BIND_EQ_SOME; EXISTS_PAIR_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `i1:byte list`
    (X_CHOOSE_THEN `o1:byte list` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`m:num`; `M:num`; `i1:byte list`; `o1:byte list`;
    `inp':byte list`; `out':byte list`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(SPECL [`m:num`; `M:num`; `inp:byte list`; `out:byte list`]
    SNAPPY_TAG_STEP_BOUND) THEN
  ASM_REWRITE_TAC[snappy_bind] THEN DISCH_TAC THEN
  ASM_CASES_TAC `LENGTH(o1:byte list) <= m` THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP SNAPPY_DECODE_TAGS_STEP o
      REWRITE_RULE[ASSUME `LENGTH(o1:byte list) <= m`]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(inp:byte list = [])` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[snappy_tag_step; option_DISTINCT]) THEN
    FIRST_ASSUM CONTR_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`m:num`; `inp:byte list`; `out:byte list`]
    SNAPPY_DECODE_TAGS_FAIL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC SNAPPY_DECODE_TAGS_LONG THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The whole stream byte by byte, in the order in which                     *)
(* ReadUncompressedLength reads the header (as SNAPPY_HEADER_BYTES), with   *)
(* the rest of the stream after the header.                                 *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_DECODE_BYTES = prove
 (`!l:byte list.
     snappy_decode l =
     if LENGTH l = 0 then NONE
     else if val(EL 0 l) < 128
     then snappy_decode_tags (val(EL 0 l)) (SUB_LIST(1,LENGTH l - 1) l) []
     else if LENGTH l = 1 then NONE
     else if val(EL 1 l) < 128
     then snappy_decode_tags (val(EL 0 l) - 128 + 128 * val(EL 1 l))
            (SUB_LIST(2,LENGTH l - 2) l) []
     else if LENGTH l = 2 then NONE
     else if val(EL 2 l) < 128
     then snappy_decode_tags (val(EL 0 l) - 128 + 128 * (val(EL 1 l) - 128 +
               128 * val(EL 2 l)))
            (SUB_LIST(3,LENGTH l - 3) l) []
     else if LENGTH l = 3 then NONE
     else if val(EL 3 l) < 128
     then snappy_decode_tags (val(EL 0 l) - 128 + 128 * (val(EL 1 l) - 128 +
               128 * (val(EL 2 l) - 128 + 128 * val(EL 3 l))))
            (SUB_LIST(4,LENGTH l - 4) l) []
     else if LENGTH l = 4 then NONE
     else if val(EL 4 l) < 16
     then snappy_decode_tags (val(EL 0 l) - 128 + 128 * (val(EL 1 l) - 128 +
               128 * (val(EL 2 l) - 128 + 128 * (val(EL 3 l) - 128 +
               128 * val(EL 4 l)))))
            (SUB_LIST(5,LENGTH l - 5) l) []
     else NONE`,
  let cases v h t =
    DISJ_CASES_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN h (X_CHOOSE_THEN t SUBST1_TAC))
      (ISPEC v list_CASES) in
  GEN_TAC THEN cases `l:byte list` `b0:byte` `t0:byte list` THENL
   [ALL_TAC; cases `t0:byte list` `b1:byte` `t1:byte list`] THENL
   [ALL_TAC; ALL_TAC; cases `t1:byte list` `b2:byte` `t2:byte list`] THENL
   [ALL_TAC; ALL_TAC; ALL_TAC; cases `t2:byte list` `b3:byte` `t3:byte list`]
  THENL
   [ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC;
    cases `t3:byte list` `b4:byte` `t4:byte list`] THEN
  REWRITE_TAC[snappy_decode; snappy_varint;
              ARITH_RULE `5 = SUC 4 /\ 4 = SUC 3 /\ 3 = SUC 2`; TWO; ONE] THEN
  REWRITE_TAC[snappy_varint_from; LENGTH; EL; HD; TL; SUC_INJ; NOT_SUC;
              SUB_LIST_CLAUSES; SUC_SUB1; SUB_0; SUB_SUC; SUB_LIST_LENGTH] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[snappy_bind; option_DISTINCT; option_INJ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC) THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; SUB_LIST_LENGTH; ARITH_RULE `SUC n - 1 = n`]);;


(* ------------------------------------------------------------------------- *)
(* The states of the fast path: after some steps with the bound mb, the      *)
(* stream is the input from position h on and the output has P bytes. The   *)
(* tags that DecompressBranchless<size_t> does, as steps from there.         *)
(* ------------------------------------------------------------------------- *)

let snappy_fast_reach = new_definition
 `snappy_fast_reach mb (inp:byte list) out h P <=>
    ?k out'. snappy_steps k mb (inp,out) =
             SOME(SUB_LIST(h,LENGTH inp - h) inp,out') /\
             LENGTH out' = P`;;

let SNAPPY_FAST_REACH_0 = prove
 (`!mb (inp:byte list) out. snappy_fast_reach mb inp out 0 (LENGTH out)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[snappy_fast_reach] THEN
  MAP_EVERY EXISTS_TAC [`0`; `out:byte list`] THEN
  REWRITE_TAC[snappy_steps; SUB_0; SUB_LIST_LENGTH]);;

let SNAPPY_FAST_REACH_STEP = prove
 (`!mb (inp:byte list) out h P h' d.
        snappy_fast_reach mb inp out h P /\
        (!out'. LENGTH out' = P
                ==> ?out''. snappy_tag_step mb (SUB_LIST(h,LENGTH inp - h) inp)
                              out' =
                            SOME(SUB_LIST(h',LENGTH inp - h') inp,out'') /\
                            LENGTH out'' = P + d)
        ==> snappy_fast_reach mb inp out h' (P + d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[snappy_fast_reach] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `o1:byte list` STRIP_ASSUME_TAC))
   (MP_TAC o SPEC `o1:byte list`)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `o2:byte list` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`SUC k`; `o2:byte list`] THEN
  ASM_REWRITE_TAC[SNAPPY_STEPS_SUC; snappy_bind]);;

let SNAPPY_FAST_REACH_LITERAL = prove
 (`!mb (inp:byte list) out h P.
        snappy_fast_reach mb inp out h P /\
        val(EL h inp) MOD 4 = 0 /\ val(EL h inp) DIV 4 < 60 /\
        h + val(EL h inp) DIV 4 + 2 <= LENGTH inp /\
        P + val(EL h inp) DIV 4 + 1 <= mb
        ==> snappy_fast_reach mb inp out (h + val(EL h inp) DIV 4 + 2)
                              (P + (val(EL h inp) DIV 4 + 1))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SNAPPY_FAST_REACH_STEP THEN
  EXISTS_TAC `h:num` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SNAPPY_TAG_STEP_LITERAL_AT o
    lhand o lhand o snd o dest_exists o snd) THEN
  ASM_REWRITE_TAC[] THEN TRY(ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[option_INJ; PAIR_EQ] THEN
  REWRITE_TAC[UNWIND_THM1; UNWIND_THM2] THEN
  ASM_REWRITE_TAC[LENGTH_APPEND; LENGTH_SUB_LIST] THEN ASM_ARITH_TAC);;

let SNAPPY_FAST_REACH_COPY1 = prove
 (`!mb (inp:byte list) out h P.
        snappy_fast_reach mb inp out h P /\
        val(EL h inp) MOD 4 = 1 /\ h + 2 <= LENGTH inp /\
        1 <= 256 * (val(EL h inp) DIV 4 DIV 8) + val(EL (h + 1) inp) /\
        256 * (val(EL h inp) DIV 4 DIV 8) + val(EL (h + 1) inp) <= P /\
        P + (val(EL h inp) DIV 4 MOD 8 + 4) <= mb
        ==> snappy_fast_reach mb inp out (h + 2)
                              (P + (val(EL h inp) DIV 4 MOD 8 + 4))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SNAPPY_FAST_REACH_STEP THEN
  EXISTS_TAC `h:num` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SNAPPY_TAG_STEP_COPY1_AT; snappy_copy_tag] THEN
  TRY(COND_CASES_TAC THENL [ALL_TAC; POP_ASSUM MP_TAC THEN ASM_ARITH_TAC]) THEN
  REWRITE_TAC[option_INJ; PAIR_EQ] THEN
  REWRITE_TAC[UNWIND_THM1; UNWIND_THM2] THEN
  ASM_REWRITE_TAC[LENGTH_SNAPPY_COPY]);;

let SNAPPY_FAST_REACH_COPY2 = prove
 (`!mb (inp:byte list) out h P.
        snappy_fast_reach mb inp out h P /\
        val(EL h inp) MOD 4 = 2 /\ h + 3 <= LENGTH inp /\
        1 <= val(EL (h + 1) inp) + 256 * val(EL (h + 2) inp) /\
        val(EL (h + 1) inp) + 256 * val(EL (h + 2) inp) <= P /\
        P + (val(EL h inp) DIV 4 + 1) <= mb
        ==> snappy_fast_reach mb inp out (h + 3)
                              (P + (val(EL h inp) DIV 4 + 1))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SNAPPY_FAST_REACH_STEP THEN
  EXISTS_TAC `h:num` THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SNAPPY_TAG_STEP_COPY2_AT; snappy_copy_tag] THEN
  TRY(COND_CASES_TAC THENL [ALL_TAC; POP_ASSUM MP_TAC THEN ASM_ARITH_TAC]) THEN
  REWRITE_TAC[option_INJ; PAIR_EQ] THEN
  REWRITE_TAC[UNWIND_THM1; UNWIND_THM2] THEN
  ASM_REWRITE_TAC[LENGTH_SNAPPY_COPY]);;

let SNAPPY_FAST_REACH_RESULT = prove
 (`!mb (inp:byte list) out h P.
        snappy_fast_reach mb inp out h P /\ h <= LENGTH inp
        ==> ?k inp' out'. snappy_steps k mb (inp,out) = SOME(inp',out') /\
                          LENGTH inp - LENGTH inp' = h /\ LENGTH out' = P`,
  REPEAT GEN_TAC THEN REWRITE_TAC[snappy_fast_reach] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `o1:byte list` STRIP_ASSUME_TAC))
   ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`k:num`; `SUB_LIST(h,LENGTH inp - h) (inp:byte list)`; `o1:byte list`] THEN
  ASM_REWRITE_TAC[SNAPPY_LENGTH_SUB_LIST_SUFFIX] THEN ASM_ARITH_TAC);;
