(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The snappy compressed format (format_description.txt of google/snappy),   *)
(* exactly as the decompressor of snappy 1.3.1 accepts it.                   *)
(*                                                                           *)
(* A compressed stream is a varint header m (the uncompressed length) and a  *)
(* sequence of tags. Each tag appends bytes to the output: a literal copies  *)
(* bytes of the stream, a copy repeats earlier output. The stream is valid   *)
(* iff the header parses, every tag is complete, every copy has             *)
(* 1 <= offset <= (bytes produced so far), no tag takes the output beyond m, *)
(* and the output has exactly m bytes when the stream ends. These are the    *)
(* conditions of SnappyDecompressor::DecompressAllTags (snappy.cc) with the  *)
(* writers SnappyArrayWriter (RawUncompress) and                             *)
(* SnappyDecompressionValidator (IsValidCompressedBuffer), whose checks      *)
(* agree; see common/snappy/FINDINGS.md for the analysis, including the     *)
(* fast path DecompressBranchless.                                           *)
(*                                                                           *)
(* The decoding is a step function on (remaining stream, output so far), so  *)
(* the loop invariant of a machine-code decoder can be                       *)
(*     snappy_decode input = snappy_decode_tags m rest out                   *)
(* where rest is the unread part of the stream and out the output so far.    *)
(*                                                                           *)
(* This file only needs the HOL Light library and the ISA-independent       *)
(* files common/{overlap,for_hollight,words2,misc}.ml (loaded in the same    *)
(* order as {arm,x86}/proofs/base.ml, so loading it after base.ml is free).  *)
(* ========================================================================= *)

needs "Library/iter.ml";;
needs "Library/rstc.ml";;
needs "Library/bitsize.ml";;
needs "Library/pocklington.ml";;
needs "Library/integer.ml";;
needs "Library/words.ml";;
needs "Library/bitmatch.ml";;
needs "common/overlap.ml";;
needs "common/for_hollight.ml";;
needs "common/words2.ml";;
needs "common/misc.ml";;

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Option sequencing (used instead of "match" so that the definitions        *)
(* evaluate with Compute.CBV_CONV, see snappy_compset below).                *)
(* ------------------------------------------------------------------------- *)

let snappy_bind = define
 `(snappy_bind (NONE:A option) (f:A->B option) = NONE) /\
  (snappy_bind (SOME x) f = f x)`;;

let SNAPPY_BIND_EQ_SOME = prove
 (`!(x:A option) (f:A->B option) y.
        snappy_bind x f = SOME y <=> ?z. x = SOME z /\ f z = SOME y`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `x:A option` (cases "option")) THEN
  REWRITE_TAC[snappy_bind; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

let SNAPPY_BIND_EQ_NONE = prove
 (`!(x:A option) (f:A->B option).
        snappy_bind x f = NONE <=> x = NONE \/ ?z. x = SOME z /\ f z = NONE`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `x:A option` (cases "option")) THEN
  REWRITE_TAC[snappy_bind; option_DISTINCT; option_INJ] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Small list lemmas.                                                        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_EL_SUB_LIST = prove
 (`!(l:A list) m n i. i < n /\ m + i < LENGTH l
                      ==> EL i (SUB_LIST(m,n) l) = EL (m + i) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  X_GEN_TAC `m:num` THEN STRUCT_CASES_TAC(SPEC `m:num` num_CASES) THENL
   [X_GEN_TAC `n:num` THEN STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
    X_GEN_TAC `i:num` THEN STRUCT_CASES_TAC(SPEC `i:num` num_CASES) THEN
    REWRITE_TAC[CONJUNCT1 LT; SUB_LIST_CLAUSES; ADD_CLAUSES; EL; HD; TL;
                LT_SUC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[SUB_LIST_CLAUSES; ADD_CLAUSES; EL; TL; LT_SUC]]);;

let SNAPPY_SUB_LIST_SUFFIX = prove
 (`!(l:A list) n. ?h. l = APPEND h (SUB_LIST(n,LENGTH l - n) l) /\
                      LENGTH h = MIN n (LENGTH l)`,
  REPEAT GEN_TAC THEN EXISTS_TAC `SUB_LIST(0,n) (l:A list)` THEN
  REWRITE_TAC[SUB_LIST_TOPSPLIT; LENGTH_SUB_LIST; SUB_0]);;

let SNAPPY_LENGTH_SUB_LIST_SUFFIX = prove
 (`!(l:A list) n. LENGTH(SUB_LIST(n,LENGTH l - n) l) = LENGTH l - n`,
  REWRITE_TAC[LENGTH_SUB_LIST] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The header: the uncompressed length as a varint of at most 5 bytes.       *)
(*                                                                           *)
(* Varint::Parse32WithLimit (used by GetUncompressedLength(const char*,..),  *)
(* snappy_uncompressed_length and snappy_uncompress) and                     *)
(* SnappyDecompressor::ReadUncompressedLength (used by RawUncompress and     *)
(* IsValidCompressedBuffer) accept the same headers: bytes 1-4 continue iff  *)
(* bit 7 is set, the 5th byte must be < 16 (so the value is < 2^32), and     *)
(* non-canonical encodings (e.g. 0x80 0x00 for 0) are accepted.              *)
(* snappy_varint_from k l reads a varint whose last byte may be the k-th.    *)
(* ------------------------------------------------------------------------- *)

let snappy_varint_from = define
 `(snappy_varint_from 0 (l:byte list) = NONE) /\
  (snappy_varint_from (SUC k) [] = NONE) /\
  (snappy_varint_from (SUC k) (CONS b t) =
     if k = 0 then (if val b < 16 then SOME(val b,t) else NONE)
     else if val b < 128 then SOME(val b,t)
     else snappy_bind (snappy_varint_from k t)
                      (\p. SOME(val b - 128 + 128 * FST p,SND p)))`;;

let snappy_varint = new_definition
 `snappy_varint (l:byte list) = snappy_varint_from 5 l`;;

let snappy_header = new_definition
 `snappy_header (l:byte list) =
    snappy_bind (snappy_varint l) (\p. SOME(FST p))`;;

let SNAPPY_VARINT_FROM_SOME = prove
 (`!k (l:byte list) v r.
        snappy_varint_from k l = SOME(v,r)
        ==> v < 2 EXP (7 * k - 3) /\
            ?h. l = APPEND h r /\ 1 <= LENGTH h /\ LENGTH h <= k`,
  INDUCT_TAC THEN REWRITE_TAC[snappy_varint_from; option_DISTINCT] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[snappy_varint_from; option_DISTINCT] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `[h:byte]` THEN REWRITE_TAC[APPEND; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THENL
   [DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN CONJ_TAC THENL
     [TRANS_TAC LTE_TRANS `2 EXP 7` THEN
      ASM_REWRITE_TAC[LE_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      EXISTS_TAC `[h:byte]` THEN REWRITE_TAC[APPEND; LENGTH] THEN ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SNAPPY_BIND_EQ_SOME; EXISTS_PAIR_THM; option_INJ; PAIR_EQ] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`v':num`; `r':byte list`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:byte list`; `v':num`; `r:byte list`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `h':byte list`
    STRIP_ASSUME_TAC)) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    SUBGOAL_THEN `7 * SUC k - 3 = (7 * k - 3) + 7` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[EXP_ADD]] THEN
    UNDISCH_TAC `v' < 2 EXP (7 * k - 3)` THEN
    SPEC_TAC(`2 EXP (7 * k - 3)`,`e:num`) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `val(h:byte) - 128 < 128` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `v' < e` THEN
    SPEC_TAC(`val(h:byte) - 128`,`d:num`) THEN
    ARITH_TAC;
    EXISTS_TAC `CONS (h:byte) h'` THEN
    ASM_REWRITE_TAC[APPEND; LENGTH] THEN ASM_ARITH_TAC]);;

let SNAPPY_VARINT_SOME = prove
 (`!(l:byte list) v r.
        snappy_varint l = SOME(v,r)
        ==> v < 2 EXP 32 /\
            ?h. l = APPEND h r /\ 1 <= LENGTH h /\ LENGTH h <= 5`,
  REWRITE_TAC[snappy_varint] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP SNAPPY_VARINT_FROM_SOME) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let SNAPPY_HEADER = prove
 (`!(l:byte list) m.
        snappy_header l = SOME m <=> ?r. snappy_varint l = SOME(m,r)`,
  REWRITE_TAC[snappy_header; SNAPPY_BIND_EQ_SOME; EXISTS_PAIR_THM;
              option_INJ] THEN
  MESON_TAC[]);;

(* An explicit form of the varint, byte by byte, for the machine proofs.     *)

let SNAPPY_VARINT_CLAUSES = prove
 (`snappy_varint [] = NONE /\
   snappy_varint (CONS b0 t0) =
    if val b0 < 128 then SOME(val b0,t0) else
    snappy_bind (snappy_varint_from 4 t0)
                (\p. SOME(val b0 - 128 + 128 * FST p,SND p))`,
  REWRITE_TAC[snappy_varint; num_CONV `5`; snappy_varint_from] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Copies from earlier output. A copy of length n at offset off appends n    *)
(* bytes, each equal to the byte off positions before it, so the copy may    *)
(* overlap its own output (IncrementalCopy semantics).                       *)
(* ------------------------------------------------------------------------- *)

let snappy_copy = define
 `(snappy_copy off 0 (out:byte list) = out) /\
  (snappy_copy off (SUC n) out =
     snappy_copy off n (APPEND out [EL (LENGTH out - off) out]))`;;

let LENGTH_SNAPPY_COPY = prove
 (`!off n (out:byte list). LENGTH(snappy_copy off n out) = LENGTH out + n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[snappy_copy; LENGTH_APPEND; LENGTH] THEN ARITH_TAC);;

let SNAPPY_COPY_ADD = prove
 (`!off a b (out:byte list).
        snappy_copy off (a + b) out = snappy_copy off b (snappy_copy off a out)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[snappy_copy; ADD_CLAUSES]);;

let SNAPPY_COPY_PREFIX = prove
 (`!off n (out:byte list). ?d. snappy_copy off n out = APPEND out d /\
                               LENGTH d = n`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[snappy_copy] THENL
   [MESON_TAC[APPEND_NIL; LENGTH]; ALL_TAC] THEN
  X_GEN_TAC `out:byte list` THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:byte list` STRIP_ASSUME_TAC o
    SPEC `APPEND out [EL (LENGTH out - off) (out:byte list)]`) THEN
  EXISTS_TAC `CONS (EL (LENGTH out - off) (out:byte list)) d` THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND; LENGTH]);;

let EL_SNAPPY_COPY_PREFIX = prove
 (`!off n (out:byte list) i.
        i < LENGTH out ==> EL i (snappy_copy off n out) = EL i out`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`off:num`; `n:num`; `out:byte list`] SNAPPY_COPY_PREFIX) THEN
  STRIP_TAC THEN ASM_SIMP_TAC[EL_APPEND]);;

let EL_SNAPPY_COPY = prove
 (`!off n (out:byte list) i.
        1 <= off /\ off <= LENGTH out /\
        LENGTH out <= i /\ i < LENGTH out + n
        ==> EL i (snappy_copy off n out) = EL (i - off) (snappy_copy off n out)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[snappy_copy] THENL
   [ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `out1 = APPEND out [EL (LENGTH out - off) (out:byte list)]` THEN
  SUBGOAL_THEN `LENGTH(out1:byte list) = LENGTH(out:byte list) + 1` ASSUME_TAC
  THENL [EXPAND_TAC "out1" THEN REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN
         ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `i = LENGTH(out:byte list)` THENL
   [ASM_SIMP_TAC[EL_SNAPPY_COPY_PREFIX; ARITH_RULE `x < x + 1`;
                 ARITH_RULE `1 <= off ==> x - off < x + 1`] THEN
    EXPAND_TAC "out1" THEN
    ASM_SIMP_TAC[EL_APPEND; LT_REFL; SUB_REFL; EL; HD;
                 ARITH_RULE `1 <= off /\ off <= x ==> x - off < x`];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let EL_SNAPPY_COPY_PERIODIC = prove
 (`!off n (out:byte list) i.
        1 <= off /\ off <= LENGTH out /\
        LENGTH out <= i /\ i < LENGTH out + n
        ==> EL i (snappy_copy off n out) =
            EL (LENGTH out - off + (i - LENGTH out) MOD off) out`,
  SUBGOAL_THEN
   `!off n (out:byte list) j.
        1 <= off /\ off <= LENGTH out /\ j < n
        ==> EL (LENGTH out + j) (snappy_copy off n out) =
            EL (LENGTH out - off + j MOD off) out`
  ASSUME_TAC THENL
   [GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_WF THEN
    X_GEN_TAC `j:num` THEN
    DISCH_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `j < off` THENL
     [ASM_SIMP_TAC[MOD_LT; EL_SNAPPY_COPY; ARITH_RULE `x <= x + j:num`;
                   ARITH_RULE `j < n ==> x + j < x + n:num`] THEN
      SUBGOAL_THEN `(LENGTH(out:byte list) + j) - off = LENGTH out - off + j`
      SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC EL_SNAPPY_COPY_PREFIX THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[EL_SNAPPY_COPY; ARITH_RULE `x <= x + j:num`;
                 ARITH_RULE `j < n ==> x + j < x + n:num`] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - off:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(j < off) ==> (x + j) - off = x + (j - off):num`] THEN
    DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `j = (j - off) + 1 * off` (fun th ->
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [th])
    THENL [ASM_ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD]];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`off:num`; `n:num`; `out:byte list`; `i - LENGTH(out:byte list)`]) THEN
    ASM_SIMP_TAC[ARITH_RULE `x <= i ==> x + (i - x) = i:num`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let SNAPPY_COPY_NONOVERLAP = prove
 (`!off n (out:byte list).
        n <= off /\ off <= LENGTH out
        ==> snappy_copy off n out =
            APPEND out (SUB_LIST(LENGTH out - off,n) out)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[snappy_copy; SUB_LIST_CLAUSES; APPEND_NIL]; ALL_TAC] THEN
  REWRITE_TAC[LIST_EQ; LENGTH_SNAPPY_COPY; LENGTH_APPEND; LENGTH_SUB_LIST] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[EL_APPEND] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[EL_SNAPPY_COPY_PREFIX] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_SNAPPY_COPY_PERIODIC o lhand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SNAPPY_EL_SUB_LIST o rand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `i - LENGTH(out:byte list) < off` (fun th -> SIMP_TAC[th; MOD_LT])
  THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* One tag. The tag byte c has type c MOD 4 and payload x = c DIV 4:         *)
(*                                                                           *)
(*  type 0, x < 60   literal of x + 1 bytes, which follow the tag;           *)
(*  type 0, x >= 60  literal; its length minus 1 is in the next x - 59       *)
(*                   bytes (little-endian; so the length can be 2^32, which  *)
(*                   no valid stream has since m < 2^32);                    *)
(*  type 1           copy, length x MOD 8 + 4, offset 256 * (x DIV 8) + the  *)
(*                   next byte;                                              *)
(*  type 2           copy, length x + 1, offset in the next 2 bytes;         *)
(*  type 3           copy, length x + 1, offset in the next 4 bytes.         *)
(*                                                                           *)
(* A tag fails (NONE) if its bytes are not all there, if it would make the   *)
(* output longer than m, or if it is a copy whose offset is 0 or more than   *)
(* the length of the output so far.                                          *)
(* ------------------------------------------------------------------------- *)

let snappy_literal = new_definition
 `snappy_literal m len (r:byte list) (out:byte list) =
    if len <= LENGTH r /\ LENGTH out + len <= m
    then SOME(SUB_LIST(len,LENGTH r - len) r,APPEND out (SUB_LIST(0,len) r))
    else NONE`;;

let snappy_copy_tag = new_definition
 `snappy_copy_tag m off len (r:byte list) (out:byte list) =
    if 1 <= off /\ off <= LENGTH out /\ LENGTH out + len <= m
    then SOME(r,snappy_copy off len out)
    else NONE`;;

let snappy_tag_step = define
 `(snappy_tag_step m [] (out:byte list) = NONE) /\
  (snappy_tag_step m (CONS c t) out =
     let x = val(c:byte) DIV 4 in
     if val c MOD 4 = 0 then
       (if x < 60 then snappy_literal m (x + 1) t out
        else if LENGTH t < x - 59 then NONE
        else snappy_literal m (num_of_bytelist(SUB_LIST(0,x - 59) t) + 1)
                            (SUB_LIST(x - 59,LENGTH t - (x - 59)) t) out)
     else if val c MOD 4 = 1 then
       (if LENGTH t < 1 then NONE
        else snappy_copy_tag m (256 * (x DIV 8) + val(HD t)) (x MOD 8 + 4)
                             (TL t) out)
     else if val c MOD 4 = 2 then
       (if LENGTH t < 2 then NONE
        else snappy_copy_tag m (num_of_bytelist(SUB_LIST(0,2) t)) (x + 1)
                             (SUB_LIST(2,LENGTH t - 2) t) out)
     else
       (if LENGTH t < 4 then NONE
        else snappy_copy_tag m (num_of_bytelist(SUB_LIST(0,4) t)) (x + 1)
                             (SUB_LIST(4,LENGTH t - 4) t) out))`;;

let SNAPPY_LITERAL_SOME = prove
 (`!m len (r:byte list) out r' out'.
        snappy_literal m len r out = SOME(r',out')
        ==> (?h. r = APPEND h r' /\ LENGTH h = len) /\
            (?d. out' = APPEND out d /\ LENGTH d = len) /\
            LENGTH out' <= m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[snappy_literal] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH_SUB_LIST] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`r:byte list`; `len:num`] SNAPPY_SUB_LIST_SUFFIX) THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
    CONJ_TAC THENL [FIRST_X_ASSUM ACCEPT_TAC; ASM_ARITH_TAC];
    EXISTS_TAC `SUB_LIST(0,len) (r:byte list)` THEN
    REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC]);;

let SNAPPY_COPY_TAG_SOME = prove
 (`!m off len (r:byte list) out r' out'.
        snappy_copy_tag m off len r out = SOME(r',out')
        ==> r' = r /\
            (?d. out' = APPEND out d /\ LENGTH d = len) /\
            LENGTH out' <= m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[snappy_copy_tag] THEN
  COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[SNAPPY_COPY_PREFIX; LENGTH_SNAPPY_COPY] THEN ASM_ARITH_TAC);;

(* Every successful tag consumes at least one byte of the stream and         *)
(* appends at least one byte to the output.                                  *)

let SNAPPY_TAG_STEP_SOME = prove
 (`!m (inp:byte list) out inp' out'.
        snappy_tag_step m inp out = SOME(inp',out')
        ==> (?h. inp = APPEND h inp' /\ ~(h = [])) /\
            (?d. out' = APPEND out d /\ ~(d = [])) /\
            LENGTH out' <= m`,
  let SUFFIX_CONS = prove
   (`!(c:byte) t r inp' h1 h0.
        t = APPEND h1 r /\ r = APPEND h0 inp'
        ==> ?h. CONS c t = APPEND h inp' /\ ~(h = [])`,
    REPEAT STRIP_TAC THEN EXISTS_TAC `CONS (c:byte) (APPEND h1 h0)` THEN
    ASM_REWRITE_TAC[APPEND; APPEND_ASSOC; NOT_CONS_NIL]) in
  let out_tac =
    EXISTS_TAC `d:byte list` THEN ASM_REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
    ARITH_TAC in
  let lit_tac rtm h1tm =
    DISCH_THEN(MP_TAC o MATCH_MP SNAPPY_LITERAL_SOME) THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `h0:byte list` (ASSUME_TAC o CONJUNCT1))
     (CONJUNCTS_THEN2 (X_CHOOSE_THEN `d:byte list` STRIP_ASSUME_TAC)
                      ASSUME_TAC)) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUFFIX_CONS THEN
      MAP_EVERY EXISTS_TAC [rtm; h1tm; `h0:byte list`] THEN
      REWRITE_TAC[SUB_LIST_TOPSPLIT; APPEND] THEN ASM_REWRITE_TAC[];
      out_tac;
      ASM_REWRITE_TAC[]]
  and copy_tac rtm h1tm =
    DISCH_THEN(MP_TAC o MATCH_MP SNAPPY_COPY_TAG_SOME) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (X_CHOOSE_THEN `d:byte list` STRIP_ASSUME_TAC)
                      ASSUME_TAC)) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUFFIX_CONS THEN
      MAP_EVERY EXISTS_TAC [rtm; h1tm; `[]:byte list`] THEN
      REWRITE_TAC[SUB_LIST_TOPSPLIT; APPEND] THEN ASM_REWRITE_TAC[] THEN
      TRY(MATCH_MP_TAC CONS_HD_TL THEN
          REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN ASM_ARITH_TAC);
      out_tac;
      ASM_REWRITE_TAC[]] in
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[snappy_tag_step; option_DISTINCT] THEN
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT]) THENL
   [lit_tac `t:byte list` `[]:byte list`;
    lit_tac `SUB_LIST(val(h:byte) DIV 4 - 59,
                      LENGTH(t:byte list) - (val h DIV 4 - 59)) t`
            `SUB_LIST(0,val(h:byte) DIV 4 - 59) (t:byte list)`;
    copy_tac `TL(t:byte list)` `[HD(t:byte list)]`;
    copy_tac `SUB_LIST(2,LENGTH(t:byte list) - 2) t`
             `SUB_LIST(0,2) (t:byte list)`;
    copy_tac `SUB_LIST(4,LENGTH(t:byte list) - 4) t`
             `SUB_LIST(0,4) (t:byte list)`]);;

let SNAPPY_TAG_STEP_LENGTH = prove
 (`!m (inp:byte list) out inp' out'.
        snappy_tag_step m inp out = SOME(inp',out')
        ==> LENGTH inp' < LENGTH inp /\
            LENGTH out < LENGTH out' /\ LENGTH out' <= m`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SNAPPY_TAG_STEP_SOME) THEN
  REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The tag loop. snappy_decode_tags m inp out decodes the tags in inp after  *)
(* the output out has been produced: the stream is valid iff all tags        *)
(* succeed and the output has length m when inp is used up (since every tag  *)
(* appends at least one byte and never beyond m, nothing may follow a tag    *)
(* that completes the output). It is defined through a fuel argument (any   *)
(* fuel >= LENGTH inp gives the same, SNAPPY_DECODE_TAGS_FUEL); the          *)
(* recursion equation is SNAPPY_DECODE_TAGS.                                 *)
(* ------------------------------------------------------------------------- *)

let snappy_decode_tags_fuel = new_recursive_definition num_RECURSION
 `(snappy_decode_tags_fuel 0 m (inp:byte list) (out:byte list) =
     if inp = [] /\ LENGTH out = m then SOME out else NONE) /\
  (snappy_decode_tags_fuel (SUC n) m inp out =
     if inp = [] then (if LENGTH out = m then SOME out else NONE)
     else snappy_bind (snappy_tag_step m inp out)
                      (\s. snappy_decode_tags_fuel n m (FST s) (SND s)))`;;

let snappy_decode_tags = new_definition
 `snappy_decode_tags m (inp:byte list) (out:byte list) =
    snappy_decode_tags_fuel (LENGTH inp) m inp out`;;

(* The whole stream: header, then the tags from an empty output.             *)

let snappy_decode = new_definition
 `snappy_decode (l:byte list) =
    snappy_bind (snappy_varint l)
                (\p. snappy_decode_tags (FST p) (SND p) [])`;;

(* The first k tags (from state s = (unread stream, output so far)).        *)

let snappy_steps = new_recursive_definition num_RECURSION
 `(snappy_steps 0 m (s:byte list # byte list) = SOME s) /\
  (snappy_steps (SUC k) m s =
     snappy_bind (snappy_tag_step m (FST s) (SND s)) (snappy_steps k m))`;;

let SNAPPY_DECODE_TAGS_FUEL = prove
 (`!n m (inp:byte list) out.
        LENGTH inp <= n
        ==> snappy_decode_tags_fuel n m inp out = snappy_decode_tags m inp out`,
  SUBGOAL_THEN
   `!n p m (inp:byte list) out.
        LENGTH inp <= n /\ LENGTH inp <= p
        ==> snappy_decode_tags_fuel n m inp out =
            snappy_decode_tags_fuel p m inp out`
   (fun th -> REWRITE_TAC[snappy_decode_tags] THEN MESON_TAC[th; LE_REFL]) THEN
  INDUCT_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[snappy_decode_tags_fuel; ARITH_RULE `x <= 0 <=> x = 0`;
              LENGTH_EQ_NIL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`m:num`; `inp:byte list`; `out:byte list`]
    SNAPPY_TAG_STEP_LENGTH) THEN
  SPEC_TAC(`snappy_tag_step m inp out`,`r:(byte list#byte list)option`) THEN
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:(byte list#byte list)option` (cases "option")) THEN
  REWRITE_TAC[snappy_bind] THEN
  DISCH_THEN(MP_TAC o SPECL [`FST(a:byte list#byte list)`; `SND(a:byte list#byte list)`]) THEN
  REWRITE_TAC[PAIR] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let SNAPPY_DECODE_TAGS = prove
 (`!m (inp:byte list) out.
        snappy_decode_tags m inp out =
          if inp = [] then (if LENGTH out = m then SOME out else NONE)
          else snappy_bind (snappy_tag_step m inp out)
                           (\s. snappy_decode_tags m (FST s) (SND s))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
  REWRITE_TAC[snappy_decode_tags; LENGTH; snappy_decode_tags_fuel;
              NOT_CONS_NIL] THEN
  MP_TAC(ISPECL [`m:num`; `CONS (h:byte) t`; `out:byte list`]
    SNAPPY_TAG_STEP_LENGTH) THEN
  SPEC_TAC(`snappy_tag_step m (CONS h t) out`,`r:(byte list#byte list)option`) THEN
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:(byte list#byte list)option` (cases "option")) THEN
  REWRITE_TAC[snappy_bind] THEN
  DISCH_THEN(MP_TAC o SPECL [`FST(a:byte list#byte list)`; `SND(a:byte list#byte list)`]) THEN
  REWRITE_TAC[PAIR; LENGTH] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM snappy_decode_tags] THEN
  MATCH_MP_TAC SNAPPY_DECODE_TAGS_FUEL THEN ASM_ARITH_TAC);;

let SNAPPY_DECODE_TAGS_NIL = prove
 (`!m (out:byte list).
        snappy_decode_tags m [] out = if LENGTH out = m then SOME out else NONE`,
  ONCE_REWRITE_TAC[SNAPPY_DECODE_TAGS] THEN REWRITE_TAC[]);;

let SNAPPY_DECODE_TAGS_STEP = prove
 (`!m (inp:byte list) out inp' out'.
        snappy_tag_step m inp out = SOME(inp',out')
        ==> snappy_decode_tags m inp out = snappy_decode_tags m inp' out'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(inp:byte list = [])` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN FIRST_X_ASSUM(MP_TAC) THEN
    REWRITE_TAC[snappy_tag_step; option_DISTINCT];
    GEN_REWRITE_TAC LAND_CONV [SNAPPY_DECODE_TAGS] THEN
    ASM_REWRITE_TAC[snappy_bind]]);;

let SNAPPY_DECODE_TAGS_FAIL = prove
 (`!m (inp:byte list) out.
        ~(inp = []) /\ snappy_tag_step m inp out = NONE
        ==> snappy_decode_tags m inp out = NONE`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[SNAPPY_DECODE_TAGS] THEN
  ASM_REWRITE_TAC[snappy_bind]);;

let SNAPPY_DECODE_TAGS_SOME = prove
 (`!m (inp:byte list) out x.
        snappy_decode_tags m inp out = SOME x
        ==> LENGTH x = m /\ ?d. x = APPEND out d`,
  SUBGOAL_THEN
   `!n m (inp:byte list) out x.
        LENGTH inp <= n /\ snappy_decode_tags m inp out = SOME x
        ==> LENGTH x = m /\ ?d. x = APPEND out d`
   (fun th -> REPEAT GEN_TAC THEN DISCH_TAC THEN
              MP_TAC(SPECL [`LENGTH(inp:byte list)`; `m:num`; `inp:byte list`;
                            `out:byte list`; `x:byte list`] th) THEN
              ASM_REWRITE_TAC[LE_REFL]) THEN
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[SNAPPY_DECODE_TAGS] THEN
  ASM_CASES_TAC `inp:byte list = []` THEN ASM_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; LENGTH; LE_0] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `[]:byte list` THEN REWRITE_TAC[APPEND_NIL];
    REWRITE_TAC[ARITH_RULE `x <= 0 <=> x = 0`; LENGTH_EQ_NIL] THEN
    ASM_REWRITE_TAC[];
    COND_CASES_TAC THEN REWRITE_TAC[option_DISTINCT; option_INJ; LENGTH; LE_0] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `[]:byte list` THEN REWRITE_TAC[APPEND_NIL];
    ALL_TAC] THEN
  REWRITE_TAC[SNAPPY_BIND_EQ_SOME; EXISTS_PAIR_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `inp':byte list`
    (X_CHOOSE_THEN `out':byte list` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SNAPPY_TAG_STEP_LENGTH) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SNAPPY_TAG_STEP_SOME) THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:byte list` STRIP_ASSUME_TAC o
    CONJUNCT1 o CONJUNCT2) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `inp':byte list`; `out':byte list`;
                                `x:byte list`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `APPEND (d0:byte list) d` THEN REWRITE_TAC[APPEND_ASSOC]);;

(* Once the output has its final length, the stream must end.                *)

let SNAPPY_DECODE_TAGS_FULL = prove
 (`!m (inp:byte list) out.
        LENGTH out = m
        ==> snappy_decode_tags m inp out = if inp = [] then SOME out else NONE`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[SNAPPY_DECODE_TAGS] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`m:num`; `inp:byte list`; `out:byte list`]
    SNAPPY_TAG_STEP_LENGTH) THEN
  SPEC_TAC(`snappy_tag_step m inp out`,`r:(byte list#byte list)option`) THEN
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:(byte list#byte list)option` (cases "option")) THEN
  REWRITE_TAC[snappy_bind] THEN
  DISCH_THEN(MP_TAC o SPECL [`FST(a:byte list#byte list)`; `SND(a:byte list#byte list)`]) THEN
  REWRITE_TAC[PAIR] THEN ASM_ARITH_TAC);;

(* The first k tags: loop invariants of machine-code decoders.              *)

let SNAPPY_STEPS_DECODE_TAGS = prove
 (`!k m (inp:byte list) out inp' out'.
        snappy_steps k m (inp,out) = SOME(inp',out')
        ==> snappy_decode_tags m inp out = snappy_decode_tags m inp' out'`,
  INDUCT_TAC THEN REWRITE_TAC[snappy_steps; option_INJ; PAIR_EQ] THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[SNAPPY_BIND_EQ_SOME; EXISTS_PAIR_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `i1:byte list` (X_CHOOSE_THEN `o1:byte list`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP SNAPPY_DECODE_TAGS_STEP) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let SNAPPY_STEPS_SUC = prove
 (`!k m (s:byte list # byte list).
        snappy_steps (SUC k) m s =
        snappy_bind (snappy_steps k m s)
                    (\s. snappy_tag_step m (FST s) (SND s))`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [CONJUNCT2 snappy_steps] THENL
   [REWRITE_TAC[CONJUNCT1 snappy_steps; snappy_bind]; ALL_TAC] THEN
  TRY(GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [CONJUNCT2 snappy_steps]) THEN
  SPEC_TAC(`snappy_tag_step m (FST(s:byte list#byte list)) (SND s)`,
           `r:(byte list#byte list)option`) THEN
  GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `r:(byte list#byte list)option` (cases "option")) THEN
  ASM_REWRITE_TAC[snappy_bind; CONJUNCT1 snappy_steps]);;

let SNAPPY_STEPS_SOME = prove
 (`!k m (inp:byte list) out inp' out'.
        snappy_steps k m (inp,out) = SOME(inp',out')
        ==> (?h. inp = APPEND h inp' /\ k <= LENGTH h) /\
            (?d. out' = APPEND out d /\ k <= LENGTH d) /\
            (LENGTH out <= m ==> LENGTH out' <= m)`,
  INDUCT_TAC THEN REWRITE_TAC[snappy_steps; option_INJ; PAIR_EQ] THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN
    REWRITE_TAC[LE_0] THEN CONJ_TAC THEN EXISTS_TAC `[]:byte list` THEN
    REWRITE_TAC[APPEND; APPEND_NIL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[SNAPPY_BIND_EQ_SOME; EXISTS_PAIR_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `i1:byte list` (X_CHOOSE_THEN `o1:byte list`
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  FIRST_X_ASSUM(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SNAPPY_TAG_STEP_SOME) THEN
  REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `h1:byte list` STRIP_ASSUME_TAC)
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `d1:byte list` STRIP_ASSUME_TAC)
                    ASSUME_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `h2:byte list` STRIP_ASSUME_TAC)
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `d2:byte list` STRIP_ASSUME_TAC)
                    ASSUME_TAC)) THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `APPEND (h1:byte list) h2` THEN
    ASM_REWRITE_TAC[APPEND_ASSOC; LENGTH_APPEND] THEN ASM_ARITH_TAC;
    EXISTS_TAC `APPEND (d1:byte list) d2` THEN
    ASM_REWRITE_TAC[APPEND_ASSOC; LENGTH_APPEND] THEN ASM_ARITH_TAC;
    DISCH_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (is_imp o concl)) THEN
    FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The whole stream.                                                         *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_DECODE = prove
 (`!l:byte list.
        snappy_decode l =
          snappy_bind (snappy_varint l)
                      (\p. snappy_decode_tags (FST p) (SND p) [])`,
  REWRITE_TAC[snappy_decode]);;

let SNAPPY_DECODE_SOME = prove
 (`!(l:byte list) x.
        snappy_decode l = SOME x
        ==> LENGTH x < 2 EXP 32 /\
            ?r. snappy_varint l = SOME(LENGTH x,r) /\
                snappy_decode_tags (LENGTH x) r [] = SOME x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[snappy_decode; SNAPPY_BIND_EQ_SOME; EXISTS_PAIR_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `r:byte list`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP SNAPPY_DECODE_TAGS_SOME) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP SNAPPY_VARINT_SOME) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `r:byte list` THEN ASM_REWRITE_TAC[]);;

let SNAPPY_DECODE_HEADER = prove
 (`!(l:byte list) x.
        snappy_decode l = SOME x ==> snappy_header l = SOME(LENGTH x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SNAPPY_DECODE_SOME) THEN
  REWRITE_TAC[SNAPPY_HEADER] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The results of the C API (snappy-c.cc) and of the C++ functions that the  *)
(* C API calls. Status values: SNAPPY_OK = 0, SNAPPY_INVALID_INPUT = 1,       *)
(* SNAPPY_BUFFER_TOO_SMALL = 2.                                              *)
(*                                                                           *)
(* snappy_uncompressed_length(in, n, &r) and                                 *)
(*   snappy::GetUncompressedLength(in, n, &r):                               *)
(*   OK / true iff snappy_header l = SOME m, and then r := m (else r is not  *)
(*   written).                                                               *)
(* snappy_validate_compressed_buffer(in, n) and                              *)
(*   snappy::IsValidCompressedBuffer(in, n):                                 *)
(*   OK / true iff snappy_decode l <> NONE.                                  *)
(* snappy::RawUncompress(in, n, out):                                        *)
(*   true iff snappy_decode l = SOME x, and then out holds x.                *)
(* snappy_uncompress(in, n, out, &ulen): status                              *)
(*   snappy_uncompress_status l ulen; if 0 then out holds x and              *)
(*   ulen := LENGTH x where snappy_decode l = SOME x; else ulen is not       *)
(*   written.                                                                *)
(* snappy::RawUncompressToIOVec(in, n, iov, cnt):                            *)
(*   true iff snappy_decode l = SOME x and LENGTH x <= the total length of   *)
(*   the iovecs, and then x is scattered over the iovecs in order.           *)
(* ------------------------------------------------------------------------- *)

let snappy_uncompressed_length_status = new_definition
 `snappy_uncompressed_length_status (l:byte list) =
    if snappy_header l = NONE then 1 else 0`;;

let snappy_validate_status = new_definition
 `snappy_validate_status (l:byte list) =
    if snappy_decode l = NONE then 1 else 0`;;

let snappy_uncompress_status_of = define
 `(snappy_uncompress_status_of NONE (d:(byte list)option) (ulen:num) = 1) /\
  (snappy_uncompress_status_of (SOME m) d ulen =
     if ulen < m then 2 else if d = NONE then 1 else 0)`;;

let snappy_uncompress_status = new_definition
 `snappy_uncompress_status (l:byte list) ulen =
    snappy_uncompress_status_of (snappy_header l) (snappy_decode l) ulen`;;

let snappy_iovec_ok = new_definition
 `snappy_iovec_ok (l:byte list) cap <=>
    ?x. snappy_decode l = SOME x /\ LENGTH x <= cap`;;

let SNAPPY_UNCOMPRESS_STATUS = prove
 (`!(l:byte list) ulen.
        (snappy_uncompress_status l ulen = 0 <=>
         ?x. snappy_decode l = SOME x /\ LENGTH x <= ulen) /\
        (snappy_uncompress_status l ulen = 2 <=>
         ?m. snappy_header l = SOME m /\ ulen < m) /\
        (snappy_uncompress_status l ulen = 1 <=>
         snappy_header l = NONE \/
         (?m. snappy_header l = SOME m /\ m <= ulen) /\ snappy_decode l = NONE)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[snappy_uncompress_status] THEN
  ASM_CASES_TAC `snappy_decode (l:byte list) = NONE` THENL
   [ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`snappy_header(l:byte list)`,`hh:num option`) THEN
    MATCH_MP_TAC option_INDUCT THEN
    REWRITE_TAC[snappy_uncompress_status_of; option_DISTINCT; option_INJ;
                UNWIND_THM1; ARITH_EQ] THEN
    X_GEN_TAC `a:num` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    ASM_ARITH_TAC;
    FIRST_X_ASSUM(X_CHOOSE_TAC `x:byte list` o MATCH_MP (MESON[cases "option"]
     `~(y:(byte list)option = NONE) ==> ?x. y = SOME x`)) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP SNAPPY_DECODE_HEADER) THEN
    ASM_REWRITE_TAC[snappy_uncompress_status_of; option_DISTINCT; option_INJ;
                    UNWIND_THM1] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Evaluation of the definitions on concrete streams by Compute.CBV_CONV.    *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_EVAL_LENGTH = prove
 (`LENGTH ([]:A list) = 0 /\ LENGTH (CONS (h:A) t) = LENGTH t + 1`,
  REWRITE_TAC[LENGTH; ADD1]);;

let SNAPPY_EVAL_NIL_EQ = prove
 (`(([]:A list) = [] <=> T) /\ (CONS (h:A) t = [] <=> F)`,
  REWRITE_TAC[NOT_CONS_NIL]);;

let SNAPPY_EVAL_SUB_LIST = prove
 (`(!m n. SUB_LIST(m,n) ([]:A list) = []) /\
   (!m n (h:A) t. SUB_LIST(m,n) (CONS h t) =
        if n = 0 then []
        else if m = 0 then CONS h (SUB_LIST(0,n - 1) t)
        else SUB_LIST(m - 1,n) t)`,
  REWRITE_TAC[SUB_LIST_CLAUSES] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  STRUCT_CASES_TAC(SPEC `m:num` num_CASES) THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; NOT_SUC; SUC_SUB1]);;

let SNAPPY_EVAL_VARINT_FROM = prove
 (`(!k. snappy_varint_from k ([]:byte list) = NONE) /\
   (!k b t. snappy_varint_from k (CONS b t) =
     if k = 0 then NONE
     else if k = 1 then (if val b < 16 then SOME(val b,t) else NONE)
     else if val b < 128 then SOME(val b,t)
     else snappy_bind (snappy_varint_from (k - 1) t)
                      (\p. SOME(val b - 128 + 128 * FST p,SND p)))`,
  CONJ_TAC THEN INDUCT_TAC THEN REWRITE_TAC[snappy_varint_from; NOT_SUC] THEN
  REWRITE_TAC[SUC_SUB1; ARITH_RULE `SUC k = 1 <=> k = 0`]);;

let SNAPPY_EVAL_COPY = prove
 (`!off n (out:byte list).
        snappy_copy off n out =
        if n = 0 then out
        else snappy_copy off (n - 1) (APPEND out [EL (LENGTH out - off) out])`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[snappy_copy; NOT_SUC; SUC_SUB1]);;

let SNAPPY_EVAL_FUEL = prove
 (`!n m (inp:byte list) out.
     snappy_decode_tags_fuel n m inp out =
     if n = 0 then (if inp = [] /\ LENGTH out = m then SOME out else NONE)
     else if inp = [] then (if LENGTH out = m then SOME out else NONE)
     else snappy_bind (snappy_tag_step m inp out)
                      (\s. snappy_decode_tags_fuel (n - 1) m (FST s) (SND s))`,
  INDUCT_TAC THEN REWRITE_TAC[snappy_decode_tags_fuel; NOT_SUC; SUC_SUB1]);;

let SNAPPY_EVAL_STEPS = prove
 (`!k m (s:byte list#byte list).
     snappy_steps k m s =
     if k = 0 then SOME s
     else snappy_bind (snappy_tag_step m (FST s) (SND s)) (snappy_steps (k - 1) m)`,
  INDUCT_TAC THEN REWRITE_TAC[snappy_steps; NOT_SUC; SUC_SUB1]);;

let SNAPPY_EVAL_EL = prove
 (`!n (h:A) t. EL n (CONS h t) = if n = 0 then h else EL (n - 1) t`,
  REWRITE_TAC[EL_CONS]);;

let SNAPPY_EQ_CONV tm =
  try NUM_EQ_CONV tm with Failure _ ->
  let l,r = dest_eq tm in
  if type_of l = `:byte` && is_comb l && is_comb r &&
     is_numeral(rand l) && is_numeral(rand r)
  then WORD_REDUCE_CONV tm else failwith "SNAPPY_EQ_CONV";;

let snappy_compset =
  let cs = Compute.bool_compset() in
  Compute.add_thms
   [snappy_bind; snappy_varint; snappy_header; SNAPPY_EVAL_VARINT_FROM;
    SNAPPY_EVAL_COPY; snappy_literal; snappy_copy_tag; snappy_tag_step;
    SNAPPY_EVAL_FUEL; snappy_decode_tags; snappy_decode; SNAPPY_EVAL_STEPS;
    snappy_uncompressed_length_status; snappy_validate_status;
    snappy_uncompress_status_of; snappy_uncompress_status;
    SNAPPY_EVAL_LENGTH; SNAPPY_EVAL_NIL_EQ; SNAPPY_EVAL_SUB_LIST;
    SNAPPY_EVAL_EL; APPEND; HD; TL; FST; SND; LET_END_DEF;
    num_of_bytelist; option_DISTINCT; option_INJ] cs;
  List.iter (fun (t,n,c) -> Compute.add_conv (t,n,c) cs)
   [`(+):num->num->num`,2,NUM_ADD_CONV;
    `(-):num->num->num`,2,NUM_SUB_CONV;
    `( * ):num->num->num`,2,NUM_MULT_CONV;
    `(DIV):num->num->num`,2,NUM_DIV_CONV;
    `(MOD):num->num->num`,2,NUM_MOD_CONV;
    `(<):num->num->bool`,2,NUM_LT_CONV;
    `(<=):num->num->bool`,2,NUM_LE_CONV;
    `(=):num->num->bool`,2,SNAPPY_EQ_CONV;
    `val:byte->num`,1,WORD_REDUCE_CONV];
  cs;;

let SNAPPY_EVAL_CONV = Compute.CBV_CONV snappy_compset;;
