(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Notions of snappy's decompressor (SnappyDecompressor in snappy.cc,        *)
(* snappy 1.3.1) that the machine-code proofs state their contracts with,    *)
(* and their relation to the format model of snappy_format.ml.               *)
(*                                                                           *)
(*  - snappy_tag_needed c is CalculateNeeded(c): the number of bytes of the  *)
(*    tag that starts with the byte c, the tag byte included, without the    *)
(*    data of a literal: 1 for a literal of at most 60 bytes, 2..5 for the   *)
(*    long literals (tag bytes 0xf0, 0xf4, 0xf8, 0xfc: 1..4 length bytes),   *)
(*    2, 3 and 5 for the copies with 1-, 2- and 4-byte offsets.              *)
(*                                                                           *)
(*  - snappy_refill_ok rest: SnappyDecompressor::RefillTag() succeeds on the *)
(*    unread stream rest: it is not empty and has all the bytes of its first *)
(*    tag (SNAPPY_TAG_STEP_SHORT: otherwise the tag fails in the model too). *)
(* ========================================================================= *)

needs "common/snappy/snappy_format.ml";;

let snappy_tag_needed = new_definition
 `snappy_tag_needed (c:byte) =
    if val c MOD 4 = 0 then (if 240 <= val c then val c DIV 4 - 58 else 1)
    else if val c MOD 4 = 1 then 2
    else if val c MOD 4 = 2 then 3
    else 5`;;

let snappy_refill_ok = new_definition
 `snappy_refill_ok (rest:byte list) <=>
    ~(rest = []) /\ snappy_tag_needed (HD rest) <= LENGTH rest`;;

let SNAPPY_TAG_NEEDED_BOUNDS = prove
 (`!c:byte. 1 <= snappy_tag_needed c /\ snappy_tag_needed c <= 5`,
  GEN_TAC THEN REWRITE_TAC[snappy_tag_needed] THEN
  MP_TAC(ISPEC `c:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  MP_TAC(SPECL [`val(c:byte)`; `4`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* A tag whose bytes are not all in the stream fails.                        *)

let SNAPPY_TAG_STEP_SHORT = prove
 (`!m (rest:byte list) out.
        ~(rest = []) /\ LENGTH rest < snappy_tag_needed (HD rest)
        ==> snappy_tag_step m rest out = NONE`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; HD; LENGTH] THEN
  X_GEN_TAC `out:byte list` THEN
  REWRITE_TAC[snappy_tag_needed; snappy_tag_step] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  MP_TAC(SPECL [`val(h:byte)`; `4`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT COND_CASES_TAC THEN REPEAT STRIP_TAC THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC);;

(* So the stream fails from any state whose first tag is short.              *)

let SNAPPY_DECODE_TAGS_SHORT = prove
 (`!m (rest:byte list) out.
        ~(rest = []) /\ ~snappy_refill_ok rest
        ==> snappy_decode_tags m rest out = NONE`,
  REWRITE_TAC[snappy_refill_ok] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SNAPPY_DECODE_TAGS_FAIL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SNAPPY_TAG_STEP_SHORT THEN ASM_MESON_TAC[NOT_LE]);;

(* ------------------------------------------------------------------------- *)
(* The header byte by byte, in the order in which the parsers read it: the   *)
(* k-th byte is EL k l, and the parsers stop at the end of the input.        *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_HEADER_BYTES = prove
 (`!l:byte list.
     snappy_header l =
     if LENGTH l = 0 then NONE
     else if val(EL 0 l) < 128 then SOME(val(EL 0 l))
     else if LENGTH l = 1 then NONE
     else if val(EL 1 l) < 128
     then SOME(val(EL 0 l) - 128 + 128 * val(EL 1 l))
     else if LENGTH l = 2 then NONE
     else if val(EL 2 l) < 128
     then SOME(val(EL 0 l) - 128 + 128 * (val(EL 1 l) - 128 +
               128 * val(EL 2 l)))
     else if LENGTH l = 3 then NONE
     else if val(EL 3 l) < 128
     then SOME(val(EL 0 l) - 128 + 128 * (val(EL 1 l) - 128 +
               128 * (val(EL 2 l) - 128 + 128 * val(EL 3 l))))
     else if LENGTH l = 4 then NONE
     else if val(EL 4 l) < 16
     then SOME(val(EL 0 l) - 128 + 128 * (val(EL 1 l) - 128 +
               128 * (val(EL 2 l) - 128 + 128 * (val(EL 3 l) - 128 +
               128 * val(EL 4 l)))))
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
  REWRITE_TAC[snappy_header; snappy_varint;
              ARITH_RULE `5 = SUC 4 /\ 4 = SUC 3 /\ 3 = SUC 2`; TWO; ONE] THEN
  REWRITE_TAC[snappy_varint_from; LENGTH; EL; HD; TL; SUC_INJ; NOT_SUC] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[snappy_bind; option_DISTINCT; option_INJ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN FIRST_ASSUM CONTR_TAC);;

(* ------------------------------------------------------------------------- *)
(* Bytes as the code tests them.                                             *)
(* ------------------------------------------------------------------------- *)

let VAL_BYTE_LT_128 = prove
 (`!b:byte. val b < 128 <=> ~bit 7 b`,
  GEN_TAC THEN REWRITE_TAC[BIT_VAL] THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ODD_MOD] THEN
  SPEC_TAC(`val(b:byte)`,`v:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV);;

let VAL_BYTE_LT_16 = prove
 (`!b:byte. val b < 16 <=> ~bit 4 b /\ ~bit 5 b /\ ~bit 6 b /\ ~bit 7 b`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_BYTE_LT_128] THEN
  REWRITE_TAC[BIT_VAL; ODD_MOD] THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(b:byte)`,`v:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV);;

let VAL_BYTE_HI = prove
 (`!b:byte. ~(val b < 128) ==> val b - 128 = val(word_and b (word 127):byte)`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `127 = 2 EXP 7 - 1`; VAL_WORD_AND_MASK_WORD] THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(b:byte)`,`v:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* The value of a header as the code assembles it from 7-bit groups:        *)
(* rewrite the subtractions into masks and the sums into words, and         *)
(* bit-blast with the facts val b < 128, ~(val b < 128), val b < 16 among    *)
(* the assumptions (the bytes, such as EL k l, generalized to variables;    *)
(* the bit-blasting is done without the other assumptions).                 *)

let SNAPPY_HEADER_WORD_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if can (term_match [] `val(b:byte) < k`) (concl th) ||
       can (term_match [] `~(val(b:byte) < k)`) (concl th)
    then MP_TAC th else NO_TAC)) THEN
  SIMP_TAC[VAL_BYTE_HI] THEN REWRITE_TAC[WORD_ADD; WORD_MUL] THEN
  REWRITE_TAC[GSYM word_zx; VAL_BYTE_LT_128; VAL_BYTE_LT_16] THEN
  W(fun (_,w) ->
    let atoms = setify(find_terms (fun t ->
      type_of t = `:byte` &&
      (match fst(strip_comb t) with
         Const(("EL"|"HD"|"read"),_) -> true | _ -> false)) w) in
    MAP_EVERY (fun t -> SPEC_TAC(t,genvar `:byte`)) atoms) THEN
  W(fun (_,w) ->
    ACCEPT_TAC(TAC_PROOF(([],w),REPEAT GEN_TAC THEN BITBLAST_TAC)));;
