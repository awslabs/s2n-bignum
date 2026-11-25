(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The tag step of snappy_format.ml by the kind of the tag, as the slow path *)
(* of SnappyDecompressor::DecompressAllTags (snappy.cc) decodes one tag: a   *)
(* literal of at most 60 bytes, a long literal with 1-4 length bytes, and    *)
(* the copies with 1-, 2- and 4-byte offsets; and what the slow path does    *)
(* with the result (the stream after the tag, the output).                  *)
(* ========================================================================= *)

needs "common/snappy/snappy_decompressor.ml";;

let SNAPPY_TAG_STEP_LITERAL = prove
 (`!m c (t:byte list) out.
        val c MOD 4 = 0 /\ val c DIV 4 < 60
        ==> snappy_tag_step m (CONS c t) out =
            snappy_literal m (val c DIV 4 + 1) t out`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[snappy_tag_step] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[]);;

let SNAPPY_TAG_STEP_LONG_LITERAL = prove
 (`!m c (t:byte list) out.
        val c MOD 4 = 0 /\ ~(val c DIV 4 < 60) /\ val c DIV 4 - 59 <= LENGTH t
        ==> snappy_tag_step m (CONS c t) out =
            snappy_literal m
              (num_of_bytelist(SUB_LIST(0,val c DIV 4 - 59) t) + 1)
              (SUB_LIST(val c DIV 4 - 59,LENGTH t - (val c DIV 4 - 59)) t)
              out`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[snappy_tag_step] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[GSYM NOT_LE]);;

let SNAPPY_TAG_STEP_COPY1 = prove
 (`!m c (t:byte list) out.
        val c MOD 4 = 1 /\ 1 <= LENGTH t
        ==> snappy_tag_step m (CONS c t) out =
            snappy_copy_tag m (256 * (val c DIV 4 DIV 8) + val(HD t))
                            (val c DIV 4 MOD 8 + 4) (TL t) out`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[snappy_tag_step] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[GSYM NOT_LE; ARITH_EQ]);;

let SNAPPY_TAG_STEP_COPY2 = prove
 (`!m c (t:byte list) out.
        val c MOD 4 = 2 /\ 2 <= LENGTH t
        ==> snappy_tag_step m (CONS c t) out =
            snappy_copy_tag m (num_of_bytelist(SUB_LIST(0,2) t))
                            (val c DIV 4 + 1) (SUB_LIST(2,LENGTH t - 2) t) out`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[snappy_tag_step] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[GSYM NOT_LE; ARITH_EQ]);;

let SNAPPY_TAG_STEP_COPY4 = prove
 (`!m c (t:byte list) out.
        val c MOD 4 = 3 /\ 4 <= LENGTH t
        ==> snappy_tag_step m (CONS c t) out =
            snappy_copy_tag m (num_of_bytelist(SUB_LIST(0,4) t))
                            (val c DIV 4 + 1) (SUB_LIST(4,LENGTH t - 4) t) out`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[snappy_tag_step] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[GSYM NOT_LE; ARITH_EQ]);;

(* A tag that succeeds or fails, in the decoding of the whole stream.        *)

let SNAPPY_DECODE_TAGS_CONS_STEP = prove
 (`!m c (t:byte list) out r o'.
        snappy_tag_step m (CONS c t) out = SOME(r,o')
        ==> snappy_decode_tags m (CONS c t) out = snappy_decode_tags m r o'`,
  MESON_TAC[SNAPPY_DECODE_TAGS_STEP]);;

let SNAPPY_DECODE_TAGS_CONS_FAIL = prove
 (`!m c (t:byte list) out.
        snappy_tag_step m (CONS c t) out = NONE
        ==> snappy_decode_tags m (CONS c t) out = NONE`,
  MESON_TAC[SNAPPY_DECODE_TAGS_FAIL; NOT_CONS_NIL]);;

(* The literal and the copy, as SOME or NONE.                                *)

let SNAPPY_LITERAL_CASES = prove
 (`!m len (r:byte list) out.
        (len <= LENGTH r /\ LENGTH out + len <= m
         ==> snappy_literal m len r out =
             SOME(SUB_LIST(len,LENGTH r - len) r,APPEND out (SUB_LIST(0,len) r))) /\
        (~(len <= LENGTH r) ==> snappy_literal m len r out = NONE) /\
        (~(LENGTH out + len <= m) ==> snappy_literal m len r out = NONE)`,
  REWRITE_TAC[snappy_literal] THEN MESON_TAC[]);;

let SNAPPY_COPY_TAG_CASES = prove
 (`!m off len (r:byte list) out.
        (1 <= off /\ off <= LENGTH out /\ LENGTH out + len <= m
         ==> snappy_copy_tag m off len r out = SOME(r,snappy_copy off len out)) /\
        (~(1 <= off /\ off <= LENGTH out /\ LENGTH out + len <= m)
         ==> snappy_copy_tag m off len r out = NONE)`,
  REWRITE_TAC[snappy_copy_tag] THEN MESON_TAC[]);;
