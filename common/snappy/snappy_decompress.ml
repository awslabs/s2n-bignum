(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas about the decoder model of snappy_format.ml that the proofs of the *)
(* machine code of the decompressor use (IncrementalCopy, MemCopy64,         *)
(* DecompressBranchless, DecompressAllTags): characterizations of            *)
(* snappy_copy by its bytes, which is how the code produces a copy; and one  *)
(* tag at position h of the input, by the bytes there                        *)
(* (SNAPPY_TAG_STEP_{LITERAL,COPY1,COPY2}_AT), as the fast path decodes it.   *)
(* ========================================================================= *)

needs "common/snappy/snappy_format.ml";;

(* A copy only looks at the last off bytes of the output.                    *)

let SNAPPY_COPY_APPEND = prove
 (`!off n (a:byte list) w.
        off <= LENGTH w
        ==> snappy_copy off n (APPEND a w) = APPEND a (snappy_copy off n w)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[snappy_copy] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `EL (LENGTH(APPEND (a:byte list) w) - off) (APPEND a w) =
    EL (LENGTH w - off) w`
  SUBST1_TAC THENL
   [REWRITE_TAC[LENGTH_APPEND; EL_APPEND] THEN
    COND_CASES_TAC THENL
     [ASM_ARITH_TAC; AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[LENGTH_APPEND] THEN ASM_ARITH_TAC);;

(* A list is the copy if it extends the output and each new byte is the one  *)
(* off positions before it (as a byte-by-byte copy makes it).                *)

let SNAPPY_COPY_UNIQUE = prove
 (`!off n (out:byte list) l.
        1 <= off /\ off <= LENGTH out /\ LENGTH l = LENGTH out + n /\
        (!i. i < LENGTH out ==> EL i l = EL i out) /\
        (!i. LENGTH out <= i /\ i < LENGTH out + n
             ==> EL i l = EL (i - off) l)
        ==> l = snappy_copy off n out`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[LIST_EQ; LENGTH_SNAPPY_COPY] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `i:num` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `i < LENGTH(out:byte list)` THENL
   [ASM_SIMP_TAC[EL_SNAPPY_COPY_PREFIX]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_SNAPPY_COPY o rand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) && is_imp(snd(dest_forall(concl th))) &&
       is_conj(lhand(snd(dest_forall(concl th))))
    then MP_TAC(SPEC `i:num` th) else NO_TAC) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN ASM_ARITH_TAC);;

(* A list is the copy if it extends the output and the new byte at t is the *)
(* byte at t MOD off of the last off bytes (as a repeated pattern makes it). *)

let SNAPPY_COPY_PERIODIC_UNIQUE = prove
 (`!off n (out:byte list) l.
        1 <= off /\ off <= LENGTH out /\ LENGTH l = LENGTH out + n /\
        (!i. i < LENGTH out ==> EL i l = EL i out) /\
        (!t. t < n ==> EL (LENGTH out + t) l =
                       EL (LENGTH out - off + t MOD off) out)
        ==> l = snappy_copy off n out`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[LIST_EQ; LENGTH_SNAPPY_COPY] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i < LENGTH(out:byte list)` THENL
   [ASM_SIMP_TAC[EL_SNAPPY_COPY_PREFIX]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) EL_SNAPPY_COPY_PERIODIC o rand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i - LENGTH(out:byte list)`) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(i < l) ==> l + (i - l) = i`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The tags of the fast path at position h of the input: the stream from h   *)
(* is SUB_LIST(h,LENGTH inp - h) inp, and the code reads the tag and the     *)
(* bytes after it by index.                                                  *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_SUFFIX_CONS = prove
 (`!(l:A list) h.
        h < LENGTH l
        ==> SUB_LIST(h,LENGTH l - h) l =
            CONS (EL h l) (SUB_LIST(h + 1,LENGTH l - (h + 1)) l)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LIST_EQ; LENGTH_SUB_LIST; LENGTH; ARITH_RULE `MIN a a = a`] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SNAPPY_EL_SUB_LIST o lhand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `j:num` SUBST_ALL_TAC)
   (SPEC `i:num` num_CASES) THEN
  GEN_REWRITE_TAC RAND_CONV [EL] THEN REWRITE_TAC[HD; TL; ADD_CLAUSES] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SNAPPY_EL_SUB_LIST o rand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let SNAPPY_SUFFIX_SUFFIX = prove
 (`!(l:A list) c a.
        c + a <= LENGTH l
        ==> SUB_LIST(a,(LENGTH l - c) - a) (SUB_LIST(c,LENGTH l - c) l) =
            SUB_LIST(c + a,LENGTH l - (c + a)) l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_SUB_LIST] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SNAPPY_EL_SUB_LIST o lhand o snd) THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SNAPPY_EL_SUB_LIST o lhand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SNAPPY_EL_SUB_LIST o rand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let SNAPPY_SUB_LIST_2 = prove
 (`!(l:A list) c. c + 2 <= LENGTH l
                  ==> SUB_LIST(c,2) l = [EL c l; EL (c + 1) l]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_SUB_LIST; LENGTH] THEN
  TRY(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SNAPPY_EL_SUB_LIST o lhand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `i = 0 \/ i = 1` MP_TAC THENL
   [ASM_ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; EL; HD; TL; ONE]]);;

let SNAPPY_SUFFIX_PREFIX = prove
 (`!(l:A list) c k.
        c + k <= LENGTH l
        ==> SUB_LIST(0,k) (SUB_LIST(c,LENGTH l - c) l) = SUB_LIST(c,k) l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_SUB_LIST] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SNAPPY_EL_SUB_LIST o lhand o snd) THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SNAPPY_EL_SUB_LIST o lhand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SNAPPY_EL_SUB_LIST o rand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES]);;

(* One tag of the fast path, at position h of the input, as the code       *)
(* decodes it.                                                               *)

let SNAPPY_TAG_STEP_LITERAL_AT = prove
 (`!m (inp:byte list) out h.
        val(EL h inp) MOD 4 = 0 /\ val(EL h inp) DIV 4 < 60 /\
        h + val(EL h inp) DIV 4 + 2 <= LENGTH inp /\
        LENGTH out + val(EL h inp) DIV 4 + 1 <= m
        ==> snappy_tag_step m (SUB_LIST(h,LENGTH inp - h) inp) out =
            SOME(SUB_LIST(h + val(EL h inp) DIV 4 + 2,
                          LENGTH inp - (h + val(EL h inp) DIV 4 + 2)) inp,
                 APPEND out (SUB_LIST(h + 1,val(EL h inp) DIV 4 + 1) inp))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SNAPPY_SUFFIX_CONS; ARITH_RULE `h + x + 2 <= l ==> h < l`] THEN
  REWRITE_TAC[snappy_tag_step] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[snappy_literal; SNAPPY_LENGTH_SUB_LIST_SUFFIX] THEN
  COND_CASES_TAC THENL [ALL_TAC; POP_ASSUM MP_TAC THEN ASM_ARITH_TAC] THEN
  REWRITE_TAC[option_INJ; PAIR_EQ] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `h + x + 2 = (h + 1) + (x + 1)`] THEN
    MATCH_MP_TAC SNAPPY_SUFFIX_SUFFIX THEN ASM_ARITH_TAC;
    AP_TERM_TAC THEN MATCH_MP_TAC SNAPPY_SUFFIX_PREFIX THEN ASM_ARITH_TAC]);;

let SNAPPY_TAG_STEP_COPY1_AT = prove
 (`!m (inp:byte list) out h.
        val(EL h inp) MOD 4 = 1 /\ h + 2 <= LENGTH inp
        ==> snappy_tag_step m (SUB_LIST(h,LENGTH inp - h) inp) out =
            snappy_copy_tag m (256 * (val(EL h inp) DIV 4 DIV 8) +
                               val(EL (h + 1) inp))
                            (val(EL h inp) DIV 4 MOD 8 + 4)
                            (SUB_LIST(h + 2,LENGTH inp - (h + 2)) inp) out`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SNAPPY_SUFFIX_CONS; ARITH_RULE `h + 2 <= l ==> h < l`;
               ARITH_RULE `h + 2 <= l ==> h + 1 < l`] THEN
  REWRITE_TAC[snappy_tag_step] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[ARITH_EQ; SNAPPY_LENGTH_SUB_LIST_SUFFIX; LENGTH; HD; TL] THEN
  COND_CASES_TAC THENL [POP_ASSUM MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(h + 1) + 1 = h + 2`]);;

let SNAPPY_TAG_STEP_COPY2_AT = prove
 (`!m (inp:byte list) out h.
        val(EL h inp) MOD 4 = 2 /\ h + 3 <= LENGTH inp
        ==> snappy_tag_step m (SUB_LIST(h,LENGTH inp - h) inp) out =
            snappy_copy_tag m (val(EL (h + 1) inp) + 256 * val(EL (h + 2) inp))
                            (val(EL h inp) DIV 4 + 1)
                            (SUB_LIST(h + 3,LENGTH inp - (h + 3)) inp) out`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SNAPPY_SUFFIX_CONS; ARITH_RULE `h + 3 <= l ==> h < l`] THEN
  REWRITE_TAC[snappy_tag_step] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_REWRITE_TAC[ARITH_EQ; SNAPPY_LENGTH_SUB_LIST_SUFFIX] THEN
  COND_CASES_TAC THENL [POP_ASSUM MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `a = a' /\ (t:byte list) = t'
    ==> snappy_copy_tag m a l t out = snappy_copy_tag m a' l t' out`) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[SNAPPY_SUFFIX_PREFIX; ARITH_RULE `h + 3 <= l ==> (h + 1) + 2 <= l`] THEN
    ASM_SIMP_TAC[SNAPPY_SUB_LIST_2; ARITH_RULE `h + 3 <= l ==> (h + 1) + 2 <= l`] THEN
    REWRITE_TAC[num_of_bytelist; ARITH_RULE `(h + 1) + 1 = h + 2`] THEN ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `h + 3 = (h + 1) + 2`] THEN
    MATCH_MP_TAC SNAPPY_SUFFIX_SUFFIX THEN ASM_ARITH_TAC]);;
