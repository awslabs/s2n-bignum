(*
 * Copyright (c) The mldsa-native project authors
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* ML-DSA Rejection uniform sampling for eta=4 (x86_64 AVX2).                *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;

(* Make silent type-variable invention an error (avoids nondeterministic     *)
(* "seqapply: Length mismatch" failures from fresh tyvars across subgoals).  *)
type_invention_error := true;;


(* ========================================================================= *)
(* Lookup table used by rejection sampling in the x86_64 AVX2 impl.          *)
(* INLINED from mldsa-native's mldsa_rej_uniform_table.ml (the 2048-byte     *)
(* x86 table). Inlined here (rather than needs-ing the mldsa-native path)    *)
(* to match how x86/proofs/mlkem_rej_uniform_VARIABLE_TIME.ml inlines its    *)
(* own table.                                                                *)
(* ========================================================================= *)

let mldsa_rej_uniform_table = (REWRITE_RULE[MAP] o define)
  `mldsa_rej_uniform_table:byte list = MAP word [
    0;   0;   0;   0;   0;   0;   0;   0;
    0;   0;   0;   0;   0;   0;   0;   0;
    1;   0;   0;   0;   0;   0;   0;   0;
    0;   1;   0;   0;   0;   0;   0;   0;
    2;   0;   0;   0;   0;   0;   0;   0;
    0;   2;   0;   0;   0;   0;   0;   0;
    1;   2;   0;   0;   0;   0;   0;   0;
    0;   1;   2;   0;   0;   0;   0;   0;
    3;   0;   0;   0;   0;   0;   0;   0;
    0;   3;   0;   0;   0;   0;   0;   0;
    1;   3;   0;   0;   0;   0;   0;   0;
    0;   1;   3;   0;   0;   0;   0;   0;
    2;   3;   0;   0;   0;   0;   0;   0;
    0;   2;   3;   0;   0;   0;   0;   0;
    1;   2;   3;   0;   0;   0;   0;   0;
    0;   1;   2;   3;   0;   0;   0;   0;
    4;   0;   0;   0;   0;   0;   0;   0;
    0;   4;   0;   0;   0;   0;   0;   0;
    1;   4;   0;   0;   0;   0;   0;   0;
    0;   1;   4;   0;   0;   0;   0;   0;
    2;   4;   0;   0;   0;   0;   0;   0;
    0;   2;   4;   0;   0;   0;   0;   0;
    1;   2;   4;   0;   0;   0;   0;   0;
    0;   1;   2;   4;   0;   0;   0;   0;
    3;   4;   0;   0;   0;   0;   0;   0;
    0;   3;   4;   0;   0;   0;   0;   0;
    1;   3;   4;   0;   0;   0;   0;   0;
    0;   1;   3;   4;   0;   0;   0;   0;
    2;   3;   4;   0;   0;   0;   0;   0;
    0;   2;   3;   4;   0;   0;   0;   0;
    1;   2;   3;   4;   0;   0;   0;   0;
    0;   1;   2;   3;   4;   0;   0;   0;
    5;   0;   0;   0;   0;   0;   0;   0;
    0;   5;   0;   0;   0;   0;   0;   0;
    1;   5;   0;   0;   0;   0;   0;   0;
    0;   1;   5;   0;   0;   0;   0;   0;
    2;   5;   0;   0;   0;   0;   0;   0;
    0;   2;   5;   0;   0;   0;   0;   0;
    1;   2;   5;   0;   0;   0;   0;   0;
    0;   1;   2;   5;   0;   0;   0;   0;
    3;   5;   0;   0;   0;   0;   0;   0;
    0;   3;   5;   0;   0;   0;   0;   0;
    1;   3;   5;   0;   0;   0;   0;   0;
    0;   1;   3;   5;   0;   0;   0;   0;
    2;   3;   5;   0;   0;   0;   0;   0;
    0;   2;   3;   5;   0;   0;   0;   0;
    1;   2;   3;   5;   0;   0;   0;   0;
    0;   1;   2;   3;   5;   0;   0;   0;
    4;   5;   0;   0;   0;   0;   0;   0;
    0;   4;   5;   0;   0;   0;   0;   0;
    1;   4;   5;   0;   0;   0;   0;   0;
    0;   1;   4;   5;   0;   0;   0;   0;
    2;   4;   5;   0;   0;   0;   0;   0;
    0;   2;   4;   5;   0;   0;   0;   0;
    1;   2;   4;   5;   0;   0;   0;   0;
    0;   1;   2;   4;   5;   0;   0;   0;
    3;   4;   5;   0;   0;   0;   0;   0;
    0;   3;   4;   5;   0;   0;   0;   0;
    1;   3;   4;   5;   0;   0;   0;   0;
    0;   1;   3;   4;   5;   0;   0;   0;
    2;   3;   4;   5;   0;   0;   0;   0;
    0;   2;   3;   4;   5;   0;   0;   0;
    1;   2;   3;   4;   5;   0;   0;   0;
    0;   1;   2;   3;   4;   5;   0;   0;
    6;   0;   0;   0;   0;   0;   0;   0;
    0;   6;   0;   0;   0;   0;   0;   0;
    1;   6;   0;   0;   0;   0;   0;   0;
    0;   1;   6;   0;   0;   0;   0;   0;
    2;   6;   0;   0;   0;   0;   0;   0;
    0;   2;   6;   0;   0;   0;   0;   0;
    1;   2;   6;   0;   0;   0;   0;   0;
    0;   1;   2;   6;   0;   0;   0;   0;
    3;   6;   0;   0;   0;   0;   0;   0;
    0;   3;   6;   0;   0;   0;   0;   0;
    1;   3;   6;   0;   0;   0;   0;   0;
    0;   1;   3;   6;   0;   0;   0;   0;
    2;   3;   6;   0;   0;   0;   0;   0;
    0;   2;   3;   6;   0;   0;   0;   0;
    1;   2;   3;   6;   0;   0;   0;   0;
    0;   1;   2;   3;   6;   0;   0;   0;
    4;   6;   0;   0;   0;   0;   0;   0;
    0;   4;   6;   0;   0;   0;   0;   0;
    1;   4;   6;   0;   0;   0;   0;   0;
    0;   1;   4;   6;   0;   0;   0;   0;
    2;   4;   6;   0;   0;   0;   0;   0;
    0;   2;   4;   6;   0;   0;   0;   0;
    1;   2;   4;   6;   0;   0;   0;   0;
    0;   1;   2;   4;   6;   0;   0;   0;
    3;   4;   6;   0;   0;   0;   0;   0;
    0;   3;   4;   6;   0;   0;   0;   0;
    1;   3;   4;   6;   0;   0;   0;   0;
    0;   1;   3;   4;   6;   0;   0;   0;
    2;   3;   4;   6;   0;   0;   0;   0;
    0;   2;   3;   4;   6;   0;   0;   0;
    1;   2;   3;   4;   6;   0;   0;   0;
    0;   1;   2;   3;   4;   6;   0;   0;
    5;   6;   0;   0;   0;   0;   0;   0;
    0;   5;   6;   0;   0;   0;   0;   0;
    1;   5;   6;   0;   0;   0;   0;   0;
    0;   1;   5;   6;   0;   0;   0;   0;
    2;   5;   6;   0;   0;   0;   0;   0;
    0;   2;   5;   6;   0;   0;   0;   0;
    1;   2;   5;   6;   0;   0;   0;   0;
    0;   1;   2;   5;   6;   0;   0;   0;
    3;   5;   6;   0;   0;   0;   0;   0;
    0;   3;   5;   6;   0;   0;   0;   0;
    1;   3;   5;   6;   0;   0;   0;   0;
    0;   1;   3;   5;   6;   0;   0;   0;
    2;   3;   5;   6;   0;   0;   0;   0;
    0;   2;   3;   5;   6;   0;   0;   0;
    1;   2;   3;   5;   6;   0;   0;   0;
    0;   1;   2;   3;   5;   6;   0;   0;
    4;   5;   6;   0;   0;   0;   0;   0;
    0;   4;   5;   6;   0;   0;   0;   0;
    1;   4;   5;   6;   0;   0;   0;   0;
    0;   1;   4;   5;   6;   0;   0;   0;
    2;   4;   5;   6;   0;   0;   0;   0;
    0;   2;   4;   5;   6;   0;   0;   0;
    1;   2;   4;   5;   6;   0;   0;   0;
    0;   1;   2;   4;   5;   6;   0;   0;
    3;   4;   5;   6;   0;   0;   0;   0;
    0;   3;   4;   5;   6;   0;   0;   0;
    1;   3;   4;   5;   6;   0;   0;   0;
    0;   1;   3;   4;   5;   6;   0;   0;
    2;   3;   4;   5;   6;   0;   0;   0;
    0;   2;   3;   4;   5;   6;   0;   0;
    1;   2;   3;   4;   5;   6;   0;   0;
    0;   1;   2;   3;   4;   5;   6;   0;
    7;   0;   0;   0;   0;   0;   0;   0;
    0;   7;   0;   0;   0;   0;   0;   0;
    1;   7;   0;   0;   0;   0;   0;   0;
    0;   1;   7;   0;   0;   0;   0;   0;
    2;   7;   0;   0;   0;   0;   0;   0;
    0;   2;   7;   0;   0;   0;   0;   0;
    1;   2;   7;   0;   0;   0;   0;   0;
    0;   1;   2;   7;   0;   0;   0;   0;
    3;   7;   0;   0;   0;   0;   0;   0;
    0;   3;   7;   0;   0;   0;   0;   0;
    1;   3;   7;   0;   0;   0;   0;   0;
    0;   1;   3;   7;   0;   0;   0;   0;
    2;   3;   7;   0;   0;   0;   0;   0;
    0;   2;   3;   7;   0;   0;   0;   0;
    1;   2;   3;   7;   0;   0;   0;   0;
    0;   1;   2;   3;   7;   0;   0;   0;
    4;   7;   0;   0;   0;   0;   0;   0;
    0;   4;   7;   0;   0;   0;   0;   0;
    1;   4;   7;   0;   0;   0;   0;   0;
    0;   1;   4;   7;   0;   0;   0;   0;
    2;   4;   7;   0;   0;   0;   0;   0;
    0;   2;   4;   7;   0;   0;   0;   0;
    1;   2;   4;   7;   0;   0;   0;   0;
    0;   1;   2;   4;   7;   0;   0;   0;
    3;   4;   7;   0;   0;   0;   0;   0;
    0;   3;   4;   7;   0;   0;   0;   0;
    1;   3;   4;   7;   0;   0;   0;   0;
    0;   1;   3;   4;   7;   0;   0;   0;
    2;   3;   4;   7;   0;   0;   0;   0;
    0;   2;   3;   4;   7;   0;   0;   0;
    1;   2;   3;   4;   7;   0;   0;   0;
    0;   1;   2;   3;   4;   7;   0;   0;
    5;   7;   0;   0;   0;   0;   0;   0;
    0;   5;   7;   0;   0;   0;   0;   0;
    1;   5;   7;   0;   0;   0;   0;   0;
    0;   1;   5;   7;   0;   0;   0;   0;
    2;   5;   7;   0;   0;   0;   0;   0;
    0;   2;   5;   7;   0;   0;   0;   0;
    1;   2;   5;   7;   0;   0;   0;   0;
    0;   1;   2;   5;   7;   0;   0;   0;
    3;   5;   7;   0;   0;   0;   0;   0;
    0;   3;   5;   7;   0;   0;   0;   0;
    1;   3;   5;   7;   0;   0;   0;   0;
    0;   1;   3;   5;   7;   0;   0;   0;
    2;   3;   5;   7;   0;   0;   0;   0;
    0;   2;   3;   5;   7;   0;   0;   0;
    1;   2;   3;   5;   7;   0;   0;   0;
    0;   1;   2;   3;   5;   7;   0;   0;
    4;   5;   7;   0;   0;   0;   0;   0;
    0;   4;   5;   7;   0;   0;   0;   0;
    1;   4;   5;   7;   0;   0;   0;   0;
    0;   1;   4;   5;   7;   0;   0;   0;
    2;   4;   5;   7;   0;   0;   0;   0;
    0;   2;   4;   5;   7;   0;   0;   0;
    1;   2;   4;   5;   7;   0;   0;   0;
    0;   1;   2;   4;   5;   7;   0;   0;
    3;   4;   5;   7;   0;   0;   0;   0;
    0;   3;   4;   5;   7;   0;   0;   0;
    1;   3;   4;   5;   7;   0;   0;   0;
    0;   1;   3;   4;   5;   7;   0;   0;
    2;   3;   4;   5;   7;   0;   0;   0;
    0;   2;   3;   4;   5;   7;   0;   0;
    1;   2;   3;   4;   5;   7;   0;   0;
    0;   1;   2;   3;   4;   5;   7;   0;
    6;   7;   0;   0;   0;   0;   0;   0;
    0;   6;   7;   0;   0;   0;   0;   0;
    1;   6;   7;   0;   0;   0;   0;   0;
    0;   1;   6;   7;   0;   0;   0;   0;
    2;   6;   7;   0;   0;   0;   0;   0;
    0;   2;   6;   7;   0;   0;   0;   0;
    1;   2;   6;   7;   0;   0;   0;   0;
    0;   1;   2;   6;   7;   0;   0;   0;
    3;   6;   7;   0;   0;   0;   0;   0;
    0;   3;   6;   7;   0;   0;   0;   0;
    1;   3;   6;   7;   0;   0;   0;   0;
    0;   1;   3;   6;   7;   0;   0;   0;
    2;   3;   6;   7;   0;   0;   0;   0;
    0;   2;   3;   6;   7;   0;   0;   0;
    1;   2;   3;   6;   7;   0;   0;   0;
    0;   1;   2;   3;   6;   7;   0;   0;
    4;   6;   7;   0;   0;   0;   0;   0;
    0;   4;   6;   7;   0;   0;   0;   0;
    1;   4;   6;   7;   0;   0;   0;   0;
    0;   1;   4;   6;   7;   0;   0;   0;
    2;   4;   6;   7;   0;   0;   0;   0;
    0;   2;   4;   6;   7;   0;   0;   0;
    1;   2;   4;   6;   7;   0;   0;   0;
    0;   1;   2;   4;   6;   7;   0;   0;
    3;   4;   6;   7;   0;   0;   0;   0;
    0;   3;   4;   6;   7;   0;   0;   0;
    1;   3;   4;   6;   7;   0;   0;   0;
    0;   1;   3;   4;   6;   7;   0;   0;
    2;   3;   4;   6;   7;   0;   0;   0;
    0;   2;   3;   4;   6;   7;   0;   0;
    1;   2;   3;   4;   6;   7;   0;   0;
    0;   1;   2;   3;   4;   6;   7;   0;
    5;   6;   7;   0;   0;   0;   0;   0;
    0;   5;   6;   7;   0;   0;   0;   0;
    1;   5;   6;   7;   0;   0;   0;   0;
    0;   1;   5;   6;   7;   0;   0;   0;
    2;   5;   6;   7;   0;   0;   0;   0;
    0;   2;   5;   6;   7;   0;   0;   0;
    1;   2;   5;   6;   7;   0;   0;   0;
    0;   1;   2;   5;   6;   7;   0;   0;
    3;   5;   6;   7;   0;   0;   0;   0;
    0;   3;   5;   6;   7;   0;   0;   0;
    1;   3;   5;   6;   7;   0;   0;   0;
    0;   1;   3;   5;   6;   7;   0;   0;
    2;   3;   5;   6;   7;   0;   0;   0;
    0;   2;   3;   5;   6;   7;   0;   0;
    1;   2;   3;   5;   6;   7;   0;   0;
    0;   1;   2;   3;   5;   6;   7;   0;
    4;   5;   6;   7;   0;   0;   0;   0;
    0;   4;   5;   6;   7;   0;   0;   0;
    1;   4;   5;   6;   7;   0;   0;   0;
    0;   1;   4;   5;   6;   7;   0;   0;
    2;   4;   5;   6;   7;   0;   0;   0;
    0;   2;   4;   5;   6;   7;   0;   0;
    1;   2;   4;   5;   6;   7;   0;   0;
    0;   1;   2;   4;   5;   6;   7;   0;
    3;   4;   5;   6;   7;   0;   0;   0;
    0;   3;   4;   5;   6;   7;   0;   0;
    1;   3;   4;   5;   6;   7;   0;   0;
    0;   1;   3;   4;   5;   6;   7;   0;
    2;   3;   4;   5;   6;   7;   0;   0;
    0;   2;   3;   4;   5;   6;   7;   0;
    1;   2;   3;   4;   5;   6;   7;   0;
    0;   1;   2;   3;   4;   5;   6;   7
]`;;

(* ------------------------------------------------------------------------- *)
(* Helper definitions/lemmas inlined from mldsa-native's                     *)
(* common/mldsa_specs.ml and x86_64/proofs/mldsa_utils.ml.                   *)
(* Inlined (not added to common/mlkem_mldsa.ml) because that file is SHARED  *)
(* with the AArch64 build; several of these are typed over x86state.         *)
(* ------------------------------------------------------------------------- *)

(* [from mldsa-native mldsa_specs.ml] *)
let EL_SUB_LIST = prove(
 `!l:'a list. !i k n. i < n /\ k + n <= LENGTH l
   ==> EL i (SUB_LIST (k, n) l) = EL (k + i) l`,
  LIST_INDUCT_TAC THENL [
    REWRITE_TAC[LENGTH; LE; ADD_EQ_0] THEN ARITH_TAC;
    REWRITE_TAC[LENGTH] THEN REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC (SPEC `k:num` num_CASES) THEN
    STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THEN
    REWRITE_TAC[LT; SUB_LIST_CLAUSES; ADD_CLAUSES] THENL [
      STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN
      REWRITE_TAC[EL; HD; TL; ADD_CLAUSES] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [`n:num`; `0`; `n':num`]) THEN
      REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[EL; TL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [`i:num`; `n':num`; `SUC n''`]) THEN
      ASM_REWRITE_TAC[LT_SUC] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

(* [from mldsa-native mldsa_specs.ml] *)
let LENGTH_SUB_LIST_0 = prove
 (`!n (l:'a list). n <= LENGTH l ==> LENGTH (SUB_LIST (0, n) l) = n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LENGTH_SUB_LIST; SUB_0] THEN ASM_ARITH_TAC);;

(* [from mldsa-native mldsa_specs.ml] *)
let WORD_SUBWORD_NUM_OF_WORDLIST = prove
 (`!(ls:(L word)list) k.
    dimindex(:KL) = dimindex(:L) * LENGTH ls /\
    k < LENGTH ls
    ==> word_subword (word (num_of_wordlist ls) : KL word) (dimindex(:L)*k, dimindex(:L)) : L word = EL k ls`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD] THEN
  REWRITE_TAC[ARITH_RULE `MIN n n = n`] THEN
  SUBGOAL_THEN `val (word (num_of_wordlist (ls:(L word)list)) : KL word) = num_of_wordlist ls` SUBST1_TAC THENL
  [W(MP_TAC o PART_MATCH (lhand o rand) VAL_WORD_EQ o lhand o snd) THEN
   ANTS_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP (dimindex(:L) * LENGTH (ls:(L word)list))` THEN
    REWRITE_TAC[NUM_OF_WORDLIST_BOUND; LE_EXP; LE_REFL] THEN ASM_ARITH_TAC;
    SIMP_TAC[]];
   MP_TAC(ISPECL [`ls:(L word)list`; `k:num`] NUM_OF_WORDLIST_EL) THEN
   ASM_REWRITE_TAC[]]);;

(* [from mldsa-native mldsa_specs.ml] *)
let REJ_SAMPLE = define
 `REJ_SAMPLE l = FILTER (\x:int32. val x < 8380417)
    (MAP (\x:24 word. word(val x MOD 2 EXP 23):int32) l)`;;

(* [from mldsa-native mldsa_specs.ml] *)
let REJ_SAMPLE_ETA4 = define
  `REJ_SAMPLE_ETA4 (l:(4 word) list) =
   MAP (\x:4 word. word_sx (word_sub (word 4:4 word) x):int32)
       (FILTER (\x:4 word. val x < 9) l)`;;

(* [from mldsa-native mldsa_utils.ml] *)
let NIBBLE_PAIR = define
  `NIBBLE_PAIR (b:byte) =
   [word(val b MOD 16):int16; word(val b DIV 16):int16]`;;

(* [from mldsa-native mldsa_utils.ml] *)
let NIBBLES_OF_BYTES = define
  `NIBBLES_OF_BYTES [] = ([]:(int16)list) /\
   NIBBLES_OF_BYTES (CONS (b:byte) t) =
   APPEND (NIBBLE_PAIR b) (NIBBLES_OF_BYTES t)`;;

(* [from mldsa-native mldsa_utils.ml] *)
let NIBBLES_OF_BYTES_APPEND = prove
 (`!l1 l2. NIBBLES_OF_BYTES(APPEND l1 l2) =
           APPEND (NIBBLES_OF_BYTES l1) (NIBBLES_OF_BYTES l2)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[NIBBLES_OF_BYTES; APPEND; APPEND_ASSOC]);;

(* Splits each input byte into its low and high 4-bit nibbles at the natural *)
(* 4-bit width consumed by the REJ_SAMPLE_ETA{2,4} spec. The output is twice *)
(* the length of the input.                                                  *)

(* [from mldsa-native mldsa_utils.ml] *)
let BYTES_TO_NIBBLES = define
  `BYTES_TO_NIBBLES [] = ([]:(4 word) list) /\
   BYTES_TO_NIBBLES (CONS (b:byte) t) =
   APPEND [word(val b MOD 16):4 word; word(val b DIV 16):4 word]
          (BYTES_TO_NIBBLES t)`;;

(* Bridge lemmas relating the byte-list and nibble-list views, used at the    *)
(* subroutine-spec boundary to state the public spec over a (4 word) list.    *)

(* [from mldsa-native mldsa_utils.ml] *)
let LENGTH_BYTES_TO_NIBBLES = prove
 (`!l:byte list. LENGTH(BYTES_TO_NIBBLES l) = 2 * LENGTH l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[BYTES_TO_NIBBLES; LENGTH; LENGTH_APPEND] THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let NUM_OF_BYTES_TO_NIBBLES = prove
 (`!l:byte list. num_of_wordlist (BYTES_TO_NIBBLES l) = num_of_wordlist l`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[BYTES_TO_NIBBLES; num_of_wordlist; NUM_OF_WORDLIST_APPEND;
              LENGTH; DIMINDEX_4; DIMINDEX_8; VAL_WORD; MOD_MOD_REFL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `val(h:byte) DIV 16 MOD 16 = val h DIV 16` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(h:byte) MOD 16 MOD 16 = val h MOD 16` SUBST1_TAC THENL
   [REWRITE_TAC[MOD_MOD_REFL]; ALL_TAC] THEN
  MP_TAC(SPECL [`val(h:byte)`; `16`] DIVISION) THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let BYTES_TO_NIBBLES_SURJ = prove
 (`!l:(4 word) list. EVEN(LENGTH l)
                     ==> ?bs:byte list. BYTES_TO_NIBBLES bs = l /\
                                        LENGTH bs = LENGTH l DIV 2`,
  GEN_TAC THEN WF_INDUCT_TAC `LENGTH(l:(4 word) list)` THEN
  DISCH_TAC THEN ASM_CASES_TAC `l:(4 word) list = []` THENL
   [EXISTS_TAC `[]:byte list` THEN ASM_REWRITE_TAC[BYTES_TO_NIBBLES; LENGTH] THEN
    CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(ISPEC `l:(4 word) list` list_CASES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n0:4 word`
              (X_CHOOSE_THEN `t0:(4 word) list` SUBST_ALL_TAC)) THEN
  ASM_CASES_TAC `t0:(4 word) list = []` THENL
   [POP_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC `EVEN (LENGTH (CONS (n0:4 word) []))` THEN
    REWRITE_TAC[LENGTH; EVEN; ARITH_RULE `~(SUC 0 = 0)`]; ALL_TAC] THEN
  MP_TAC(ISPEC `t0:(4 word) list` list_CASES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:4 word`
              (X_CHOOSE_THEN `t:(4 word) list` SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:(4 word) list`) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `n < SUC(SUC n)`] THEN
  UNDISCH_TAC `EVEN (LENGTH (CONS (n0:4 word) (CONS n1 t)))` THEN
  REWRITE_TAC[LENGTH; EVEN] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `bs:byte list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `CONS (word(val(n0:4 word) + 16 * val(n1:4 word)):byte) bs` THEN
  ASM_REWRITE_TAC[BYTES_TO_NIBBLES; LENGTH; APPEND; CONS_11] THEN
  MP_TAC(ISPEC `n0:4 word` VAL_BOUND) THEN
  MP_TAC(ISPEC `n1:4 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_4] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT DISCH_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
    `(val(n0:4 word) + 16 * val(n1:4 word)) MOD 256 = val n0 + 16 * val n1`
    SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `val(n0:4 word) + 16 * val(n1:4 word) = val n1 * 16 + val n0` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ; MOD_LT; DIV_LT;
               ADD_CLAUSES] THEN
  REWRITE_TAC[WORD_VAL] THEN
  UNDISCH_TAC `EVEN (LENGTH (t:(4 word) list))` THEN
  REWRITE_TAC[EVEN_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
  REWRITE_TAC[ARITH_RULE `2 * m = m * 2`; DIV_MULT; ARITH_EQ] THEN ARITH_TAC);;

(* ========================================================================= *)
(* Lemmas shared by the AVX2 rejection-sampling proofs (rej_uniform_eta2 and  *)
(* rej_uniform_eta4): popcount / accepted-count bounds, byte/nibble value     *)
(* lemmas, word-slice and sub-list helpers, and modular-split arithmetic.     *)
(* ========================================================================= *)

(* [from mldsa-native mldsa_utils.ml] *)
let VAL_WORD_ZX_64_32 = prove
 (`!a. a < 2 EXP 32 ==> val(word_zx(word a:int64):int32) = a`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_32; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `a MOD 2 EXP 64 = a` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]);;

(* Loop-guard fall-through bridge: after `cmp $k, %e_x` with the 64-bit      *)
(* register holding `word a` (a <= k <= 2^32-1), the `ja` (jump-if-above,    *)
(* unsigned >) is NOT taken. The x86 model emits the taken-condition as      *)
(* `~(~EQ \/ ZF)` where EQ is the CF-via-int-equality and ZF the zero test;  *)
(* this lemma proves `~EQ \/ ZF` holds so the taken-condition is false and   *)
(* execution falls through. Stated with `word a:int64` (the register width)  *)
(* and `&`:int (int_of_num) to match the model's flag terms EXACTLY, so      *)
(* X86_STEPS_TAC resolves the conditional RIP automatically when this lemma  *)
(* (instantiated for the right a,k) is in the assumptions. Used at all five  *)
(* cmp/ja sites in the SIMD loop body (the two loop-head guards on ctr<=248  *)
(* and pos<=256, plus the three mid-iteration early-exit checks).            *)

(* [from mldsa-native mldsa_utils.ml] *)
let NIBBLES_OF_BYTES_EQ_BYTES_TO_NIBBLES = prove
 (`!l:byte list.
     NIBBLES_OF_BYTES l = MAP (\x:4 word. word_zx x:int16) (BYTES_TO_NIBBLES l)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[NIBBLES_OF_BYTES; BYTES_TO_NIBBLES; MAP]; ALL_TAC] THEN
  REWRITE_TAC[NIBBLES_OF_BYTES; BYTES_TO_NIBBLES; MAP; APPEND] THEN
  ASM_REWRITE_TAC[NIBBLE_PAIR; MAP; APPEND] THEN
  REPEAT(AP_THM_TAC ORELSE AP_TERM_TAC) THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_4; DIMINDEX_16; word_zx] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REPEAT AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(GSYM MOD_LT) THEN MP_TAC(ISPEC `h:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

(* Bridge: byte-shape composition equals the public nibble-list spec         *)
(* applied to BYTES_TO_NIBBLES. Used only at the subroutine-spec boundary.   *)

(* [from mldsa-native mldsa_utils.ml] *)
let RB64 = prove
 (`!(a:int64) (s:x86state). read(memory:>bytes64 a) s = word(read(memory:>bytes(a,8)) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bytes64; READ_COMPONENT_COMPOSE; asword; through; read]);;

(* Read an n-byte window at offset k of a byte region known to hold num_of_wordlist L:
   the window holds num_of_wordlist(SUB_LIST(k,n) L).  (NB: HOL parses `k + LENGTH L - k`
   as `k + (LENGTH L - k)` since `-` binds tighter than `+`; the SUB_ADD-style reductions
   here go through ASM_ARITH_TAC with the k+n<=LENGTH L hypothesis.) *)

(* [from mldsa-native mldsa_utils.ml] *)
let BYTES256_PREFIX_WORDLIST = prove
 (`!(A:int64) (V:int256) k (s:x86state).
      read(memory:>bytes256 A) s = V /\ k <= 8
      ==> read(memory:>bytes(A, 4*k)) s = num_of_wordlist(wordlist_of_num k (val V):int32 list)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NUM_OF_WORDLIST_OF_NUM; DIMINDEX_32; READ_COMPONENT_COMPOSE] THEN
  SUBGOAL_THEN `read (bytes(A,32)) (read memory (s:x86state)) = val(V:int256)` ASSUME_TAC THENL
   [UNDISCH_TAC `read(memory:>bytes256 A) s = V` THEN
    REWRITE_TAC[bytes256; READ_COMPONENT_COMPOSE; asword; through; read] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[VAL_WORD; DIMINDEX_256] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[GSYM DIMINDEX_256] THEN
    MP_TAC(ISPECL[`A:int64`;`32`;`read memory (s:x86state)`] READ_BYTES_BOUND) THEN
    REWRITE_TAC[DIMINDEX_256] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:int64`; `32`; `4*k`; `read memory (s:x86state)`] READ_BYTES_MOD) THEN
  ASM_REWRITE_TAC[ARITH_RULE `8 * 4 * k = 32 * k`] THEN
  SUBGOAL_THEN `MIN 32 (4*k) = 4*k` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

(* The j-th lane (j<k<=8) of wordlist_of_num k (val V) is word_subword V (32j,32). *)

(* [from mldsa-native mldsa_utils.ml] *)
let EL_WORDLIST_OF_NUM_VAL = prove
 (`!(V:int256) k j. j < k
     ==> EL j (wordlist_of_num k (val V):int32 list) = word_subword V (32*j,32)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`wordlist_of_num k (val(V:int256)):int32 list`; `j:num`] EL_NUM_OF_WORDLIST) THEN
  REWRITE_TAC[LENGTH_WORDLIST_OF_NUM; NUM_OF_WORDLIST_OF_NUM; DIMINDEX_32] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[word_subword; DIMINDEX_32; DIMINDEX_256] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC(MESON[] `(word x:int32) = word y ==> word x:int32 = word y`) THEN
  ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN REWRITE_TAC[DIMINDEX_32] THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`; MOD_MOD_REFL] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  SUBGOAL_THEN `MIN (32 * k) (32 * j + 32) = 32 * j + 32` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[]]);;

(* If V's first k lanes match L's elements (and LENGTH L = k <= 8), the low-k-lane digit
   list of V is exactly L. *)

(* [from mldsa-native mldsa_utils.ml] *)
let WORDLIST_OF_NUM_VAL_EQ = prove
 (`!(V:int256) (L:int32 list) k.
      LENGTH L = k /\ (!j. j < k ==> word_subword V (32*j,32) = EL j L)
      ==> wordlist_of_num k (val V) = L`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[LIST_EQ] THEN
  REWRITE_TAC[LENGTH_WORDLIST_OF_NUM] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[EL_WORDLIST_OF_NUM_VAL] THEN ASM_MESON_TAC[]);;

(* Full-width subword identity (used to close the per-lane vpmovsxbd extraction:
   word_subword (word_sx b:int32) (0,32) = word_sx b, with the word_sx(..) taken as W). *)

(* [from mldsa-native mldsa_utils.ml] *)
let SUB_LIST_0_MAP = prove
 (`!(f:A->B) n l. SUB_LIST(0,n) (MAP f l) = MAP f (SUB_LIST(0,n) l)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[SUB_LIST_CLAUSES; MAP] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[SUB_LIST_CLAUSES; MAP]);;

(* Nesting/composition of SUB_LIST: a window of width n starting at a, taken from
   a window of width m starting at b, equals the width-n window starting at b+a in
   the original list (provided the inner window covers it and lies inside the list).
   Used to slice the 4-byte sub-iter block SUB_LIST(16i,4) out of the 16-byte chunk
   SUB_LIST(16i,16) when threading per-block facts in the clean loop body. *)

(* [from mldsa-native mldsa_utils.ml] *)
let MAP_FILTER_WORD_NIB = prove
 (`!(f:int16->int32) P (L:num list).
     (!v. MEM v L ==> v < 16)
     ==> MAP f (FILTER P (MAP (word:num->int16) L)) =
         MAP (\v. f(word v)) (FILTER (\v. P(word v)) L)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; FILTER] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ASM_CASES_TAC `(P:int16->bool)(word h)` THEN
    ASM_REWRITE_TAC[MAP; th]));;

(* For a list of nibble values (< 16), the int16-word accept predicate         *)
(* val(word v) < 9 agrees with the numeric v < 9, so the two FILTERs coincide. *)

(* [from mldsa-native mldsa_utils.ml] *)
let WZZ_LOW = prove
 (`!(p:int256) j. j < 8
    ==> word_subword (word_zx (word_zx p:int128):int64) (8*j,8):byte = word_subword p (8*j,8)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word_zx (p:int256):int128`;`8*j`;`8`]
    (INST_TYPE[`:64`,`:N`;`:128`,`:M`;`:8`,`:P`] WORD_SUBWORD_ZX)) THEN
  MP_TAC(ISPECL [`p:int256`;`8*j`;`8`]
    (INST_TYPE[`:128`,`:N`;`:256`,`:M`;`:8`,`:P`] WORD_SUBWORD_ZX)) THEN
  REWRITE_TAC[DIMINDEX_8;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
  SUBGOAL_THEN `MIN (8*j+8) 128 <= 256 /\ MIN (8*j+8) 256 <= 128 /\ MIN(8*j+8) 128 <= 64` MP_TAC THENL
   [POP_ASSUM MP_TAC THEN ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 -> REWRITE_TAC[th2;th1]))]);;

(* ZZCOLLAPSE: strip word_zx 128<-256<-128 on a low-lane byte subword (j<8); used in    *)
(* the sub-iter store gather subgoal (the vpmovsxbd source g = word_zx(word_zx(...))).  *)

(* [from mldsa-native mldsa_utils.ml] *)
let WORD_BYTE_MOD = prove
 (`!n. word(n MOD 256):byte = word n`,
  GEN_TAC THEN SUBGOAL_THEN `256 = 2 EXP dimindex(:8)` SUBST1_TAC THENL
   [REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV; REWRITE_TAC[WORD_MOD_SIZE]]);;

(* [from mldsa-native mldsa_utils.ml] *)
let WORD_ADD_256_BYTE = prove
 (`!a x. word(a + 256 * x):byte = word a`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM WORD_BYTE_MOD] THEN
  AP_TERM_TAC THEN REWRITE_TAC[MOD_MULT_ADD; ARITH_RULE `256 * x = x * 256`] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

(* [from mldsa-native mldsa_utils.ml] *)
let WORD_ZX_BYTE_TO_INT16 = prove
 (`!n. n < 256 ==> word_zx (word n:byte):int16 = word n`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD;
              DIMINDEX_8; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `n < 256 ==> n < 65536`]);;

(* LENGTH FILTER (val<9) commutes with MAP word_zx (byte->int16).            *)

(* [from mldsa-native mldsa_utils.ml] *)
let ENSURES_STRENGTHEN_POST_X86 = prove
 (`!P (Q:x86state->bool) Q' R.
     ensures x86 P Q' R /\ (!s. Q' s ==> Q s) ==> ensures x86 P Q R`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[ensures] THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `s0:x86state` THEN MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MP_TAC(BETA_RULE(ISPECL [`x86`;
    `\s':x86state. (Q':x86state->bool) s' /\
                   (R:x86state->x86state->bool) (s0:x86state) s'`;
    `\s':x86state. (Q:x86state->bool) s' /\
                   (R:x86state->x86state->bool) (s0:x86state) s'`]
    EVENTUALLY_MONO)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; MESON_TAC[]]);;

(* SUB_LIST length cap: outlist length <= 256, used for SUBROUTINE_CORRECT   *)
(* `outlen <= 256` postcondition.                                            *)

(* [from mldsa-native mldsa_utils.ml] *)
let ADD256_MOD = prove
 (`!a b. a < 256 ==> (a + 256 * b) MOD 256 = a`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT]);;

(* [from mldsa-native mldsa_utils.ml] *)
let LOW8_LT = prove
 (`!p:num->bool. bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) < 256`,
  GEN_TAC THEN
  MAP_EVERY (fun k -> MP_TAC(ISPEC (mk_comb(`p:num->bool`,mk_small_numeral k)) BITVAL_BOUND))
    [0;1;2;3;4;5;6;7] THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let MOD_RED = prove
 (`!p:num->bool.
    (bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
     65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
     1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
     16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
     268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) MOD 256 =
    bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
    16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `(bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
     65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
     1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
     16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
     268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) =
    (bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7)) +
    256 * (bitval(p 8) + 2*bitval(p 9) + 4*bitval(p 10) + 8*bitval(p 11) +
     16*bitval(p 12) + 32*bitval(p 13) + 64*bitval(p 14) + 128*bitval(p 15) +
     256*bitval(p 16) + 512*bitval(p 17) + 1024*bitval(p 18) + 2048*bitval(p 19) +
     4096*bitval(p 20) + 8192*bitval(p 21) + 16384*bitval(p 22) + 32768*bitval(p 23) +
     65536*bitval(p 24) + 131072*bitval(p 25) + 262144*bitval(p 26) + 524288*bitval(p 27) +
     1048576*bitval(p 28) + 2097152*bitval(p 29) + 4194304*bitval(p 30) + 8388608*bitval(p 31))`
   SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC ADD256_MOD THEN REWRITE_TAC[LOW8_LT]);;

(* [from mldsa-native mldsa_utils.ml] *)
let RAX_NEST_REDUCE = prove
 (`!a b. a + b < 2 EXP 32
     ==> word_zx (word_add (word_zx (word a:int64):int32)
                           (word_zx (word_zx (word b:int32):int64):int32):int32):int64 =
         word(a + b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a < 2 EXP 32 /\ b < 2 EXP 32 /\ a + b < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `x < 2 EXP 32 ==> x < 2 EXP 64`] THEN
  ASM_SIMP_TAC[MOD_LT]);;

(* [from mldsa-native mldsa_utils.ml] *)
let JA_NOT_TAKEN_LE = prove
 (`!a k:num. a <= k /\ k < 2 EXP 32
     ==> ~(&(val(word_zx(word a:int64):int32)):int - &k =
           &(val(word_sub (word_zx(word a:int64):int32) (word k:int32)))) \/
         val(word_sub (word_zx(word a:int64):int32) (word k:int32)) = 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_zx(word a:int64):int32) = a` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_ZX_64_32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word k:int32) = k` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `a = k:num` THEN ASM_REWRITE_TAC[] THENL
   [DISJ2_TAC THEN
    SUBGOAL_THEN `word_zx(word k:int64):int32 = word k` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM VAL_EQ] THEN ASM_SIMP_TAC[VAL_WORD_ZX_64_32] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC VAL_WORD_EQ THEN
      REWRITE_TAC[DIMINDEX_32] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0]];
    DISJ1_TAC THEN
    SUBGOAL_THEN `a < k` ASSUME_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word_sub (word_zx(word a:int64):int32) (word k:int32)) =
                  a + 2 EXP 32 - k` SUBST1_TAC THENL
     [REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THENL
       [REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC; REFL_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&a:int < &k` MP_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_LT] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SPEC_TAC(`a + 2 EXP 32 - k`,`m:num`) THEN INT_ARITH_TAC]);;

(* word_add evaluation when both summands are bounded by 248 (and thus the   *)
(* sum is also bounded). Used to compute exact RAX value after `add eax, r9d`*)
(* in sub-iter 1 of the body proof.                                          *)

(* [from mldsa-native mldsa_utils.ml] *)
let NUM_OF_WORDLIST_SINGLETON_INT32 = prove
 (`!(x:int32). num_of_wordlist [x] = val x`,
  REWRITE_TAC[num_of_wordlist] THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let SUB_LIST_256_LE = prove
 (`!(l:int32 list). LENGTH l <= 256 ==> SUB_LIST(0, 256) l = l`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `m = LENGTH (l:int32 list)` THEN
  MP_TAC(ISPECL [`l:int32 list`; `m:num`; `256 - m`; `0`] SUB_LIST_SPLIT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 + a = a`] THEN
  ASM_SIMP_TAC[ARITH_RULE `m <= 256 ==> m + (256 - m) = 256`] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[SUB_LIST_LENGTH; SUB_LIST_TRIVIAL; LE_REFL; APPEND_NIL] THEN
  UNDISCH_TAC `LENGTH (l:int32 list) = m` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[SUB_LIST_LENGTH] THEN
  MP_TAC(ISPECL [`l:int32 list`; `LENGTH (l:int32 list)`;
                 `256 - LENGTH (l:int32 list)`] SUB_LIST_TRIVIAL) THEN
  REWRITE_TAC[LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[APPEND_NIL]);;

(* When the input has its full known length, SUB_LIST(0, that length) is a   *)
(* no-op: applies to LENGTH inlist = 272.                                    *)

(* [from mldsa-native mldsa_utils.ml] *)
let PURGE_STALE_STATES_TAC names =
  let rec refs_stale tm = match tm with
    | Comb(Comb(Const("read",_),_),Var(nm,_)) when List.mem nm names -> true
    | Comb(a,b) -> refs_stale a || refs_stale b | Abs(_,b) -> refs_stale b | _ -> false in
  REPEAT(FIRST_X_ASSUM(fun th -> if refs_stale (concl th) then ALL_TAC else failwith "keep"));;

(* [from mldsa-native mldsa_utils.ml] *)
let DROP_WORDJOIN_TAC : tactic = fun (asl,w) ->
  (REPEAT(FIRST_X_ASSUM(fun th ->
     if can (find_term (fun u -> match u with Const("word_join",_) -> true | _ -> false)) (concl th)
     then ALL_TAC else failwith "keep"))) (asl,w);;

(* [from mldsa-native mldsa_utils.ml] *)
let VAL_WORD_BYTE_LT256 = prove
 (`!n. n < 256 ==> val(word n:byte) = n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]);;

(* [from mldsa-native mldsa_utils.ml] *)
let BYTE_DIV16_LT = prove
 (`!b:byte. val b DIV 16 < 256`,
  GEN_TAC THEN MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC `b:byte` VAL_BOUND)) THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let BYTE_MOD16_LT = prove
 (`!b:byte. val b MOD 16 < 256`,
  GEN_TAC THEN MP_TAC(SPECL[`val(b:byte)`;`16`] MOD_LT_EQ) THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let MM64_256 = prove
 (`!a. a MOD 18446744073709551616 MOD 256 = a MOD 256`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
    [ARITH_RULE `18446744073709551616 = 256 * 72057594037927936`] THEN
  REWRITE_TAC[MOD_MOD]);;

(* a MOD 2^32 MOD 2^64 = a MOD 2^32                                          *)

(* [from mldsa-native mldsa_utils.ml] *)
let MM32_64 = prove
 (`!a. a MOD 4294967296 MOD 18446744073709551616 = a MOD 4294967296`,
  GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL[`a:num`;`4294967296`] MOD_LT_EQ) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* (x DIV 2^8) MOD 2^8 = (x MOD 2^16) DIV 2^8                                *)

(* [from mldsa-native mldsa_utils.ml] *)
let divmod_swap = prove
 (`!x. (x DIV 2 EXP 8) MOD 2 EXP 8 = (x MOD 2 EXP 16) DIV 2 EXP 8`,
  GEN_TAC THEN REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV);;

(* (S MOD 2^32 DIV 256) MOD 256 = (S DIV 256) MOD 256                        *)

(* [from mldsa-native mldsa_utils.ml] *)
let MM32_DIV256 = prove
 (`!S. (S MOD 4294967296 DIV 256) MOD 256 = (S DIV 256) MOD 256`,
  GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`; ARITH_RULE `256 = 2 EXP 8`] THEN
  REWRITE_TAC[divmod_swap] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* mask8b = word_zx(word_ushr(word_zx(word_zx(word S:int32):int64):int32) 8):int64,
   the R8-shifted-by-8 value at the start of sub-iter 2.  Its low byte = byte 1 of S. *)

(* [from mldsa-native mldsa_utils.ml] *)
let LOW16_LT = prove
 (`!p:num->bool. bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) < 65536`,
  GEN_TAC THEN
  MAP_EVERY (fun k -> MP_TAC(ISPEC (mk_comb(`p:num->bool`,mk_small_numeral k)) BITVAL_BOUND))
    [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15] THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let MASK_USHR8_STEP = prove
 (`!m:int64. val(word_zx(word_ushr(word_zx m:int32) 8):int64) MOD 256 = (val m DIV 256) MOD 256`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR; DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN REWRITE_TAC[MM64_256; MM32_DIV256]);;

(* [from mldsa-native mldsa_utils.ml] *)
let DIVLT = prove(`!a k e. a < e ==> a DIV k < e`,
  REPEAT STRIP_TAC THEN TRANS_TAC LET_TRANS `a:num` THEN ASM_REWRITE_TAC[DIV_LE]);;

(* [from mldsa-native mldsa_utils.ml] *)
let divmod_swap16 = prove(`!x. (x DIV 2 EXP 16) MOD 2 EXP 8 = (x MOD 2 EXP 24) DIV 2 EXP 16`,
  GEN_TAC THEN REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV);;

(* [from mldsa-native mldsa_utils.ml] *)
let divmod_swap24 = prove(`!x. (x DIV 2 EXP 24) MOD 2 EXP 8 = (x MOD 2 EXP 32) DIV 2 EXP 24`,
  GEN_TAC THEN REWRITE_TAC[DIV_MOD; GSYM EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV);;

(* full val of the byte-1 / byte-2 masks (mask8b = ushr8 once; mask8c = ushr8 twice) *)

(* [from mldsa-native mldsa_utils.ml] *)
let VAL_MASK8B = prove
 (`!S. val(word_zx(word_ushr(word_zx(word_zx(word S:int32):int64):int32) 8):int64) = (S MOD 4294967296) DIV 256`,
  GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`; ARITH_RULE `256 = 2 EXP 8`] THEN
  MP_TAC(SPECL[`S:num`;`2 EXP 32`] MOD_LT_EQ) THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  ABBREV_TAC `q = S MOD 2 EXP 32` THEN DISCH_TAC THEN
  SUBGOAL_THEN `q < 2 EXP 64` ASSUME_TAC THENL
   [TRANS_TAC LTE_TRANS `2 EXP 32` THEN ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `q MOD 2 EXP 64 MOD 2 EXP 32 = q` SUBST1_TAC THENL
   [ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
  MATCH_MP_TAC MOD_LT THEN TRANS_TAC LET_TRANS `q:num` THEN REWRITE_TAC[DIV_LE] THEN ASM_REWRITE_TAC[]);;

(* [from mldsa-native mldsa_utils.ml] *)
let VAL_MASK8C = prove
 (`!S. val(word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word S:int32):int64):int32) 8):int64):int32) 8):int64) =
       (S MOD 4294967296) DIV 65536`,
  GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`] THEN
  MP_TAC(SPECL[`S:num`;`2 EXP 32`] MOD_LT_EQ) THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
  ABBREV_TAC `q = S MOD 2 EXP 32` THEN DISCH_TAC THEN
  SUBGOAL_THEN `q < 2 EXP 64 /\ q DIV 2 EXP 8 < 2 EXP 64 /\ q DIV 2 EXP 8 < 2 EXP 32 /\
                q DIV 2 EXP 8 DIV 2 EXP 8 < 2 EXP 64` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `q < 2 EXP 64 /\ q < 2 EXP 32` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN TRANS_TAC LTE_TRANS `2 EXP 32` THEN ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DIVLT]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN REWRITE_TAC[DIV_DIV] THEN AP_TERM_TAC THEN CONV_TAC NUM_REDUCE_CONV);;

(* mask byte for sub-iter 3 (double ushr) = byte 2 ; sub-iter 4 (triple ushr) = byte 3 *)

(* [from mldsa-native mldsa_utils.ml] *)
let SUMTERM_BYTE23 = `(bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
   16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
   256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
   4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
   65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
   1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
   16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
   268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31))`;;

(* [from mldsa-native mldsa_utils.ml] *)
let R_EQ = prove(`val (word_zx (word_zx (word (val (mask8:int64) MOD 256):byte):int32):int64):num = val (mask8:int64) MOD 256`,
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* [from mldsa-native mldsa_utils.ml] *)
let RLT = prove(`val (mask8:int64) MOD 256 < 256`, REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let SUBWORD_ZX_LOW = prove
 (`!(y:(M)word) lo wid. lo + wid <= dimindex(:P)
     ==> word_subword (word_zx y:(P)word) (lo,wid):(N)word = word_subword y (lo,wid)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_ZX] THEN
  ASM_CASES_TAC `k < MIN wid (dimindex(:N))` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[ARITH_RULE `k < MIN a b <=> k < a /\ k < b`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `lo + k < dimindex(:P)` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let ZX_128_256_128 = prove(`!(x:(128)word). word_zx(word_zx x:(256)word):(128)word = x`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT; DIMINDEX_128] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[BIT_WORD_ZX; DIMINDEX_128; DIMINDEX_256] THEN
  SUBGOAL_THEN `k < 128 /\ k < 256` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let SUBWORD_USHR = prove
 (`!(x:(M)word) n lo wid. word_subword (word_ushr x n) (lo,wid):(N)word = word_subword x (lo+n,wid)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[BIT_WORD_SUBWORD; BIT_WORD_USHR] THEN
  REWRITE_TAC[ARITH_RULE `(lo + k) + n = (lo + n) + k`]);;


(* --- prefix_g_full_tac ---                                                 *)

(* [from mldsa-native mldsa_utils.ml] *)
let DIVMOD256_SPLIT = prove
 (`!a b c. a < 256 /\ b < 256 ==> (a + 256 * b + 65536 * c) DIV 256 MOD 256 = b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a + 256 * b + 65536 * c) DIV 256 = b + 256 * c` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `a:num` THEN ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `b + 256 * c = c * 256 + b`; MOD_MULT_ADD] THEN
    ASM_SIMP_TAC[MOD_LT]]);;

(* [from mldsa-native mldsa_utils.ml] *)
let R_EQ_B = prove(`val (word_zx (word_zx (word (val (mask8b:int64) MOD 256):byte):int32):int64):num = val (mask8b:int64) MOD 256`,
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* [from mldsa-native mldsa_utils.ml] *)
let RLT_B = prove(`val (mask8b:int64) MOD 256 < 256`, REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let DIVMOD65536_SPLIT = prove
 (`!a b c. a < 65536 /\ b < 256 ==> (a + 65536 * b + 16777216 * c) DIV 65536 MOD 256 = b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a + 65536 * b + 16777216 * c) DIV 65536 = b + 256 * c` SUBST1_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `a:num` THEN ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `b + 256 * c = c * 256 + b`; MOD_MULT_ADD] THEN ASM_SIMP_TAC[MOD_LT]]);;

(* [from mldsa-native mldsa_utils.ml] *)
let R_EQ_C = prove(`val (word_zx (word_zx (word (val (mask8c:int64) MOD 256):byte):int32):int64):num = val (mask8c:int64) MOD 256`,
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* [from mldsa-native mldsa_utils.ml] *)
let RLT_C = prove(`val (mask8c:int64) MOD 256 < 256`, REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let DIVMOD16777216_SPLIT = prove
 (`!a b. a < 16777216 ==> (a + 16777216 * b) DIV 16777216 MOD 256 = b MOD 256`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a + 16777216 * b) DIV 16777216 = b` (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `a:num` THEN ASM_ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let R_EQ_D = prove(`val (word_zx (word_zx (word (val (mask8d:int64) MOD 256):byte):int32):int64):num = val (mask8d:int64) MOD 256`,
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* [from mldsa-native mldsa_utils.ml] *)
let RLT_D = prove(`val (mask8d:int64) MOD 256 < 256`, REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC);;

(* [from mldsa-native mldsa_utils.ml] *)
let MM64_32 = prove(`!a. a MOD 2 EXP 64 MOD 2 EXP 32 = a MOD 2 EXP 32`,
  GEN_TAC THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* [from mldsa-native mldsa_utils.ml] *)
let LENGTH_BUTLAST_GEN = prove
 (`!l:A list. ~(l = []) ==> LENGTH l = LENGTH(BUTLAST l) + 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `l:A list` APPEND_BUTLAST_LAST) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC);;


let mldsa_rej_uniform_eta4_mc = define_assert_from_elf
  "mldsa_rej_uniform_eta4_mc" "x86/mldsa/mldsa_rej_uniform_eta4_VARIABLE_TIME.o"
(*** BYTECODE START ***)
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x41; 0xb8; 0x0f; 0x0f; 0x0f; 0x0f;
                           (* MOV (% r8d) (Imm32 (word 252645135)) *)
  0xc4; 0xc1; 0x79; 0x6e; 0xd0;
                           (* VMOVD (%_% xmm2) (% r8d) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xd2;
                           (* VPBROADCASTD (%_% ymm2) (%_% xmm2) *)
  0x41; 0xb8; 0x04; 0x04; 0x04; 0x04;
                           (* MOV (% r8d) (Imm32 (word 67372036)) *)
  0xc4; 0xc1; 0x79; 0x6e; 0xd8;
                           (* VMOVD (%_% xmm3) (% r8d) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xdb;
                           (* VPBROADCASTD (%_% ymm3) (%_% xmm3) *)
  0x41; 0xb8; 0x09; 0x09; 0x09; 0x09;
                           (* MOV (% r8d) (Imm32 (word 151587081)) *)
  0xc4; 0xc1; 0x79; 0x6e; 0xe0;
                           (* VMOVD (%_% xmm4) (% r8d) *)
  0xc4; 0xe2; 0x7d; 0x58; 0xe4;
                           (* VPBROADCASTD (%_% ymm4) (%_% xmm4) *)
  0x31; 0xc0;              (* XOR (% eax) (% eax) *)
  0x31; 0xc9;              (* XOR (% ecx) (% ecx) *)
  0x3d; 0xf8; 0x00; 0x00; 0x00;
                           (* CMP (% eax) (Imm32 (word 248)) *)
  0x0f; 0x87; 0xfb; 0x00; 0x00; 0x00;
                           (* JA (Imm32 (word 251)) *)
  0x81; 0xf9; 0x00; 0x01; 0x00; 0x00;
                           (* CMP (% ecx) (Imm32 (word 256)) *)
  0x0f; 0x87; 0xef; 0x00; 0x00; 0x00;
                           (* JA (Imm32 (word 239)) *)
  0xc4; 0xe2; 0x7d; 0x30; 0x04; 0x0e;
                           (* VPMOVZXBW (%_% ymm0) (Memop Word128 (%%% (rsi,0,rcx))) *)
  0xc5; 0xf5; 0x71; 0xf0; 0x04;
                           (* VPSLLW (%_% ymm1) (%_% ymm0) (Imm8 (word 4)) *)
  0xc5; 0xfd; 0xeb; 0xc1;  (* VPOR (%_% ymm0) (%_% ymm0) (%_% ymm1) *)
  0xc5; 0xfd; 0xdb; 0xc2;  (* VPAND (%_% ymm0) (%_% ymm0) (%_% ymm2) *)
  0xc5; 0xfd; 0xf8; 0xcc;  (* VPSUBB (%_% ymm1) (%_% ymm0) (%_% ymm4) *)
  0xc5; 0xe5; 0xf8; 0xc0;  (* VPSUBB (%_% ymm0) (%_% ymm3) (%_% ymm0) *)
  0xc5; 0x7d; 0xd7; 0xc1;  (* VPMOVMSKB (% r8d) (%_% ymm1) *)
  0xc4; 0xe3; 0x7d; 0x39; 0xc5; 0x00;
                           (* VEXTRACTI128 (%_% xmm5) (%_% ymm0) (Imm8 (word 0)) *)
  0x45; 0x0f; 0xb6; 0xd0;  (* MOVZX (% r10d) (% r8b) *)
  0xc4; 0xa1; 0x7a; 0x7e; 0x34; 0xd2;
                           (* VMOVQ (%_% xmm6) (Memop Quadword (%%% (rdx,3,r10))) *)
  0xc4; 0xe2; 0x51; 0x00; 0xf6;
                           (* VPSHUFB (%_% xmm6) (%_% xmm5) (%_% xmm6) *)
  0xc4; 0xe2; 0x7d; 0x21; 0xce;
                           (* VPMOVSXBD (%_% ymm1) (%_% xmm6) *)
  0xc5; 0xfe; 0x7f; 0x0c; 0x87;
                           (* VMOVDQU (Memop Word256 (%%% (rdi,2,rax))) (%_% ymm1) *)
  0xf3; 0x45; 0x0f; 0xb8; 0xca;
                           (* POPCNT (% r9d) (% r10d) *)
  0x44; 0x01; 0xc8;        (* ADD (% eax) (% r9d) *)
  0x41; 0xc1; 0xe8; 0x08;  (* SHR (% r8d) (Imm8 (word 8)) *)
  0x83; 0xc1; 0x04;        (* ADD (% ecx) (Imm8 (word 4)) *)
  0x3d; 0xf8; 0x00; 0x00; 0x00;
                           (* CMP (% eax) (Imm32 (word 248)) *)
  0x0f; 0x87; 0x97; 0x00; 0x00; 0x00;
                           (* JA (Imm32 (word 151)) *)
  0xc5; 0xd1; 0x73; 0xdd; 0x08;
                           (* VPSRLDQ (%_% xmm5) (%_% xmm5) (Imm8 (word 8)) *)
  0x45; 0x0f; 0xb6; 0xd0;  (* MOVZX (% r10d) (% r8b) *)
  0xc4; 0xa1; 0x7a; 0x7e; 0x34; 0xd2;
                           (* VMOVQ (%_% xmm6) (Memop Quadword (%%% (rdx,3,r10))) *)
  0xc4; 0xe2; 0x51; 0x00; 0xf6;
                           (* VPSHUFB (%_% xmm6) (%_% xmm5) (%_% xmm6) *)
  0xc4; 0xe2; 0x7d; 0x21; 0xce;
                           (* VPMOVSXBD (%_% ymm1) (%_% xmm6) *)
  0xc5; 0xfe; 0x7f; 0x0c; 0x87;
                           (* VMOVDQU (Memop Word256 (%%% (rdi,2,rax))) (%_% ymm1) *)
  0xf3; 0x45; 0x0f; 0xb8; 0xca;
                           (* POPCNT (% r9d) (% r10d) *)
  0x44; 0x01; 0xc8;        (* ADD (% eax) (% r9d) *)
  0x41; 0xc1; 0xe8; 0x08;  (* SHR (% r8d) (Imm8 (word 8)) *)
  0x83; 0xc1; 0x04;        (* ADD (% ecx) (Imm8 (word 4)) *)
  0x3d; 0xf8; 0x00; 0x00; 0x00;
                           (* CMP (% eax) (Imm32 (word 248)) *)
  0x77; 0x63;              (* JA (Imm8 (word 99)) *)
  0xc4; 0xe3; 0x7d; 0x39; 0xc5; 0x01;
                           (* VEXTRACTI128 (%_% xmm5) (%_% ymm0) (Imm8 (word 1)) *)
  0x45; 0x0f; 0xb6; 0xd0;  (* MOVZX (% r10d) (% r8b) *)
  0xc4; 0xa1; 0x7a; 0x7e; 0x34; 0xd2;
                           (* VMOVQ (%_% xmm6) (Memop Quadword (%%% (rdx,3,r10))) *)
  0xc4; 0xe2; 0x51; 0x00; 0xf6;
                           (* VPSHUFB (%_% xmm6) (%_% xmm5) (%_% xmm6) *)
  0xc4; 0xe2; 0x7d; 0x21; 0xce;
                           (* VPMOVSXBD (%_% ymm1) (%_% xmm6) *)
  0xc5; 0xfe; 0x7f; 0x0c; 0x87;
                           (* VMOVDQU (Memop Word256 (%%% (rdi,2,rax))) (%_% ymm1) *)
  0xf3; 0x45; 0x0f; 0xb8; 0xca;
                           (* POPCNT (% r9d) (% r10d) *)
  0x44; 0x01; 0xc8;        (* ADD (% eax) (% r9d) *)
  0x41; 0xc1; 0xe8; 0x08;  (* SHR (% r8d) (Imm8 (word 8)) *)
  0x83; 0xc1; 0x04;        (* ADD (% ecx) (Imm8 (word 4)) *)
  0x3d; 0xf8; 0x00; 0x00; 0x00;
                           (* CMP (% eax) (Imm32 (word 248)) *)
  0x77; 0x2e;              (* JA (Imm8 (word 46)) *)
  0xc5; 0xd1; 0x73; 0xdd; 0x08;
                           (* VPSRLDQ (%_% xmm5) (%_% xmm5) (Imm8 (word 8)) *)
  0x45; 0x0f; 0xb6; 0xd0;  (* MOVZX (% r10d) (% r8b) *)
  0xc4; 0xa1; 0x7a; 0x7e; 0x34; 0xd2;
                           (* VMOVQ (%_% xmm6) (Memop Quadword (%%% (rdx,3,r10))) *)
  0xc4; 0xe2; 0x51; 0x00; 0xf6;
                           (* VPSHUFB (%_% xmm6) (%_% xmm5) (%_% xmm6) *)
  0xc4; 0xe2; 0x7d; 0x21; 0xce;
                           (* VPMOVSXBD (%_% ymm1) (%_% xmm6) *)
  0xc5; 0xfe; 0x7f; 0x0c; 0x87;
                           (* VMOVDQU (Memop Word256 (%%% (rdi,2,rax))) (%_% ymm1) *)
  0xf3; 0x45; 0x0f; 0xb8; 0xca;
                           (* POPCNT (% r9d) (% r10d) *)
  0x44; 0x01; 0xc8;        (* ADD (% eax) (% r9d) *)
  0x83; 0xc1; 0x04;        (* ADD (% ecx) (Imm8 (word 4)) *)
  0xe9; 0xfa; 0xfe; 0xff; 0xff;
                           (* JMP (Imm32 (word 4294967034)) *)
  0x3d; 0x00; 0x01; 0x00; 0x00;
                           (* CMP (% eax) (Imm32 (word 256)) *)
  0x73; 0x51;              (* JAE (Imm8 (word 81)) *)
  0x81; 0xf9; 0x10; 0x01; 0x00; 0x00;
                           (* CMP (% ecx) (Imm32 (word 272)) *)
  0x73; 0x49;              (* JAE (Imm8 (word 73)) *)
  0x44; 0x0f; 0xb6; 0x1c; 0x0e;
                           (* MOVZX (% r11d) (Memop Byte (%%% (rsi,0,rcx))) *)
  0xff; 0xc1;              (* INC (% ecx) *)
  0x45; 0x89; 0xda;        (* MOV (% r10d) (% r11d) *)
  0x41; 0x83; 0xe2; 0x0f;  (* AND (% r10d) (Imm8 (word 15)) *)
  0x41; 0x83; 0xfa; 0x09;  (* CMP (% r10d) (Imm8 (word 9)) *)
  0x73; 0x16;              (* JAE (Imm8 (word 22)) *)
  0x41; 0xb9; 0x04; 0x00; 0x00; 0x00;
                           (* MOV (% r9d) (Imm32 (word 4)) *)
  0x45; 0x29; 0xd1;        (* SUB (% r9d) (% r10d) *)
  0x44; 0x89; 0x0c; 0x87;  (* MOV (Memop Doubleword (%%% (rdi,2,rax))) (% r9d) *)
  0xff; 0xc0;              (* INC (% eax) *)
  0x3d; 0x00; 0x01; 0x00; 0x00;
                           (* CMP (% eax) (Imm32 (word 256)) *)
  0x73; 0x1f;              (* JAE (Imm8 (word 31)) *)
  0x41; 0xc1; 0xeb; 0x04;  (* SHR (% r11d) (Imm8 (word 4)) *)
  0x41; 0x83; 0xe3; 0x0f;  (* AND (% r11d) (Imm8 (word 15)) *)
  0x41; 0x83; 0xfb; 0x09;  (* CMP (% r11d) (Imm8 (word 9)) *)
  0x73; 0xb9;              (* JAE (Imm8 (word 185)) *)
  0x41; 0xba; 0x04; 0x00; 0x00; 0x00;
                           (* MOV (% r10d) (Imm32 (word 4)) *)
  0x45; 0x29; 0xda;        (* SUB (% r10d) (% r11d) *)
  0x44; 0x89; 0x14; 0x87;  (* MOV (Memop Doubleword (%%% (rdi,2,rax))) (% r10d) *)
  0xff; 0xc0;              (* INC (% eax) *)
  0xeb; 0xa8;              (* JMP (Imm8 (word 168)) *)
  0xc3                     (* RET *)
];;
(*** BYTECODE END ***)

let mldsa_rej_uniform_eta4_tmc = define_trimmed
  "mldsa_rej_uniform_eta4_tmc" mldsa_rej_uniform_eta4_mc;;

let MLDSA_REJ_UNIFORM_ETA4_EXEC = X86_MK_CORE_EXEC_RULE mldsa_rej_uniform_eta4_tmc;;

(* ------------------------------------------------------------------------- *)
(* Length helpers                                                            *)
(* ------------------------------------------------------------------------- *)

let LENGTH_MLDSA_REJ_UNIFORM_ETA4_TMC =
  REWRITE_CONV[mldsa_rej_uniform_eta4_tmc] `LENGTH mldsa_rej_uniform_eta4_tmc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

(* ------------------------------------------------------------------------- *)
(* Supporting spec lemmas, byte-shape interior aliases.                      *)
(*                                                                           *)
(* The public spec REJ_SAMPLE_ETA4 (in common/mldsa_specs.ml) takes a        *)
(* nibble list. The proof below is naturally written against the byte-list   *)
(* shape, since the loop invariant peels off bytes per iteration, so we      *)
(* introduce private byte-shape aliases below and bridge to the public spec  *)
(* at the subroutine spec.                                                   *)
(* ------------------------------------------------------------------------- *)

let REJ_NIBBLES_ETA4 = define
  `REJ_NIBBLES_ETA4 (l:byte list) =
   FILTER (\x:int16. val x < 9) (NIBBLES_OF_BYTES l)`;;

let REJ_SAMPLE_ETA4_BYTES = define
  `REJ_SAMPLE_ETA4_BYTES (l:byte list) =
   MAP (\x:int16. word_sx(word_sub (word 4:int16) x):int32)
       (REJ_NIBBLES_ETA4 l)`;;

(* Conversion lemma: NIBBLES_OF_BYTES (int16 list) = MAP word_zx of BYTES_TO_NIBBLES (4 word list) *)
let REJ_SAMPLE_ETA4_BYTES_EQ = prove
 (`!l:byte list. REJ_SAMPLE_ETA4_BYTES l =
                 REJ_SAMPLE_ETA4 (BYTES_TO_NIBBLES l)`,
  GEN_TAC THEN
  REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES; REJ_NIBBLES_ETA4; REJ_SAMPLE_ETA4;
              NIBBLES_OF_BYTES_EQ_BYTES_TO_NIBBLES] THEN
  REWRITE_TAC[FILTER_MAP; o_DEF; GSYM MAP_o] THEN
  SUBGOAL_THEN `!x:4 word. val (word_zx x:int16) = val x`
    (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC VAL_WORD_ZX THEN
    REWRITE_TAC[DIMINDEX_4; DIMINDEX_16] THEN ARITH_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`BYTES_TO_NIBBLES (l:byte list)`,`xs:(4 word) list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; MAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM(K ALL_TAC) THEN
  BITBLAST_TAC);;

(* ========================================================================= *)
(* Shared rejection-sampling lemmas (gather / table / store-compaction),     *)
(* independent of the eta parameter.                                         *)
(* ========================================================================= *)

let TABLE_ENTRY = define
 `TABLE_ENTRY (m:byte) = SUB_LIST(8 * val m, 8) (mldsa_rej_uniform_table:byte list)`;;

(* bytes64 read = word of the 8-byte little-endian value.                    *)

let READ_BYTES_SLICE = prove
 (`!(a:int64) k n (L:byte list) (s:x86state).
      read(memory:>bytes(a,LENGTH L)) s = num_of_wordlist L /\ k + n <= LENGTH L
      ==> read(memory:>bytes(word_add a (word k), n)) s = num_of_wordlist(SUB_LIST(k,n) L)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k + (LENGTH(L:byte list) - k) = LENGTH L` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `n + (LENGTH(L:byte list) - (k+n)) = LENGTH L - k` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `read(memory:>bytes(word_add a (word k), LENGTH(L:byte list) - k)) s =
                num_of_wordlist(SUB_LIST(k, LENGTH L - k) L)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `a:int64`; `s:x86state`;
       `SUB_LIST(0,k) (L:byte list)`; `SUB_LIST(k, LENGTH(L:byte list) - k) L`;
       `k:num`; `LENGTH(L:byte list) - k`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
    REWRITE_TAC[DIMINDEX_8; LENGTH_SUB_LIST; SUB_0] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[SUB_LIST_TOPSPLIT] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `word_add a (word k):int64`; `s:x86state`;
     `SUB_LIST(k,n) (L:byte list)`; `SUB_LIST(k+n, LENGTH(L:byte list) - (k+n)) L`;
     `n:num`; `LENGTH(L:byte list) - (k + n)`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
  REWRITE_TAC[DIMINDEX_8; LENGTH_SUB_LIST] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:byte list`; `n:num`; `LENGTH(L:byte list) - (k+n)`; `k:num`] SUB_LIST_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* NOTE: in the clean loop body, the stepped vpmovsxbd output `read YMM1 sN` (a word_join
   nest of word_sx over the low-8 bytes of word_zx(word_zx pshuf)) is rewritten to the
   canonical `usimd8 (\b. word_sx b) (word_zx(word_zx pshuf))` form in-context (where the
   term is fully typed by the simulator) via `REWRITE_TAC[usimd8;usimd4;usimd2] THEN
   SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_*;ARITH] THEN CONV_TAC NUM_REDUCE_CONV`, after which
   the committed VPMOVSXBD_LANE_EXTRACT gives each int32 lane = word_sx of the pshuf byte.
   (Kept as an in-body step rather than a standalone lemma because the
   word_join associativity/widths are simulator-determined.) *)

(* Store-value memory lemma: the first k int32 lanes of a 256-bit store at A read back as
   num_of_wordlist L, where L is the int32 list whose elements are V's lanes.  This is the
   bridge from the vmovdqu writeback to the REJ_SAMPLE block: with V = vpmovsxbd output and
   L = REJ_SAMPLE_ETA4_BYTES block (via SUBITER1_VALUE + VPMOVSXBD_LANE_EXTRACT giving
   word_subword V (32j,32) = EL j L), this yields the sub-iter store memory postcondition. *)

let STORE_BYTES256_NUM_OF_WORDLIST = prove
 (`!(A:int64) (V:int256) (L:int32 list) k (s:x86state).
      read(memory:>bytes256 A) s = V /\ LENGTH L = k /\ k <= 8 /\
      (!j. j < k ==> word_subword V (32*j,32):int32 = EL j L)
      ==> read(memory:>bytes(A, 4*k)) s = num_of_wordlist L`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:int64`; `V:int256`; `k:num`; `s:x86state`] BYTES256_PREFIX_WORDLIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC WORDLIST_OF_NUM_VAL_EQ THEN ASM_REWRITE_TAC[]);;

(* The vmovq table load: with the table memory invariant, reading the 8-byte entry at
   index r (byte offset 8r) yields word(num_of_wordlist(TABLE_ENTRY(word r))) — i.e. the
   gather-control word for mask r.  Bridge (1) of the sub-iter store value. *)

let TABLE_VMOVQ_READ = prove
 (`!(table:int64) r (s:x86state).
      read(memory:>bytes(table,2048)) s = num_of_wordlist(mldsa_rej_uniform_table:byte list) /\ r < 256
      ==> read(memory:>bytes64(word_add table (word(8*r)))) s =
          word(num_of_wordlist(TABLE_ENTRY(word r:byte)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RB64; TABLE_ENTRY] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `LENGTH(mldsa_rej_uniform_table:byte list) = 2048` ASSUME_TAC THENL
   [REWRITE_TAC[mldsa_rej_uniform_table; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `val(word r:byte) = r` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_8] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`table:int64`; `8*r`; `8`; `mldsa_rej_uniform_table:byte list`; `s:x86state`]
    READ_BYTES_SLICE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN MATCH_ACCEPT_TAC]);;

let ACC_IDX = define
 `ACC_IDX (m:byte) = FILTER (\i. bit i m) [0;1;2;3;4;5;6;7]`;;

(* Keystone table-correspondence lemma: for every mask m, the first          *)
(* |ACC_IDX m| bytes of the table entry table[m] are exactly the accepted    *)
(* (set-bit) positions of m, in increasing order. This is what makes the     *)
(* pshufb gather compact the accepted nibbles to the front: gathering the    *)
(* source vector at these table indices reads precisely the accepted lanes.  *)
(* Proved by exhaustive 256-mask evaluation: each case evaluates             *)
(* ACC_IDX(word m) and table[m] concretely and checks the prefix. There is   *)
(* no closed form for the literal 256x8 table, so the case split is honest.  *)

let TABLE_PREFIX_ACC = prove
 (`!m. m < 256 ==>
    SUB_LIST(0, LENGTH(ACC_IDX(word m:byte))) (TABLE_ENTRY(word m)) =
    MAP word (ACC_IDX(word m:byte)):byte list`,
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[ACC_IDX; TABLE_ENTRY; FILTER] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[mldsa_rej_uniform_table] THEN
  CONV_TAC(DEPTH_CONV SUB_LIST_CONV) THEN
  REWRITE_TAC[MAP] THEN CONV_TAC(DEPTH_CONV WORD_RED_CONV));;

(* Per-byte VPSHUFB gather behavior: a control byte c with c < 8 (top bit    *)
(* clear, so the byte is selected not zeroed; low nibble = c since c < 8)    *)
(* selects source byte c. This is the building block for the table-driven    *)
(* compaction: the rej_uniform table stores accepted-nibble indices < 8 in   *)
(* each control lane, and this lemma reduces VPSHUFB's f8 selector to a      *)
(* plain source-byte pick. Matches the f8 in x86_VPSHUFB exactly.            *)

let PSHUFB_GATHER_BYTE = prove
 (`!(w:int128) (c:byte). val c < 8
     ==> (if bit 7 c then word 0:byte
          else word_subword w (8 * val (word_subword c (0,4):byte),8)) =
         word_subword w (8 * val c,8)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(bit 7 (c:byte))` ASSUME_TAC THENL
   [REWRITE_TAC[BIT_VAL] THEN
    SUBGOAL_THEN `val(c:byte) DIV 2 EXP 7 = 0` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC DIV_LT THEN UNDISCH_TAC `val(c:byte) < 8` THEN ARITH_TAC;
      CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(word_subword (c:byte) (0,4):byte) = val c` SUBST1_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[DIV_1] THEN
    MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `val(c:byte) < 8` THEN ARITH_TAC;
    REFL_TAC]);;

(* Per-lane extraction of a VPSHUFB low-128 result. For any byte->byte lane  *)
(* function ff (the f8 selector in x86_VPSHUFB) and a 64-bit control c       *)
(* lifted to 128 by word_zx, the k-th low output byte (k<8) is               *)
(* ff(control-byte k). Proved by unfolding usimd16/8/4/2, routing the        *)
(* word_subword through the nested word_joins with WORD_SUBWORD_JOIN_LOWER/  *)
(* UPPER (the control side is a fixed bit-routing -> WORD_BLAST), and        *)
(* collapsing the outer byte-subword via WORD_SUBWORD_TRIVIAL. Composing     *)
(* this with PSHUFB_GATHER_BYTE (when each control byte < 8) gives the       *)
(* gather g.byte(c.byte k); with TABLE_BYTES_LT_8 the < 8 side condition is  *)
(* automatic for table-sourced controls.                                     *)

let PSHUFB_LANE_EXTRACT = prove
 (`!(ff:byte->byte) (c:int64).
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (0,8):byte = ff(word_subword c (0,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (8,8):byte = ff(word_subword c (8,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (16,8):byte = ff(word_subword c (16,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (24,8):byte = ff(word_subword c (24,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (32,8):byte = ff(word_subword c (32,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (40,8):byte = ff(word_subword c (40,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (48,8):byte = ff(word_subword c (48,8)) /\
     word_subword (usimd16 ff (word_zx (word_zx c:int128):int128):int128) (56,8):byte = ff(word_subword c (56,8))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[usimd16; usimd8; usimd4; usimd2] THEN
  SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
           DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128; ARITH] THEN
  REPEAT CONJ_TAC THEN
  (SIMP_TAC[WORD_SUBWORD_TRIVIAL; DIMINDEX_8; LE_REFL] THEN
   AP_TERM_TAC THEN CONV_TAC WORD_BLAST));;

(* The pshufb control bytes come from the rej_uniform table; every table     *)
(* byte is < 8 (the table stores 8-element index permutations of {0..7}      *)
(* with the unused tail zeroed). Hence in the compaction step every pshufb   *)
(* control lane has its top bit clear and PSHUFB_GATHER_BYTE applies -- the  *)
(* shuffle never zeroes, it always gathers. Proved via ALL over the literal  *)
(* table (fast:) then specialised to EL form.                                *)

let ALL_TABLE_LT_8 = prove
 (`ALL (\b:byte. val b < 8) mldsa_rej_uniform_table`,
  REWRITE_TAC[mldsa_rej_uniform_table; ALL] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let TABLE_BYTES_LT_8 = prove
 (`!j. j < 2048 ==> val(EL j (mldsa_rej_uniform_table:byte list)) < 8`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\b:byte. val b < 8`; `mldsa_rej_uniform_table:byte list`]
                ALL_EL) THEN
  REWRITE_TAC[ALL_TABLE_LT_8] THEN
  DISCH_THEN(MP_TAC o SPEC `j:num`) THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `LENGTH(mldsa_rej_uniform_table:byte list) = 2048`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[mldsa_rej_uniform_table; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
    ASM_REWRITE_TAC[]]);;

let PSHUFB_TABLE_GATHER_8 = prove
 (`!(g:int128) (c:int64).
     (!k. k < 8 ==> val(word_subword c (8*k,8):byte) < 8)
     ==> (!k. k < 8 ==>
            word_subword (usimd16
              (\(i:byte). if bit 7 i then word 0:byte
                  else word_subword g (8 * val(word_subword i (0,4):byte),8))
              (word_zx (word_zx c:int128):int128):int128) (8*k,8):byte =
            word_subword g (8 * val(word_subword c (8*k,8):byte),8))`,
  GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[PSHUFB_LANE_EXTRACT] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC PSHUFB_GATHER_BYTE THEN
  ASM_SIMP_TAC[ARITH] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN
    MP_TAC(SPEC `3` th) THEN MP_TAC(SPEC `4` th) THEN MP_TAC(SPEC `5` th) THEN
    MP_TAC(SPEC `6` th) THEN MP_TAC(SPEC `7` th)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* The vmovq load puts table[m] into an int64 register as                    *)
(* word(num_of_wordlist(TABLE_ENTRY m)); its k-th byte is EL k (TABLE_ENTRY  *)
(* m). (Inverse of the little-endian num_of_wordlist packing.)               *)

let CTRL_BYTE_TABLE = prove
 (`!m k. k < 8
     ==> word_subword (word(num_of_wordlist(TABLE_ENTRY m)):int64) (8*k,8):byte
         = EL k (TABLE_ENTRY m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`TABLE_ENTRY m:byte list`; `k:num`]
    (INST_TYPE[`:64`,`:KL`; `:8`,`:L`] WORD_SUBWORD_NUM_OF_WORDLIST)) THEN
  REWRITE_TAC[DIMINDEX_64; DIMINDEX_8] THEN
  SUBGOAL_THEN `LENGTH(TABLE_ENTRY m:byte list) = 8` SUBST1_TAC THENL
   [REWRITE_TAC[TABLE_ENTRY; LENGTH_SUB_LIST] THEN
    SUBGOAL_THEN `LENGTH(mldsa_rej_uniform_table:byte list) = 2048`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[mldsa_rej_uniform_table; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    MP_TAC(ISPEC `m:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Every byte of any table entry is < 8 (from TABLE_BYTES_LT_8 via the       *)
(* SUB_LIST offset arithmetic). So all pshufb control lanes gather.          *)

let TABLE_ENTRY_BYTES_LT_8 = prove
 (`!m k. k < 8 ==> val(EL k (TABLE_ENTRY m):byte) < 8`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[TABLE_ENTRY] THEN
  MP_TAC(ISPECL [`mldsa_rej_uniform_table:byte list`; `k:num`; `8 * val(m:byte)`; `8`]
    EL_SUB_LIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `LENGTH(mldsa_rej_uniform_table:byte list) = 2048`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[mldsa_rej_uniform_table; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    MP_TAC(ISPEC `m:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC TABLE_BYTES_LT_8 THEN
  MP_TAC(ISPEC `m:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ASM_ARITH_TAC);;

(* Full per-output-byte compaction for a table-driven VPSHUFB control: the   *)
(* k-th output byte (k<8) is the source byte g at index EL k (TABLE_ENTRY    *)
(* m). Combines PSHUFB_TABLE_GATHER_8 (gather) + CTRL_BYTE_TABLE (control    *)
(* byte = table entry) + TABLE_ENTRY_BYTES_LT_8 (< 8 side condition). With   *)
(* TABLE_PREFIX_ACC, the first popcount(m) of these are exactly g's bytes    *)
(* at the accepted nibble positions -- i.e. the accepted nibbles compacted.  *)

let PSHUFB_OUT_BYTE = prove
 (`!(g:int128) (m:byte) k. k < 8
     ==> word_subword (usimd16
            (\(i:byte). if bit 7 i then word 0:byte
                else word_subword g (8 * val(word_subword i (0,4):byte),8))
            (word_zx (word_zx (word(num_of_wordlist(TABLE_ENTRY m)):int64):int128):int128):int128)
            (8*k,8):byte =
         word_subword g (8 * val(EL k (TABLE_ENTRY m):byte), 8)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g:int128`; `word(num_of_wordlist(TABLE_ENTRY m)):int64`]
    PSHUFB_TABLE_GATHER_8) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CTRL_BYTE_TABLE] THEN
    ASM_SIMP_TAC[TABLE_ENTRY_BYTES_LT_8];
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[CTRL_BYTE_TABLE]]);;

(* The 8 low output bytes of the table-driven VPSHUFB, as an explicit list,  *)
(* and its identification with the gather MAP over the table entry.          *)

let PSHUFB_OUT_LIST = define
 `PSHUFB_OUT_LIST (g:int128) (m:byte) =
    [word_subword g (8 * val(EL 0 (TABLE_ENTRY m):byte),8):byte;
     word_subword g (8 * val(EL 1 (TABLE_ENTRY m):byte),8);
     word_subword g (8 * val(EL 2 (TABLE_ENTRY m):byte),8);
     word_subword g (8 * val(EL 3 (TABLE_ENTRY m):byte),8);
     word_subword g (8 * val(EL 4 (TABLE_ENTRY m):byte),8);
     word_subword g (8 * val(EL 5 (TABLE_ENTRY m):byte),8);
     word_subword g (8 * val(EL 6 (TABLE_ENTRY m):byte),8);
     word_subword g (8 * val(EL 7 (TABLE_ENTRY m):byte),8)]`;;

let PSHUFB_OUT_LIST_AS_MAP = prove
 (`!g m. PSHUFB_OUT_LIST g m =
         MAP (\b:byte. word_subword g (8 * val b,8):byte) (TABLE_ENTRY m)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?a0 a1 a2 a3 a4 a5 a6 a7:byte.
       TABLE_ENTRY m = [a0;a1;a2;a3;a4;a5;a6;a7]` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `LENGTH(TABLE_ENTRY m:byte list) = 8` MP_TAC THENL
     [REWRITE_TAC[TABLE_ENTRY; LENGTH_SUB_LIST] THEN
      SUBGOAL_THEN `LENGTH(mldsa_rej_uniform_table:byte list) = 2048`
        (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[mldsa_rej_uniform_table; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC] THEN
      MP_TAC(ISPEC `m:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
      ALL_TAC] THEN
    SPEC_TAC(`TABLE_ENTRY m:byte list`,`l:byte list`) THEN
    REWRITE_TAC[ARITH_RULE `8 = SUC(SUC(SUC(SUC(SUC(SUC(SUC(SUC 0)))))))`] THEN
    REWRITE_TAC[LENGTH_EQ_CONS; LENGTH_EQ_NIL] THEN MESON_TAC[];
    ASM_REWRITE_TAC[PSHUFB_OUT_LIST; MAP] THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]]);;

let SUB_LIST_NEST = prove
 (`!a n b m l:A list. a + n <= m /\ b + m <= LENGTH l
     ==> SUB_LIST(a,n)(SUB_LIST(b,m) l) = SUB_LIST(b+a,n) l`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[LIST_EQ] THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN CONJ_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `j < n` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(b,m) (l:A list)) = m` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `EL j (SUB_LIST(a,n)(SUB_LIST(b,m) (l:A list))) = EL (a+j) (SUB_LIST(b,m) l)`
    SUBST1_TAC THENL
   [MATCH_MP_TAC EL_SUB_LIST THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `EL (a+j) (SUB_LIST(b,m) (l:A list)) = EL (b+(a+j)) l`
    SUBST1_TAC THENL
   [MATCH_MP_TAC EL_SUB_LIST THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `EL j (SUB_LIST(b+a,n) (l:A list)) = EL ((b+a)+j) l`
    SUBST1_TAC THENL
   [MATCH_MP_TAC EL_SUB_LIST THEN ASM_ARITH_TAC; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

(* From the 16-byte chunk decomposition SUB_LIST(16i,16) inlist = [chunk0 bytes 0..15],
   extract the four 4-byte sub-iter blocks SUB_LIST(16i+4k,4) inlist (k=0,1,2,3) as the
   corresponding 4-byte slices of chunk0. One application yields all four blocks; the
   clean loop body uses these as the [b0;b1;b2;b3] argument to the per-block popcount /
   REJ_SAMPLE bridges. *)

let SUBITER_BLOCK_BYTES = prove
 (`!inlist i chunk0:int128.
      16 * i + 16 <= LENGTH(inlist:byte list) /\
      SUB_LIST(16*i,16) inlist =
        [word_subword chunk0 (0,8); word_subword chunk0 (8,8);
         word_subword chunk0 (16,8); word_subword chunk0 (24,8);
         word_subword chunk0 (32,8); word_subword chunk0 (40,8);
         word_subword chunk0 (48,8); word_subword chunk0 (56,8);
         word_subword chunk0 (64,8); word_subword chunk0 (72,8);
         word_subword chunk0 (80,8); word_subword chunk0 (88,8);
         word_subword chunk0 (96,8); word_subword chunk0 (104,8);
         word_subword chunk0 (112,8); word_subword chunk0 (120,8)]
      ==> SUB_LIST(16*i,4) inlist =
            [word_subword chunk0 (0,8); word_subword chunk0 (8,8);
             word_subword chunk0 (16,8); word_subword chunk0 (24,8)] /\
          SUB_LIST(16*i+4,4) inlist =
            [word_subword chunk0 (32,8); word_subword chunk0 (40,8);
             word_subword chunk0 (48,8); word_subword chunk0 (56,8)] /\
          SUB_LIST(16*i+8,4) inlist =
            [word_subword chunk0 (64,8); word_subword chunk0 (72,8);
             word_subword chunk0 (80,8); word_subword chunk0 (88,8)] /\
          SUB_LIST(16*i+12,4) inlist =
            [word_subword chunk0 (96,8); word_subword chunk0 (104,8);
             word_subword chunk0 (112,8); word_subword chunk0 (120,8)]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL[`0`;`4`;`16*i:num`;`16`;`inlist:byte list`] SUB_LIST_NEST);
    MP_TAC(ISPECL[`4`;`4`;`16*i:num`;`16`;`inlist:byte list`] SUB_LIST_NEST);
    MP_TAC(ISPECL[`8`;`4`;`16*i:num`;`16`;`inlist:byte list`] SUB_LIST_NEST);
    MP_TAC(ISPECL[`12`;`4`;`16*i:num`;`16`;`inlist:byte list`] SUB_LIST_NEST)] THEN
  (ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[ARITH_RULE `16*i+0 = 16*i`] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
   ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV SUB_LIST_CONV) THEN REFL_TAC));;

let ACC_IDX_LT_8 = prove
 (`!m x. MEM x (ACC_IDX m) ==> x < 8`,
  REWRITE_TAC[ACC_IDX] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[MEM_FILTER; MEM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* LENGTH_ACC_IDX_BITSUM: the accept count = sum of the 8 mask bits. Bridges *)
(* LENGTH(ACC_IDX m) to the bitval-sum used by the popcount / maskbit chain, hence to *)
(* LENGTH(REJ_NIBBLES block) = LENGTH(REJ_SAMPLE block) for the SUBITER_STORE_EXTEND *)
(* width reconciliation.                                                     *)

let LENGTH_ACC_IDX_BITSUM = prove
 (`!m:byte. LENGTH(ACC_IDX m) =
            bitval(bit 0 m) + bitval(bit 1 m) + bitval(bit 2 m) + bitval(bit 3 m) +
            bitval(bit 4 m) + bitval(bit 5 m) + bitval(bit 6 m) + bitval(bit 7 m)`,
  GEN_TAC THEN REWRITE_TAC[ACC_IDX] THEN
  MAP_EVERY ASM_CASES_TAC
   [`bit 0 (m:byte)`;`bit 1 (m:byte)`;`bit 2 (m:byte)`;`bit 3 (m:byte)`;
    `bit 4 (m:byte)`;`bit 5 (m:byte)`;`bit 6 (m:byte)`;`bit 7 (m:byte)`] THEN
  ASM_REWRITE_TAC[FILTER; LENGTH; BITVAL_CLAUSES] THEN ARITH_TAC);;

(* (STORE_LANE_MATCH and its table-dependent deps PSHUF1_BYTE_EQ_OUTLIST /   *)
(*  LENGTH_TABLE_ENTRY are defined later, just after                         *)
(*  LENGTH_MLDSA_REJ_UNIFORM_TABLE, since they need the table length.)       *)

(* Gather-at-accepted-positions = filter: gathering an 8-element list at the *)
(* positions where a predicate holds equals filtering the list by that       *)
(* predicate.                                                                *)

let GATHER_FILTERED_IDX_8 = prove
 (`!(P:A->bool) a0 a1 a2 a3 a4 a5 a6 a7.
     MAP (\j. EL j [a0;a1;a2;a3;a4;a5;a6;a7])
         (FILTER (\j. P (EL j [a0;a1;a2;a3;a4;a5;a6;a7])) [0;1;2;3;4;5;6;7]) =
     FILTER P [a0;a1;a2;a3;a4;a5;a6;a7]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FILTER; MAP] THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP; FILTER]) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* Per-sub-iter value bridge: gathering source bytes g at the accepted       *)
(* positions ACC_IDX m (mask m) equals FILTERing the 8 source bytes by the   *)
(* accept predicate val(.) < 9, PROVIDED the mask bit j agrees with that     *)
(* predicate on byte j. This connects the pshufb-compaction output (indexed  *)
(* by ACC_IDX m) to the functional spec's FILTER over byte values. The       *)
(* hypothesis is discharged at the call site from the vpsubb/vpmovmskb mask  *)
(* construction (bit j of the mask = sign bit of nibble_j - 9 = (nibble<9)). *)

let GATHER_FILTER_MAP_IDX_8 = prove
 (`!(f:byte->A) (P:byte->bool) n0 n1 n2 n3 n4 n5 n6 n7.
     MAP (\j. f (EL j [n0;n1;n2;n3;n4;n5;n6;n7]:byte))
         (FILTER (\j. P (EL j [n0;n1;n2;n3;n4;n5;n6;n7])) [0;1;2;3;4;5;6;7]) =
     MAP f (FILTER P [n0;n1;n2;n3;n4;n5;n6;n7])`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`P:byte->bool`; `n0:byte`;`n1:byte`;`n2:byte`;`n3:byte`;
                 `n4:byte`;`n5:byte`;`n6:byte`;`n7:byte`] GATHER_FILTERED_IDX_8) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[GSYM MAP_o; o_DEF]);;

(* The full abstract pshufb-compaction-correctness statement: the first      *)
(* popcount(m) = |ACC_IDX m| output bytes of the table-driven VPSHUFB are    *)
(* exactly the source bytes g at the accepted nibble positions ACC_IDX m,    *)
(* in order. This closes item (d): combined with the nibble-extraction and   *)
(* popcount bridges it shows each sub-iter writes the accepted (4-nibble)    *)
(* values compacted to the front. _NUM form maps over num positions.         *)

let PSHUFB_ACCEPTED_PREFIX = prove
 (`!(g:int128) m. m < 256 ==>
     SUB_LIST(0, LENGTH(ACC_IDX(word m:byte))) (PSHUFB_OUT_LIST g (word m)) =
     MAP (\b:byte. word_subword g (8 * val b,8):byte)
         (MAP word (ACC_IDX(word m:byte)):byte list)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[PSHUFB_OUT_LIST_AS_MAP] THEN
  REWRITE_TAC[SUB_LIST_0_MAP] THEN
  AP_TERM_TAC THEN
  ASM_SIMP_TAC[TABLE_PREFIX_ACC]);;

let PSHUFB_ACCEPTED_PREFIX_NUM = prove
 (`!(g:int128) m. m < 256 ==>
     SUB_LIST(0, LENGTH(ACC_IDX(word m:byte))) (PSHUFB_OUT_LIST g (word m)) =
     MAP (\j:num. word_subword g (8 * j,8):byte) (ACC_IDX(word m:byte))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PSHUFB_ACCEPTED_PREFIX] THEN
  REWRITE_TAC[GSYM MAP_o; o_DEF] THEN
  MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word x:byte) = x` (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_8] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ACC_IDX_LT_8) THEN ARITH_TAC);;

(* word_subword of a byte at (0,8) is the identity — closes the byte-of-byte *)
(* wrapper left by the lane extraction.                                      *)

let WORD_SUBWORD_BYTE_ID = prove
 (`!x:byte. word_subword x (0,8):byte = x`,
  GEN_TAC THEN CONV_TAC WORD_BLAST);;

(* MASK_LOW_BIT: bit j (j<8) of the packed 8-bit mask word                   *)
(* `word(Sum_k 2^k * bitval(p k))` equals the predicate p j.                 *)

let MASK_LOW_BIT = prove
 (`!(p:num->bool) j. j < 8
     ==> (bit j (word(bitval(p 0) + 2 * bitval(p 1) + 4 * bitval(p 2) + 8 * bitval(p 3) +
                       16 * bitval(p 4) + 32 * bitval(p 5) + 64 * bitval(p 6) +
                       128 * bitval(p 7)):byte) <=> p j)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
    `j < 8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
  POP_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  MAP_EVERY BOOL_CASES_TAC [`(p:num->bool) 0`;`(p:num->bool) 1`;`(p:num->bool) 2`;`(p:num->bool) 3`;
                            `(p:num->bool) 4`;`(p:num->bool) 5`;`(p:num->bool) 6`;`(p:num->bool) 7`] THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV BIT_WORD_CONV) THEN REWRITE_TAC[]);;

(* SUB_LIST_16_BYTES_FROM_INT128: the 16 byte-subwords of the bytes128 load  *)
(* at buf + 16*i equal SUB_LIST(16*i,16) inlist, given the buffer contract.  *)

let SUB_LIST_16_BYTES_FROM_INT128 = prove
 (`!buf:int64 buflen inlist i s.
    16 * (i + 1) <= buflen /\
    LENGTH (inlist:byte list) = buflen /\
    read (memory :> bytes (buf, buflen)) s = num_of_wordlist inlist
    ==> SUB_LIST (16 * i, 16) inlist =
        [word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (0,8):byte;
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (8,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (16,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (24,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (32,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (40,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (48,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (56,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (64,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (72,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (80,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (88,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (96,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (104,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (112,8);
         word_subword (read (memory :> bytes128 (word_add buf (word (16 * i)))) s) (120,8)]`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
    `loaded_d = read (memory :> bytes128 (word_add buf (word (16 * i)))) s` THEN
  CONV_TAC SYM_CONV THEN
  REWRITE_TAC[LISTS_NUM_OF_WORDLIST_EQ] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LENGTH; LENGTH_SUB_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST; DIMINDEX_8] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM
    `\x. x DIV 2 EXP (8 * 16 * i) MOD 2 EXP (8 * 16)`) THEN
  CONV_TAC(ONCE_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  SUBGOAL_THEN `MIN (buflen - 16 * i) 16 = 16` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
    [`word_add buf (word (16 * i)):int64`; `read memory s`]
    (INST_TYPE[`:128`,`:N`] VAL_READ_WBYTES)) THEN
  REWRITE_TAC[DIMINDEX_128] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM BYTES128_WBYTES; GSYM READ_COMPONENT_COMPOSE] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[num_of_wordlist; DIMINDEX_8] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST);;

(* OP8_R8B_READ: the r8b sub-register read = word(val(read R8 s) MOD 256).   *)

let OP8_R8B_READ = prove
 (`!s:x86state. read (OPERAND8 (% r8b) s) s = word(val(read R8 s) MOD 256)`,
  GEN_TAC THEN REWRITE_TAC[OPERAND8; r8b; GPR8; register_size; regsize] THEN
  REWRITE_TAC[GSYM(NUM_EXP_CONV `2 EXP 8`)] THEN
  ONCE_REWRITE_TAC[MESON[EXP; DIV_1] `x MOD 2 EXP n = x DIV 2 EXP 0 MOD 2 EXP n`] THEN
  REWRITE_TAC[GSYM word_subword; READ_COMPONENT_COMPOSE; R8] THEN
  REWRITE_TAC[bottom_32; bottom_16; bottom_8; bottomhalf; READ_SUBWORD] THEN
  ONCE_REWRITE_TAC [WORD_EQ_BITS_ALT] THEN REWRITE_TAC[BIT_WORD_SUBWORD] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let MOVZBL_R10_CAPTURE_TAC : tactic =
  RULE_ASSUM_TAC(CONV_RULE(REWRITE_CONV[OP8_R8B_READ] THENC ONCE_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV));;

(* LACC8: the accepted-index list has length <= 8. *)

let LACC8 = prove(`!m:byte. LENGTH(ACC_IDX m) <= 8`,
  GEN_TAC THEN REWRITE_TAC[ACC_IDX] THEN
  MP_TAC(ISPECL [`\i. bit i (m:byte)`; `[0;1;2;3;4;5;6;7]:num list`] LENGTH_FILTER) THEN
  REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* SUBITER_STORE_EXTEND: fold a freshly-stored int32 block onto the running  *)
(* output prefix (both int32 lists; the new block sits at res + 4*|prefix|). *)

let SUBITER_STORE_EXTEND = prove
 (`!res s (prefix:int32 list) (block:int32 list).
     read (memory :> bytes(res, 4 * LENGTH prefix)) s = num_of_wordlist prefix /\
     read (memory :> bytes(word_add res (word (4 * LENGTH prefix)), 4 * LENGTH block)) s
       = num_of_wordlist block
     ==> read (memory :> bytes(res, 4 * LENGTH prefix + 4 * LENGTH block)) s
         = num_of_wordlist (APPEND prefix block)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s:x86state`;
                 `prefix:int32 list`; `block:int32 list`;
                 `4 * LENGTH(prefix:int32 list)`; `4 * LENGTH(block:int32 list)`]
        (INST_TYPE [`:32`,`:N`] BYTES_EQ_NUM_OF_WORDLIST_APPEND)) THEN
  REWRITE_TAC[DIMINDEX_32] THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[]);;

(* VPMOVSXBD_LANE_EXTRACT: each 32-bit lane of `usimd8 word_sx x` is the     *)
(* sign-extend of the corresponding source byte.                             *)

let VPMOVSXBD_LANE_EXTRACT = prove
 (`!(x:int64).
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (0,32):int32 = word_sx(word_subword x (0,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (32,32):int32 = word_sx(word_subword x (8,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (64,32):int32 = word_sx(word_subword x (16,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (96,32):int32 = word_sx(word_subword x (24,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (128,32):int32 = word_sx(word_subword x (32,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (160,32):int32 = word_sx(word_subword x (40,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (192,32):int32 = word_sx(word_subword x (48,8):byte)) /\
     (word_subword (usimd8 (\b:byte. word_sx b:int32) x:int256) (224,32):int32 = word_sx(word_subword x (56,8):byte))`,
  GEN_TAC THEN
  REWRITE_TAC[usimd8; usimd4; usimd2] THEN
  SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
           DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64; DIMINDEX_128;
           DIMINDEX_256; ARITH] THEN
  REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST);;

(* ========================================================================= *)
(* STORE-VALUE LANE BRIDGE.                                                  *)
(* These compose the full sub-iter SIMD store value: vpshufb (compacts       *)
(* accepted nibbles via the precomputed table) then vpmovsxbd (sign-         *)
(* extends each byte to int32). STORE_LANE_MATCH gives lane j of the         *)
(* YMM store value = word_sx of the j-th PSHUFB-gathered table byte,         *)
(* feeding STORE_BYTES256_NUM_OF_WORDLIST's lane-match hypothesis.           *)
(* pshuf1 is int256 (vpshufb operates on the full YMM); the store reads      *)
(* only the low 64 bits = low 128-lane = exactly the PSHUFB_OUT_BYTE         *)
(* form (j<8), so the outer word_zx 256<-128 is transparent (WSZ_OK).        *)
(* ========================================================================= *)

(* VPMOVSXBD_LANE_J: the j<8 quantified form of VPMOVSXBD_LANE_EXTRACT.      *)

let VPMOVSXBD_LANE_J = prove
 (`!(x:int64) j. j < 8
    ==> word_subword (usimd8 (\b:byte. word_sx b:int32) x) (32*j,32):int32
        = word_sx (word_subword x (8*j,8):byte)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `j < 8 <=> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[VPMOVSXBD_LANE_EXTRACT]);;

(* WSZ_OK: outer word_zx 256<-128 is transparent for low-lane bytes (j<8).   *)

let WSZ_OK = prove
 (`!(x:int128) j. j < 8
    ==> word_subword (word_zx x:int256) (8 * j,8):byte = word_subword x (8 * j,8)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC (ISPECL [`x:int128`; `8*j`; `8`]
    (INST_TYPE [`:256`,`:N`; `:128`,`:M`; `:8`,`:P`] WORD_SUBWORD_ZX)) THEN
  REWRITE_TAC[DIMINDEX_8;DIMINDEX_128;DIMINDEX_256] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

(* LENGTH_MLDSA_REJ_UNIFORM_TABLE: the shuffle-control table is 2048 bytes.  *)
(* The store-value lemmas below are table-length-dependent, so they live here. *)

let LENGTH_MLDSA_REJ_UNIFORM_TABLE = prove
 (`LENGTH (mldsa_rej_uniform_table:byte list) = 2048`,
  REWRITE_TAC[mldsa_rej_uniform_table; LENGTH] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* LENGTH_TABLE_ENTRY: a table entry is always 8 bytes (val m < 256 always). *)

let LENGTH_TABLE_ENTRY = prove
 (`!m:byte. LENGTH(TABLE_ENTRY m) = 8`,
  GEN_TAC THEN REWRITE_TAC[TABLE_ENTRY; LENGTH_SUB_LIST; LENGTH_MLDSA_REJ_UNIFORM_TABLE] THEN
  MP_TAC(ISPEC `m:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

(* VAL4EQ8: structural pshuf1 F uses (4)word index extraction; PSHUFB_OUT_BYTE *)
(* uses (8)word -- same low 4 bits, so the vals agree.                       *)

let VAL4EQ8 = prove
 (`!i:byte. val(word_subword i (0,4):4 word) = val(word_subword i (0,4):8 word)`,
  GEN_TAC THEN REWRITE_TAC[VAL_WORD_SUBWORD] THEN
  SIMP_TAC[DIMINDEX_4;DIMINDEX_8;DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* PSHUF1_LOWLANE_BYTE: byte j of the int256 pshuf result (low lane, j<8)    *)
(* reduces to PSHUFB_OUT_BYTE.                                               *)

let PSHUF1_LOWLANE_BYTE = prove
 (`!g m j. j < 8
    ==> word_subword
          (word_zx
            (usimd16 (\i. if bit 7 i then word 0:byte
                          else word_subword (g:int128) (8 * val (word_subword i (0,4):4 word),8))
              (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256)
          (8 * j,8):byte
        = word_subword g (8 * val (EL j (TABLE_ENTRY m)),8)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WSZ_OK] THEN
  REWRITE_TAC[VAL4EQ8] THEN ASM_SIMP_TAC[PSHUFB_OUT_BYTE]);;

(* LENGTH_PSHUFB_OUT_LIST: the gathered table-byte list is always 8 long.    *)

let LENGTH_PSHUFB_OUT_LIST = prove
 (`!g:int128. !m:byte. LENGTH(PSHUFB_OUT_LIST g m) = 8`,
  REWRITE_TAC[PSHUFB_OUT_LIST_AS_MAP; LENGTH_MAP; LENGTH_TABLE_ENTRY]);;

(* PSHUF1_BYTE_EQ_OUTLIST: byte j of the pshuf result = EL j (PSHUFB_OUT_LIST). *)

let PSHUF1_BYTE_EQ_OUTLIST = prove
 (`!g m j. j < 8
    ==> word_subword
          (word_zx
            (usimd16 (\i. if bit 7 i then word 0:byte
                          else word_subword (g:int128) (8 * val (word_subword i (0,4):4 word),8))
              (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256)
          (8 * j,8):byte
        = EL j (PSHUFB_OUT_LIST g m)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PSHUF1_LOWLANE_BYTE] THEN
  ASM_SIMP_TAC[PSHUFB_OUT_LIST_AS_MAP; EL_MAP; LENGTH_TABLE_ENTRY]);;

(* STORE_LANE_MATCH: the capstone -- lane j (j<8) of the full vpshufb->vpmovsxbd *)
(* store value equals word_sx of the j-th PSHUFB-gathered table byte.        *)

let STORE_LANE_MATCH = prove
 (`!(g:int128) m j. j < 8
    ==> word_subword
          (usimd8 (\b:byte. word_sx b:int32)
            (word_zx (word_zx
              (word_zx
                (usimd16 (\i. if bit 7 i then word 0:byte
                              else word_subword g (8 * val (word_subword i (0,4):4 word),8))
                  (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256)
              :int128):int64))
          (32*j,32):int32
        = word_sx (EL j (PSHUFB_OUT_LIST g m))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VPMOVSXBD_LANE_J] THEN ASM_SIMP_TAC[WZZ_LOW] THEN
  ASM_SIMP_TAC[PSHUF1_BYTE_EQ_OUTLIST]);;

(* SUBWORD_ZX_LOW_CONV: discharge the SUBWORD_ZX_LOW side-condition by       *)
(* dimindex reduction.                                                       *)

let SUBWORD_ZX_LOW_CONV : conv =
  fun tm ->
      let inst = PART_MATCH (lhs o snd o dest_imp) SUBWORD_ZX_LOW tm in
      let ant = REWRITE_RULE[DIMINDEX_4;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] inst in
      MP ant (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl ant))));;

(* MASK_SHIFT8_MOD256: (SUM32 DIV 256) MOD 256 = the shifted low-byte mask.  *)

let MASK_SHIFT8_MOD256 = prove
 (`!S. val(word_zx(word_ushr(word_zx(word_zx(word S:int32):int64):int32) 8):int64) MOD 256 =
       (S DIV 256) MOD 256`,
  GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[MM32_64; MOD_MOD_REFL; MM64_256; MM32_DIV256]);;

(* LOW24_LT: the low-24-bit weighted bitval sum (lanes 0..23) is < 2^24.     *)

let LOW24_LT = prove
 (`!p:num->bool. bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
     65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
     1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) < 16777216`,
  GEN_TAC THEN
  MAP_EVERY (fun k -> MP_TAC(ISPEC (mk_comb(`p:num->bool`,mk_small_numeral k)) BITVAL_BOUND))
    [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23] THEN ARITH_TAC);;

(* BYTE1_DIVMOD: (SUM32 DIV 256) MOD 256 = lanes-8..15 weighted sum.         *)

let BYTE1_DIVMOD = prove
 (`!p:num->bool.
    ((bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
      16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
      256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
      4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
      65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
      1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
      16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
      268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) DIV 256) MOD 256 =
    bitval(p 8) + 2*bitval(p 9) + 4*bitval(p 10) + 8*bitval(p 11) +
    16*bitval(p 12) + 32*bitval(p 13) + 64*bitval(p 14) + 128*bitval(p 15)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `(bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
     65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
     1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
     16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
     268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) =
    (bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7)) +
    256 * (bitval(p 8) + 2*bitval(p 9) + 4*bitval(p 10) + 8*bitval(p 11) +
     16*bitval(p 12) + 32*bitval(p 13) + 64*bitval(p 14) + 128*bitval(p 15) +
     256*(bitval(p 16) + 2*bitval(p 17) + 4*bitval(p 18) + 8*bitval(p 19) +
     16*bitval(p 20) + 32*bitval(p 21) + 64*bitval(p 22) + 128*bitval(p 23) +
     256*(bitval(p 24) + 2*bitval(p 25) + 4*bitval(p 26) + 8*bitval(p 27) +
     16*bitval(p 28) + 32*bitval(p 29) + 64*bitval(p 30) + 128*bitval(p 31))))`
   SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ; LOW8_LT; DIV_LT; ADD_CLAUSES] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ARITH_RULE
   `bitval (p 8) + 2 * bitval (p 9) + 4 * bitval (p 10) + 8 * bitval (p 11) +
    16 * bitval (p 12) + 32 * bitval (p 13) + 64 * bitval (p 14) + 128 * bitval (p 15) + Z =
    (bitval (p 8) + 2 * bitval (p 9) + 4 * bitval (p 10) + 8 * bitval (p 11) +
     16 * bitval (p 12) + 32 * bitval (p 13) + 64 * bitval (p 14) + 128 * bitval (p 15)) + Z`] THEN
  MATCH_MP_TAC ADD256_MOD THEN
  MAP_EVERY (fun k -> MP_TAC(ISPEC (mk_comb(`p:num->bool`,mk_small_numeral k)) BITVAL_BOUND))
    [8;9;10;11;12;13;14;15] THEN ARITH_TAC);;

(* SUB-ITER 2 popcount = unweighted lanes-8..15 bitval sum.  This is the sub-iter-2
   analog of the sub-iter-1 low-8 popcount reduction.  After the
   mask8b fold the R9 popcount at s30 matches this LHS with
   p k := bit 7 (word_subword f1bnd (8*k,8)).  Compose with the wide maskbit fact
   (bit 7 (f1bnd byte k) <=> val(nibble k) < 9, provable for all 32 lanes via MASK_WIDE)
   to get the lanes-8..15 sum = LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i+4,4) inlist)). *)

let BYTE2_DIVMOD = prove
 (`!p:num->bool.
    ((bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
      16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
      256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
      4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
      65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
      1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
      16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
      268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) DIV 65536) MOD 256 =
    bitval(p 16) + 2*bitval(p 17) + 4*bitval(p 18) + 8*bitval(p 19) +
    16*bitval(p 20) + 32*bitval(p 21) + 64*bitval(p 22) + 128*bitval(p 23)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `(bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
     65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
     1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
     16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
     268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) =
    (bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15)) +
    65536 * ((bitval(p 16) + 2*bitval(p 17) + 4*bitval(p 18) + 8*bitval(p 19) +
     16*bitval(p 20) + 32*bitval(p 21) + 64*bitval(p 22) + 128*bitval(p 23)) +
     256*(bitval(p 24) + 2*bitval(p 25) + 4*bitval(p 26) + 8*bitval(p 27) +
     16*bitval(p 28) + 32*bitval(p 29) + 64*bitval(p 30) + 128*bitval(p 31)))`
   SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ; LOW16_LT; DIV_LT; ADD_CLAUSES] THEN
  MATCH_MP_TAC ADD256_MOD THEN
  MAP_EVERY (fun k -> MP_TAC(ISPEC (mk_comb(`p:num->bool`,mk_small_numeral k)) BITVAL_BOUND))
    [16;17;18;19;20;21;22;23] THEN ARITH_TAC);;

let BYTE3_DIVMOD = prove
 (`!p:num->bool.
    ((bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
      16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
      256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
      4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
      65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
      1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
      16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
      268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) DIV 16777216) MOD 256 =
    bitval(p 24) + 2*bitval(p 25) + 4*bitval(p 26) + 8*bitval(p 27) +
    16*bitval(p 28) + 32*bitval(p 29) + 64*bitval(p 30) + 128*bitval(p 31)`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `(bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
     65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
     1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
     16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
     268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)) =
    (bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
     16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
     256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
     4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
     65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
     1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23)) +
    16777216 * (bitval(p 24) + 2*bitval(p 25) + 4*bitval(p 26) + 8*bitval(p 27) +
     16*bitval(p 28) + 32*bitval(p 29) + 64*bitval(p 30) + 128*bitval(p 31))`
   SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT_ADD; ARITH_EQ; LOW24_LT; DIV_LT; ADD_CLAUSES] THEN
  MATCH_MP_TAC MOD_LT THEN
  MAP_EVERY (fun k -> MP_TAC(ISPEC (mk_comb(`p:num->bool`,mk_small_numeral k)) BITVAL_BOUND))
    [24;25;26;27;28;29;30;31] THEN ARITH_TAC);;

(* --- subiter_byte23_lemmas ---                                             *)
(* ========================================================================= *)
(* Sub-iters 3,4 popcount->length keystones. Load AFTER                      *)
(* .subiter_k_lemmas.ml (needs BYTE2_DIVMOD/BYTE3_DIVMOD/divmod_swap/MM* etc.). *)
(* These give POPCNT_BYTE2/BYTE3 = the unweighted lanes-16..23 / 24..31 bitval sums, *)
(* over the double/triple word_ushr mask forms produced by the simulator at sub-iters *)
(* 3,4 (mask = R8 after 2 / 3 ushr-by-8). Analogous to POPCNT_BYTE1.         *)
(* ========================================================================= *)

(* peel one ushr-8 layer of a 64-bit mask through the i32 round-trip         *)

let MASK_SHIFT16_MOD256 = prove
 (`!S. val(word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word S:int32):int64):int32) 8):int64):int32) 8):int64) MOD 256 =
       (S DIV 65536) MOD 256`,
  GEN_TAC THEN
  REWRITE_TAC[MASK_USHR8_STEP; VAL_MASK8B; DIV_DIV] THEN
  REWRITE_TAC[ARITH_RULE `256 * 256 = 65536`] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`; ARITH_RULE `65536 = 2 EXP 16`; ARITH_RULE `256 = 2 EXP 8`] THEN
  REWRITE_TAC[divmod_swap16] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

let MASK_SHIFT24_MOD256 = prove
 (`!S. val(word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word S:int32):int64):int32) 8):int64):int32) 8):int64):int32) 8):int64) MOD 256 =
       (S DIV 16777216) MOD 256`,
  GEN_TAC THEN
  REWRITE_TAC[MASK_USHR8_STEP; VAL_MASK8C; DIV_DIV] THEN
  REWRITE_TAC[ARITH_RULE `65536 * 256 = 16777216`] THEN
  REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`; ARITH_RULE `16777216 = 2 EXP 24`; ARITH_RULE `256 = 2 EXP 8`] THEN
  REWRITE_TAC[divmod_swap24] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Sub-iter k outlen bound: outlen + sum of popcnts up to sub-iter k <= 248. *)
(* Used to prove JA-not-taken at each sub-iter's `cmp eax, 0xf8`.            *)

(* Unweighted bitval sum = filter-length: the clean-body counter chain leaves R9/RAX
   carrying word_popcount(...) = Σ_{k<8} bitval(bit 7 (f1bnd byte k)) (after the
   POPCNT_VPMOVMSKB low-byte reduction; see the movzbl/popcnt recipe).  With the maskbit
   fact bit 7 (f1bnd byte k) <=> val(nibble_k) < 9, this rewrites the sum to
   LENGTH(FILTER (\x. val x < 9) [nibbles]) = LENGTH(REJ_NIBBLES_ETA4 block) — the block
   accept count = the RAX advance for the mid-guard. *)
(* Collapse the stepped RAX add-nest word_zx(word_add(word_zx(word a))(word_zx(word_zx(word b))))
   to word(a+b) when a+b < 2^32.  After the popcnt+add the clean-body RAX has exactly this
   shape (a = outlen0, b = block accept count); with a+b <= 248 it folds to word(outlen0+count),
   from which the niblen bound + JA_NOT_TAKEN_LE discharges the mid-guard ja. *)

let POPCNT_BYTE1 = prove
 (`!p:num->bool.
     word_popcount
       (word_zx (word_zx (word_zx
          (word (val (word_zx (word_ushr (word_zx (word_zx
             (word (bitval(p 0) + 2*bitval(p 1) + 4*bitval(p 2) + 8*bitval(p 3) +
              16*bitval(p 4) + 32*bitval(p 5) + 64*bitval(p 6) + 128*bitval(p 7) +
              256*bitval(p 8) + 512*bitval(p 9) + 1024*bitval(p 10) + 2048*bitval(p 11) +
              4096*bitval(p 12) + 8192*bitval(p 13) + 16384*bitval(p 14) + 32768*bitval(p 15) +
              65536*bitval(p 16) + 131072*bitval(p 17) + 262144*bitval(p 18) + 524288*bitval(p 19) +
              1048576*bitval(p 20) + 2097152*bitval(p 21) + 4194304*bitval(p 22) + 8388608*bitval(p 23) +
              16777216*bitval(p 24) + 33554432*bitval(p 25) + 67108864*bitval(p 26) + 134217728*bitval(p 27) +
              268435456*bitval(p 28) + 536870912*bitval(p 29) + 1073741824*bitval(p 30) + 2147483648*bitval(p 31)):int32):int64):int32) 8):int64)
            MOD 256):int32):int32):int32):int32) =
     bitval(p 8) + bitval(p 9) + bitval(p 10) + bitval(p 11) +
     bitval(p 12) + bitval(p 13) + bitval(p 14) + bitval(p 15)`,
  GEN_TAC THEN
  REWRITE_TAC[MASK_SHIFT8_MOD256; BYTE1_DIVMOD] THEN
  MAP_EVERY (fun k -> BOOL_CASES_TAC (mk_comb(`p:num->bool`, mk_small_numeral k)))
    [8;9;10;11;12;13;14;15] THEN
  REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC WORD_REDUCE_CONV);;

(* POPCNT_BYTE2: popcount of the byte-2 mask slice = the lanes-16..23 sum.   *)

let POPCNT_BYTE2 =
  let arg = subst [SUMTERM_BYTE23, `SUMV:num`]
    (subst [`word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word SUMV:int32):int64):int32) 8):int64):int32) 8):int64`, `MASKC:int64`]
       `word_zx(word_zx(word_zx(word(val (MASKC:int64) MOD 256):byte):int32):int64):int32`) in
  prove(mk_forall(`p:num->bool`, mk_eq(mk_comb(`word_popcount:int32->num`, arg),
     `bitval(p 16) + bitval(p 17) + bitval(p 18) + bitval(p 19) +
      bitval(p 20) + bitval(p 21) + bitval(p 22) + bitval(p 23)`)),
    GEN_TAC THEN REWRITE_TAC[MASK_SHIFT16_MOD256; BYTE2_DIVMOD] THEN
    MAP_EVERY (fun k -> BOOL_CASES_TAC (mk_comb(`p:num->bool`, mk_small_numeral k)))
      [16;17;18;19;20;21;22;23] THEN
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV);;

let POPCNT_BYTE3 =
  let arg = subst [SUMTERM_BYTE23, `SUMV:num`]
    (subst [`word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word_ushr(word_zx(word_zx(word SUMV:int32):int64):int32) 8):int64):int32) 8):int64):int32) 8):int64`, `MASKC:int64`]
       `word_zx(word_zx(word_zx(word(val (MASKC:int64) MOD 256):byte):int32):int64):int32`) in
  prove(mk_forall(`p:num->bool`, mk_eq(mk_comb(`word_popcount:int32->num`, arg),
     `bitval(p 24) + bitval(p 25) + bitval(p 26) + bitval(p 27) +
      bitval(p 28) + bitval(p 29) + bitval(p 30) + bitval(p 31)`)),
    GEN_TAC THEN REWRITE_TAC[MASK_SHIFT24_MOD256; BYTE3_DIVMOD] THEN
    MAP_EVERY (fun k -> BOOL_CASES_TAC (mk_comb(`p:num->bool`, mk_small_numeral k)))
      [24;25;26;27;28;29;30;31] THEN
    REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV);;

(* cumulative outlen bound through sub-iter 4 (4th block), for the final RAX/store-safety. *)

let zxbyte_eq = prove
 (`!v. v < 256 ==>
     word_zx(word_zx(word_zx(word v:byte):int32):int64):int32 =
     word_zx(word_zx(word_zx(word v:int32):int32):int32):int32`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `v < 256 ==> v < 2 EXP 8 /\ v < 2 EXP 32 /\ v < 2 EXP 64`] THEN
  CONV_TAC(DEPTH_CONV NUM_REDUCE_CONV) THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `v < 256 ==> v < 2 EXP 8 /\ v < 2 EXP 32`]);;

(* MASKBIT_TGT_TAC: derive maskbit_tgt (the mask8-byte <-> chunk0-nibble<9   *)
(* correspondence in EL-list form) in-context at ~s13, via the MASK_LOW_BIT  *)
(* low-byte split + the pre-derived byte-0 maskbit forall.                   *)

let MASKBIT_TGT_TAC : tactic =
  W(fun (asl,w) ->
    let m8 = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8:int64` &&
        can(find_term(fun u->match u with Const("bitval",_)->true|_->false))(concl th)) (map snd asl) in
    let sum32 = rand(rand(lhand(concl m8))) in
    let summands = striplist (dest_binop `(+):num->num->num`) sum32 in
    let getbitval s = if is_binop `( * ):num->num->num` s then rand s else s in
    let bvs = map getbitval summands in
    let sum8 = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
      (List.map2 (fun wt bv -> if wt=1 then bv else mk_binop `( * ):num->num->num` (mk_small_numeral wt) bv) [1;2;4;8;16;32;64;128] (map (fun i->List.nth bvs i) (0--7))) in
    let high = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
      (map (fun i -> let wt = 1 lsl (i-8) in if wt=1 then List.nth bvs i else mk_binop `( * ):num->num->num` (mk_small_numeral wt) (List.nth bvs i)) (8--31)) in
    let splitth = prove(mk_eq(sum32, mk_binop `(+):num->num->num` sum8 (mk_binop `( * ):num->num->num` `256` high)), ARITH_TAC) in
    let byteeq32 = TRANS (AP_TERM `word:num->byte` splitth) (SPECL [sum8; high] WORD_ADD_256_BYTE) in
    let beq = mk_eq(`word (val (mask8:int64) MOD 256):byte`, mk_comb(`word:num->byte`, sum8)) in
    let preds8 = map (fun i -> rand (List.nth bvs i)) (0--7) in
    let plist = mk_abs(`k:num`, mk_comb(mk_comb(`EL:num->(bool)list->bool`,`k:num`),
       (end_itlist (fun a b -> mk_binop `CONS:bool->(bool)list->(bool)list` a b) (preds8 @ [`[]:(bool)list`])))) in
    let mb0 = find (fun th -> let c=concl th in is_forall c &&
        can(find_term(fun u->u=`f1bnd:int256`))c &&
        can(find_term(fun u->match u with Comb(Const("bit",_),_)->true|_->false))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (24,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (32,8):byte`))c)) (map snd asl) in
    let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mb0 in
       CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
    SUBGOAL_THEN beq ASSUME_TAC THENL
     [SUBGOAL_THEN (mk_eq(`val (mask8:int64)`, mk_binop `MOD` sum32 `2 EXP 32`)) SUBST1_TAC THENL
       [SUBST1_TAC(SYM m8) THEN REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_64; DIMINDEX_32] THEN
        MATCH_MP_TAC MOD_LT THEN MP_TAC(SPECL [sum32; `2 EXP 32`] MOD_LT_EQ) THEN REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN (mk_eq(mk_binop `MOD` (mk_binop `MOD` sum32 `2 EXP 32`) `256`, mk_binop `MOD` sum32 `256`)) SUBST1_TAC THENL
       [REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV); ALL_TAC] THEN
      REWRITE_TAC[WORD_BYTE_MOD] THEN ACCEPT_TAC byteeq32;
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun beqth -> if is_eq(concl beqth) && lhand(concl beqth)=`word (val (mask8:int64) MOD 256):byte` then REWRITE_TAC[beqth] else NO_TAC) THEN
    MP_TAC(SPECL [plist; `j:num`] MASK_LOW_BIT) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
      (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC mbs THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC);;

(* --- tab1_teq_tac ---                                                      *)
(* Table-load bridge: derive teq `tab1 = word_zx(word_zx(word(nwl(TABLE_ENTRY(word(val mask8 MOD 256))))))`
   at s14 from the raw vmovq read, via TABLE_VMOVQ_READ + R_EQ (zx-collapse) + RLT (r<256). This is
   the genuine table-correspondence that the earlier fold left unproven. After REABBREV tab1, ASSUMEd fact's lhand
   read YMM6 s14 -> tab1, giving the teq the pf_target proof needs. *)

let F0NIB_CHUNK0 =
  `word_and (word_or (usimd16 (\b:byte. word_zx b:int16) chunk0:int256)
                     (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) chunk0:int256):int256))
            (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)`;;

(* STORE_LANE_EQ_REJBLOCK: for j<k<=8, lane j of the usimd8 word_sx store over *)
(* the vpshufb-gathered TABLE_ENTRY equals EL j (MAP word_sx (SUB_LIST(0,k)  *)
(* (PSHUFB_OUT_LIST g m))) — the lane-match hypothesis of the store bridge.  *)

let STORE_LANE_EQ_REJBLOCK = prove
 (`!(g:int128) m k j. j < k /\ k <= 8
    ==> word_subword
          (usimd8 (\b:byte. word_sx b:int32)
            (word_zx (word_zx
              (word_zx
                (usimd16 (\i. if bit 7 i then word 0:byte
                              else word_subword g (8 * val (word_subword i (0,4):4 word),8))
                  (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256)
              :int128):int64))
          (32*j,32):int32
        = EL j (MAP (\b:byte. word_sx b:int32) (SUB_LIST(0,k) (PSHUFB_OUT_LIST g m)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `j < 8` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[STORE_LANE_MATCH] THEN
  SUBGOAL_THEN `LENGTH(SUB_LIST(0,k)(PSHUFB_OUT_LIST (g:int128) m)) = k` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST; LENGTH_PSHUFB_OUT_LIST] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[EL_MAP] THEN
    ASM_SIMP_TAC[EL_SUB_LIST; LENGTH_PSHUFB_OUT_LIST; ADD_CLAUSES] THEN
    ASM_ARITH_TAC]);;

(* SUBITER_STORE_POSTCOND: the full single-store value bridge. Given the     *)
(* bytes256 read of the destination equals the vpshufb->vpmovsxbd store      *)
(* value (PSHUFB pipeline form) and k<=8, the 4k stored bytes = the          *)
(* num_of_wordlist of the k-element accepted block. Lane-match is discharged *)
(* internally via STORE_LANE_EQ_REJBLOCK.                                    *)

let SUBITER_STORE_POSTCOND = prove
 (`!A s (g:int128) m k.
     k <= 8 /\
     read (memory :> bytes256 A) s =
       (usimd8 (\b:byte. word_sx b:int32)
            (word_zx (word_zx (word_zx (usimd16 (\i. if bit 7 i then word 0:byte
                else word_subword g (8 * val (word_subword i (0,4):4 word),8))
              (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256):int128):int64))
     ==> read (memory :> bytes(A, 4 * k)) s =
         num_of_wordlist (MAP (\b:byte. word_sx b:int32) (SUB_LIST(0,k) (PSHUFB_OUT_LIST g m)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`A:int64`;
    `usimd8 (\b:byte. word_sx b:int32)
            (word_zx (word_zx (word_zx (usimd16 (\i. if bit 7 i then word 0:byte
                else word_subword (g:int128) (8 * val (word_subword i (0,4):4 word),8))
              (word_zx (word_zx (word (num_of_wordlist (TABLE_ENTRY m)):int64):int128):int128)):int256):int128):int64)`;
    `MAP (\b:byte. word_sx b:int32) (SUB_LIST(0,k) (PSHUFB_OUT_LIST (g:int128) m))`;
    `k:num`; `s:x86state`] STORE_BYTES256_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LENGTH_MAP; LENGTH_SUB_LIST; LENGTH_PSHUFB_OUT_LIST] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC STORE_LANE_EQ_REJBLOCK THEN ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

(* pf_target: the sub-iter-1 pshufb lane-gather form (= read YMM6 s15),      *)
(* matching the usimd16/TABLE_ENTRY control of the store bridge.             *)

let pf_target =
  `pshuf1:int256 =
   word_zx
   (usimd16
    (\i:byte. if bit 7 i
         then word 0:byte
         else word_subword (word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128)
              (8 * val (word_subword i (0,4):4 word),8):byte)
   (word_zx
   (word_zx (word (num_of_wordlist (TABLE_ENTRY (word (val (mask8:int64) MOD 256):byte))):int64):int128):int128):int128)`;;

let MASKBIT_TGT_2_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let m8b = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8b:int64` &&
        can(find_term(fun u->match u with Const("bitval",_)->true|_->false))(concl th)) asms in
    let sum32 = find_term (fun u -> match u with
       Comb(Comb(Const("+",_),_),_) -> can(find_term(fun v->match v with Const("bitval",_)->true|_->false)) u | _ -> false) (concl m8b) in
    let summands = striplist (dest_binop `(+):num->num->num`) sum32 in
    let getbitval s = if is_binop `( * ):num->num->num` s then rand s else s in
    let bvs = map getbitval summands in
    let mksum idxs wts = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
       (List.map2 (fun wt i -> let bv = List.nth bvs i in if wt=1 then bv else mk_binop `( * ):num->num->num` (mk_small_numeral wt) bv) wts idxs) in
    let sum_low8 = mksum [0;1;2;3;4;5;6;7] [1;2;4;8;16;32;64;128] in
    let sum8' = mksum [8;9;10;11;12;13;14;15] [1;2;4;8;16;32;64;128] in
    let sum_high16 = mksum (16--31) (map (fun i->1 lsl (i-16)) (16--31)) in
    let regroup = prove(mk_eq(sum32, mk_binop `(+):num->num->num` sum_low8
       (mk_binop `(+):num->num->num` (mk_binop `( * ):num->num->num` `256` sum8')
                                      (mk_binop `( * ):num->num->num` `65536` sum_high16))), ARITH_TAC) in
    let low8lt = prove(mk_binop `(<):num->num->bool` sum_low8 `256`,
       MP_TAC(end_itlist CONJ (map (fun b -> SPEC b BITVAL_BOUND) (map (fun i->rand(List.nth bvs i)) (0--7)))) THEN ARITH_TAC) in
    let s8lt = prove(mk_binop `(<):num->num->bool` sum8' `256`,
       MP_TAC(end_itlist CONJ (map (fun b -> SPEC b BITVAL_BOUND) (map (fun i->rand(List.nth bvs i)) (8--15)))) THEN ARITH_TAC) in
    let vshift = SPEC sum32 MASK_SHIFT8_MOD256 in
    let dms = MP (SPECL [sum_low8; sum8'; sum_high16] DIVMOD256_SPLIT) (CONJ low8lt s8lt) in
    let valeq = REWRITE_RULE[m8b] (TRANS vshift (TRANS (AP_THM (AP_TERM `(MOD)` (AP_THM (AP_TERM `(DIV)` regroup) `256`)) `256`) dms)) in
    let beq = mk_eq(`word (val (mask8b:int64) MOD 256):byte`, mk_comb(`word:num->byte`, sum8')) in
    let preds8 = map (fun i -> rand (List.nth bvs i)) (8--15) in
    let plist = mk_abs(`k:num`, mk_comb(mk_comb(`EL:num->(bool)list->bool`,`k:num`),
       (end_itlist (fun a b -> mk_binop `CONS:bool->(bool)list->(bool)list` a b) (preds8 @ [`[]:(bool)list`])))) in
    let mb2 = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f1bnd:int256`))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (32,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (64,8):byte`))c) &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (24,8):byte`))c)) asms in
    let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mb2 in
       CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
    SUBGOAL_THEN beq ASSUME_TAC THENL
     [REWRITE_TAC[AP_TERM `word:num->byte` valeq];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun beqth -> if is_eq(concl beqth) && lhand(concl beqth)=`word (val (mask8b:int64) MOD 256):byte` then REWRITE_TAC[beqth] else NO_TAC) THEN
    MP_TAC(SPECL [plist; `j:num`] MASK_LOW_BIT) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
      (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC mbs THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC);;

(* --- tab2_teq_tac ---                                                      *)
(* Sub-iter-2 table-load bridge: R_EQ_B/RLT_B (mask8b zx-collapse + bound) + TAB2_TEQ_TAC.
   At s26 (after the vmovq table load), read YMM6 s26 = word_zx(word_zx(read(bytes64(table+8*r)) s25))
   with r = val(word_zx(word_zx(word(val mask8b MOD 256)))). Same shape as si1's tab1 but mask8b/s25/s26.
   After REABBREV tab2, gives teq2: word_zx(word_zx(word(nwl(TABLE_ENTRY(word(val mask8b MOD 256)))))) = tab2. *)

let pf_target_2 =
  let g1 = `word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128` in
  let g2 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128) 64):int128):int128` in
  subst [g2,g1; `mask8b:int64`,`mask8:int64`; `pshuf2:int256`,`pshuf1:int256`] pf_target;;

(* MASKBIT_TGT_3_TAC: derive the sub-iter-3 maskbit_tgt correspondence in-context. *)

let MASKBIT_TGT_3_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let m8c_def = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8c:int64` &&
        can(find_term(fun u->u=`mask8b:int64`))(concl th)) asms in
    let m8b_def = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8b:int64` &&
        can(find_term(fun u->match u with Const("bitval",_)->true|_->false))(concl th)) asms in
    let sum32 = find_term (fun u -> match u with
       Comb(Comb(Const("+",_),_),_) -> can(find_term(fun v->match v with Const("bitval",_)->true|_->false)) u | _ -> false) (concl m8b_def) in
    let summands = striplist (dest_binop `(+):num->num->num`) sum32 in
    let getbitval s = if is_binop `( * ):num->num->num` s then rand s else s in
    let bvs = map getbitval summands in
    let mksum idxs wts = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
       (List.map2 (fun wt i -> let bv = List.nth bvs i in if wt=1 then bv else mk_binop `( * ):num->num->num` (mk_small_numeral wt) bv) wts idxs) in
    let low16 = mksum (0--15) (map (fun i->1 lsl i) (0--15)) in
    let sum8'' = mksum [16;17;18;19;20;21;22;23] [1;2;4;8;16;32;64;128] in
    let high8 = mksum (24--31) (map (fun i->1 lsl (i-24)) (24--31)) in
    let regroup = prove(mk_eq(sum32, mk_binop `(+):num->num->num` low16
       (mk_binop `(+):num->num->num` (mk_binop `( * ):num->num->num` `65536` sum8'')
                                      (mk_binop `( * ):num->num->num` `16777216` high8))), ARITH_TAC) in
    let low16lt = prove(mk_binop `(<):num->num->bool` low16 `65536`,
       MP_TAC(end_itlist CONJ (map (fun b -> SPEC b BITVAL_BOUND) (map (fun i->rand(List.nth bvs i)) (0--15)))) THEN ARITH_TAC) in
    let s8lt = prove(mk_binop `(<):num->num->bool` sum8'' `256`,
       MP_TAC(end_itlist CONJ (map (fun b -> SPEC b BITVAL_BOUND) (map (fun i->rand(List.nth bvs i)) (16--23)))) THEN ARITH_TAC) in
    let m8c_over_sum = REWRITE_RULE[SYM m8b_def] m8c_def in
    let vshift = SPEC sum32 MASK_SHIFT16_MOD256 in
    let dms = MP (SPECL [low16; sum8''; high8] DIVMOD65536_SPLIT) (CONJ low16lt s8lt) in
    let valeq = TRANS (REWRITE_RULE[m8c_over_sum] vshift) (TRANS (AP_THM (AP_TERM `(MOD)` (AP_THM (AP_TERM `(DIV)` regroup) `65536`)) `256`) dms) in
    let beq = mk_eq(`word (val (mask8c:int64) MOD 256):byte`, mk_comb(`word:num->byte`, sum8'')) in
    let preds8 = map (fun i -> rand (List.nth bvs i)) (16--23) in
    let plist = mk_abs(`k:num`, mk_comb(mk_comb(`EL:num->(bool)list->bool`,`k:num`),
       (end_itlist (fun a b -> mk_binop `CONS:bool->(bool)list->(bool)list` a b) (preds8 @ [`[]:(bool)list`])))) in
    let mb3 = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f1bnd:int256`))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (64,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (96,8):byte`))c) &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (56,8):byte`))c)) asms in
    let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mb3 in
       CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
    SUBGOAL_THEN beq ASSUME_TAC THENL
     [REWRITE_TAC[AP_TERM `word:num->byte` valeq];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun beqth -> if is_eq(concl beqth) && lhand(concl beqth)=`word (val (mask8c:int64) MOD 256):byte` then REWRITE_TAC[beqth] else NO_TAC) THEN
    MP_TAC(SPECL [plist; `j:num`] MASK_LOW_BIT) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
      (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC mbs THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC);;

let pf_target_3 =
  let g1 = `word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128` in
  let g3 = `word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128` in
  subst [g3,g1; `mask8c:int64`,`mask8:int64`; `pshuf3:int256`,`pshuf1:int256`] pf_target;;

let MASKBIT_TGT_4_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let m8d_def = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8d:int64` && can(find_term(fun u->u=`mask8c:int64`))(concl th)) asms in
    let m8c_def = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8c:int64` && can(find_term(fun u->u=`mask8b:int64`))(concl th)) asms in
    let m8b_def = find (fun th -> is_eq(concl th) && rand(concl th)=`mask8b:int64` && can(find_term(fun u->match u with Const("bitval",_)->true|_->false))(concl th)) asms in
    let sum32 = find_term (fun u -> match u with
       Comb(Comb(Const("+",_),_),_) -> can(find_term(fun v->match v with Const("bitval",_)->true|_->false)) u | _ -> false) (concl m8b_def) in
    let summands = striplist (dest_binop `(+):num->num->num`) sum32 in
    let getbitval s = if is_binop `( * ):num->num->num` s then rand s else s in
    let bvs = map getbitval summands in
    let mksum idxs wts = end_itlist (fun a b -> mk_binop `(+):num->num->num` a b)
       (List.map2 (fun wt i -> let bv = List.nth bvs i in if wt=1 then bv else mk_binop `( * ):num->num->num` (mk_small_numeral wt) bv) wts idxs) in
    let low24 = mksum (0--23) (map (fun i->1 lsl i) (0--23)) in
    let sum8''' = mksum [24;25;26;27;28;29;30;31] [1;2;4;8;16;32;64;128] in
    let regroup = prove(mk_eq(sum32, mk_binop `(+):num->num->num` low24
       (mk_binop `( * ):num->num->num` `16777216` sum8''')), ARITH_TAC) in
    let low24lt = prove(mk_binop `(<):num->num->bool` low24 `16777216`,
       MP_TAC(end_itlist CONJ (map (fun b -> SPEC b BITVAL_BOUND) (map (fun i->rand(List.nth bvs i)) (0--23)))) THEN ARITH_TAC) in
    let s8lt = prove(mk_binop `(<):num->num->bool` sum8''' `256`,
       MP_TAC(end_itlist CONJ (map (fun b -> SPEC b BITVAL_BOUND) (map (fun i->rand(List.nth bvs i)) (24--31)))) THEN ARITH_TAC) in
    (* mask8d over SUM32: subst mask8c def (over mask8b) then mask8b def (over SUM32) *)
    let m8d_over_sum = REWRITE_RULE[SYM m8b_def] (REWRITE_RULE[SYM m8c_def] m8d_def) in
    let vshift = SPEC sum32 MASK_SHIFT24_MOD256 in
    let dms = MP (SPECL [low24; sum8'''] DIVMOD16777216_SPLIT) low24lt in
    let s8mod = prove(mk_eq(mk_binop `MOD` sum8''' `256`, sum8'''), MATCH_MP_TAC MOD_LT THEN ACCEPT_TAC s8lt) in
    let valeq = TRANS (REWRITE_RULE[m8d_over_sum] vshift)
                  (TRANS (AP_THM (AP_TERM `(MOD)` (AP_THM (AP_TERM `(DIV)` regroup) `16777216`)) `256`) (TRANS dms s8mod)) in
    let beq = mk_eq(`word (val (mask8d:int64) MOD 256):byte`, mk_comb(`word:num->byte`, sum8''')) in
    let preds8 = map (fun i -> rand (List.nth bvs i)) (24--31) in
    let plist = mk_abs(`k:num`, mk_comb(mk_comb(`EL:num->(bool)list->bool`,`k:num`),
       (end_itlist (fun a b -> mk_binop `CONS:bool->(bool)list->(bool)list` a b) (preds8 @ [`[]:(bool)list`])))) in
    let mb4 = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f1bnd:int256`))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (96,8):byte`))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (120,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (64,8):byte`))c)) asms in
    let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mb4 in
       CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
    SUBGOAL_THEN beq ASSUME_TAC THENL
     [REWRITE_TAC[AP_TERM `word:num->byte` valeq];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(fun beqth -> if is_eq(concl beqth) && lhand(concl beqth)=`word (val (mask8d:int64) MOD 256):byte` then REWRITE_TAC[beqth] else NO_TAC) THEN
    MP_TAC(SPECL [plist; `j:num`] MASK_LOW_BIT) THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
      (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC mbs THEN
    CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC);;

let pf_target_4 =
  let g1 = `word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128` in
  let g4 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128) 64):int128):int128` in
  subst [g4,g1; `mask8d:int64`,`mask8:int64`; `pshuf4:int256`,`pshuf1:int256`] pf_target;;

let SL16_4WAY = prove
 (`SUB_LIST(16*i,16) (inlist:byte list) =
   APPEND (SUB_LIST(16*i,4) inlist)
   (APPEND (SUB_LIST(16*i+4,4) inlist)
   (APPEND (SUB_LIST(16*i+8,4) inlist) (SUB_LIST(16*i+12,4) inlist)))`,
  MP_TAC(ISPECL[`inlist:byte list`;`4`;`12`;`16*i`] SUB_LIST_SPLIT) THEN
  MP_TAC(ISPECL[`inlist:byte list`;`4`;`8`;`16*i+4`] SUB_LIST_SPLIT) THEN
  MP_TAC(ISPECL[`inlist:byte list`;`4`;`4`;`16*i+8`] SUB_LIST_SPLIT) THEN
  REWRITE_TAC[ARITH_RULE `(16*i+4)+4=16*i+8`; ARITH_RULE `(16*i+8)+4=16*i+12`;
    ARITH_RULE `4+8=12`; ARITH_RULE `4+4=8`; ARITH_RULE `4+12=16`] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC);;

let MM_4G_4G = prove(`!a. a MOD 4294967296 MOD 4294967296 = a MOD 4294967296`, REWRITE_TAC[MOD_MOD_REFL]);;

let MM_4G_18 = prove(`!a. a MOD 4294967296 MOD 18446744073709551616 = a MOD 4294967296`,
  GEN_TAC THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(SPECL[`a:num`;`4294967296`] MOD_LT_EQ) THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

(* STORE4_FROM_SPEC: derive `read(bytes(addr,4)) sN = val(word_sx ...)` from a *)
(* spec-form bytes32 store hypothesis.                                       *)

let STORE4_FROM_SPEC sN addrt =
  REWRITE_TAC[bytes32; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  DISCH_THEN(MP_TAC o AP_TERM `val:int32->num`) THEN REWRITE_TAC[VAL_WORD] THEN
  SUBGOAL_THEN (subst[sN,`s:x86state`;addrt,`a:int64`]
     `read (bytes (a:int64,4)) (read memory (s:x86state)) < 2 EXP dimindex(:32)`) ASSUME_TAC THENL
   [REWRITE_TAC[DIMINDEX_32] THEN
    MP_TAC(ISPECL[addrt;`4`;mk_comb(`read memory:x86state->int64->byte`,sN)] READ_BYTES_BOUND) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;;

let JA_TAKEN_GT = prove
 (`!a k:num. k < a /\ a < 2 EXP 32
     ==> ~(~(&(val(word_zx(word a:int64):int32)):int - &k =
             &(val(word_sub(word_zx(word a:int64):int32) (word k):int32))) \/
           val(word_sub(word_zx(word a:int64):int32) (word k):int32) = 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_zx(word a:int64):int32) = a` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_ZX_64_32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub (word_zx(word a:int64):int32) (word k:int32)) = a - k` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val(word k:int32) = k` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL [REFL_TAC; REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(a - k = 0) <=> F` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MP_TAC(SPECL[`k:num`;`a:num`] INT_OF_NUM_SUB) THEN ANTS_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC) THEN REWRITE_TAC[]]);;

(* --- correct_scaffold ---                                                  *)
(* RCX4_COLLAPSE: collapse the stepped RCX +4 nest word_zx(word_add(word_zx  *)
(* (word a))(word 4)) to word(a+4) when a+4 < 2^32.                          *)

let RCX4_COLLAPSE = prove
 (`!a:num. a + 4 < 2 EXP 32 ==> word_zx(word_add(word_zx(word a:int64):int32)(word 4:int32)):int64 = word(a + 4)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_64; DIMINDEX_32; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32] THEN
  SUBGOAL_THEN `a MOD 2 EXP 64 = a` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  SUBGOAL_THEN `(a + 4) MOD 2 EXP 32 = a + 4` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; REFL_TAC]);;

(*** print_literal_from_elf "x86_64/mldsa/rej_uniform_eta4_avx2_asm.o";;
 ***)

let REJ_NIBBLES_ETA4_EMPTY = prove
 (`REJ_NIBBLES_ETA4 [] = []`,
  REWRITE_TAC[REJ_NIBBLES_ETA4; NIBBLES_OF_BYTES; FILTER]);;

let REJ_NIBBLES_ETA4_APPEND = prove
 (`!l1 l2. REJ_NIBBLES_ETA4(APPEND l1 l2) =
           APPEND (REJ_NIBBLES_ETA4 l1) (REJ_NIBBLES_ETA4 l2)`,
  REWRITE_TAC[REJ_NIBBLES_ETA4; NIBBLES_OF_BYTES_APPEND; FILTER_APPEND]);;

(* Loop step: peel off 16 bytes per iteration. Used in loop body.            *)
let REJ_NIBBLES_ETA4_STEP_16 = prove
 (`!inlist:byte list. !i:num.
   16 * (i + 1) <= LENGTH inlist
   ==> REJ_NIBBLES_ETA4(SUB_LIST(0, 16 * (i + 1)) inlist) =
       APPEND (REJ_NIBBLES_ETA4(SUB_LIST(0, 16 * i) inlist))
              (REJ_NIBBLES_ETA4(SUB_LIST(16 * i, 16) inlist))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REJ_NIBBLES_ETA4_APPEND] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `16 * (i + 1) = 0 + 16 * i + 16` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUB_LIST_SPLIT; SUB_LIST_CLAUSES; APPEND; ADD_CLAUSES]);;

(* Length bound on filtered nibbles - used for ABBREV bounds                 *)
let LENGTH_REJ_NIBBLES_ETA4 = prove
 (`!l:byte list. LENGTH(REJ_NIBBLES_ETA4 l) <= 2 * LENGTH l`,
  GEN_TAC THEN REWRITE_TAC[REJ_NIBBLES_ETA4] THEN
  TRANS_TAC LE_TRANS `LENGTH(NIBBLES_OF_BYTES l:int16 list)` THEN
  CONJ_TAC THENL [REWRITE_TAC[LENGTH_FILTER]; ALL_TAC] THEN
  SPEC_TAC(`l:byte list`,`l:byte list`) THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[NIBBLES_OF_BYTES; LENGTH; NIBBLE_PAIR;
                  APPEND; LENGTH_APPEND; LE_0] THEN
  UNDISCH_TAC `LENGTH(NIBBLES_OF_BYTES t:int16 list) <=
               2 * LENGTH(t:byte list)` THEN ARITH_TAC);;

(* General prefix monotonicity of the accepted-nibble count: a shorter       *)
(* input prefix accepts no more nibbles than a longer one. (niblen is        *)
(* FILTER of NIBBLES_OF_BYTES, both monotone under list prefix.) Used to     *)
(* derive the intra-block sub-iter bounds from the binding end-of-block      *)
(* bound -- the clean-block control-flow argument: the SIMD loop has three   *)
(* mid-iteration `ja` early-exits (after sub-iters 1,2,3), and a block runs  *)
(* to completion (loops back) exactly when niblen at its END (offset         *)
(* 16*j+12 covering all but the last sub-iter's stores; the 4th adds no      *)
(* further guard) stays <= 248; this lemma propagates that bound to the      *)
(* earlier sub-iter offsets so all three mid-iter ja's fall through.         *)
let NIBLEN_PREFIX_MONO = prove
 (`!l:byte list a b. a <= b
     ==> LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,a) l):int16 list) <=
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,b) l):int16 list)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `SUB_LIST(0,b) (l:byte list) =
                APPEND (SUB_LIST(0,a) l) (SUB_LIST(a,b-a) l)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`l:byte list`; `a:num`; `b - a`; `0`] SUB_LIST_SPLIT) THEN
    ASM_SIMP_TAC[ARITH_RULE `a <= b ==> a + (b - a) = b`; ADD_CLAUSES];
    REWRITE_TAC[REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND] THEN ARITH_TAC]);;

(* Bridge: relate val (word_zx of byte) < 9 to val byte < 9, useful for      *)
(* the popcnt-to-FILTER bridge in each sub-iter.                             *)
let VAL_WORD_ZX_BYTE_LT_9 = prove
 (`!b:byte. (val (word_zx b:int16) < 9) <=> (val b < 9)`,
  GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VAL_WORD_ZX THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_16] THEN ARITH_TAC);;

(* SUB_ITER_TAC: processes one of the 4 sub-iterations.                      *)
(* Parameters:                                                               *)
(*   start   - state index where this sub-iter begins (e.g. 35 for k=2)      *)
(*   stop    - state index where this sub-iter ends (e.g. 47 for k=2)        *)
(*   sub_pc  - PC offset where this sub-iter's first instr is located        *)
(*   end_pc  - PC offset of the cmp-eax-0xf8 (after popcntl/add/shr/add)*)
(*   k       - sub-iter index (0..3): 0 uses extracted xmm5 directly;        *)
(*             1 uses vpsrldq xmm5,8; 2 uses vextracti128 $1; 3 uses         *)
(*             vpsrldq xmm5,8 again                                          *)
(*   chunk_off - byte offset within the 16-byte block (0, 4, 8, or 12)       *)
(*                                                                           *)
(* This tactic is conceptual; calling it requires the full pipeline of       *)
(* (1) establish RIP=word(pc + sub_pc) via JA-not-taken,                     *)
(* (2) X86_STEPS_TAC stop-start instructions,                                *)
(* (3) bridge popcnt -> LENGTH FILTER via FILTER_LT_9_LENGTH_8,              *)
(* (4) bridge vmovdqu store data -> num_of_wordlist of accepted nibbles      *)
(*     (an 8-way ASM_CASES_TAC + WORD_BLAST),                                *)
(* (5) update outlen invariant: outlen' = outlen + popcnt_k.                 *)
(* These are too dependent on local state to abstract cleanly, but the       *)
(* shape is identical for k=0..3.                                            *)

(* REJ_SAMPLE_ETA4_BYTES decomposition: append on lists.                     *)
let REJ_SAMPLE_ETA4_BYTES_APPEND = prove
 (`!l1 l2:byte list. REJ_SAMPLE_ETA4_BYTES (APPEND l1 l2) =
                     APPEND (REJ_SAMPLE_ETA4_BYTES l1) (REJ_SAMPLE_ETA4_BYTES l2)`,
  REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES; REJ_NIBBLES_ETA4_APPEND;
              MAP_APPEND]);;

(* For sub-iter k (0 <= k <= 3), the contribution to outlen is               *)
(* LENGTH(REJ_NIBBLES_ETA4 [b_(4k); ...; b_(4k+3)])                          *)
(* Equivalently in int32 form:                                               *)
(* LENGTH(REJ_SAMPLE_ETA4_BYTES [b_(4k); ...; b_(4k+3)])                     *)
let LENGTH_REJ_SAMPLE_ETA4_BYTES = prove
 (`!l:byte list.
     LENGTH(REJ_SAMPLE_ETA4_BYTES l:int32 list) =
     LENGTH(REJ_NIBBLES_ETA4 l:int16 list)`,
  REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES; LENGTH_MAP]);;

(* The popcnt of the low byte of any int32 is at most 8. Used to bound       *)
(* the increment to RAX from popcntl in each sub-iteration.                  *)
let VPSUBB_SIGN_BIT_LT_9 = prove
 (`!a:byte. val a < 16
     ==> (bit 7 (word_sub a (word 9):byte) <=> val a < 9)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[BIT_VAL; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[VAL_WORD_SUB; DIMINDEX_8; VAL_WORD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `val(a:byte) < 9` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `(val(a:byte) + 247) MOD 256 = val a + 247`
    SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[ODD; ARITH_RULE `ODD 1`] `n = 1 ==> ODD n`) THEN
    MATCH_MP_TAC DIV_UNIQ THEN
    EXISTS_TAC `val(a:byte) + 119` THEN ASM_ARITH_TAC;
    REWRITE_TAC[NOT_ODD] THEN
    SUBGOAL_THEN `(val(a:byte) + 247) MOD 256 = val a - 9`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `val(a:byte) + 247 = (val a - 9) + 1 * 256`
      SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[MOD_MULT_ADD] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[DIV_LT; EVEN] THEN ASM_ARITH_TAC]);;

(* Generalization of GATHER_FILTERED_IDX_8 post-composed with a value map f: *)
(* gathering f-of-element at the positions where P holds equals MAP f of the *)
(* P-FILTERed list. Used at the vmovdqu store where the gathered (compacted) *)
(* bytes are sign-extended (f = word_sx) and the predicate P selects accepted *)
(* nibbles. Keeps the value function f and predicate P independent, matching *)
(* the asm where pshufb gathers the (4-nibble) vector while the mask predicate *)
(* is on the nibble value.                                                   *)
let SUBITER_STORE = prove
 (`!(g:int128) (m:byte) (n0:byte) n1 n2 n3 n4 n5 n6 n7.
    val n0 < 16 /\ val n1 < 16 /\ val n2 < 16 /\ val n3 < 16 /\
    val n4 < 16 /\ val n5 < 16 /\ val n6 < 16 /\ val n7 < 16 /\
    (!j. j < 8 ==> (bit j m <=> val(EL j [n0;n1;n2;n3;n4;n5;n6;n7]:byte) < 9)) /\
    (!j. j < 8 ==> word_subword g (8*j,8):byte =
                   word_sub (word 4) (EL j [n0;n1;n2;n3;n4;n5;n6;n7]))
    ==> SUB_LIST(0, LENGTH(ACC_IDX m)) (PSHUFB_OUT_LIST g m) =
        MAP (\x:byte. word_sub (word 4) x)
            (FILTER (\x:byte. val x < 9) [n0;n1;n2;n3;n4;n5;n6;n7])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g:int128`; `val(m:byte)`] PSHUFB_ACCEPTED_PREFIX_NUM) THEN
  REWRITE_TAC[WORD_VAL] THEN
  ANTS_TAC THENL
   [MP_TAC(ISPEC `m:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ACC_IDX] THEN
  MP_TAC(ISPECL [`\x:byte. word_sub (word 4) x:byte`; `\x:byte. val x < 9`;
                 `n0:byte`;`n1:byte`;`n2:byte`;`n3:byte`;`n4:byte`;`n5:byte`;`n6:byte`;`n7:byte`]
                GATHER_FILTER_MAP_IDX_8) THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `(!j. MEM j [0;1;2;3;4;5;6;7] ==> (bit j (m:byte) <=> val(EL j [n0;n1;n2;n3;n4;n5;n6;n7]:byte) < 9)) /\
    (!j. MEM j [0;1;2;3;4;5;6;7] ==> word_subword (g:int128) (8*j,8):byte =
                   word_sub (word 4) (EL j [n0;n1;n2;n3;n4;n5;n6;n7]))`
   MP_TAC THENL
   [CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[MEM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN
  REWRITE_TAC[FILTER; MAP; MEM] THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) then
      (MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN
       MP_TAC(SPEC `3` th) THEN MP_TAC(SPEC `4` th) THEN MP_TAC(SPEC `5` th) THEN
       MP_TAC(SPEC `6` th) THEN MP_TAC(SPEC `7` th))
    else NO_TAC)) THEN
  REWRITE_TAC[MEM] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV EL_CONV)) THEN
  CONV_TAC(DEPTH_CONV EL_CONV) THEN ASM_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(DEPTH_CONV EL_CONV) THEN ASM_REWRITE_TAC[]);;

(* For an accepted nibble (n < 9), the byte-width and int16-width forms of the *)
(* eta coefficient (4 - n) sign-extend to the SAME int32. Needed because the *)
(* asm computes 4-nibble in byte lanes (vpsubb) then vpmovsxbd, while the spec *)
(* uses int16 nibbles; both give word(4-n):int32 for n<9 (no underflow since *)
(* n<=4 gives 4-n, and 5..8 give the sign-extended negative). 9-way blast.   *)
let SX_SUB4_BYTE_EQ_INT16 = prove
 (`!n. n < 9
       ==> word_sx(word_sub (word 4:byte) (word n:byte)):int32 =
           word_sx(word_sub (word 4:int16) (word n:int16)):int32`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
    `n < 9 ==> n=0\/n=1\/n=2\/n=3\/n=4\/n=5\/n=6\/n=7\/n=8`)) THEN
  POP_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  CONV_TAC WORD_BLAST);;

(* SUBITER STORE (int32 form) — the per-sub-iter store-value lemma keyed to  *)
(* numeric nibble values. Given gather byte j = (4 - v_j) and mask bit j =   *)
(* (v_j < 9), the 8-int32 vpmovsxbd output, truncated to popcount(m) lanes,  *)
(* equals MAP (\v. word_sx(word_sub 4 v)) over the accepted nibbles — i.e. the *)
(* int32 eta coefficients in compacted order. This is exactly the vmovdqu    *)
(* store contribution of one sub-iter; instantiated 4x and composed over the *)
(* four 4-byte blocks to give the iteration's REJ_SAMPLE step.               *)
let SUBITER_STORE_INT32 = prove
 (`!(g:int128) (m:byte) v0 v1 v2 v3 v4 v5 v6 v7.
    v0<16/\v1<16/\v2<16/\v3<16/\v4<16/\v5<16/\v6<16/\v7<16 /\
    (!j. j < 8 ==> (bit j m <=> EL j [v0;v1;v2;v3;v4;v5;v6;v7] < 9)) /\
    (!j. j < 8 ==> word_subword g (8*j,8):byte =
                   word_sub (word 4) (word(EL j [v0;v1;v2;v3;v4;v5;v6;v7]):byte))
    ==> MAP (\b:byte. word_sx b:int32)
            (SUB_LIST(0, LENGTH(ACC_IDX m)) (PSHUFB_OUT_LIST g m)) =
        MAP (\v. word_sx(word_sub (word 4:int16) (word v)):int32)
            (FILTER (\v. v < 9) [v0;v1;v2;v3;v4;v5;v6;v7])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g:int128`; `m:byte`;
    `word v0:byte`;`word v1:byte`;`word v2:byte`;`word v3:byte`;
    `word v4:byte`;`word v5:byte`;`word v6:byte`;`word v7:byte`] SUBITER_STORE) THEN
  SUBGOAL_THEN `val(word v0:byte)=v0/\val(word v1:byte)=v1/\val(word v2:byte)=v2/\
                val(word v3:byte)=v3/\val(word v4:byte)=v4/\val(word v5:byte)=v5/\
                val(word v6:byte)=v6/\val(word v7:byte)=v7`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN
      `!j. j < 8 ==> val(EL j [word v0;word v1;word v2;word v3;
                               word v4;word v5;word v6;word v7]:byte) =
                     EL j [v0;v1;v2;v3;v4;v5;v6;v7]`
      ASSUME_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`
        (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THENL
       [ASM_ARITH_TAC; ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC] THEN
      CONV_TAC(DEPTH_CONV EL_CONV) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        let s=string_of_term(concl th) in
        let h n=let nl=String.length n and hl=String.length s in
          let rec go i=if i+nl>hl then false else if String.sub s i nl=n then true else go(i+1) in go 0 in
        h "bit j")) THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        let s=string_of_term(concl th) in
        let h n=let nl=String.length n and hl=String.length s in
          let rec go i=if i+nl>hl then false else if String.sub s i nl=n then true else go(i+1) in go 0 in
        h "word_subword")) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`
        (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THENL
       [ASM_ARITH_TAC; ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC;ALL_TAC] THEN
      CONV_TAC(DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM MAP_o; o_DEF] THEN
  REWRITE_TAC[FILTER; MAP] THEN ASM_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP]) THEN
  ASM_SIMP_TAC[SX_SUB4_BYTE_EQ_INT16]);;

(* Push a num->int16 word-cast through MAP/FILTER: gathering f over the int16 *)
(* P-filtered (word-cast) list equals gathering (f o word) over the numeric  *)
(* (P o word)-filtered list. Used to convert SUBITER_STORE_INT32's numeric   *)
(* nibble form to the spec's int16 NIBBLES_OF_BYTES form.                    *)
let FILTER_VAL_WORD_NIB = prove
 (`!L:num list. (!v. MEM v L ==> v < 16)
     ==> FILTER (\v. val(word v:int16) < 9) L = FILTER (\v. v < 9) L`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[FILTER; MEM] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word h:int16) = h` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_16] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `h:num`) THEN REWRITE_TAC[MEM] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FILTER (\v. val(word v:int16) < 9) t = FILTER (\v. v < 9) t`
    SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  REWRITE_TAC[]);;

(* SUBITER STORE (spec form) — the body-ready per-sub-iter store lemma.      *)
(* Given mask m = accept predicate on the 8 nibbles of a 4-byte block        *)
(* [b0;b1;b2;b3] (in NIBBLES_OF_BYTES order: lo,hi per byte) and gather byte *)
(* j = (4 - nibble_j), the int32 vmovdqu store of one sub-iter (truncated to *)
(* popcount(m) lanes) equals REJ_SAMPLE_ETA4_BYTES [b0;b1;b2;b3]. The two    *)
(* hypotheses are discharged in the loop body from the proven nibble-extract *)
(* and bound/mask (VPSUBB_SIGN_BIT_LT_9, VMOVMSKB) lane lemmas.              *)
(* Instantiated 4x (one per sub-iter) and composed over the four 4-byte      *)
(* blocks to give the full iteration's contribution.                         *)
let SUBITER_STORE_SPEC = prove
 (`!(g:int128) (m:byte) (b0:byte) b1 b2 b3.
    (!j. j < 8 ==> (bit j m <=>
        EL j [val b0 MOD 16; val b0 DIV 16; val b1 MOD 16; val b1 DIV 16;
              val b2 MOD 16; val b2 DIV 16; val b3 MOD 16; val b3 DIV 16] < 9)) /\
    (!j. j < 8 ==> word_subword g (8*j,8):byte =
        word_sub (word 4) (word(EL j [val b0 MOD 16; val b0 DIV 16; val b1 MOD 16; val b1 DIV 16;
              val b2 MOD 16; val b2 DIV 16; val b3 MOD 16; val b3 DIV 16]):byte))
    ==> MAP (\b:byte. word_sx b:int32)
            (SUB_LIST(0, LENGTH(ACC_IDX m)) (PSHUFB_OUT_LIST g m)) =
        REJ_SAMPLE_ETA4_BYTES [b0;b1;b2;b3]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`g:int128`; `m:byte`;
    `val(b0:byte) MOD 16`; `val(b0:byte) DIV 16`; `val(b1:byte) MOD 16`; `val(b1:byte) DIV 16`;
    `val(b2:byte) MOD 16`; `val(b2:byte) DIV 16`; `val(b3:byte) MOD 16`; `val(b3:byte) DIV 16`]
    SUBITER_STORE_INT32) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
    MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN
    SIMP_TAC[MOD_LT_EQ; ARITH_EQ; RDIV_LT_EQ] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES; REJ_NIBBLES_ETA4] THEN
  SUBGOAL_THEN
   `NIBBLES_OF_BYTES [b0;b1;b2;b3] =
    MAP (word:num->int16)
        [val b0 MOD 16; val b0 DIV 16; val b1 MOD 16; val b1 DIV 16;
         val b2 MOD 16; val b2 DIV 16; val b3 MOD 16; val b3 DIV 16]`
   SUBST1_TAC THENL
   [REWRITE_TAC[NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND; MAP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:int16. word_sx(word_sub (word 4) x):int32`; `\x:int16. val x < 9`;
    `[val(b0:byte) MOD 16; val b0 DIV 16; val(b1:byte) MOD 16; val b1 DIV 16;
      val(b2:byte) MOD 16; val b2 DIV 16; val(b3:byte) MOD 16; val b3 DIV 16]`]
    MAP_FILTER_WORD_NIB) THEN
  SUBGOAL_THEN
   `!v. MEM v [val(b0:byte) MOD 16; val b0 DIV 16; val(b1:byte) MOD 16; val b1 DIV 16;
               val(b2:byte) MOD 16; val b2 DIV 16; val(b3:byte) MOD 16; val b3 DIV 16]
        ==> v < 16`
   ASSUME_TAC THENL
   [REWRITE_TAC[MEM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
    MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
    REWRITE_TAC[DIMINDEX_8] THEN
    SIMP_TAC[MOD_LT_EQ; ARITH_EQ; RDIV_LT_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[] THEN
  ASM_SIMP_TAC[FILTER_VAL_WORD_NIB]);;

(* General length bound: at most 2 nibbles per byte.                         *)
let LENGTH_REJ_SAMPLE_ETA4_BYTES_BOUND = prove
 (`!l:byte list. LENGTH(REJ_SAMPLE_ETA4_BYTES l:int32 list) <= 2 * LENGTH l`,
  GEN_TAC THEN
  REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES; LENGTH_REJ_NIBBLES_ETA4]);;

(* Per-sub-iter monotonicity bounds: partial outlen at sub-iter k is at      *)
(* most outlen at end of main iter (= 16-byte chunk). Used to show           *)
(* JA-not-taken for intermediate sub-iters when end-of-iter outlen ≤ 248.    *)

(* Generic prefix monotonicity for REJ_SAMPLE_ETA4_BYTES (int32 form).       *)
let LENGTH_REJ_SAMPLE_ETA4_BYTES_APPEND_LE = prove
 (`!l1 l2:byte list.
     LENGTH(REJ_SAMPLE_ETA4_BYTES l1:int32 list) <=
     LENGTH(REJ_SAMPLE_ETA4_BYTES (APPEND l1 l2):int32 list)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES_APPEND; LENGTH_APPEND] THEN ARITH_TAC);;

(* SHR by 8/16/24 commutes with low-byte extraction.                         *)
(* After `shr r8d, 8`, the low 8 bits of r8d are bits 8..15 of original.     *)
(* Used to identify the per-sub-iter mask byte after each SHR.               *)
let LENGTH_FILTER_LT_9_MAP_WORD_ZX = prove
 (`!l:byte list. LENGTH(FILTER (\x:int16. val x < 9) (MAP word_zx l)) =
                  LENGTH(FILTER (\x:byte. val x < 9) l)`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; FILTER; LENGTH; VAL_WORD_ZX_BYTE_LT_9] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH]);;

(* Array_bound element lemma: each element of REJ_SAMPLE_ETA4_BYTES l is     *)
(* in [-4, 4]. This is the per-element form of the CBMC array_bound          *)
(* postcondition.                                                            *)
let REJ_SAMPLE_ETA4_BYTES_COEFF_BOUND = prove
 (`!(l:byte list) c:int32.
     MEM c (REJ_SAMPLE_ETA4_BYTES l)
     ==> --(&4):int <= ival c /\ ival c <= &4`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES; REJ_NIBBLES_ETA4; MEM_MAP; MEM_FILTER] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `(x:int16) = word(val x)` SUBST1_TAC THENL
     [REWRITE_TAC[WORD_VAL]; ALL_TAC] THEN
    UNDISCH_TAC `val(x:int16) < 9` THEN
    SPEC_TAC(`val(x:int16)`,`n:num`) THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `n IN {0,1,2,3,4,5,6,7,8}` MP_TAC THENL
     [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN CONV_TAC INT_REDUCE_CONV;
    SUBGOAL_THEN `(x:int16) = word(val x)` SUBST1_TAC THENL
     [REWRITE_TAC[WORD_VAL]; ALL_TAC] THEN
    UNDISCH_TAC `val(x:int16) < 9` THEN
    SPEC_TAC(`val(x:int16)`,`n:num`) THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `n IN {0,1,2,3,4,5,6,7,8}` MP_TAC THENL
     [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN CONV_TAC INT_REDUCE_CONV]);;

(* Strengthen-post lemma: an `ensures` whose post implies a stronger post    *)
(* gives an `ensures` for the stronger post.                                 *)
(* Used to derive SUBROUTINE_CORRECT (with array_bound) from CORRECT         *)
(* (without array_bound) by showing the array_bound holds at exit.           *)
let LENGTH_SUB_LIST_REJ_SAMPLE_ETA4_BYTES = prove
 (`!(l:byte list).
     LENGTH(SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES l):int32 list) <= 256`,
  GEN_TAC THEN REWRITE_TAC[LENGTH_SUB_LIST] THEN ARITH_TAC);;

(* The exact form needed for SUBROUTINE_CORRECT postcondition:               *)
(*   (!i. i < outlen ==> ival(EL i outlist) < &5 /\ -- &5 < ival(EL i ...))  *)
(* matching PR #1040's aarch64 eta4 SUBROUTINE_CORRECT.                      *)
let REJ_SAMPLE_ETA4_BYTES_EL_BOUND = prove
 (`!(l:byte list) i.
     i < LENGTH(SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES l):int32 list)
     ==> ival(EL i (SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES l):int32 list)) < &5 /\
         -- &5 < ival(EL i (SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES l):int32 list))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`l:byte list`;
                 `EL i (SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES (l:byte list)):int32 list):int32`]
                REJ_SAMPLE_ETA4_BYTES_COEFF_BOUND) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`REJ_SAMPLE_ETA4_BYTES (l:byte list):int32 list`; `256`]
                  SUB_LIST_TOPSPLIT) THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th]) THEN
    REWRITE_TAC[MEM_APPEND] THEN DISJ1_TAC THEN
    MATCH_MP_TAC MEM_EL THEN ASM_REWRITE_TAC[];
    INT_ARITH_TAC]);;

(* MAJOR BRIDGE: byte-form LENGTH FILTER for the 8 nibbles extracted from    *)
(* 4 input bytes (after VPMOVZXBW + VPSLLW + VPOR + VPAND) equals            *)
(* LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3]).                                   *)
let LENGTH_FILTER_BYTE_NIBBLES_4_BYTES = prove
 (`!(b0:byte) (b1:byte) (b2:byte) (b3:byte).
     LENGTH(FILTER (\x:byte. val x < 9)
             [word(val b0 MOD 16); word(val b0 DIV 16);
              word(val b1 MOD 16); word(val b1 DIV 16);
              word(val b2 MOD 16); word(val b2 DIV 16);
              word(val b3 MOD 16); word(val b3 DIV 16)]) =
     LENGTH(REJ_NIBBLES_ETA4 [b0;b1;b2;b3]:int16 list)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4; NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND] THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(SPEC
   `[word(val(b0:byte) MOD 16); word(val(b0:byte) DIV 16);
     word(val(b1:byte) MOD 16); word(val(b1:byte) DIV 16);
     word(val(b2:byte) MOD 16); word(val(b2:byte) DIV 16);
     word(val(b3:byte) MOD 16); word(val(b3:byte) DIV 16)]:byte list`
   LENGTH_FILTER_LT_9_MAP_WORD_ZX) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[MAP] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[CONS_11; PAIR_EQ] THEN
  REPEAT CONJ_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC WORD_ZX_BYTE_TO_INT16 THEN
  MP_TAC(ISPEC `b0:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b1:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b2:byte` VAL_BOUND) THEN
  MP_TAC(ISPEC `b3:byte` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_8] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* movzbl/popcnt low-byte reduction for the clean loop body.  After the      *)
(* movzbl r8b->r10d the popcnt operand is word_zx layers over                *)
(* word(val mask8 MOD 256) where mask8 = word_zx(word(32-term vpmovmskb      *)
(* bitval sum)); the low-8 popcount reduction collapses the whole popcnt to  *)
(* the low-8 bitval sum bitval(p0)+..+bitval(p7), which then composes with   *)
(* the maskbit bridge (p k = bit 7 of f1bnd byte k) to give the              *)
(* block accept count.  Supporting: ADD256_MOD, LOW8_LT, MOD_RED.            *)
(* ------------------------------------------------------------------------- *)

let BITVAL_SUM_8_EQ_LENGTH_FILTER = prove
 (`!a0 a1 a2 a3 a4 a5 a6 a7:byte.
     bitval(val a0 < 9) + bitval(val a1 < 9) + bitval(val a2 < 9) + bitval(val a3 < 9) +
     bitval(val a4 < 9) + bitval(val a5 < 9) + bitval(val a6 < 9) + bitval(val a7 < 9) =
     LENGTH(FILTER (\x:byte. val x < 9) [a0;a1;a2;a3;a4;a5;a6;a7])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FILTER; LENGTH] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; BITVAL_CLAUSES]) THEN ARITH_TAC);;

(* ACC_LENGTH_EQ_FILTER: given the per-lane mask<->accept correspondence, the accept *)
(* count LENGTH(ACC_IDX m) equals LENGTH(FILTER (<9) [the 8 nibble bytes]) = LENGTH *)
(* (REJ_NIBBLES block) = LENGTH(REJ_SAMPLE block). Width reconciliation for the *)
(* SUBITER_STORE_EXTEND fold. (Placed after BITVAL_SUM_8_EQ_LENGTH_FILTER which it uses.)*)
let ACC_LENGTH_EQ_FILTER = prove
 (`!(m:byte) (n0:byte) (n1:byte) (n2:byte) (n3:byte) (n4:byte) (n5:byte) (n6:byte) (n7:byte).
     (bit 0 m <=> val n0 < 9) /\ (bit 1 m <=> val n1 < 9) /\ (bit 2 m <=> val n2 < 9) /\
     (bit 3 m <=> val n3 < 9) /\ (bit 4 m <=> val n4 < 9) /\ (bit 5 m <=> val n5 < 9) /\
     (bit 6 m <=> val n6 < 9) /\ (bit 7 m <=> val n7 < 9)
     ==> LENGTH(ACC_IDX m) = LENGTH(FILTER (\x:byte. val x < 9) [n0;n1;n2;n3;n4;n5;n6;n7])`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_ACC_IDX_BITSUM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[BITVAL_SUM_8_EQ_LENGTH_FILTER]);;

let SUBITER_OUTLEN_BOUND_1 = prove
 (`!(inlist:byte list) i.
     16*(i+1) <= LENGTH inlist /\
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16*(i+1)) inlist):int16 list) <= 248
     ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i, 4) inlist):int16 list) <= 248`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
  MP_TAC(SPECL [`inlist:byte list`; `i:num`] REJ_NIBBLES_ETA4_STEP_16) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; LENGTH_APPEND])) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `4 + 12 = 16`]
                     (ISPECL [`inlist:byte list`; `4`; `12`; `16*i`] SUB_LIST_SPLIT)) THEN
  DISCH_THEN(fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th; REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND])) THEN
  ASM_ARITH_TAC);;

let SUBITER_OUTLEN_BOUND_2 = prove
 (`!(inlist:byte list) i.
     16*(i+1) <= LENGTH inlist /\
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16*(i+1)) inlist):int16 list) <= 248
     ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i + 4, 4) inlist):int16 list)
         <= 248`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
  MP_TAC(SPECL [`inlist:byte list`; `i:num`] REJ_NIBBLES_ETA4_STEP_16) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; LENGTH_APPEND])) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `8 + 8 = 16`]
                     (ISPECL [`inlist:byte list`; `8`; `8`; `16*i`] SUB_LIST_SPLIT)) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `4 + 4 = 8`]
                     (ISPECL [`inlist:byte list`; `4`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 ->
    RULE_ASSUM_TAC(REWRITE_RULE[th2; REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND;
                                th1]))) THEN
  ASM_ARITH_TAC);;

let SUBITER_OUTLEN_BOUND_3 = prove
 (`!(inlist:byte list) i.
     16*(i+1) <= LENGTH inlist /\
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16*(i+1)) inlist):int16 list) <= 248
     ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i + 4, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i + 8, 4) inlist):int16 list)
         <= 248`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
  MP_TAC(SPECL [`inlist:byte list`; `i:num`] REJ_NIBBLES_ETA4_STEP_16) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; LENGTH_APPEND])) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `12 + 4 = 16`]
                     (ISPECL [`inlist:byte list`; `12`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `8 + 4 = 12`]
                     (ISPECL [`inlist:byte list`; `8`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `4 + 4 = 8`]
                     (ISPECL [`inlist:byte list`; `4`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 -> DISCH_THEN(fun th3 ->
    RULE_ASSUM_TAC(REWRITE_RULE[th3; th2; th1; REJ_NIBBLES_ETA4_APPEND;
                                LENGTH_APPEND])))) THEN
  ASM_ARITH_TAC);;

(* Byte structure of the full nibble-extraction SIMD chain (vpmovzxbw +
   vpsllw $4 + vpor + vpand mask) against the CONCRETE 0x0F0F0F0F broadcast
   constant carried in the loop invariant (YMM2). Output byte 2j = low
   nibble of input byte j (= val MOD 16), byte 2j+1 = high nibble (val DIV
   16) -- matching NIBBLES_OF_BYTES order. This is what reduces the vpand
   result (opaque without the YMM2 invariant) to nibble form in CLEAN_BODY. *)
let F0NIB_BYTES = prove
 (`!q:int128.
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (0,8):byte =
     word(val(word_subword q (0,8):byte) MOD 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (8,8):byte =
     word(val(word_subword q (0,8):byte) DIV 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (16,8):byte =
     word(val(word_subword q (8,8):byte) MOD 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (24,8):byte =
     word(val(word_subword q (8,8):byte) DIV 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (32,8):byte =
     word(val(word_subword q (16,8):byte) MOD 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (40,8):byte =
     word(val(word_subword q (16,8):byte) DIV 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (48,8):byte =
     word(val(word_subword q (24,8):byte) MOD 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (56,8):byte =
     word(val(word_subword q (24,8):byte) DIV 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (64,8):byte =
     word(val(word_subword q (32,8):byte) MOD 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (72,8):byte =
     word(val(word_subword q (32,8):byte) DIV 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (80,8):byte =
     word(val(word_subword q (40,8):byte) MOD 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (88,8):byte =
     word(val(word_subword q (40,8):byte) DIV 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (96,8):byte =
     word(val(word_subword q (48,8):byte) MOD 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (104,8):byte =
     word(val(word_subword q (48,8):byte) DIV 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (112,8):byte =
     word(val(word_subword q (56,8):byte) MOD 16)) /\
    (word_subword (word_and (word_or (usimd16 (\b:byte. word_zx b:int16) q:int256)
              (usimd16 (\z:int16. word_shl z 4) (usimd16 (\b:byte. word_zx b:int16) q:int256):int256))
        (word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256)) (120,8):byte =
     word(val(word_subword q (56,8):byte) DIV 16))`,
  GEN_TAC THEN
  REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* HIGH-HALF byte lemmas (output bytes 16..31 of the 32-byte SIMD vectors,   *)
(* i.e. bit offsets 128..248).  Sub-iters 3 and 4 read the high 128-bit lane *)
(* of f0sub/f1bnd (via `vextracti128 $1`), which holds the nibbles of input  *)
(* chunk bytes 8..15.  The low-half F0NIB_BYTES lemma only covers bytes      *)
(* 0..15; these are the verbatim analogues for bytes 16..31, proved by the   *)
(* identical recipes.                                                        *)
let F0NIB_BYTES_HI =
  let chain = rand(rator(lhand(hd(conjuncts(snd(strip_forall(concl F0NIB_BYTES))))))) in
  let mk_cj bi =
    let off = 128 + 8*bi in
    let qbyte = 8 + bi/2 in
    let hi = (bi mod 2 = 1) in
    let lhs = mk_comb(mk_comb(`word_subword:int256->num#num->byte`, chain),
                      mk_pair(mk_small_numeral off, `8`)) in
    let v = mk_comb(`val:byte->num`, mk_comb(mk_comb(`word_subword:int128->num#num->byte`,`q:int128`),
                      mk_pair(mk_small_numeral(8*qbyte), `8`))) in
    let nib = if hi then mk_binop `DIV` v `16` else mk_binop `MOD` v `16` in
    mk_eq(lhs, mk_comb(`word:num->byte`, nib)) in
  prove(mk_forall(`q:int128`, end_itlist (curry mk_conj) (map mk_cj (0--15))),
    GEN_TAC THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;
                DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_BLAST);;

(* ------------------------------------------------------------------------- *)
(* Mid-guard / partial-outlen lemmas for CLEAN_BODY's sub-iter `ja` checks.  *)
(* After sub-iter 1 (which appends the first 4-byte block), the running      *)
(* count RAX = outlen0 + |accepted nibbles in block 0| = niblen(16i+4); the  *)
(* mid-iter `ja $248` must NOT fire on a clean iteration (i+1 < N), i.e. that *)
(* partial count is <= 248 because it is a prefix of niblen(16(i+1)) <= 248. *)

(* SCALAR TAIL HELPER: REJ_SAMPLE_ETA4_BYTES on a single byte = at most 2    *)
(* int32s, computed from low nibble (b MOD 16) and high nibble (b DIV 16).*)
(* The scalar tail loop processes one byte per iteration this way.           *)
let REJ_SAMPLE_ETA4_BYTES_1 = prove
 (`!b:byte.
     REJ_SAMPLE_ETA4_BYTES [b] =
     APPEND
      (if val b MOD 16 < 9
       then [word_sx(word_sub (word 4:int16) (word(val b MOD 16))):int32]
       else [])
      (if val b DIV 16 < 9
       then [word_sx(word_sub (word 4:int16) (word(val b DIV 16))):int32]
       else [])`,
  GEN_TAC THEN
  REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES; REJ_NIBBLES_ETA4;
              NIBBLES_OF_BYTES; NIBBLE_PAIR; APPEND; FILTER; MAP] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_16] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN
   `val(b:byte) MOD 16 MOD 65536 = val b MOD 16 /\
    val(b:byte) DIV 16 MOD 65536 = val b DIV 16`
   (fun th -> REWRITE_TAC[th]) THENL
   [MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
    STRIP_TAC THEN CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP; APPEND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MAP; APPEND]);;

(* Length bound on REJ_SAMPLE_ETA4_BYTES restricted to a SUB_LIST prefix.    *)
let LENGTH_REJ_SAMPLE_ETA4_BYTES_SUB_LIST_BOUND = prove
 (`!(inlist:byte list) k.
     k <= LENGTH inlist
     ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,k) inlist):int32 list) <= 2 * k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `SUB_LIST(0, k) (inlist:byte list):byte list`
              LENGTH_REJ_SAMPLE_ETA4_BYTES_BOUND) THEN
  ASM_SIMP_TAC[LENGTH_SUB_LIST_0]);;

(* Prefix lemma: REJ_SAMPLE_ETA4_BYTES has a prefix structure on SUB_LIST    *)
let REJ_SAMPLE_ETA4_SUB_LIST_PREFIX = prove
 (`!k (l:byte list).
     k <= LENGTH l
     ==> ?rest:int32 list.
         APPEND (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,k) l)) rest =
         REJ_SAMPLE_ETA4_BYTES l`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `REJ_SAMPLE_ETA4_BYTES (SUB_LIST(k, LENGTH l - k) l):int32 list` THEN
  REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES; GSYM MAP_APPEND] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4; GSYM FILTER_APPEND] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[GSYM NIBBLES_OF_BYTES_APPEND] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`l:byte list`; `k:num`] SUB_LIST_TOPSPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  REFL_TAC);;

(* Step lemma: outlen after processing one more byte equals current outlen   *)
(* + contribution of that byte (0, 1, or 2 elements).                        *)
let SUB_LIST_STEP_BYTE = prove
 (`!(l:byte list) (k:num).
     k < LENGTH l
     ==> SUB_LIST(0, k+1) l = APPEND (SUB_LIST(0, k) l) [EL k l]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:byte list`; `k:num`; `1`; `0`] SUB_LIST_SPLIT) THEN
  REWRITE_TAC[ARITH_RULE `0 + k = k`] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN ASM_REWRITE_TAC[SUB_LIST_1]);;

let REJ_SAMPLE_ETA4_BYTES_STEP_1 = prove
 (`!(l:byte list) (k:num).
     k < LENGTH l
     ==> REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, k+1) l) =
         APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, k) l))
                (REJ_SAMPLE_ETA4_BYTES [EL k l])`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SUB_LIST_STEP_BYTE; REJ_SAMPLE_ETA4_BYTES_APPEND]);;

(* SUB_LIST capping: when output already has length <= 256, the SUB_LIST(0,  *)
(* 256) cap is a no-op. Used in scalar-tail final-state composition.         *)
let SUB_LIST_BYTE_272 = prove
 (`!(l:byte list). LENGTH l = 272 ==> SUB_LIST(0, 272) l = l`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `LENGTH (l:byte list) = 272` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_ACCEPT_TAC SUB_LIST_LENGTH);;

(* Per-byte helpers for the scalar tail proof. Three cases by which nibble   *)
(* (low and/or high) is < 9 (accepted) or >= 9 (rejected).                   *)
let REJ_SAMPLE_ETA4_BYTES_1_REJECT_BOTH = prove
 (`!b:byte. ~(val b MOD 16 < 9) /\ ~(val b DIV 16 < 9)
            ==> REJ_SAMPLE_ETA4_BYTES [b] = []`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES_1; APPEND]);;

let REJ_SAMPLE_ETA4_BYTES_1_LOW_ONLY = prove
 (`!b:byte. val b MOD 16 < 9 /\ ~(val b DIV 16 < 9)
            ==> REJ_SAMPLE_ETA4_BYTES [b] =
                [word_sx(word_sub (word 4:int16) (word(val b MOD 16))):int32]`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES_1; APPEND]);;

let REJ_SAMPLE_ETA4_BYTES_1_HIGH_ONLY = prove
 (`!b:byte. ~(val b MOD 16 < 9) /\ val b DIV 16 < 9
            ==> REJ_SAMPLE_ETA4_BYTES [b] =
                [word_sx(word_sub (word 4:int16) (word(val b DIV 16))):int32]`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES_1; APPEND]);;

let REJ_SAMPLE_ETA4_BYTES_1_BOTH = prove
 (`!b:byte. val b MOD 16 < 9 /\ val b DIV 16 < 9
            ==> REJ_SAMPLE_ETA4_BYTES [b] =
                [word_sx(word_sub (word 4:int16) (word(val b MOD 16))):int32;
                 word_sx(word_sub (word 4:int16) (word(val b DIV 16))):int32]`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES_1; APPEND]);;

let LENGTH_REJ_SAMPLE_ETA4_BYTES_1 = prove
 (`!b:byte. LENGTH(REJ_SAMPLE_ETA4_BYTES [b] :int32 list) =
            (if val b MOD 16 < 9 then 1 else 0) +
            (if val b DIV 16 < 9 then 1 else 0)`,
  GEN_TAC THEN REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES_1; LENGTH_APPEND] THEN
  COND_CASES_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* ===== INLINED CLEAN_BODY chain + exit-block assets =====                  *)

(* ========================================================================= *)
(* CLEAN_BODY full proof build. Uses EXEC, the store lemmas,                 *)
(* SUBITER_STORE_SPEC, etc., and proves MLDSA_REJ_UNIFORM_ETA4_CLEAN_BODY.   *)
(* ========================================================================= *)

let EXEC = MLDSA_REJ_UNIFORM_ETA4_EXEC;;

let LEN_RECONCILE = prove
 (`!(m:byte) (chunk0:int128).
     (!j. j < 8 ==> (bit j m <=>
        EL j [val(word_subword chunk0 (0,8):byte) MOD 16; val(word_subword chunk0 (0,8):byte) DIV 16;
              val(word_subword chunk0 (8,8):byte) MOD 16; val(word_subword chunk0 (8,8):byte) DIV 16;
              val(word_subword chunk0 (16,8):byte) MOD 16; val(word_subword chunk0 (16,8):byte) DIV 16;
              val(word_subword chunk0 (24,8):byte) MOD 16; val(word_subword chunk0 (24,8):byte) DIV 16] < 9))
     ==> LENGTH(ACC_IDX m) =
         LENGTH(REJ_SAMPLE_ETA4_BYTES [word_subword chunk0 (0,8); word_subword chunk0 (8,8);
                                       word_subword chunk0 (16,8); word_subword chunk0 (24,8)]:int32 list)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:byte`;
    `word(val(word_subword (chunk0:int128) (0,8):byte) MOD 16):byte`;
    `word(val(word_subword (chunk0:int128) (0,8):byte) DIV 16):byte`;
    `word(val(word_subword (chunk0:int128) (8,8):byte) MOD 16):byte`;
    `word(val(word_subword (chunk0:int128) (8,8):byte) DIV 16):byte`;
    `word(val(word_subword (chunk0:int128) (16,8):byte) MOD 16):byte`;
    `word(val(word_subword (chunk0:int128) (16,8):byte) DIV 16):byte`;
    `word(val(word_subword (chunk0:int128) (24,8):byte) MOD 16):byte`;
    `word(val(word_subword (chunk0:int128) (24,8):byte) DIV 16):byte`] ACC_LENGTH_EQ_FILTER) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    W(fun (asl,gw) -> let n = rand(rator(lhand gw)) in
       MP_TAC(SPEC n (find (fun th -> is_forall(concl th) && can(find_term(fun u->match u with Const("EL",_)->true|_->false))(concl th)) (map snd asl)))) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN
    W(fun (asl,gw) -> let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_subword" && type_of u=`:byte` with _->false) gw in
       MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN STRIP_TAC THEN
       SUBGOAL_THEN (mk_eq(mk_comb(`val:byte->num`,mk_comb(`word:num->byte`,mk_binop `MOD` (mk_comb(`val:byte->num`,bt)) `16`)), mk_binop `MOD` (mk_comb(`val:byte->num`,bt)) `16`)) SUBST1_TAC THENL
        [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
       SUBGOAL_THEN (mk_eq(mk_comb(`val:byte->num`,mk_comb(`word:num->byte`,mk_binop `DIV` (mk_comb(`val:byte->num`,bt)) `16`)), mk_binop `DIV` (mk_comb(`val:byte->num`,bt)) `16`)) SUBST1_TAC THENL
        [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
       REFL_TAC);
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[LENGTH_FILTER_BYTE_NIBBLES_4_BYTES; LENGTH_REJ_SAMPLE_ETA4_BYTES]]);;

(* SUBITER_FOLD_STEP: reusable fold of one sub-iter's REJ block onto the running prefix.
   Given (a) the accept-count = block length [from LEN_RECONCILE], (b) the prefix store
   read(bytes(res, 4*LEN(REJ prefixbytes))) = nwl(REJ prefixbytes), and (c) this sub-iter's
   block store read(bytes(res + 4*LEN(REJ prefixbytes), 4*LEN(ACC_IDX m))) = nwl(REJ blk),
   conclude read(bytes(res, 4*LEN(REJ (prefixbytes++blk)))) = nwl(REJ (prefixbytes++blk)).
   Applies identically to all 4 sub-iters (prefixbytes = SUB_LIST(0,16i+4k), blk = next 4 bytes),
   turning prefixbytes++blk back into SUB_LIST(0,16i+4(k+1)). *)
let SUBITER_FOLD_STEP = prove
 (`!res s (m:byte) (blk:byte list) (prefixbytes:byte list).
     LENGTH(ACC_IDX m) = LENGTH(REJ_SAMPLE_ETA4_BYTES blk:int32 list) /\
     read(memory:>bytes(res, 4*LENGTH(REJ_SAMPLE_ETA4_BYTES prefixbytes:int32 list))) s =
       num_of_wordlist(REJ_SAMPLE_ETA4_BYTES prefixbytes) /\
     read(memory:>bytes(word_add res (word(4*LENGTH(REJ_SAMPLE_ETA4_BYTES prefixbytes:int32 list))),
                        4*LENGTH(ACC_IDX m))) s =
       num_of_wordlist(REJ_SAMPLE_ETA4_BYTES blk)
     ==> read(memory:>bytes(res, 4*LENGTH(REJ_SAMPLE_ETA4_BYTES(APPEND prefixbytes blk):int32 list))) s =
         num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(APPEND prefixbytes blk))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`res:int64`; `s:x86state`;
                 `REJ_SAMPLE_ETA4_BYTES prefixbytes:int32 list`;
                 `REJ_SAMPLE_ETA4_BYTES blk:int32 list`] SUBITER_STORE_EXTEND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> if can(find_term(fun u->u=`ACC_IDX (m:byte)`)) (concl th)
                            then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES_APPEND; LENGTH_APPEND;
                ARITH_RULE `4*a+4*b = 4*(a+b)`]]);;

let maskbit_tgt =
  `!j. j < 8 ==> (bit j (word (val (mask8:int64) MOD 256):byte) <=>
       EL j [val(word_subword (chunk0:int128) (0,8):byte) MOD 16;
         val(word_subword chunk0 (0,8):byte) DIV 16; val(word_subword chunk0 (8,8):byte) MOD 16;
         val(word_subword chunk0 (8,8):byte) DIV 16; val(word_subword chunk0 (16,8):byte) MOD 16;
         val(word_subword chunk0 (16,8):byte) DIV 16; val(word_subword chunk0 (24,8):byte) MOD 16;
         val(word_subword chunk0 (24,8):byte) DIV 16] < 9)`;;

let clean_body_tm = `
   !res buf table (inlist:byte list) pc N (i:num) stackpointer.
        LENGTH inlist = 272 /\
        nonoverlapping_modulo (2 EXP 64) (pc, 403) (val res,1024) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 403) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 403) (val table,2048) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val table,2048) /\
        ~(N = 0) /\ i + 1 < N /\ 16 * (i + 1) <= 272 /\
        LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16 * (i+1)) inlist)) <= 248
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word(pc + 52) /\ read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s = num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  read YMM2 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
                  read YMM3 s = word 1816346497840254045859937019744124044757176230049263749638550337379029484548 /\
                  read YMM4 s = word 4086779620140571603184858294424279100703646517610843436686738259102816340233 /\
                  read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list)) /\
                  read RCX s = word(16*i) /\
                  read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list))) s = num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist)))
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word(pc + 52) /\ read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  read YMM2 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
                  read YMM3 s = word 1816346497840254045859937019744124044757176230049263749638550337379029484548 /\
                  read YMM4 s = word 4086779620140571603184858294424279100703646517610843436686738259102816340233 /\
                  read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(i+1)) inlist):int32 list)) /\
                  read RCX s = word(16*(i+1)) /\
                  read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(i+1)) inlist):int32 list))) s = num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(i+1)) inlist)))
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM5; ZMM6] ,,
              MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`;;

(* ========================================================================= *)
(* Sub-iter k (k>=1) popcount->length keystone lemmas.                       *)
(* These generalize sub-iter 1's popeq/pop_len recipe to sub-iters 2,3,4 whose *)
(* mask byte is R8 shifted right by 8*k bits.  Sub-iter 2's mask8b is reabbreved *)
(* to a bare var before the movzbl read, giving the clean R10/R9 popcnt shape *)
(* word_zx(word_zx(word(val mask8b MOD 256))) identical to sub-iter 1.       *)
(* ========================================================================= *)

(* SUBITER_OUTLEN_BOUND_4: the 5-term niblen sum through sub-iter 4 stays <=248. *)
let SUBITER_OUTLEN_BOUND_4 = prove
 (`!(inlist:byte list) i.
     16*(i+1) <= LENGTH inlist /\
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16*(i+1)) inlist):int16 list) <= 248
     ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i + 4, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i + 8, 4) inlist):int16 list) +
         LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i + 12, 4) inlist):int16 list)
         <= 248`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
  MP_TAC(SPECL [`inlist:byte list`; `i:num`] REJ_NIBBLES_ETA4_STEP_16) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; LENGTH_APPEND])) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `12 + 4 = 16`]
                     (ISPECL [`inlist:byte list`; `12`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `8 + 4 = 12`]
                     (ISPECL [`inlist:byte list`; `8`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  MP_TAC(REWRITE_RULE[ARITH_RULE `4 + 4 = 8`]
                     (ISPECL [`inlist:byte list`; `4`; `4`; `16*i`] SUB_LIST_SPLIT)) THEN
  DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 -> DISCH_THEN(fun th3 ->
    RULE_ASSUM_TAC(REWRITE_RULE[th3; th2; th1; REJ_NIBBLES_ETA4_APPEND;
                                LENGTH_APPEND])))) THEN
  ASM_ARITH_TAC);;

(* --- maskbit_tgt_tac ---                                                   *)
(* TAB1_TEQ_TAC: derive the sub-iter-1 table-load bridge teq                 *)
(* `tab1 = word_zx(word_zx(word(num_of_wordlist(TABLE_ENTRY ...))))` at s13. *)
(* Generator for the four per-sub-iter table-load teq tactics: read the vmovq  *)
(* table load at state `rds`, MP TABLE_VMOVQ_READ with the mask<256 bound, then *)
(* rewrite the YMM6 read at state `ymms` by the zx-collapse lemma.  Varies only *)
(* in the two state indices, the mask var, and the RLT/R_EQ support lemmas.     *)
let mk_tab_teq (rds:int) (ymms:int) (maskv:term) (rlt:thm) (req:thm) : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let rdst = mk_var("s"^string_of_int rds,`:x86state`)
    and ymmst = mk_var("s"^string_of_int ymms,`:x86state`) in
    let tblinv = find (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),v)),_) ->
         v=rdst && can(find_term(fun u->u=`mldsa_rej_uniform_table:byte list`)) (concl th) | _ -> false) asms in
    let mmod = mk_binop `MOD` (mk_comb(`val:int64->num`,maskv)) `256` in
    let tvr = MP (ISPECL[`table:int64`; mmod; rdst] TABLE_VMOVQ_READ) (CONJ tblinv rlt) in
    let ymm6 = find (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("YMM6",_)),v)),_)-> v=ymmst |_->false) asms in
    ASSUME_TAC (REWRITE_RULE[req; tvr] ymm6));;

let TAB1_TEQ_TAC : tactic = mk_tab_teq 13 14 `mask8:int64` RLT R_EQ;;

(* --- pf_target_proof ---                                                   *)
(* ===== pf_target proof for sub-iter 1 =====
   Establishes pshuf1 = pf_target by: SYM pshuf1-word_join def, rewrite tab1 via the
   genuine teq (tab1 = word_zx^k(word(nwl(TABLE_ENTRY(word(val mask8 MOD 256)))))) derived
   by TAB1_TEQ_TAC, expand usimd16, then COLLAPSE the redundant word_zx towers:
     - SUBWORD_ZX_LOW: word_subword(word_zx y)(lo,wid) = word_subword y (lo,wid) when lo+wid<=dimindex(P)
       (covers BOTH widening and narrowing zx, since only the low target bits matter)
     - ZX_128_256_128: word_zx(word_zx(x:int128):int256):int128 = x   (the f0sub gather-source g) *)
(* Generator for the four per-sub-iter pshufb gather-target discharge tactics: *)
(* find the `pshuf` word_join def + the `tab` TABLE_ENTRY eq by shape, then run *)
(* the fixed rewrite/conv pipeline.  PF_PROOF{,_2,_3,_4} are instances.         *)
let mk_pf_proof (pshuf:term) (tab:term) : tactic =
  W(fun (asl,w) ->
    let pdef = find (fun th -> is_eq(concl th) && rand(concl th)=pshuf && can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
    let teq0 = find (fun th -> is_eq(concl th) &&
        (lhand(concl th)=tab || rand(concl th)=tab) &&
        can(find_term(fun u->match u with Const("TABLE_ENTRY",_)->true|_->false))(concl th) &&
        not(can(find_term(fun u->u=`f1bnd:int256`))(concl th))) (map snd asl) in
    let teq = if lhand(concl teq0)=tab then teq0 else SYM teq0 in
    SUBST1_TAC(SYM pdef) THEN REWRITE_TAC[teq] THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;DIMINDEX_4;ARITH] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ZX_TRIVIAL; VAL_WORD_ZX_GEN; DIMINDEX_64; DIMINDEX_32; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(TOP_DEPTH_CONV SUBWORD_ZX_LOW_CONV) THEN REWRITE_TAC[ZX_128_256_128]);;

let PF_PROOF : tactic = mk_pf_proof `pshuf1:int256` `tab1:int256`;;

(* SUBWORD_USHR: word_subword(word_ushr x n)(lo,wid) = word_subword x (lo+n,wid). Needed for
   the >>64-shifted gather sources of sub-iters 2 and 4 (vpsrldq). *)
(* Shared RIP-resolution step used by the mid-guard / mid-exit twins.  The     *)
(* value chain grabs the assumption mentioning `pc + pcoff` directly; the      *)
(* memory-safety chain must additionally require RIP on the LHS at state       *)
(* `s<st>` (the anchored events fact also mentions `pc + pcoff`, so the bare    *)
(* find_term would grab it and REFL_TAC would fail).                            *)
let rip_mp (memsafe:bool) (pcoff:int) (st:int) : tactic =
  let pctm = mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral pcoff) in
  let stv = mk_var("s"^string_of_int st,`:x86state`) in
  if memsafe then
    FIRST_ASSUM(fun th -> if can(find_term(fun u->u=pctm))(concl th) &&
                             (match concl th with
                                Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),v)),_) -> v=stv
                              | _ -> false)
                          then MP_TAC th else NO_TAC)
  else
    FIRST_ASSUM(fun th -> if can(find_term(fun u->u=pctm))(concl th) then MP_TAC th else NO_TAC);;

let mk_prefix_g_full (memsafe:bool) : tactic =
  REPEAT GEN_TAC THEN
  (ALL_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `16 * i <= 256` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (i + 1) <= 272` THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  (if memsafe then STRIP_EXISTS_ASSUM_TAC else ALL_TAC) THEN
  MP_TAC(SPECL [`buf:int64`;`272`;`inlist:byte list`;`i:num`;`s0:x86state`] SUB_LIST_16_BYTES_FROM_INT128) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `16 * (i + 1) <= 272` THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `chunk0 = read(memory:>bytes128(word_add buf (word(16*i)))) s0` THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) <= 248` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
    TRANS_TAC LE_TRANS `LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16 * (i+1)) inlist):int16 list)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NIBLEN_PREFIX_MONO THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `outlen0 = LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list)` THEN
  FIRST_ASSUM(fun th -> if concl th =
      `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) = outlen0`
    then (RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) else NO_TAC) THEN
  MP_TAC(SPECL [`outlen0:num`;`248`] JA_NOT_TAKEN_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`16*i`;`256`] JA_NOT_TAKEN_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  VAL_INT64_TAC `outlen0:num` THEN
  X86_STEPS_TAC EXEC (1--2) THEN
  SUBGOAL_THEN `read RIP s2 = word(pc + 63):int64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && can(find_term((=)`&248:int`))(concl th)
                           then ASSUME_TAC(MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if can(find_term((=)`pc + 314`))(concl th) then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC; ALL_TAC] THEN
  X86_STEPS_TAC EXEC (3--4) THEN
  SUBGOAL_THEN `read RIP s4 = word(pc + 75):int64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && can(find_term((=)`&256:int`))(concl th)
                           then ASSUME_TAC(MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if can(find_term((=)`pc + 314`))(concl th) then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC; ALL_TAC] THEN
  X86_VSTEPS_TAC EXEC (5--5) THEN
  SUBGOAL_THEN `val(word(16*i):int64) = 16*i` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `16*i <= 256` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word(16*i):int64) = 16*i`; ARITH_RULE `1 * x = x`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read (memory :> bytes128 (word_add buf (word (16 * i)))) s4 = chunk0`]) THEN
  SUBGOAL_THEN `read YMM0 s5 = usimd16 (\b:byte. word_zx b:int16) chunk0:int256` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can(find_term((=)`read YMM0 s5`))(lhand(concl th)) then SUBST1_TAC th else NO_TAC) THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DROP_WORDJOIN_TAC THEN PURGE_STALE_STATES_TAC ["s4"] THEN
  X86_VSTEPS_TAC EXEC (6--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s5 = usimd16 (\b:byte. word_zx b:int16) chunk0:int256`]) THEN
  X86_VSTEPS_TAC EXEC (7--7) THEN X86_VSTEPS_TAC EXEC (8--8) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM2 s5 =
    word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256`]) THEN
  SUBGOAL_THEN (mk_eq(`read YMM0 s8:int256`, F0NIB_CHUNK0)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can(find_term((=)`read YMM0 s8`))(lhand(concl th)) then SUBST1_TAC th else NO_TAC) THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DROP_WORDJOIN_TAC THEN PURGE_STALE_STATES_TAC ["s5";"s6";"s7"] THEN
  ASSUME_TAC(SPEC `chunk0:int128` F0NIB_BYTES) THEN
  ASSUME_TAC(SPEC `chunk0:int128` F0NIB_BYTES_HI) THEN
  ABBREV_TAC `fn:int256 = read YMM0 s8` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(ASSUME(mk_eq(`fn:int256`, F0NIB_CHUNK0)))]) THEN
  X86_VSTEPS_TAC EXEC (9--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s8 = fn:int256`;
     ASSUME `read YMM4 s8 = word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256`]) THEN
  ABBREV_TAC `f1bnd:int256 = read YMM1 s9` THEN
  X86_VSTEPS_TAC EXEC (10--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s9 = fn:int256`;
     ASSUME `read YMM3 s9 = word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256`]) THEN
  ABBREV_TAC `f0sub:int256 = read YMM0 s10` THEN
  W(fun (asl,w) ->
      let f0d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f0sub:int256`) (map snd asl) in
      let gather_imp = prove
       (mk_imp(concl f0d,
        `!j. j < 8 ==>
           word_subword (word_subword (f0sub:int256) (0,128):int128) (8*j,8):byte =
           word_sub (word 4) (word(EL j [val(word_subword (chunk0:int128) (0,8):byte) MOD 16;
              val(word_subword chunk0 (0,8):byte) DIV 16; val(word_subword chunk0 (8,8):byte) MOD 16;
              val(word_subword chunk0 (8,8):byte) DIV 16; val(word_subword chunk0 (16,8):byte) MOD 16;
              val(word_subword chunk0 (16,8):byte) DIV 16; val(word_subword chunk0 (24,8):byte) MOD 16;
              val(word_subword chunk0 (24,8):byte) DIV 16]):byte)`),
        DISCH_THEN(fun f0eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
          REWRITE_TAC[f0eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC)) in
      ASSUME_TAC (MP gather_imp f0d)) THEN
  (* bg2: sub-iter-2 gather forall over the >>64-shifted low-lane source g2 (lanes 8-15 /
     chunk0 nibbles 32,40,48,56). Derived early (f0sub word_join live); survives to s28.
     Built as the SUBITER_STORE_SPEC gather-hyp shape so SI2_FOLD discharges by MATCH_ACCEPT. *)
  W(fun (asl,w) ->
      let f0d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f0sub:int256`) (map snd asl) in
      let g2 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128) 64):int128):int128` in
      let bg2_concl = List.nth (conjuncts(lhand(concl(ISPECL [g2; `word (val (mask8b:int64) MOD 256):byte`;
           `word_subword (chunk0:int128) (32,8):byte`; `word_subword (chunk0:int128) (40,8):byte`;
           `word_subword (chunk0:int128) (48,8):byte`; `word_subword (chunk0:int128) (56,8):byte`] SUBITER_STORE_SPEC)))) 1 in
      let bg2_imp = prove(mk_imp(concl f0d, bg2_concl),
        DISCH_THEN(fun f0eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[SUBWORD_USHR] THEN CONV_TAC NUM_REDUCE_CONV THEN
          SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
          REWRITE_TAC[f0eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC)) in
      ASSUME_TAC (MP bg2_imp f0d)) THEN
  (* bg3: sub-iter-3 gather forall over the HIGH 128 lane g3 (lanes 16-23 / chunk0 nibbles 64,72,80,88).
     No shift (vextracti128 ,1 then vpshufb). Same JOIN-extract proof as bg1 (no SUBWORD_USHR). *)
  W(fun (asl,w) ->
      let f0d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f0sub:int256`) (map snd asl) in
      let g3 = `word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128` in
      let bg3_concl = List.nth (conjuncts(lhand(concl(ISPECL [g3; `word (val (mask8c:int64) MOD 256):byte`;
           `word_subword (chunk0:int128) (64,8):byte`; `word_subword (chunk0:int128) (72,8):byte`;
           `word_subword (chunk0:int128) (80,8):byte`; `word_subword (chunk0:int128) (88,8):byte`] SUBITER_STORE_SPEC)))) 1 in
      let bg3_imp = prove(mk_imp(concl f0d, bg3_concl),
        DISCH_THEN(fun f0eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN
          SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
          REWRITE_TAC[f0eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC)) in
      ASSUME_TAC (MP bg3_imp f0d)) THEN
  (* bg4: sub-iter-4 gather forall over the HIGH 128 lane >>64 (lanes 24-31 / chunk0 nibbles 96,104,112,120). *)
  W(fun (asl,w) ->
      let f0d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f0sub:int256`) (map snd asl) in
      let g4 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128) 64):int128):int128` in
      let bg4_concl = List.nth (conjuncts(lhand(concl(ISPECL [g4; `word (val (mask8d:int64) MOD 256):byte`;
           `word_subword (chunk0:int128) (96,8):byte`; `word_subword (chunk0:int128) (104,8):byte`;
           `word_subword (chunk0:int128) (112,8):byte`; `word_subword (chunk0:int128) (120,8):byte`] SUBITER_STORE_SPEC)))) 1 in
      let bg4_imp = prove(mk_imp(concl f0d, bg4_concl),
        DISCH_THEN(fun f0eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[SUBWORD_USHR] THEN CONV_TAC NUM_REDUCE_CONV THEN
          SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
          REWRITE_TAC[f0eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC)) in
      ASSUME_TAC (MP bg4_imp f0d)) THEN
  (* MASKBIT forall derived NOW (f1bnd word_join def still present): bit 7(f1bnd lane k) <=>
     EL k[chunk0 nibbles]<9. ASSUME it — survives the DROP below + downstream purges. Used by
     counter stage 3b. *)
  W(fun (asl,w) ->
      let f1d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f1bnd:int256`) (map snd asl) in
      let maskbit_imp = prove
       (mk_imp(concl f1d,
        `!k. k < 8 ==> (bit 7 (word_subword (f1bnd:int256) (8*(k+16),8):byte) <=>
            EL k ([val(word_subword (chunk0:int128) (64,8):byte) MOD 16; val(word_subword chunk0 (64,8):byte) DIV 16;
                  val(word_subword chunk0 (72,8):byte) MOD 16; val(word_subword chunk0 (72,8):byte) DIV 16;
                  val(word_subword chunk0 (80,8):byte) MOD 16; val(word_subword chunk0 (80,8):byte) DIV 16;
                  val(word_subword chunk0 (88,8):byte) MOD 16; val(word_subword chunk0 (88,8):byte) DIV 16]:num list) < 9)`),
        DISCH_THEN(fun f1eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `k<8 ==> k=0\/k=1\/k=2\/k=3\/k=4\/k=5\/k=6\/k=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
          REWRITE_TAC[f1eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN
          W(fun (asl2,w2) ->
             let nibarg = find_term (fun u -> match u with
                Comb(Comb(Const("MOD",_),_),_) | Comb(Comb(Const("DIV",_),_),_) -> true | _ -> false) w2 in
             let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_subword" &&
               type_of u = `:byte` && can(find_term(fun v->v=`chunk0:int128`)) u with _->false) w2 in
             let valeq = prove(mk_eq(mk_comb(`val:byte->num`, mk_comb(`word:num->byte`, nibarg)), nibarg),
                REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let nlt16 = prove(mk_binop `(<):num->num->bool` nibarg `16`,
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let vp = REWRITE_RULE[valeq] (SPEC (mk_comb(`word:num->byte`, nibarg)) VPSUBB_SIGN_BIT_LT_9) in
             ACCEPT_TAC (MP vp nlt16)))) in
      ASSUME_TAC (MP maskbit_imp f1d)) THEN
  W(fun (asl,w) ->
      let f1d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f1bnd:int256`) (map snd asl) in
      let maskbit_imp = prove
       (mk_imp(concl f1d,
        `!k. k < 8 ==> (bit 7 (word_subword (f1bnd:int256) (8*(k+24),8):byte) <=>
            EL k ([val(word_subword (chunk0:int128) (96,8):byte) MOD 16; val(word_subword chunk0 (96,8):byte) DIV 16;
                  val(word_subword chunk0 (104,8):byte) MOD 16; val(word_subword chunk0 (104,8):byte) DIV 16;
                  val(word_subword chunk0 (112,8):byte) MOD 16; val(word_subword chunk0 (112,8):byte) DIV 16;
                  val(word_subword chunk0 (120,8):byte) MOD 16; val(word_subword chunk0 (120,8):byte) DIV 16]:num list) < 9)`),
        DISCH_THEN(fun f1eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `k<8 ==> k=0\/k=1\/k=2\/k=3\/k=4\/k=5\/k=6\/k=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
          REWRITE_TAC[f1eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN
          W(fun (asl2,w2) ->
             let nibarg = find_term (fun u -> match u with
                Comb(Comb(Const("MOD",_),_),_) | Comb(Comb(Const("DIV",_),_),_) -> true | _ -> false) w2 in
             let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_subword" &&
               type_of u = `:byte` && can(find_term(fun v->v=`chunk0:int128`)) u with _->false) w2 in
             let valeq = prove(mk_eq(mk_comb(`val:byte->num`, mk_comb(`word:num->byte`, nibarg)), nibarg),
                REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let nlt16 = prove(mk_binop `(<):num->num->bool` nibarg `16`,
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let vp = REWRITE_RULE[valeq] (SPEC (mk_comb(`word:num->byte`, nibarg)) VPSUBB_SIGN_BIT_LT_9) in
             ACCEPT_TAC (MP vp nlt16)))) in
      ASSUME_TAC (MP maskbit_imp f1d)) THEN
  W(fun (asl,w) ->
      let f1d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f1bnd:int256`) (map snd asl) in
      let maskbit_imp2 = prove
       (mk_imp(concl f1d,
        `!k. k < 8 ==> (bit 7 (word_subword (f1bnd:int256) (8*(k+8),8):byte) <=>
            EL k ([val(word_subword (chunk0:int128) (32,8):byte) MOD 16; val(word_subword chunk0 (32,8):byte) DIV 16;
                  val(word_subword chunk0 (40,8):byte) MOD 16; val(word_subword chunk0 (40,8):byte) DIV 16;
                  val(word_subword chunk0 (48,8):byte) MOD 16; val(word_subword chunk0 (48,8):byte) DIV 16;
                  val(word_subword chunk0 (56,8):byte) MOD 16; val(word_subword chunk0 (56,8):byte) DIV 16]:num list) < 9)`),
        DISCH_THEN(fun f1eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `k<8 ==> k=0\/k=1\/k=2\/k=3\/k=4\/k=5\/k=6\/k=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
          REWRITE_TAC[f1eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN
          W(fun (asl2,w2) ->
             let nibarg = find_term (fun u -> match u with
                Comb(Comb(Const("MOD",_),_),_) | Comb(Comb(Const("DIV",_),_),_) -> true | _ -> false) w2 in
             let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_subword" &&
               type_of u = `:byte` && can(find_term(fun v->v=`chunk0:int128`)) u with _->false) w2 in
             let valeq = prove(mk_eq(mk_comb(`val:byte->num`, mk_comb(`word:num->byte`, nibarg)), nibarg),
                REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let nlt16 = prove(mk_binop `(<):num->num->bool` nibarg `16`,
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let vp = REWRITE_RULE[valeq] (SPEC (mk_comb(`word:num->byte`, nibarg)) VPSUBB_SIGN_BIT_LT_9) in
             ACCEPT_TAC (MP vp nlt16)))) in
      ASSUME_TAC (MP maskbit_imp2 f1d)) THEN
  W(fun (asl,w) ->
      let f1d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f1bnd:int256`) (map snd asl) in
      (* prove `f1bnd = wj ==> (!k...)` as a CLOSED implication (f1d discharged as antecedent,
         so the result has NO extra hyps), then MP with f1d. The DISCH'd eq is used to rewrite. *)
      let maskbit_imp = prove
       (mk_imp(concl f1d,
        `!k. k < 8 ==> (bit 7 (word_subword (f1bnd:int256) (8*k,8):byte) <=>
            EL k ([val(word_subword (chunk0:int128) (0,8):byte) MOD 16; val(word_subword chunk0 (0,8):byte) DIV 16;
                  val(word_subword chunk0 (8,8):byte) MOD 16; val(word_subword chunk0 (8,8):byte) DIV 16;
                  val(word_subword chunk0 (16,8):byte) MOD 16; val(word_subword chunk0 (16,8):byte) DIV 16;
                  val(word_subword chunk0 (24,8):byte) MOD 16; val(word_subword chunk0 (24,8):byte) DIV 16]:num list) < 9)`),
        DISCH_THEN(fun f1eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `k<8 ==> k=0\/k=1\/k=2\/k=3\/k=4\/k=5\/k=6\/k=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
          REWRITE_TAC[f1eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN
          W(fun (asl2,w2) ->
             let nibarg = find_term (fun u -> match u with
                Comb(Comb(Const("MOD",_),_),_) | Comb(Comb(Const("DIV",_),_),_) -> true | _ -> false) w2 in
             let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_subword" &&
               type_of u = `:byte` && can(find_term(fun v->v=`chunk0:int128`)) u with _->false) w2 in
             let valeq = prove(mk_eq(mk_comb(`val:byte->num`, mk_comb(`word:num->byte`, nibarg)), nibarg),
                REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let nlt16 = prove(mk_binop `(<):num->num->bool` nibarg `16`,
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let vp = REWRITE_RULE[valeq] (SPEC (mk_comb(`word:num->byte`, nibarg)) VPSUBB_SIGN_BIT_LT_9) in
             ACCEPT_TAC (MP vp nlt16)))) in
      ASSUME_TAC (MP maskbit_imp f1d)) THEN
  (* DROP f0sub/f1bnd word_join defs BEFORE vpmovmskb (s11).
     This keeps R8/R9's vpmovmskb+popcount over the OPAQUE `f1bnd` var (via the
     `read YMM1 s10 = f1bnd` fold) instead of the expanded word_join, so stage d's popeq / low8 /
     BOOL_CASES (over `word_subword f1bnd (8k,8)`) match the popcount term. Without this, R9 s21 =
     popcount(...word_join expanded...) and stage d leaves unsolved goals. *)
  REPEAT(FIRST_X_ASSUM(fun th ->
     if is_eq(concl th) && (lhand(concl th) = `f0sub:int256` || lhand(concl th) = `f1bnd:int256`)
     then ALL_TAC else failwith "keep")) THEN
  (* ---- STEP s11-s17 FIRST (vpmovmskb, vextracti128, movzbl R10 capture, vmovq, vpshufb,
     vpmovsxbd, vmovdqu store), keeping f0sub/f1bnd defs. The gather/mask SUBGOALs are proven
     AFTER stepping: their `EL j [...]`-shaped assumptions confuse X86_VSTEPS' simulator
     (vextracti128 at s12 fails with "mk_comb: types do not agree" if they're in context). ---- *)
  X86_VSTEPS_TAC EXEC (11--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM1 s10 = f1bnd:int256`]) THEN
  PURGE_STALE_STATES_TAC ["s10"] THEN
  X86_VSTEPS_TAC EXEC (12--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s11 = f0sub:int256`]) THEN
  PURGE_STALE_STATES_TAC ["s11"] THEN
  REABBREV_TAC `mask8 = read R8 s12` THEN
  X86_VERBOSE_STEP_TAC EXEC "s13" THEN
  MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s12 = mask8:int64`]) THEN
  (SUBGOAL_THEN maskbit_tgt ASSUME_TAC THENL [MASKBIT_TGT_TAC; ALL_TAC]) THEN
  X86_VSTEPS_TAC EXEC (14--14) THEN
  TAB1_TEQ_TAC THEN
  REABBREV_TAC `tab1 = read YMM6 s14` THEN
  X86_VSTEPS_TAC EXEC (15--15) THEN REABBREV_TAC `pshuf1 = read YMM6 s15` THEN
  PURGE_STALE_STATES_TAC ["s14"] THEN
  X86_VSTEPS_TAC EXEC (16--16) THEN REABBREV_TAC `sx1 = read YMM1 s16` THEN
  (* stepA: establish sx1 = usimd8 word_sx (word_zx(word_zx pshuf1)) (the vpmovsxbd lane form). *)
  SUBGOAL_THEN `sx1:int256 = usimd8 (\b:byte. word_sx b:int32) (word_zx(word_zx (pshuf1:int256):int128):int64)` ASSUME_TAC THENL
   [W(fun (asl,w) ->
       let sx1def = find (fun th -> is_eq(concl th) && rand(concl th)=`sx1:int256` &&
           can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
       SUBST1_TAC(SYM sx1def) THEN
       REWRITE_TAC[usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
       CONV_TAC WORD_BLAST);
    ALL_TAC] THEN
  PURGE_STALE_STATES_TAC ["s15"] THEN
  X86_STEPS_TAC EXEC (17--17) THEN
  PURGE_STALE_STATES_TAC ["s16"] THEN
  X86_STEPS_TAC EXEC (18--21) THEN
  MP_TAC(ISPECL[`inlist:byte list`;`i:num`;`chunk0:int128`] SUBITER_BLOCK_BYTES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `LENGTH(inlist:byte list) = 272` THEN
    UNDISCH_TAC `16 * i <= 256` THEN ARITH_TAC; STRIP_TAC] THEN
  W(fun (asl,w) ->
     let m8def = find (fun th -> match concl th with Comb(Comb(Const("=",_),_),Var("mask8",_)) -> true | _ -> false) (map snd asl) in
     RULE_ASSUM_TAC(fun th -> if concl th = maskbit_tgt ||
        can(find_term(fun u->match u with Const("TABLE_ENTRY",_)->true|_->false))(concl th)
        then th else REWRITE_RULE[GSYM m8def] th)) THEN
  (* === REORDERED branch resolution (NO RULE_ASSUM over s21 state) ===      *)
  W(fun (asl,w) ->
    (* 1. popeq: word_popcount(word_zx^3(word(val mask8 MOD 256))) = bitsum8(low8 of f1bnd) *)
    let r9 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("R9",_)),Var("s21",_))),_) -> true | _ -> false) asl in
    let goal_pc = find_term (fun t -> match t with Comb(Const("word_popcount",_),_) -> true | _ -> false) (concl(snd r9)) in
    let low8 = `bitval(bit 7 (word_subword (f1bnd:int256) (0,8):byte)) + bitval(bit 7 (word_subword f1bnd (8,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (16,8):byte)) + bitval(bit 7 (word_subword f1bnd (24,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (32,8):byte)) + bitval(bit 7 (word_subword f1bnd (40,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (48,8):byte)) + bitval(bit 7 (word_subword f1bnd (56,8):byte))` in
    let mr = CONV_RULE(DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV)
               (SPEC `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` MOD_RED) in
    let popeq = prove(mk_eq(goal_pc, low8),
      REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
      REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; MOD_MOD_EXP_MIN] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; mr] THEN
      MAP_EVERY (fun b -> BOOL_CASES_TAC b)
        [`bit 7 (word_subword (f1bnd:int256) (0,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (8,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (16,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (24,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (32,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (40,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (48,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (56,8):byte)`] THEN
      REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV) in
    (* 2. bitsum8 = LENGTH(REJ_NIBBLES block0) via maskbit forall + block byte facts *)
    let maskbit = snd(find (fun (_,th) -> let c=concl th in is_forall c &&
        can(find_term(fun u->u=`f1bnd:int256`))c && can(find_term(fun u->match u with Comb(Const("bit",_),_)->true|_->false))c &&
        not(can(find_term(fun u->match u with Const("word_zx",_)->true|_->false))c) &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (24,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (32,8):byte`))c)) asl) in
    let mb_tm = concl maskbit in
    let mb_assumed = ASSUME mb_tm in
    let mbits = map (fun k -> let th=SPEC(mk_small_numeral k) mb_assumed in
         CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
    let blk0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
           (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
    let blkeq = mk_eq(low8, `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list)`) in
    let blk0_tm = concl(snd blk0) in
    let bsum_raw = prove(mk_imp(mb_tm, mk_imp(blk0_tm, blkeq)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN DISCH_THEN(fun b -> REWRITE_TAC[b]) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER] THEN
      ASM_SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let bsum = MP (MP bsum_raw maskbit) (snd blk0) in
    (* combined: word_popcount(...) = LENGTH(REJ_NIBBLES block0)             *)
    let pop_len = TRANS popeq bsum in
    (* 3. bound: outlen0 + LENGTH(REJ_NIBBLES block0) <= 248                 *)
    let leninl = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Var("inlist",_))),_) -> true | _ -> false) asl in
    let i116 = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("<=",_),Comb(Comb(Const("*",_),_),Comb(Comb(Const("+",_),Var("i",_)),_))),_) -> true | _ -> false) asl in
    let nible = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("<=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_NIBBLES_ETA4",_),_))),_) -> true | _ -> false) asl in
    let len_eq = find (fun (_,th) -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) asl in
    let a1 = MP (MP (ARITH_RULE `16*(i+1)<=272 ==> (LENGTH(inlist:byte list)=272 ==> 16*(i+1)<=LENGTH inlist)`)
                    (snd i116)) (snd leninl) in
    let bnd0 = MP (ISPECL[`inlist:byte list`;`i:num`] SUBITER_OUTLEN_BOUND_1) (CONJ a1 (snd nible)) in
    let bnd = REWRITE_RULE[snd len_eq] bnd0 in  (* outlen0 + LENGTH(REJ_NIBBLES block0) <= 248 *)
    (* 4. RAX collapse: word_zx(word_add(word_zx(word outlen0))(word_zx(word_zx(word popcount)))) = word(outlen0+block0len) *)
    let block0len = `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list)` in
    let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in  (* word_zx(...word outlen0...word block0len...) = word(outlen0+block0len) *)
    (* but RAX has popcount, not block0len; rewrite popcount->block0len first via pop_len *)
    let rax_red = REWRITE_RULE[pop_len] (GSYM(REWRITE_RULE[GSYM pop_len] (SYM rax_red0))) in
    (* JA_NOT_TAKEN: outlen0+block0len <= 248                                *)
    let ja = MP (ISPECL[mk_binop `(+):num->num->num` `outlen0:num` block0len; `248`] JA_NOT_TAKEN_LE)
                (CONJ bnd (ARITH_RULE `248 < 2 EXP 32`)) in
    (* stash these as assumptions for the step                               *)
    ASSUME_TAC pop_len THEN ASSUME_TAC bnd THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja) THEN
  X86_STEPS_TAC EXEC (22--23) THEN
  (* resolve the ja branch: RIP s23 = pc+163 (fall through to sub-iter 2)    *)
  SUBGOAL_THEN `read RIP s23 = word (pc + 163):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let blk0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
             (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
      let rax_red0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
      let ja = find (fun (_,th) -> is_disj(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th)) asl in
      rip_mp memsafe 163 23 THEN
      REWRITE_TAC[GSYM(snd blk0)] THEN REWRITE_TAC[snd rax_red0] THEN
      REWRITE_TAC[snd ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  (* fold RAX read clean using the assumed pop_len + rax_red0 (now in asl)   *)
  W(fun (asl,w) ->
    let pl = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl in
    let rr = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
    RULE_ASSUM_TAC(REWRITE_RULE[snd pl]) THEN RULE_ASSUM_TAC(REWRITE_RULE[snd rr])) THEN
  ALL_TAC);;

let PREFIX_G_FULL_TAC : tactic = mk_prefix_g_full false;;

(* --- si1_fold_v2 ---                                                       *)
(* SI1_FOLD_V2: sub-iter-1 store recombination. gather forall + maskbit_tgt are
   ALREADY ASSUMEd by PREFIX_G_FULL_TAC, so fetch them from asl (no SUBGOAL_THEN). Only
   pf_target is a real subgoal, discharged by PF_PROOF (genuine table-load bridge). *)
let SI1_FOLD_V2 : tactic =
  SUBGOAL_THEN pf_target (fun pfth ->
    W(fun (asl,w) ->
      let asms = map snd asl in
      let bg = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f0sub:int256`))c &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))c &&
          not(can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))c) &&
          can(find_term(fun u->u=`word_subword (chunk0:int128) (24,8):byte`))c) asms in
      let mthm = find (fun th -> concl th = maskbit_tgt) asms in
      let storef = find (fun th -> can(find_term(fun u->match u with Const("bytes256",_)->true|_->false))(concl th) &&
          can(find_term(fun u->match u with Const("usimd8",_)->true|_->false))(concl th) &&
          (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s23",_))),_)->true|_->false)) asms in
      let store_full = REWRITE_RULE[pfth] storef in
      let g = `word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128` in
      let m = `word (val (mask8:int64) MOD 256):byte` in
      let pc = ISPECL [`word_add res (word (4 * outlen0)):int64`; `s23:x86state`; g; m; `LENGTH(ACC_IDX (word (val (mask8:int64) MOD 256):byte))`] SUBITER_STORE_POSTCOND in
      let res_th0 = MP pc (CONJ (SPEC m LACC8) store_full) in
      let spec = ISPECL [g; m; `word_subword (chunk0:int128) (0,8):byte`; `word_subword (chunk0:int128) (8,8):byte`; `word_subword (chunk0:int128) (16,8):byte`; `word_subword (chunk0:int128) (24,8):byte`] SUBITER_STORE_SPEC in
      let gather_hyp = List.nth (conjuncts(lhand(concl spec))) 1 in
      let gthm = EQ_MP (SYM(REWRITE_CONV[WORD_ZX_TRIVIAL] gather_hyp)) bg in
      let specres = MP spec (CONJ mthm gthm) in
      let rej_store = REWRITE_RULE[specres] res_th0 in
      let hasC nm th = can (find_term (fun u -> match u with Const(n,_) when n=nm -> true | _ -> false)) (concl th) in
      let blk = `[word_subword (chunk0:int128) (0,8); word_subword chunk0 (8,8); word_subword chunk0 (16,8); word_subword chunk0 (24,8)]:byte list` in
      let prefixbytes = `SUB_LIST(0,16*i) (inlist:byte list)` in
      let prefix_store = find (fun th ->
           (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s23",_))),_) -> true | _ -> false) &&
           hasC "num_of_wordlist" th && hasC "SUB_LIST" th &&
           can(find_term(fun u->u=`res:int64`))(lhand(concl th)) &&
           can(find_term(fun u->u=`outlen0:num`))(lhand(concl th)) &&
           not(hasC "ACC_IDX" th)) asms in
      let len_eq = find (fun th -> match concl th with
           Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) asms in
      let blk16 = find (fun th -> is_eq(concl th) && hasC "SUB_LIST" th &&
           (try length(dest_list(rand(concl th))) = 16 with _ -> false)) asms in
      let leninl = find (fun th -> match concl th with
           Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Var("inlist",_))),_) -> true | _ -> false) asms in
      let i116 = find (fun th -> match concl th with
           Comb(Comb(Const("<=",_),Comb(Comb(Const("*",_),_),Comb(Comb(Const("+",_),Var("i",_)),_))),_) -> true | _ -> false) asms in
      let lenle = REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*(i+1) <= 272 ==> 16*i+16 <= 272`) i116) in
      let lr = MP (ISPECL [m; `chunk0:int128`] LEN_RECONCILE) mthm in
      let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES) (CONJ lenle blk16) in
      let blk_bytes = CONJUNCT1 bb in
      let rej_store2 = REWRITE_RULE[SYM len_eq] rej_store in
      let prefix_store2 = REWRITE_RULE[SYM len_eq] prefix_store in
      let fold = MP (ISPECL [`res:int64`;`s23:x86state`;m;blk;prefixbytes] SUBITER_FOLD_STEP)
                    (CONJ lr (CONJ prefix_store2 rej_store2)) in
      let split0 = REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i`;`4`;`0`] SUB_LIST_SPLIT) in
      let clean = REWRITE_RULE[GSYM blk_bytes; GSYM split0] fold in
      ASSUME_TAC clean))
  THENL [PF_PROOF; ALL_TAC];;

(* --- maskbit_tgt_2_tac ---                                                 *)
(* maskbit_tgt_2 + MASKBIT_TGT_2_TAC: sub-iter-2 analog of maskbit_tgt/MASKBIT_TGT_TAC.
   mask8b = R8 after the ushr-by-8 (= bits 8-15 of SUM32). maskbit_tgt_2 relates
   bit j (word(val mask8b MOD 256)) to chunk0 nibbles 32,40,48,56 (lanes 8-15) < 9.
   KEY EXTRA vs si1: val mask8b MOD 256 = (SUM32 DIV 256) MOD 256 (MASK_SHIFT8_MOD256);
   regroup SUM32 = SUM_low8 + 256*SUM8' + 65536*SUM_high16 (ARITH, linear in bitvals);
   DIVMOD256_SPLIT extracts SUM8' (= the lanes-8-15 8-term bitsum). Then same MASK_LOW_BIT
   + lanes-8-15 maskbit forall mechanism as si1. valeq MUST be folded via REWRITE_RULE[m8b]
   so its LHS is `val mask8b MOD 256` (not the unfolded word_zx tower). *)
let maskbit_tgt_2 =
  `!j. j < 8 ==> (bit j (word (val (mask8b:int64) MOD 256):byte) <=>
       EL j [val(word_subword (chunk0:int128) (32,8):byte) MOD 16;
         val(word_subword chunk0 (32,8):byte) DIV 16; val(word_subword chunk0 (40,8):byte) MOD 16;
         val(word_subword chunk0 (40,8):byte) DIV 16; val(word_subword chunk0 (48,8):byte) MOD 16;
         val(word_subword chunk0 (48,8):byte) DIV 16; val(word_subword chunk0 (56,8):byte) MOD 16;
         val(word_subword chunk0 (56,8):byte) DIV 16] < 9)`;;

let TAB2_TEQ_TAC : tactic = mk_tab_teq 25 26 `mask8b:int64` RLT_B R_EQ_B;;

(* --- si2_fold_pieces ---                                                   *)
(* Sub-iter-2 store-fold pieces (gather-side ingredients + fold-carry-forward
   across states). *)

(* PF_PROOF_2: discharge the sub-iter-2 `pshuf2 = pf_target_2` subgoal.      *)
let PF_PROOF_2 : tactic = mk_pf_proof `pshuf2:int256` `tab2:int256`;;

(* --- si2_fold_complete ---                                                 *)
(* Sub-iter-2 store fold COMPLETE +. The full generalized mechanism:
   gather (bg2 early) + maskbit_tgt_2 + teq2 + pf_target_2 + SUBITER_STORE_SPEC fold + carry-forward.
   KEY: the running prefix store must be stated with length = acc1 (the next write's offset var) so
   it carries past the s29 vpmovdqu write; acc1_ident bridges LENGTH(REJ_SAMPLE(SUB_LIST(0,16i+4)))=acc1.
   Load after main + cbb_defs + .pf_target_proof + .maskbit_tgt_2_tac + .tab2_teq_tac + .si2_fold_pieces. *)

(* LEN_RECONCILE_GEN: LEN_RECONCILE generalized to arbitrary 4 block bytes b0..b3 (si1 had block0
   hardcoded). Needed because sub-iter k's block bytes are chunk0 (32,40,48,56) etc, not (0,8,16,24). *)
let LEN_RECONCILE_GEN = prove
 (`!(m:byte) (b0:byte) (b1:byte) (b2:byte) (b3:byte).
     (!j. j < 8 ==> (bit j m <=>
        EL j [val b0 MOD 16; val b0 DIV 16; val b1 MOD 16; val b1 DIV 16;
              val b2 MOD 16; val b2 DIV 16; val b3 MOD 16; val b3 DIV 16] < 9))
     ==> LENGTH(ACC_IDX m) =
         LENGTH(REJ_SAMPLE_ETA4_BYTES [b0;b1;b2;b3]:int32 list)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:byte`;
    `word(val(b0:byte) MOD 16):byte`; `word(val(b0:byte) DIV 16):byte`;
    `word(val(b1:byte) MOD 16):byte`; `word(val(b1:byte) DIV 16):byte`;
    `word(val(b2:byte) MOD 16):byte`; `word(val(b2:byte) DIV 16):byte`;
    `word(val(b3:byte) MOD 16):byte`; `word(val(b3:byte) DIV 16):byte`] ACC_LENGTH_EQ_FILTER) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    W(fun (asl,gw) -> let n = rand(rator(lhand gw)) in
       MP_TAC(SPEC n (find (fun th -> is_forall(concl th) && can(find_term(fun u->match u with Const("EL",_)->true|_->false))(concl th)) (map snd asl)))) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    DISCH_THEN SUBST1_TAC THEN
    W(fun (asl,gw) -> let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="val" && type_of(rand u)=`:byte` with _->false) gw in
       let bt = rand bt in
       MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN STRIP_TAC THEN
       SUBGOAL_THEN (mk_eq(mk_comb(`val:byte->num`,mk_comb(`word:num->byte`,mk_binop `MOD` (mk_comb(`val:byte->num`,bt)) `16`)), mk_binop `MOD` (mk_comb(`val:byte->num`,bt)) `16`)) SUBST1_TAC THENL
        [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
       SUBGOAL_THEN (mk_eq(mk_comb(`val:byte->num`,mk_comb(`word:num->byte`,mk_binop `DIV` (mk_comb(`val:byte->num`,bt)) `16`)), mk_binop `DIV` (mk_comb(`val:byte->num`,bt)) `16`)) SUBST1_TAC THENL
        [REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
       REFL_TAC);
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[LENGTH_FILTER_BYTE_NIBBLES_4_BYTES; LENGTH_REJ_SAMPLE_ETA4_BYTES]]);;

(* ACC1_IDENT_TAC: prove & ASSUME `LENGTH(REJ_SAMPLE(SUB_LIST(0,16i+4)))=acc1` (acc1 must be ABBREV'd
   as outlen0 + LENGTH(REJ_NIBBLES(SUB_LIST(16i,4))), outlen0 def + that ABBREV in asl). Re-run right
   before each fold (it gets consumed by the store-address restate). *)
let ACC1_IDENT_TAC : tactic =
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) = acc1` ASSUME_TAC THENL
  [ONCE_REWRITE_TAC[REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i`;`4`;`0`] SUB_LIST_SPLIT)] THEN
   REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES; REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND] THEN
   FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_))->true|_->false)
       then ASSUME_TAC(REWRITE_RULE[LENGTH_REJ_SAMPLE_ETA4_BYTES] th) else NO_TAC) THEN
   FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_NIBBLES_ETA4",_),_))),Var("outlen0",_))->true|_->false)
       then REWRITE_TAC[th] else NO_TAC) THEN
   FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),_),Var("acc1",_))->can(find_term(fun u->u=`outlen0:num`))(concl th)|_->false) then (MP_TAC th THEN ARITH_TAC) else NO_TAC); ALL_TAC];;

let SI2_MG_TAC : tactic =
W(fun (asl,w) ->
  let asms = map snd asl in
  let find_a p = find p asms in
  let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
  let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
  let popcnt2 = REWRITE_RULE[m8b_def]
     (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE1)) in
  let lanesum8 = rand(concl popcnt2) in
  let mb2 = find_a (fun th -> let c=concl th in is_forall c &&
     can(find_term(fun u->u=`f1bnd:int256`))c &&
     can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),_) -> true | _ -> false))c) in
  let mb2_tm = concl mb2 in
  let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
  let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
  let blk16 = find_a (fun th -> is_eq(concl th) &&
     (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" &&
          length(dest_list(rand(concl th)))=16 with _->false)) in
  let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
              (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le))
                    blk16) in
  let blk1_eq = el 1 (CONJUNCTS bb) in
  let block1 = `[word_subword (chunk0:int128) (32,8); word_subword chunk0 (40,8);
                 word_subword chunk0 (48,8); word_subword chunk0 (56,8)]:byte list` in
  let block1len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA4`, block1)) in
  let bsum2_raw = prove(mk_imp(mb2_tm, mk_eq(lanesum8, block1len_x)),
    DISCH_THEN(fun mbthm ->
      let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
        CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV)
          (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
      REWRITE_TAC mbs) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
    REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER] THEN
    SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
  (* fold explicit block1 -> SUB_LIST(16i+4,4) via blk1_eq (GSYM)            *)
  let pop_len2 = REWRITE_RULE[GSYM blk1_eq] (TRANS popcnt2 (MP bsum2_raw mb2)) in
  (* bound: outlen0 + niblen(block0) + block1len <= 248                      *)
  let i116 = find_a (fun th -> concl th = `16 * (i + 1) <= 272`) in
  let nibbnd = find_a (fun th -> concl th = `LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (0,16 * (i + 1)) inlist):int16 list) <= 248`) in
  let a1 = MP (MP (ARITH_RULE `16*(i+1)<=272 ==> (LENGTH(inlist:byte list)=272 ==> 16*(i+1)<=LENGTH inlist)`) i116) leninl in
  let bnd2 = MP (ISPECL[`inlist:byte list`;`i:num`] SUBITER_OUTLEN_BOUND_2) (CONJ a1 nibbnd) in
  (* acc1 = outlen0 + niblen(block0); outlen0 = LENGTH(REJ_SAMPLE...(SUB_LIST(0,16i))). Rewrite bnd2's
     first two terms into acc1. *)
  let outlen0_def = find_a (fun th -> match concl th with
     Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) in
  let acc1_def = find_a (fun th -> match concl th with
     Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),_),_)),Var("acc1",_)) -> true | _ -> false) in
  (* bnd2 : LENGTH(REJ_SAMPLE(SUB_LIST(0,16i))) + niblen(SUB_LIST(16i,4)) + block1len <= 248
     rewrite LENGTH(REJ_SAMPLE...) -> outlen0, then (outlen0 + niblen(...)) -> acc1. *)
  let bnd2a = REWRITE_RULE[outlen0_def; ADD_ASSOC] bnd2 in
  let bnd2c = REWRITE_RULE[acc1_def] bnd2a in
  (* bnd2c : acc1 + block1len <= 248                                         *)
  let block1len = `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+4,4) inlist):int16 list)` in
  let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd2c in
  let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
  let ja = MP (ISPECL[mk_binop `(+):num->num->num` `acc1:num` block1len; `248`] JA_NOT_TAKEN_LE)
              (CONJ bnd2c (ARITH_RULE `248 < 2 EXP 32`)) in
  ASSUME_TAC pop_len2 THEN ASSUME_TAC bnd2c THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja);;

let SI2_RESOLVE : tactic =
  X86_STEPS_TAC EXEC (34--35) THEN
  SUBGOAL_THEN `read RIP s35 = word (pc + 215):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let asms = map snd asl in
      let pop_len2_old = find (fun th -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asms in
      let zbe = MP (SPEC `val (mask8b:int64) MOD 256` zxbyte_eq) (ARITH_RULE `val (mask8b:int64) MOD 256 < 256`) in
      let pop_len2_typed = TRANS (AP_TERM `word_popcount:int32->num` zbe) pop_len2_old in
      let rax_red0 = find (fun th -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asms in
      let ja = find (fun th -> is_disj(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`acc1:num`))(concl th)) asms in
      let ifrip = find (fun th -> match concl th with
         Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),Var("s35",_))),r) ->
           (match r with Comb(Comb(Comb(Const("COND",_),_),_),_) -> true | _ -> false) | _ -> false) asms in
      MP_TAC ifrip THEN REWRITE_TAC[pop_len2_typed] THEN REWRITE_TAC[rax_red0] THEN
      REWRITE_TAC[ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC];;

(* --- si2_integrated ---                                                    *)
(* SI2_INTEGRATED: complete sub-iter-2 = gather + store-fold + counter + mid-guard.
   From post-SI1 s23 (RIP=pc+163, si1 clean store for SUB_LIST(0,16i+4) present), reaches s35 RIP=pc+215
   with the running clean store folded to SUB_LIST(0,16i+8). Composes SI2_GATHER_TO_STORE +
   ACC1_IDENT/restate + the si2 fold W + SI2_MG_TAC + SI2_RESOLVE.
   Load deps: .pf_target_proof, .maskbit_tgt_2_tac, .tab2_teq_tac, .si2_fold_pieces, .si2_fold_complete, .si2_full.
   NB the si1 store must FIRST be restated to bytes(res,4*acc1) (via ACC1_IDENT) BEFORE the gather, so it
   carries past the s29 vpmovdqu. *)
let SI2_INTEGRATED : tactic =
  REABBREV_TAC `mask8b = read R8 s23` THEN
  ABBREV_TAC `acc1 = outlen0 + LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list)` THEN
  ACC1_IDENT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) = acc1`]) THEN
  X86_VSTEPS_TAC EXEC (24--24) THEN
  X86_VERBOSE_STEP_TAC EXEC "s25" THEN MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s24 = mask8b:int64`]) THEN
  X86_VSTEPS_TAC EXEC (26--26) THEN TAB2_TEQ_TAC THEN REABBREV_TAC `tab2 = read YMM6 s26` THEN
  X86_VSTEPS_TAC EXEC (27--27) THEN REABBREV_TAC `pshuf2 = read YMM6 s27` THEN
  PURGE_STALE_STATES_TAC ["s26"] THEN
  X86_VSTEPS_TAC EXEC (28--28) THEN REABBREV_TAC `sx2 = read YMM1 s28` THEN
  VAL_INT64_TAC `acc1:num` THEN
  X86_STEPS_TAC EXEC (29--29) THEN
  SUBGOAL_THEN `sx2:int256 = usimd8 (\b:byte. word_sx b:int32) (word_zx(word_zx (pshuf2:int256):int128):int64)` ASSUME_TAC THENL
   [W(fun (asl,w) ->
       let sx2def = find (fun th -> is_eq(concl th) && rand(concl th)=`sx2:int256` &&
           can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
       SUBST1_TAC(SYM sx2def) THEN
       REWRITE_TAC[usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
       CONV_TAC WORD_BLAST);
    ALL_TAC] THEN
  (SUBGOAL_THEN maskbit_tgt_2 ASSUME_TAC THENL [MASKBIT_TGT_2_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN pf_target_2 ASSUME_TAC THENL [PF_PROOF_2; ALL_TAC]) THEN
  ACC1_IDENT_TAC THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let hasC nm th = can (find_term (fun u -> match u with Const(n,_) when n=nm -> true | _ -> false)) (concl th) in
    let bg2 = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f0sub:int256`))c &&
        can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (32,8):byte`))c) asms in
    let mthm2 = find (fun th -> concl th = maskbit_tgt_2) asms in
    let pfth2 = find (fun th -> concl th = pf_target_2) asms in
    let sx2u = find (fun th -> match concl th with Comb(Comb(Const("=",_),Var("sx2",_)),r)->can(find_term(fun u->match u with Const("usimd8",_)->true|_->false))r|_->false) asms in
    let storef0 = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),m),Var("s29",_))),Var("sx2",_)) -> can(find_term(fun u->match u with Const("bytes256",_)->true|_->false)) m |_->false) asms in
    let store_full = REWRITE_RULE[pfth2] (REWRITE_RULE[sx2u] storef0) in
    let g2 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128) 64):int128):int128` in
    let m = `word (val (mask8b:int64) MOD 256):byte` in
    let pc = ISPECL [`word_add res (word (4 * acc1)):int64`; `s29:x86state`; g2; m; `LENGTH(ACC_IDX (word (val (mask8b:int64) MOD 256):byte))`] SUBITER_STORE_POSTCOND in
    let res_th0 = MP pc (CONJ (SPEC m LACC8) store_full) in
    let spec = ISPECL [g2; m; `word_subword (chunk0:int128) (32,8):byte`; `word_subword (chunk0:int128) (40,8):byte`; `word_subword (chunk0:int128) (48,8):byte`; `word_subword (chunk0:int128) (56,8):byte`] SUBITER_STORE_SPEC in
    let rej_store = REWRITE_RULE[MP spec (CONJ mthm2 bg2)] res_th0 in
    let leninl = find (fun th -> concl th = `LENGTH(inlist:byte list)=272`) asms in
    let i116 = find (fun th -> concl th = `16 * (i + 1) <= 272`) asms in
    let blk16 = find (fun th -> is_eq(concl th) && hasC "SUB_LIST" th && (try length(dest_list(rand(concl th)))=16 with _->false)) asms in
    let bb = MP (ISPECL [`inlist:byte list`;`i:num`;`chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*(i+1)<=272 ==> 16*i+16<=272`) i116)) blk16) in
    let blk1_eq = el 1 (CONJUNCTS bb) in
    let lr0 = MP (ISPECL [m;`word_subword (chunk0:int128) (32,8):byte`;`word_subword (chunk0:int128) (40,8):byte`;`word_subword (chunk0:int128) (48,8):byte`;`word_subword (chunk0:int128) (56,8):byte`] LEN_RECONCILE_GEN) mthm2 in
    let lr = REWRITE_RULE[GSYM blk1_eq] lr0 in
    let rej_store1 = REWRITE_RULE[GSYM blk1_eq] rej_store in
    let acc1_ident = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),Var("acc1",_)) -> true | _ -> false) asms in
    let prefix_store0 = find (fun th -> (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s29",_))),_) -> true | _ -> false) &&
         hasC "num_of_wordlist" th && hasC "SUB_LIST" th && can(find_term(fun u->u=`acc1:num`))(lhand(concl th)) && not(hasC "ACC_IDX" th) && not(hasC "bytes256" th)) asms in
    let prefix_store = REWRITE_RULE[GSYM acc1_ident] prefix_store0 in
    let rej_store2 = REWRITE_RULE[GSYM acc1_ident] rej_store1 in
    let fold = MP (ISPECL [`res:int64`;`s29:x86state`;m;`SUB_LIST(16*i+4,4) (inlist:byte list)`;`SUB_LIST(0,16*i+4) (inlist:byte list)`] SUBITER_FOLD_STEP)
                  (CONJ lr (CONJ prefix_store rej_store2)) in
    let split = REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i+4`;`4`;`0`] SUB_LIST_SPLIT) in
    let clean = REWRITE_RULE[GSYM split; ARITH_RULE `(16*i+4)+4 = 16*i+8`] fold in
    ASSUME_TAC clean) THEN
  X86_STEPS_TAC EXEC (30--33) THEN
  SI2_MG_TAC THEN SI2_RESOLVE;;

(* --- si3_full ---                                                          *)
(* Sub-iter 3: from RIP=pc+215 (after SI2_RESOLVE) to RIP=pc+268 (mid-guard 3 fall-through).
   Mask = mask8c (R8 ushr16, byte 2 -> lanes 16-23, block2 = SUB_LIST(16i+8,4)). Uses PREFIX4's
   lanes-16..23 maskbit + POPCNT_BYTE2. Requires SI2 chain already applied (RIP=pc+215, RAX still
   the unfolded sub-iter-2 popcount nest). *)

(* SI3_PRE: fold RAX s35 -> word acc2, abbrev acc2, reabbrev mask8c, establish acc2<=248. *)
let SI3_PRE : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let pop_len2_old = find (fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asms in
    let zbe = MP (SPEC `val (mask8b:int64) MOD 256` zxbyte_eq) (ARITH_RULE `val (mask8b:int64) MOD 256 < 256`) in
    let pop_len2_typed = TRANS (AP_TERM `word_popcount:int32->num` zbe) pop_len2_old in
    let rax_red0 = find (fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asms in
    RULE_ASSUM_TAC(REWRITE_RULE[pop_len2_typed]) THEN RULE_ASSUM_TAC(REWRITE_RULE[rax_red0])) THEN
  ABBREV_TAC `acc2 = acc1 + LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (16*i+4,4) inlist):int16 list)` THEN
  REABBREV_TAC `mask8c = read R8 s35` THEN
  (* bound acc2 + niblen(16i+8,4) <= 248, then acc2 <= 248                   *)
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
    let i116 = find_a (fun th -> concl th = `16 * (i + 1) <= 272`) in
    let nibbnd = find_a (fun th -> concl th = `LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (0,16 * (i + 1)) inlist):int16 list) <= 248`) in
    let a1 = MP (MP (ARITH_RULE `16*(i+1)<=272 ==> (LENGTH(inlist:byte list)=272 ==> 16*(i+1)<=LENGTH inlist)`) i116) leninl in
    let bnd3 = MP (ISPECL[`inlist:byte list`;`i:num`] SUBITER_OUTLEN_BOUND_3) (CONJ a1 nibbnd) in
    let outlen0_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) in
    let acc1_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),Var("acc1",_)) -> true | _ -> false) in
    let acc2_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),Var("acc2",_)) -> true | _ -> false) in
    let bnd3a = REWRITE_RULE[outlen0_def; ADD_ASSOC] bnd3 in
    let bnd3b = REWRITE_RULE[acc1_def] bnd3a in
    let bnd3c = REWRITE_RULE[acc2_def] (REWRITE_RULE[ADD_ASSOC] bnd3b) in
    ASSUME_TAC bnd3c THEN
    ASSUME_TAC (MATCH_MP (ARITH_RULE `acc2 + x <= 248 ==> acc2 <= 248`) bnd3c)) THEN
  VAL_INT64_TAC `acc2:num`;;

(* SI3_MG: forward facts pop_len3/bnd3c'/rax_red0_3/ja3 for mid-guard 3.     *)
let SI3_MG : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let m8c_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8c:int64` | _ -> false) in
    let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
    let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
    let popcnt3 = REWRITE_RULE[m8b_def; m8c_def]
       (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE2)) in
    let lanesum = rand(concl popcnt3) in
    let mb3 = find_a (fun th -> let c=concl th in is_forall c &&
       can(find_term(fun u->u=`f1bnd:int256`))c &&
       can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),n) -> n=`16` | _ -> false))c) in
    let mb3_tm = concl mb3 in
    let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
    let blk16 = find_a (fun th -> is_eq(concl th) &&
       (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" &&
            length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le)) blk16) in
    let blk2_eq = el 2 (CONJUNCTS bb) in   (* SUB_LIST(16*i+8,4) = [chunk0 64,72,80,88] *)
    let block2 = `[word_subword (chunk0:int128) (64,8); word_subword chunk0 (72,8);
                   word_subword chunk0 (80,8); word_subword chunk0 (88,8)]:byte list` in
    let block2len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA4`, block2)) in
    let bsum3_raw = prove(mk_imp(mb3_tm, mk_eq(lanesum, block2len_x)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV)
            (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER] THEN
      SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let pop_len3 = REWRITE_RULE[GSYM blk2_eq] (TRANS popcnt3 (MP bsum3_raw mb3)) in
    let bnd3c = find_a (fun th -> match concl th with
       Comb(Comb(Const("<=",_),Comb(Comb(Const("+",_),Var("acc2",_)),_)),_) -> true | _ -> false) in
    let block2len = `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+8,4) inlist):int16 list)` in
    let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd3c in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let ja = MP (ISPECL[mk_binop `(+):num->num->num` `acc2:num` block2len; `248`] JA_NOT_TAKEN_LE)
                (CONJ bnd3c (ARITH_RULE `248 < 2 EXP 32`)) in
    ASSUME_TAC pop_len3 THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja);;

(* SI3_RESOLVE: step cmp/ja (s46-47), typed-popcount branch resolution -> RIP s47 = pc+268. *)
let SI3_RESOLVE : tactic =
  X86_STEPS_TAC EXEC (46--47) THEN
  SUBGOAL_THEN `read RIP s47 = word (pc + 268):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let asms = map snd asl in
      let find_a p = find p asms in
      (* The counter step already folded popcnt->LENGTH(REJ_NIBBLES[explicit block2]) into the COND.
         Convert that explicit block2 to SUB_LIST(16i+8,4) form via GSYM blk2_eq so rax_red0/ja match. *)
      let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
      let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
      let blk16 = find_a (fun th -> is_eq(concl th) &&
         (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" && length(dest_list(rand(concl th)))=16 with _->false)) in
      let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                  (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le)) blk16) in
      let blk2_eq = el 2 (CONJUNCTS bb) in
      let rax_red0 = find (fun th -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) ->
            can(find_term(fun u->u=`acc2:num`))(concl th) | _ -> false) asms in
      let ja = find (fun th -> is_disj(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`acc2:num`))(concl th)) asms in
      let ifrip = find (fun th -> match concl th with
         Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),Var("s47",_))),r) ->
           (match r with Comb(Comb(Comb(Const("COND",_),_),_),_) -> true | _ -> false) | _ -> false) asms in
      MP_TAC ifrip THEN REWRITE_TAC[GSYM blk2_eq] THEN REWRITE_TAC[rax_red0] THEN
      REWRITE_TAC[ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC];;

(* --- si3_fold_pieces ---                                                   *)
(* Sub-iter-3 fold pieces. g3 = hi 128 lane (no shift) = word_zx(word_zx(word_subword f0sub (128,128))).
   mask8c (R8 ushr16), block2 = SUB_LIST(16i+8,4), lanes 16-23. Load after main+cbb+pf_target_proof+
   si2_fold_complete (DIVMOD256_SPLIT, ACC1_IDENT_TAC) + .si3_full (SI3_PRE/MG/RESOLVE). *)

let maskbit_tgt_3 =
  `!j. j < 8 ==> (bit j (word (val (mask8c:int64) MOD 256):byte) <=>
       EL j [val(word_subword (chunk0:int128) (64,8):byte) MOD 16;
         val(word_subword chunk0 (64,8):byte) DIV 16; val(word_subword chunk0 (72,8):byte) MOD 16;
         val(word_subword chunk0 (72,8):byte) DIV 16; val(word_subword chunk0 (80,8):byte) MOD 16;
         val(word_subword chunk0 (80,8):byte) DIV 16; val(word_subword chunk0 (88,8):byte) MOD 16;
         val(word_subword chunk0 (88,8):byte) DIV 16] < 9)`;;

let TAB3_TEQ_TAC : tactic = mk_tab_teq 37 38 `mask8c:int64` RLT_C R_EQ_C;;

let PF_PROOF_3 : tactic = mk_pf_proof `pshuf3:int256` `tab3:int256`;;

(* ACC2_IDENT_TAC: prove & ASSUME LENGTH(REJ_SAMPLE(SUB_LIST(0,16i+8)))=acc2 by forward inference
   (non-destructive; needs acc1_ident [LENGTH REJ_SAMPLE form] + acc2 ABBREV def in asl). *)
let ACC2_IDENT_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let acc1_ident = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),Var("acc1",_))->true|_->false) asms in
    let acc2_def = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),Var("acc2",_))->true|_->false) asms in
    let split = REWRITE_RULE[ADD_CLAUSES; ARITH_RULE `(16*i+4)+4 = 16*i+8`] (ISPECL[`inlist:byte list`;`16*i+4`;`4`;`0`] SUB_LIST_SPLIT) in
    let step1 = (REWRITE_CONV[LENGTH_REJ_SAMPLE_ETA4_BYTES] THENC ONCE_DEPTH_CONV(REWR_CONV split) THENC REWRITE_CONV[REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND])
                  `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)` in
    let acc1_nib = REWRITE_RULE[LENGTH_REJ_SAMPLE_ETA4_BYTES] acc1_ident in
    let final = TRANS step1 (TRANS (AP_THM (AP_TERM `(+):num->num->num` acc1_nib) `LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i+4,4) inlist):int16 list)`) acc2_def) in
    ASSUME_TAC final);;

(* --- si3_integrated ---                                                    *)
(* SI3_INTEGRATED: full sub-iter-3 (gather + store-fold + counter + mid-guard).
   From s35 (RIP=pc+215, running store SUB_LIST(0,16i+8)) to s47 (RIP=pc+268), store folded to
   SUB_LIST(0,16i+12). Deps: .si3_full (SI3_PRE/GATHER/MG/RESOLVE), .si3_fold_pieces, .si2_fold_complete
   (LEN_RECONCILE_GEN), .pf_target_proof. g3 = hi 128 lane (no shift) so gthm=bg3 directly. *)
let SI3_INTEGRATED : tactic =
  SI3_PRE THEN              (* abbrev acc2, reabbrev mask8c, bounds; RAX folded to word acc2 *)
  ACC2_IDENT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) = acc2`]) THEN
  X86_VSTEPS_TAC EXEC (36--36) THEN
  X86_VERBOSE_STEP_TAC EXEC "s37" THEN MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s36 = mask8c:int64`]) THEN
  X86_VSTEPS_TAC EXEC (38--38) THEN TAB3_TEQ_TAC THEN REABBREV_TAC `tab3 = read YMM6 s38` THEN
  X86_VSTEPS_TAC EXEC (39--39) THEN REABBREV_TAC `pshuf3 = read YMM6 s39` THEN
  PURGE_STALE_STATES_TAC ["s38"] THEN
  X86_VSTEPS_TAC EXEC (40--40) THEN REABBREV_TAC `sx3 = read YMM1 s40` THEN
  VAL_INT64_TAC `acc2:num` THEN
  X86_STEPS_TAC EXEC (41--41) THEN
  SUBGOAL_THEN `sx3:int256 = usimd8 (\b:byte. word_sx b:int32) (word_zx(word_zx (pshuf3:int256):int128):int64)` ASSUME_TAC THENL
   [W(fun (asl,w) ->
       let sx3def = find (fun th -> is_eq(concl th) && rand(concl th)=`sx3:int256` &&
           can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
       SUBST1_TAC(SYM sx3def) THEN
       REWRITE_TAC[usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
       CONV_TAC WORD_BLAST);
    ALL_TAC] THEN
  (SUBGOAL_THEN maskbit_tgt_3 ASSUME_TAC THENL [MASKBIT_TGT_3_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN pf_target_3 ASSUME_TAC THENL [PF_PROOF_3; ALL_TAC]) THEN
  ACC2_IDENT_TAC THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let hasC nm th = can (find_term (fun u -> match u with Const(n,_) when n=nm -> true | _ -> false)) (concl th) in
    let bg3 = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f0sub:int256`))c &&
        not(can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))c) &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (64,8):byte`))c &&
        can(find_term(fun u->u=`word_subword (f0sub:int256) (128,128):int128`))c) asms in
    let mthm3 = find (fun th -> concl th = maskbit_tgt_3) asms in
    let pfth3 = find (fun th -> concl th = pf_target_3) asms in
    let sx3u = find (fun th -> match concl th with Comb(Comb(Const("=",_),Var("sx3",_)),r)->can(find_term(fun u->match u with Const("usimd8",_)->true|_->false))r|_->false) asms in
    let storef0 = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),m),Var("s41",_))),Var("sx3",_)) -> can(find_term(fun u->match u with Const("bytes256",_)->true|_->false)) m |_->false) asms in
    let store_full = REWRITE_RULE[pfth3] (REWRITE_RULE[sx3u] storef0) in
    let g3 = `word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128` in
    let m = `word (val (mask8c:int64) MOD 256):byte` in
    let pc = ISPECL [`word_add res (word (4 * acc2)):int64`; `s41:x86state`; g3; m; `LENGTH(ACC_IDX (word (val (mask8c:int64) MOD 256):byte))`] SUBITER_STORE_POSTCOND in
    let res_th0 = MP pc (CONJ (SPEC m LACC8) store_full) in
    let spec = ISPECL [g3; m; `word_subword (chunk0:int128) (64,8):byte`; `word_subword (chunk0:int128) (72,8):byte`; `word_subword (chunk0:int128) (80,8):byte`; `word_subword (chunk0:int128) (88,8):byte`] SUBITER_STORE_SPEC in
    let rej_store = REWRITE_RULE[MP spec (CONJ mthm3 bg3)] res_th0 in
    let leninl = find (fun th -> concl th = `LENGTH(inlist:byte list)=272`) asms in
    let i116 = find (fun th -> concl th = `16 * (i + 1) <= 272`) asms in
    let blk16 = find (fun th -> is_eq(concl th) && hasC "SUB_LIST" th && (try length(dest_list(rand(concl th)))=16 with _->false)) asms in
    let bb = MP (ISPECL [`inlist:byte list`;`i:num`;`chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*(i+1)<=272 ==> 16*i+16<=272`) i116)) blk16) in
    let blk2_eq = el 2 (CONJUNCTS bb) in
    let lr0 = MP (ISPECL [m;`word_subword (chunk0:int128) (64,8):byte`;`word_subword (chunk0:int128) (72,8):byte`;`word_subword (chunk0:int128) (80,8):byte`;`word_subword (chunk0:int128) (88,8):byte`] LEN_RECONCILE_GEN) mthm3 in
    let lr = REWRITE_RULE[GSYM blk2_eq] lr0 in
    let rej_store1 = REWRITE_RULE[GSYM blk2_eq] rej_store in
    let acc2_ident = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),Var("acc2",_)) -> true | _ -> false) asms in
    let prefix_store0 = find (fun th -> (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s41",_))),_) -> true | _ -> false) &&
         hasC "num_of_wordlist" th && hasC "SUB_LIST" th && can(find_term(fun u->u=`acc2:num`))(lhand(concl th)) && not(hasC "ACC_IDX" th) && not(hasC "bytes256" th)) asms in
    let prefix_store = REWRITE_RULE[GSYM acc2_ident] prefix_store0 in
    let rej_store2 = REWRITE_RULE[GSYM acc2_ident] rej_store1 in
    let fold = MP (ISPECL [`res:int64`;`s41:x86state`;m;`SUB_LIST(16*i+8,4) (inlist:byte list)`;`SUB_LIST(0,16*i+8) (inlist:byte list)`] SUBITER_FOLD_STEP)
                  (CONJ lr (CONJ prefix_store rej_store2)) in
    let split = REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i+8`;`4`;`0`] SUB_LIST_SPLIT) in
    let clean = REWRITE_RULE[GSYM split; ARITH_RULE `(16*i+8)+4 = 16*i+12`] fold in
    ASSUME_TAC clean) THEN
  X86_STEPS_TAC EXEC (42--45) THEN
  SI3_MG THEN SI3_RESOLVE;;

(* --- si4_full ---                                                          *)
(* Sub-iter 4: from RIP=pc+268 (after SI3_RESOLVE) through the jmp pc+52 (loop back-edge).
   Mask = mask8d (R8 ushr24, byte 3 -> lanes 24-31, block3 = SUB_LIST(16i+12,4)). NO mid-guard
   (sub-iter 4 has no cmp/ja; ends jmp pc+52). Uses PREFIX4's lanes-24..31 maskbit + POPCNT_BYTE3. *)

(* SI4_PRE: fold RAX s47 -> word acc3, abbrev acc3, reabbrev mask8d, establish acc3<=248. *)
let SI4_PRE : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let pop_len3 = find (fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) ->
          can(find_term(fun u->u=`mask8c:int64`))(concl th) | _ -> false) asms in
    let rax_red0 = find (fun th -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) ->
          can(find_term(fun u->u=`acc2:num`))(concl th) | _ -> false) asms in
    (* fold popcnt->block2len(SUB_LIST) then collapse the nest to word(acc2+block2len) *)
    RULE_ASSUM_TAC(REWRITE_RULE[pop_len3]) THEN RULE_ASSUM_TAC(REWRITE_RULE[rax_red0])) THEN
  ABBREV_TAC `acc3 = acc2 + LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (16*i+8,4) inlist):int16 list)` THEN
  REABBREV_TAC `mask8d = read R8 s47` THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
    let i116 = find_a (fun th -> concl th = `16 * (i + 1) <= 272`) in
    let nibbnd = find_a (fun th -> concl th = `LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (0,16 * (i + 1)) inlist):int16 list) <= 248`) in
    let a1 = MP (MP (ARITH_RULE `16*(i+1)<=272 ==> (LENGTH(inlist:byte list)=272 ==> 16*(i+1)<=LENGTH inlist)`) i116) leninl in
    let bnd4 = MP (ISPECL[`inlist:byte list`;`i:num`] SUBITER_OUTLEN_BOUND_4) (CONJ a1 nibbnd) in
    let outlen0_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) in
    let acc1_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),Var("acc1",_)) -> true | _ -> false) in
    let acc2_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),Var("acc2",_)) -> true | _ -> false) in
    let acc3_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc2",_)),_)),Var("acc3",_)) -> true | _ -> false) in
    let bnd4a = REWRITE_RULE[outlen0_def; ADD_ASSOC] bnd4 in
    let bnd4b = REWRITE_RULE[acc1_def] bnd4a in
    let bnd4c = REWRITE_RULE[acc2_def] (REWRITE_RULE[ADD_ASSOC] bnd4b) in
    let bnd4d = REWRITE_RULE[acc3_def] (REWRITE_RULE[ADD_ASSOC] bnd4c) in
    ASSUME_TAC bnd4d THEN
    ASSUME_TAC (MATCH_MP (ARITH_RULE `acc3 + x <= 248 ==> acc3 <= 248`) bnd4d)) THEN
  VAL_INT64_TAC `acc3:num`;;

(* --- si4_fold_pieces ---                                                   *)
(* Sub-iter-4 fold pieces. g4 = hi 128 lane >>64 = word_zx(word_zx(word_ushr(word_zx(word_zx(word_subword
   f0sub (128,128)))) 64)). mask8d (R8 ushr24), block3 = SUB_LIST(16i+12,4), lanes 24-31. BYTE3 (DIV 2^24).
   NO mid-guard (sub-iter 4 ends jmp pc+52). *)

let maskbit_tgt_4 =
  `!j. j < 8 ==> (bit j (word (val (mask8d:int64) MOD 256):byte) <=>
       EL j [val(word_subword (chunk0:int128) (96,8):byte) MOD 16;
         val(word_subword chunk0 (96,8):byte) DIV 16; val(word_subword chunk0 (104,8):byte) MOD 16;
         val(word_subword chunk0 (104,8):byte) DIV 16; val(word_subword chunk0 (112,8):byte) MOD 16;
         val(word_subword chunk0 (112,8):byte) DIV 16; val(word_subword chunk0 (120,8):byte) MOD 16;
         val(word_subword chunk0 (120,8):byte) DIV 16] < 9)`;;

let TAB4_TEQ_TAC : tactic = mk_tab_teq 49 50 `mask8d:int64` RLT_D R_EQ_D;;

let PF_PROOF_4 : tactic = mk_pf_proof `pshuf4:int256` `tab4:int256`;;

(* ACC3_IDENT_TAC: LENGTH(REJ_SAMPLE(SUB_LIST(0,16i+12)))=acc3 by forward inference. acc3 = acc2 +
   niblen(SUB_LIST(16i+8,4)); needs acc2_ident + acc3 ABBREV def. *)
let ACC3_IDENT_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let acc2_ident = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),Var("acc2",_))->true|_->false) asms in
    let acc3_def = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc2",_)),_)),Var("acc3",_))->true|_->false) asms in
    let split = REWRITE_RULE[ADD_CLAUSES; ARITH_RULE `(16*i+8)+4 = 16*i+12`] (ISPECL[`inlist:byte list`;`16*i+8`;`4`;`0`] SUB_LIST_SPLIT) in
    let step1 = (REWRITE_CONV[LENGTH_REJ_SAMPLE_ETA4_BYTES] THENC ONCE_DEPTH_CONV(REWR_CONV split) THENC REWRITE_CONV[REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND])
                  `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list)` in
    let acc2_nib = REWRITE_RULE[LENGTH_REJ_SAMPLE_ETA4_BYTES] acc2_ident in
    let final = TRANS step1 (TRANS (AP_THM (AP_TERM `(+):num->num->num` acc2_nib) `LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i+8,4) inlist):int16 list)`) acc3_def) in
    ASSUME_TAC final);;

(* --- si4_integrated ---                                                    *)
(* SI4_INTEGRATED: full sub-iter-4 (gather + store-fold + counter + jmp).
   From s47 (RIP=pc+268, running store SUB_LIST(0,16i+12)) to s57 (RIP=pc+52, back-edge),
   store folded to SUB_LIST(0,16i+16). NO mid-guard. g4 = hi 128 lane >>64. Deps: .si4_full
   (SI4_PRE/GATHER), .si4_fold_pieces, .si2_fold_complete (LEN_RECONCILE_GEN), .pf_target_proof. *)
let SI4_INTEGRATED : tactic =
  SI4_PRE THEN
  ACC3_IDENT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) = acc3`]) THEN
  X86_VSTEPS_TAC EXEC (48--48) THEN
  X86_VERBOSE_STEP_TAC EXEC "s49" THEN MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s48 = mask8d:int64`]) THEN
  X86_VSTEPS_TAC EXEC (50--50) THEN TAB4_TEQ_TAC THEN REABBREV_TAC `tab4 = read YMM6 s50` THEN
  X86_VSTEPS_TAC EXEC (51--51) THEN REABBREV_TAC `pshuf4 = read YMM6 s51` THEN
  PURGE_STALE_STATES_TAC ["s50"] THEN
  X86_VSTEPS_TAC EXEC (52--52) THEN REABBREV_TAC `sx4 = read YMM1 s52` THEN
  VAL_INT64_TAC `acc3:num` THEN
  X86_STEPS_TAC EXEC (53--53) THEN
  SUBGOAL_THEN `sx4:int256 = usimd8 (\b:byte. word_sx b:int32) (word_zx(word_zx (pshuf4:int256):int128):int64)` ASSUME_TAC THENL
   [W(fun (asl,w) ->
       let sx4def = find (fun th -> is_eq(concl th) && rand(concl th)=`sx4:int256` &&
           can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
       SUBST1_TAC(SYM sx4def) THEN
       REWRITE_TAC[usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
       CONV_TAC WORD_BLAST);
    ALL_TAC] THEN
  (SUBGOAL_THEN maskbit_tgt_4 ASSUME_TAC THENL [MASKBIT_TGT_4_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN pf_target_4 ASSUME_TAC THENL [PF_PROOF_4; ALL_TAC]) THEN
  ACC3_IDENT_TAC THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let hasC nm th = can (find_term (fun u -> match u with Const(n,_) when n=nm -> true | _ -> false)) (concl th) in
    let bg4 = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f0sub:int256`))c &&
        can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (96,8):byte`))c &&
        can(find_term(fun u->u=`word_subword (f0sub:int256) (128,128):int128`))c) asms in
    let mthm4 = find (fun th -> concl th = maskbit_tgt_4) asms in
    let pfth4 = find (fun th -> concl th = pf_target_4) asms in
    let sx4u = find (fun th -> match concl th with Comb(Comb(Const("=",_),Var("sx4",_)),r)->can(find_term(fun u->match u with Const("usimd8",_)->true|_->false))r|_->false) asms in
    let storef0 = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),m),Var("s53",_))),Var("sx4",_)) -> can(find_term(fun u->match u with Const("bytes256",_)->true|_->false)) m |_->false) asms in
    let store_full = REWRITE_RULE[pfth4] (REWRITE_RULE[sx4u] storef0) in
    let g4 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128) 64):int128):int128` in
    let m = `word (val (mask8d:int64) MOD 256):byte` in
    let pc = ISPECL [`word_add res (word (4 * acc3)):int64`; `s53:x86state`; g4; m; `LENGTH(ACC_IDX (word (val (mask8d:int64) MOD 256):byte))`] SUBITER_STORE_POSTCOND in
    let res_th0 = MP pc (CONJ (SPEC m LACC8) store_full) in
    let spec = ISPECL [g4; m; `word_subword (chunk0:int128) (96,8):byte`; `word_subword (chunk0:int128) (104,8):byte`; `word_subword (chunk0:int128) (112,8):byte`; `word_subword (chunk0:int128) (120,8):byte`] SUBITER_STORE_SPEC in
    let rej_store = REWRITE_RULE[MP spec (CONJ mthm4 bg4)] res_th0 in
    let leninl = find (fun th -> concl th = `LENGTH(inlist:byte list)=272`) asms in
    let i116 = find (fun th -> concl th = `16 * (i + 1) <= 272`) asms in
    let blk16 = find (fun th -> is_eq(concl th) && hasC "SUB_LIST" th && (try length(dest_list(rand(concl th)))=16 with _->false)) asms in
    let bb = MP (ISPECL [`inlist:byte list`;`i:num`;`chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*(i+1)<=272 ==> 16*i+16<=272`) i116)) blk16) in
    let blk3_eq = el 3 (CONJUNCTS bb) in
    let lr0 = MP (ISPECL [m;`word_subword (chunk0:int128) (96,8):byte`;`word_subword (chunk0:int128) (104,8):byte`;`word_subword (chunk0:int128) (112,8):byte`;`word_subword (chunk0:int128) (120,8):byte`] LEN_RECONCILE_GEN) mthm4 in
    let lr = REWRITE_RULE[GSYM blk3_eq] lr0 in
    let rej_store1 = REWRITE_RULE[GSYM blk3_eq] rej_store in
    let acc3_ident = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),Var("acc3",_)) -> true | _ -> false) asms in
    let prefix_store0 = find (fun th -> (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s53",_))),_) -> true | _ -> false) &&
         hasC "num_of_wordlist" th && hasC "SUB_LIST" th && can(find_term(fun u->u=`acc3:num`))(lhand(concl th)) && not(hasC "ACC_IDX" th) && not(hasC "bytes256" th)) asms in
    let prefix_store = REWRITE_RULE[GSYM acc3_ident] prefix_store0 in
    let rej_store2 = REWRITE_RULE[GSYM acc3_ident] rej_store1 in
    let fold = MP (ISPECL [`res:int64`;`s53:x86state`;m;`SUB_LIST(16*i+12,4) (inlist:byte list)`;`SUB_LIST(0,16*i+12) (inlist:byte list)`] SUBITER_FOLD_STEP)
                  (CONJ lr (CONJ prefix_store rej_store2)) in
    let split = REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i+12`;`4`;`0`] SUB_LIST_SPLIT) in
    let clean = REWRITE_RULE[GSYM split; ARITH_RULE `(16*i+12)+4 = 16*i+16`] fold in
    ASSUME_TAC clean) THEN
  X86_STEPS_TAC EXEC (54--57);;

(* --- acc_full_len ---                                                      *)
(* ACC_FULL_LEN: the 5-term niblen sum (outlen0-block + 4 sub-iter blocks) = niblen(SUB_LIST(0,16(i+1))).
   Needed by RAX_FINAL_TAC. Plus SL16_4WAY helper (SUB_LIST(16i,16) = APPEND of the 4 4-blocks). *)
let ACC_FULL_LEN = prove
 (`!inlist:byte list. !i:num. 16*i+16 <= LENGTH inlist ==>
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*i) inlist):int16 list) +
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i,4) inlist):int16 list) +
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i+4,4) inlist):int16 list) +
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i+8,4) inlist):int16 list) +
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(16*i+12,4) inlist):int16 list) =
     LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*(i+1)) inlist):int16 list)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `16*(i+1) = 16*i+16`] THEN
  ONCE_REWRITE_TAC[ISPECL[`inlist:byte list`;`16*i`;`16`;`0`] SUB_LIST_SPLIT] THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  REWRITE_TAC[SL16_4WAY] THEN
  REWRITE_TAC[REJ_NIBBLES_ETA4_APPEND; LENGTH_APPEND] THEN ARITH_TAC);;

(* --- rax_final ---                                                         *)
(* Discharge the RAX final-state subgoal (goal 0):
   word_zx(word_add(word_zx(word acc3))(word_zx(word_zx(word(word_popcount(mask8d-arg)))))) =
     word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16(i+1))))). *)
let RAX_FINAL_TAC : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let m8c_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8c:int64` | _ -> false) in
    let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
    let m8d_val = find_a (fun th -> match concl th with
        Comb(Comb(Const("=",_),_),r) -> r = `mask8d:int64` &&
          can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))(concl th) | _ -> false) in
    let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
    (* popcnt4: fold SUM->mask8b->mask8c (forward), then mask8c-ushr-form -> mask8d via m8d_val *)
    let popcnt4 = REWRITE_RULE[m8d_val] (REWRITE_RULE[m8b_def; m8c_def]
       (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE3))) in
    let lanesum = rand(concl popcnt4) in
    (* lanes-24..31 maskbit                                                  *)
    let mb4 = find_a (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f1bnd:int256`))c &&
       can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),n) -> n=`24` | _ -> false))c) in
    let mb4_tm = concl mb4 in
    let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
    let blk16 = find_a (fun th -> is_eq(concl th) &&
       (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" && length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le)) blk16) in
    let blk3_eq = el 3 (CONJUNCTS bb) in   (* SUB_LIST(16*i+12,4) = [chunk0 96,104,112,120] *)
    let block3 = `[word_subword (chunk0:int128) (96,8); word_subword chunk0 (104,8);
                   word_subword chunk0 (112,8); word_subword chunk0 (120,8)]:byte list` in
    let block3len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA4`, block3)) in
    let bsum4_raw = prove(mk_imp(mb4_tm, mk_eq(lanesum, block3len_x)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV)
            (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER] THEN
      SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let pop_len4 = REWRITE_RULE[GSYM blk3_eq] (TRANS popcnt4 (MP bsum4_raw mb4)) in
    (* bound acc3 + block3len < 2^32                                         *)
    let bnd4d = find_a (fun th -> match concl th with
       Comb(Comb(Const("<=",_),Comb(Comb(Const("+",_),Var("acc3",_)),_)),_) -> true | _ -> false) in
    let block3len = `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+12,4) inlist):int16 list)` in
    let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd4d in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    (* rewrite goal: popcnt -> block3len, then rax_red0 -> word(acc3+block3len) *)
    REWRITE_TAC[pop_len4] THEN REWRITE_TAC[rax_red0]) THEN
  (* now goal: word(acc3 + block3len) = word(LENGTH(REJ_SAMPLE(SUB_LIST(0,16(i+1))))) *)
  AP_TERM_TAC THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let outlen0_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),_)),Var("outlen0",_)) -> true | _ -> false) in
    let acc1_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),Var("acc1",_)) -> true | _ -> false) in
    let acc2_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),Var("acc2",_)) -> true | _ -> false) in
    let acc3_def = find_a (fun th -> match concl th with
       Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc2",_)),_)),Var("acc3",_)) -> true | _ -> false) in
    let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
    let af = MP (ISPECL [`inlist:byte list`; `i:num`] ACC_FULL_LEN)
                (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le)) in
    REWRITE_TAC[SYM acc3_def; SYM acc2_def; SYM acc1_def] THEN
    REWRITE_TAC[SYM outlen0_def] THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
    MP_TAC af THEN ARITH_TAC);;

(* --- rcx_final ---                                                         *)
(* Final-state RCX discharge for CLEAN_BODY: the quadruple-nested word_zx/word_add(+4)
   counter chain = word(16*(i+1)). Plus helper lemmas. Load after main file. *)

let RCX_FINAL_TAC : tactic =
  SUBGOAL_THEN `16 * (i + 1) = 16 * i + 4 + 4 + 4 + 4` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  REWRITE_TAC[MM64_32] THEN CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  REWRITE_TAC[MM_4G_4G; MM_4G_18] THEN
  SUBGOAL_THEN `16 * i < 4294967296 /\ 16*i+4 < 4294967296 /\ 16*i+4+4 < 4294967296 /\
                16*i+4+4+4 < 4294967296 /\ 16*i+16 < 18446744073709551616 /\
                (16*i+4)+4 < 4294967296 /\ ((16*i+4)+4)+4 < 4294967296 /\ (((16*i+4)+4)+4)+4 < 4294967296`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN UNDISCH_TAC `16 * (i + 1) <= 272` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;;

(* --- clean_body_full ---                                                   *)
(* CLEAN_BODY_FULL_TAC: the complete proof of clean_body_tm (the eta4 SIMD loop body,
   pc+52 -> pc+52). Composes the prologue + 4 sub-iter gather/fold/counter/midguard + final state.
   Load order (after main file + cbb_defs):
     .subiter_k_lemmas, .subiter_byte23_lemmas, .maskbit_tgt_tac, .tab1_teq_tac, .pf_target_proof,
     .prefix_g_full_tac, .si1_fold_v2, .maskbit_tgt_2_tac, .tab2_teq_tac, .si2_fold_pieces, .si2_fold_complete,
     .si2_full, .si2_integrated, .si3_full, .si3_fold_pieces, .si3_integrated, .si4_full,
     .si4_fold_pieces, .si4_integrated, .acc_full_len, .rax_final, .rcx_final.
     (.tab2_teq_tac MUST precede .si2_fold_pieces — TAB2_TEQ_TAC dependency. Verified
 , hyps=0 = clean_body_tm exactly.) *)
let CLEAN_BODY_FULL_TAC : tactic =
  PREFIX_G_FULL_TAC THEN SI1_FOLD_V2 THEN SI2_INTEGRATED THEN SI3_INTEGRATED THEN SI4_INTEGRATED THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16*i+16 = 16*(i+1)`]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [RAX_FINAL_TAC; RCX_FINAL_TAC];;

(* ---- prove CLEAN_BODY ----                                                *)
let MLDSA_REJ_UNIFORM_ETA4_CLEAN_BODY = prove(clean_body_tm, CLEAN_BODY_FULL_TAC);;

(* --- clean_block ---                                                       *)
(* ========================================================================= *)
(* CLEAN_BLOCK: the SIMD 16-byte block body pc+52 -> pc+52,                  *)
(* WITHOUT the `~(N=0)` and `i+1<N` hyps of clean_body_tm (the gather tactics *)
(* never use them), and with the relaxed bound `16*(i+1)<=272` (so it covers *)
(* BOTH clean blocks AND the exit block at i=N-1 where 16*N=272). Proved by the *)
(* same CLEAN_BODY_FULL_TAC. This is the asset for the exit-block OFFSET arm: *)
(* CLEAN_BLOCK @ i=N-1 takes pc+52/pos=16(N-1) -> pc+52/pos=16N, then the head *)
(* guard cmp ecx,256 fires (16N=272>256) -> pc+314, then SCALAR_TAIL_AT_P@272. *)
(* Load after the full CLEAN_BODY chain (needs CLEAN_BODY_FULL_TAC + clean_body_tm). *)
(* ========================================================================= *)
let clean_block_tm =
  let hs = conjuncts(fst(dest_imp(snd(strip_forall clean_body_tm)))) in
  let hs' = filter (fun h -> h <> `~(N = 0)` && h <> `i + 1 < N`) hs in
  list_mk_forall(fst(strip_forall clean_body_tm),
    mk_imp(list_mk_conj hs', snd(dest_imp(snd(strip_forall clean_body_tm)))));;

let CLEAN_BLOCK = prove(clean_block_tm, CLEAN_BODY_FULL_TAC);;

(* --- scalar_tail_lemmas ---                                                *)
(* Foundational spec lemmas for the SCALAR_TAIL proof (pc+314 byte-at-a-time loop).
   Each scalar iteration consumes 1 input byte = 2 nibbles (low then high), accepting each if <9,
   matching REJ_SAMPLE_ETA4_BYTES_1. These give the per-byte step of the loop invariant. *)

let SUB_LIST_1_EL = prove
 (`!l:byte list. !p. p < LENGTH l ==> SUB_LIST(p,1) l = [EL p l]`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; LT] THEN
  X_GEN_TAC `p:num` THEN ASM_CASES_TAC `p = 0` THEN
  ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[ARITH_RULE `1 = SUC 0`; SUB_LIST_CLAUSES; SUB_LIST; EL; HD] THEN
    REWRITE_TAC[ONE; SUB_LIST_CLAUSES];
    DISCH_TAC THEN
    SUBGOAL_THEN `?q. p = SUC q` (CHOOSE_THEN SUBST_ALL_TAC) THENL
     [EXISTS_TAC `p - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUB_LIST_CLAUSES; EL; TL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let SUB_LIST_STEP_1 = prove
 (`!l:byte list. !p. p < LENGTH l ==> SUB_LIST(0,p+1) l = APPEND (SUB_LIST(0,p) l) [EL p l]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`l:byte list`;`p:num`;`1`;`0`] SUB_LIST_SPLIT) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[SUB_LIST_1_EL]);;

let REJ_SAMPLE_STEP_1 = prove
 (`!inlist:byte list. !p. p < LENGTH inlist ==>
     REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist) =
     APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist)) (REJ_SAMPLE_ETA4_BYTES [EL p inlist])`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SUB_LIST_STEP_1; REJ_SAMPLE_ETA4_BYTES_APPEND]);;

let LENGTH_REJ_SAMPLE_STEP_1 = prove
 (`!inlist:byte list. !p. p < LENGTH inlist ==>
     LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list) =
     LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) +
     (if val(EL p inlist) MOD 16 < 9 then 1 else 0) + (if val(EL p inlist) DIV 16 < 9 then 1 else 0)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REJ_SAMPLE_STEP_1; LENGTH_APPEND; LENGTH_REJ_SAMPLE_ETA4_BYTES_1] THEN ARITH_TAC);;

(* --- scalar_tail_build ---                                                 *)
(* Scalar-tail proof build file. Loaded after the main eta4 file + .scalar_tail_lemmas.ml.
   Builds: READ_1BYTE_EL, the per-byte loop body lemma, the WOP scalar-loop wrapper,
   and finally MLDSA_REJ_UNIFORM_ETA4_SCALAR_TAIL. *)

(* Read one input byte at offset p from the buffer's num_of_wordlist contract. *)
let READ_1BYTE_EL = prove
 (`!(inlist:byte list) (buf:int64) (s:x86state) p n.
     LENGTH inlist = n /\ p < n /\
     read(memory :> bytes(buf, n)) s = num_of_wordlist inlist
     ==> read(memory :> bytes8 (word_add buf (word p))) s = EL p inlist`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`inlist:byte list`; `p:num`] EL_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[DIMINDEX_8] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[bytes8; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  SUBGOAL_THEN
   `read (bytes (word_add buf (word p),1)) (read memory s) =
    read (bytes (buf,n)) (read memory s) DIV 2 EXP (8 * p) MOD 256`
   SUBST1_TAC THENL
   [REWRITE_TAC[READ_BYTES_DIV] THEN
    MP_TAC(ISPECL [`word_add buf (word p):int64`; `n - p`; `1`; `read memory s:int64->byte`] READ_BYTES_MOD) THEN
    SUBGOAL_THEN `MIN (n - p) 1 = 1` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `MIN a 1 = 1 <=> 1 <= a`] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `read (memory :> bytes (buf,n)) s = num_of_wordlist (inlist:byte list)` THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(256:num) = 2 EXP dimindex(:8)` SUBST1_TAC THENL
   [REWRITE_TAC[DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[WORD_MOD_SIZE]);;

(* jae(Condition_NB) fall-through: when a<k the unsigned >= jump is NOT taken.
   The model's flag condition is INT-typed (int_of_num &), NOT real — matching
   it requires the :int annotation (the classic invisible-type trap). Resolves
   the scalar-tail guards at pc+319 (256), pc+327 (272), pc+369/pc+383 (256). *)
let JAE_NOT_TAKEN_LT = prove
 (`!a k:num. a < k /\ k < 2 EXP 32
     ==> ~(&(val(word_zx(word a:int64):int32)):int - &k =
           &(val(word_sub(word_zx(word a:int64):int32) (word k):int32)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_zx(word a:int64):int32) = a` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_ZX_64_32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub (word_zx(word a:int64):int32) (word k:int32)) = a + 2 EXP 32 - k` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val(word k:int32) = k` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL [REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC; REFL_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a + 2 EXP 32 - k = (a + 2 EXP 32) - k /\ k <= a + 2 EXP 32` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&((a + 2 EXP 32) - k):int = &(a + 2 EXP 32) - &k` SUBST1_TAC THENL
   [MATCH_MP_TAC(GSYM INT_OF_NUM_SUB) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ARITH_RULE `0 < 2 EXP 32`) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC);;

(* jae(Condition_NB) TAKEN: when k<=a the unsigned >= jump IS taken (flag eq holds).
   Companion of JAE_NOT_TAKEN_LT for the nibble-reject branches (cmp r10d/r11d, 9). *)
let JAE_TAKEN_GE = prove
 (`!a k:num. k <= a /\ a < 2 EXP 32
     ==> (&(val(word_zx(word a:int64):int32)):int - &k =
          &(val(word_sub(word_zx(word a:int64):int32) (word k):int32)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `val(word_zx(word a:int64):int32) = a` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_ZX_64_32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_sub (word_zx(word a:int64):int32) (word k:int32)) = a - k` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_CASES; DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val(word k:int32) = k` SUBST1_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_32] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL [REFL_TAC; REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&(a - k):int = &a - &k` SUBST1_TAC THENL
   [MATCH_MP_TAC(GSYM INT_OF_NUM_SUB) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REFL_TAC);;

(* Fast RIP-cond resolver: rewrites ONLY the RIP equation (a small term), not the
   whole eventually-goal — avoids a catastrophic whole-goal REWRITE. Finds
   the RIP=(if cond then..else..) assumption, the matching ~cond among assumptions
   (must be present and SAME-TYPED), and collapses via COND_CLAUSES. *)

(* ========================================================================= *)
(* Per-byte scalar-tail body lemma: one trip pc+314 -> pc+314, consuming     *)
(* input byte at position p, extending output by REJ_SAMPLE_ETA4_BYTES[b].   *)
(* Entry generalized to arbitrary p so the wrapper can iterate; the          *)
(* ~(L=255 /\ low<9) hypothesis rules out the mid-byte exit (handled by the  *)
(* terminal segment, not this looping body).                                 *)
(* ========================================================================= *)

(* Nibble-value bridge: the X86_VSTEPS-produced R10 expression (low nibble) after
   `mov r10d,r11d; and r10d,15` over the movzbl-loaded byte b, collapses to
   word(val b MOD 16):int64. The zx-tower shape (byte->int16->int32 widenings)
   is exactly what VSTEPS emits for the load + zero-extends. *)
let R10_NIBBLE_VAL = prove
 (`!b:byte. word_zx(word_and (word_zx (word_zx (word_zx (word_zx (word_zx b:int32):int64):int32):int64):int32) (word 15:int32)):int64 = word(val b MOD 16)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `(word 15:int32) = word(2 EXP 4 - 1)` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SIMP_TAC[VAL_WORD_ZX_GEN; VAL_WORD_AND_MASK_WORD; DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64;
           VAL_WORD; ARITH] THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN STRIP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `val(b:byte) MOD 4294967296 = val b /\ val(b:byte) MOD 18446744073709551616 = val b`
    STRIP_ASSUME_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `val(b:byte) MOD 16 < 18446744073709551616` ASSUME_TAC THENL
   [MP_TAC(SPECL[`val(b:byte)`;`16`] MOD_LT_EQ) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOD_LT] THEN CONV_TAC NUM_REDUCE_CONV);;

(* High-nibble bridge: R11 after `shr r11d,4; and r11d,15` collapses to
   word(val b DIV 16):int64. Shape matches the X86_VSTEPS emission (ushr after a
   byte->int32->int64->int32 zx-tower, then 2 more zx, then and). *)
let R11_NIBBLE_VAL = prove
 (`!b:byte. word_zx (word_and (word_zx (word_zx (word_ushr (word_zx (word_zx (word_zx (b:byte) :int32) :int64) :int32) 4) :int64) :int32) (word 15 :int32)) :int64 = word (val b DIV 16)`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `(word 15:int32) = word(2 EXP 4 - 1)` SUBST1_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SIMP_TAC[VAL_WORD_ZX_GEN; VAL_WORD_AND_MASK_WORD; VAL_WORD_USHR; DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64;
           VAL_WORD; ARITH] THEN
  MP_TAC(ISPEC `b:byte` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN STRIP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `val(b:byte) MOD 4294967296 = val b /\ val(b:byte) MOD 18446744073709551616 = val b /\ (val(b:byte) DIV 16) MOD 18446744073709551616 = val b DIV 16 /\ (val(b:byte) DIV 16) MOD 4294967296 = val b DIV 16 /\ (val(b:byte) DIV 16) MOD 16 = val b DIV 16`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN MP_TAC(SPECL[`val(b:byte)`;`16`] DIV_LT) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* RAX after `inc eax` over RAX=word L (L<256): the int32 inc widens back to word(L+1):int64. *)
let RAX_INC = prove
 (`!L. L < 256 ==> word_zx(word_add (word_zx (word L:int64):int32) (word 1:int32)):int64 = word(L+1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word_zx(word L:int64):int32) = L` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_ZX_64_32 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `val(word_zx(word_add (word_zx (word L:int64):int32) (word 1:int32)):int64) = L+1` SUBST1_TAC THENL
   [SUBGOAL_THEN `val(word_add (word_zx (word L:int64):int32) (word 1:int32)) = L + 1` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_32] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
      CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `val(word_add (word_zx (word L:int64):int32) (word 1:int32))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC VAL_WORD_ZX THEN REWRITE_TAC[DIMINDEX_32;DIMINDEX_64] THEN ARITH_TAC; ASM_REWRITE_TAC[]];
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC]);;

(* Store-value bridges: the scalar tail computes `4 - nibble` as int32 then the
   model wraps it in word_zx(word_zx(...)) (32->64->32 round trip) at the vmovd/store.
   For accepted nibbles (<9) this equals the spec coefficient word_sx(word_sub(word 4:int16)..).
   Proved by enumerating the 9 accepted nibble values + WORD_BLAST. *)
let LO_STORE_VAL = prove
 (`!b:byte. val b MOD 16 < 9
   ==> word_zx(word_zx(word_sub (word 4:int32) (word_zx(word(val b MOD 16):int64):int32):int32):int64):int32 =
       word_sx(word_sub (word 4:int16) (word(val b MOD 16):int16):int16):int32`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(b:byte) MOD 16 = 0 \/ val b MOD 16 = 1 \/ val b MOD 16 = 2 \/ val b MOD 16 = 3 \/
                val b MOD 16 = 4 \/ val b MOD 16 = 5 \/ val b MOD 16 = 6 \/ val b MOD 16 = 7 \/ val b MOD 16 = 8`
   MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST);;

let HI_STORE_VAL = prove
 (`!b:byte. val b DIV 16 < 9
   ==> word_zx(word_zx(word_sub (word 4:int32) (word_zx(word(val b DIV 16):int64):int32):int32):int64):int32 =
       word_sx(word_sub (word 4:int16) (word(val b DIV 16):int16):int16):int32`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(b:byte) DIV 16 = 0 \/ val b DIV 16 = 1 \/ val b DIV 16 = 2 \/ val b DIV 16 = 3 \/
                val b DIV 16 = 4 \/ val b DIV 16 = 5 \/ val b DIV 16 = 6 \/ val b DIV 16 = 7 \/ val b DIV 16 = 8`
   MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_BLAST);;

(* Per-byte output-length step lemmas, one per nibble-acceptance combination.
   Drive the loop invariant's RAX update (LENGTH outlist grows by 0/1/2). *)
let LEN_STEP_BOTH = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ val(EL p inlist) MOD 16 < 9 /\ val(EL p inlist) DIV 16 < 9
   ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list) =
       LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) + 2`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_STEP_1) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;
let LEN_STEP_LO = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ val(EL p inlist) MOD 16 < 9 /\ ~(val(EL p inlist) DIV 16 < 9)
   ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list) =
       LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) + 1`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_STEP_1) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;
let LEN_STEP_HI = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ ~(val(EL p inlist) MOD 16 < 9) /\ val(EL p inlist) DIV 16 < 9
   ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list) =
       LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) + 1`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_STEP_1) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;
let LEN_STEP_NONE = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ ~(val(EL p inlist) MOD 16 < 9) /\ ~(val(EL p inlist) DIV 16 < 9)
   ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list) =
       LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_STEP_1) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* Per-byte output-list APPEND step, one per acceptance combination.
   Used in the body lemma's memory fold: REJ(SUB(0,p+1)) = APPEND (REJ(SUB(0,p))) <new coeffs>. *)
let REJ_STEP_BOTH = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ val(EL p inlist) MOD 16 < 9 /\ val(EL p inlist) DIV 16 < 9
   ==> REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist) =
       APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
              [word_sx(word_sub (word 4:int16) (word(val(EL p inlist) MOD 16))):int32;
               word_sx(word_sub (word 4:int16) (word(val(EL p inlist) DIV 16))):int32]`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_SAMPLE_ETA4_BYTES_STEP_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC REJ_SAMPLE_ETA4_BYTES_1_BOTH THEN ASM_REWRITE_TAC[]);;
let REJ_STEP_LO = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ val(EL p inlist) MOD 16 < 9 /\ ~(val(EL p inlist) DIV 16 < 9)
   ==> REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist) =
       APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
              [word_sx(word_sub (word 4:int16) (word(val(EL p inlist) MOD 16))):int32]`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_SAMPLE_ETA4_BYTES_STEP_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC REJ_SAMPLE_ETA4_BYTES_1_LOW_ONLY THEN ASM_REWRITE_TAC[]);;
let REJ_STEP_HI = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ ~(val(EL p inlist) MOD 16 < 9) /\ val(EL p inlist) DIV 16 < 9
   ==> REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist) =
       APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
              [word_sx(word_sub (word 4:int16) (word(val(EL p inlist) DIV 16))):int32]`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_SAMPLE_ETA4_BYTES_STEP_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC REJ_SAMPLE_ETA4_BYTES_1_HIGH_ONLY THEN ASM_REWRITE_TAC[]);;
let REJ_STEP_NONE = prove
 (`!(inlist:byte list) p. p < LENGTH inlist /\ ~(val(EL p inlist) MOD 16 < 9) /\ ~(val(EL p inlist) DIV 16 < 9)
   ==> REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist) = REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_SAMPLE_ETA4_BYTES_STEP_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `REJ_SAMPLE_ETA4_BYTES [EL p (inlist:byte list)] = []` SUBST1_TAC THENL
   [MATCH_MP_TAC REJ_SAMPLE_ETA4_BYTES_1_REJECT_BOTH THEN ASM_REWRITE_TAC[]; REWRITE_TAC[APPEND_NIL]]);;

(* Count-exit cap lemmas for the WOP wrapper terminal case (outlen >= 256).  *)
(* Spec side: SUB_LIST(0,256) of full REJ = SUB_LIST(0,256) of any prefix whose
   output already reached >=256 elements. *)
let SUB_LIST_256_PREFIX_GE = prove
 (`!(inlist:byte list) k.
     k <= LENGTH inlist /\
     256 <= LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,k) inlist):int32 list)
     ==> SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist :int32 list) =
         SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,k) inlist))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `inlist:byte list`] REJ_SAMPLE_ETA4_SUB_LIST_PREFIX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ext:int32 list` (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th])) THEN
  MATCH_MP_TAC SUB_LIST_APPEND_LEFT THEN ASM_REWRITE_TAC[]);;

(* --- scalar_body_lemma ---                                                 *)
(* ========================================================================= *)
(* SCALAR_TAIL per-byte body lemma — full proof.                             *)
(* One trip pc+314 -> pc+314 consuming input byte at position p, extending   *)
(* the output by REJ_SAMPLE_ETA4_BYTES[EL p inlist]. Entry generalized to    *)
(* arbitrary p. The ~(L=255 /\ low<9) hyp rules out the mid-byte exit (that  *)
(* case is the terminal segment, handled by the WOP wrapper, not this body). *)
(* Loaded after main eta4 file + .scalar_tail_lemmas + .scalar_tail_build.   *)
(* Requires type_invention_error := true.                                    *)
(* ========================================================================= *)

(* Common RCX closer: word_zx(word_add(word_zx(word p))(word 1)):int64 = word(p+1) for p<272. *)
let RCX_INC_TAC =
  REWRITE_TAC[GSYM VAL_EQ] THEN
  SUBGOAL_THEN `val(word_zx(word p:int64):int32) = p` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_ZX_64_32 THEN MP_TAC(ASSUME `p<272`) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `val(word_zx(word_add (word_zx (word p:int64):int32) (word 1:int32)):int64) = p+1` SUBST1_TAC THENL
   [SUBGOAL_THEN `val(word_add (word_zx (word p:int64):int32) (word 1:int32)) = p + 1` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD_ADD; DIMINDEX_32] THEN ASM_REWRITE_TAC[VAL_WORD; DIMINDEX_32] THEN
      CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC MOD_LT THEN MP_TAC(ASSUME `p<272`) THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `val(word_add (word_zx (word p:int64):int32) (word 1:int32))` THEN
    CONJ_TAC THENL [MATCH_MP_TAC VAL_WORD_ZX THEN REWRITE_TAC[DIMINDEX_32;DIMINDEX_64] THEN ARITH_TAC; ASM_REWRITE_TAC[]];
    REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
    MP_TAC(ASSUME `p<272`) THEN ARITH_TAC];;

(* setup to s8: lands RIP=pc+343 with R10=word(val(EL p (inlist:byte list)) MOD 16), outlen0 abbreviated,
   LENGTH(REJ(SUB(0,p)))=outlen0 kept. *)
let SCALAR_BODY_SETUP =
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  MP_TAC(ISPECL [`inlist:byte list`; `buf:int64`; `s0:x86state`; `p:num`; `272`] READ_1BYTE_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `outlen0 = LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list)` THEN
  FIRST_X_ASSUM(fun th -> if concl th = `L:num = outlen0` then SUBST_ALL_TAC th else NO_TAC) THEN
  SUBGOAL_THEN `~(&(val(word_zx(word outlen0:int64):int32)):int - &256 = &(val(word_sub(word_zx(word outlen0:int64):int32) (word 256):int32)))` ASSUME_TAC THENL
   [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(&(val(word_zx(word p:int64):int32)):int - &272 = &(val(word_sub(word_zx(word p:int64):int32) (word 272):int32)))` ASSUME_TAC THENL
   [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--8) THEN
  SUBGOAL_THEN `word_add buf (word (1 * val (word p:int64))) = word_add buf (word p):int64` ASSUME_TAC THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
    MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `p < 272`) THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `word_add buf (word (1 * val (word p:int64))) = word_add buf (word p):int64`;
                              ASSUME `read (memory :> bytes8 (word_add buf (word p))) s4 = EL p (inlist:byte list)`;
                              R10_NIBBLE_VAL]) THEN
  DISCARD_OLDSTATE_TAC "s8";;

(* prove read(bytes(addr,4)) sN = val(word_sx ...) from a spec-form bytes32 store hyp. *)
let SCALAR_TAIL_BODY = prove
 (`!res buf table (inlist:byte list) pc (p:num) (L:num) stackpointer.
        LENGTH inlist = 272 /\
        nonoverlapping_modulo (2 EXP 64) (pc, 403) (val res,1024) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 403) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val table, 2048) /\
        p < 272 /\ L < 256 /\
        L = LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) /\
        ~(L = 255 /\ val(EL p (inlist:byte list)) MOD 16 < 9)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word(pc + 314) /\ read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  read RAX s = word L /\ read RCX s = word p /\
                  read(memory :> bytes(res, 4 * L)) s =
                    num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist)))
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word(pc + 314) /\ read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  (let outlist = REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist) in
                   read RAX s = word(LENGTH outlist) /\ read RCX s = word(p+1) /\
                   read(memory :> bytes(res, 4 * LENGTH outlist)) s = num_of_wordlist outlist))
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
              MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`,
  SCALAR_BODY_SETUP THEN
  ASM_CASES_TAC `val(EL p (inlist:byte list)) MOD 16 < 9` THENL
   [(* ===== ACCEPT-LOW (low<9): step to pc+364, store low, to pc+379 ===== *)
    SUBGOAL_THEN `~(&(val(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32) (word 9):int32)))` ASSUME_TAC THENL
     [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (9--14) THEN DISCARD_OLDSTATE_TAC "s14" THEN
    SUBGOAL_THEN `outlen0 + 1 < 256` ASSUME_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o check(fun th->let c=concl th in c=`outlen0<256`||c=`val(EL p (inlist:byte list)) MOD 16 < 9`||c=`~(outlen0=255/\val(EL p (inlist:byte list)) MOD 16 < 9)`))) THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> let c=concl th in
       if is_eq c && can(find_term(fun t->t=`RAX`))c && can(find_term(fun t->t=`s14:x86state`))c
       then ASSUME_TAC(REWRITE_RULE[MATCH_MP RAX_INC (ASSUME `outlen0<256`)] th) else NO_TAC) THEN
    SUBGOAL_THEN `~(&(val(word_zx(word(outlen0+1):int64):int32)):int - &256 = &(val(word_sub(word_zx(word(outlen0+1):int64):int32) (word 256):int32)))` ASSUME_TAC THENL
     [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (15--18) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[R11_NIBBLE_VAL]) THEN DISCARD_OLDSTATE_TAC "s18" THEN
    ASM_CASES_TAC `val(EL p (inlist:byte list)) DIV 16 < 9` THENL
     [(* ACCEPT-ACCEPT *)
      SUBGOAL_THEN `~(&(val(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32) (word 9):int32)))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (19--22) THEN
      SUBGOAL_THEN `val(word(outlen0+1):int64) = outlen0+1` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `outlen0+1<256`) THEN ARITH_TAC; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (23--25) THEN DISCARD_OLDSTATE_TAC "s25" THEN
      FIRST_X_ASSUM(fun th -> let c=concl th in
         if is_eq c && can(find_term(fun t->t=`RAX`))c && can(find_term(fun t->t=`s25:x86state`))c
         then ASSUME_TAC(REWRITE_RULE[MATCH_MP RAX_INC (ASSUME `outlen0+1<256`)] th) else NO_TAC) THEN
      ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist):int32 list) = outlen0 + 2` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LEN_STEP_BOTH) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        DISCH_THEN(fun th->REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC); ALL_TAC] THEN
      ASM_REWRITE_TAC[ARITH_RULE `(outlen0+1)+1 = outlen0+2`] THEN
      CONJ_TAC THENL
       [RCX_INC_TAC;
        SUBGOAL_THEN `REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist) =
           APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                  [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32;
                   word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) DIV 16))):int32]` SUBST1_TAC THENL
         [MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_BOTH) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `4 * (outlen0 + 2) = 4 * outlen0 + 8` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s25:x86state`;
           `REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list`;
           `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32;
             word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) DIV 16))):int32]`;
           `4*outlen0`; `8`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[DIMINDEX_32] THEN
          FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC) THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          (* 8-byte = [lo;hi]                                                *)
          GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM(REWRITE_CONV[APPEND] `APPEND [a:int32] [b:int32]`)] THEN
          SUBGOAL_THEN `(8:num) = 4 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
          MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `word_add res (word(4*outlen0)):int64`; `s25:x86state`;
             `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]`;
             `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) DIV 16))):int32]`;
             `4`; `4`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
          ANTS_TAC THENL [REWRITE_TAC[DIMINDEX_32; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_WORDLIST_SINGLETON_INT32] THEN
          SUBGOAL_THEN `val(word outlen0:int64) = outlen0` ASSUME_TAC THENL
           [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `outlen0<256`) THEN ARITH_TAC; ALL_TAC] THEN
          (* bridge both stores to spec form                                 *)
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`s25:x86state`))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c
             then ASSUME_TAC(REWRITE_RULE[ASSUME `val(word outlen0:int64) = outlen0`; MATCH_MP LO_STORE_VAL (ASSUME `val(EL p (inlist:byte list)) MOD 16 < 9`)] th) else NO_TAC) THEN
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`s25:x86state`))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) DIV 16`))c
             then ASSUME_TAC(REWRITE_RULE[MATCH_MP HI_STORE_VAL (ASSUME `val(EL p (inlist:byte list)) DIV 16 < 9`)] th) else NO_TAC) THEN
          CONJ_TAC THENL
           [FIRST_X_ASSUM(fun th -> let c=concl th in
               if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c && not(can(find_term is_cond)c)
               then MP_TAC th else NO_TAC) THEN
            STORE4_FROM_SPEC `s25:x86state` `word_add res (word(4 * outlen0)):int64`;
            SUBGOAL_THEN `word_add (word_add res (word (4 * outlen0))) (word 4):int64 = word_add res (word (4 * (outlen0+1)))` SUBST1_TAC THENL
             [CONV_TAC WORD_RULE; ALL_TAC] THEN
            FIRST_X_ASSUM(fun th -> let c=concl th in
               if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) DIV 16`))c && not(can(find_term is_cond)c)
               then MP_TAC th else NO_TAC) THEN
            STORE4_FROM_SPEC `s25:x86state` `word_add res (word(4 * (outlen0+1))):int64`]]];
      (* ===== LO-only (low<9, high>=9): jae pc+383 taken -> pc+314 =====    *)
      SUBGOAL_THEN `&(val(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32) (word 9):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL
         [MP_TAC(ASSUME `~(val(EL p (inlist:byte list)) DIV 16 < 9)`) THEN ARITH_TAC;
          MP_TAC(ISPEC `EL p (inlist:byte list)` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
          MP_TAC(SPECL[`val(EL p (inlist:byte list))`;`16`] DIV_LE) THEN ARITH_TAC]; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (19--20) THEN DISCARD_OLDSTATE_TAC "s20" THEN
      ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist):int32 list) = outlen0 + 1` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LEN_STEP_LO) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        DISCH_THEN(fun th->REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC); ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [RCX_INC_TAC;
        SUBGOAL_THEN `REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist) =
           APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                  [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]` SUBST1_TAC THENL
         [MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_LO) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `4 * (outlen0 + 1) = 4 * outlen0 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s20:x86state`;
           `REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list`;
           `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]`;
           `4*outlen0`; `4`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[DIMINDEX_32] THEN
          FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC) THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_WORDLIST_SINGLETON_INT32] THEN
        CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          SUBGOAL_THEN `val(word outlen0:int64) = outlen0` ASSUME_TAC THENL
           [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `outlen0<256`) THEN ARITH_TAC; ALL_TAC] THEN
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`s20:x86state`))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c
             then ASSUME_TAC(REWRITE_RULE[ASSUME `val(word outlen0:int64) = outlen0`; MATCH_MP LO_STORE_VAL (ASSUME `val(EL p (inlist:byte list)) MOD 16 < 9`)] th) else NO_TAC) THEN
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c && not(can(find_term is_cond)c)
             then MP_TAC th else NO_TAC) THEN
          STORE4_FROM_SPEC `s20:x86state` `word_add res (word(4 * outlen0)):int64`]]];
    (* ===== REJECT-LOW (low>=9): jae pc+347 taken -> pc+371 =====           *)
    SUBGOAL_THEN `&(val(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32) (word 9):int32))` ASSUME_TAC THENL
     [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL
       [MP_TAC(ASSUME `~(val(EL p (inlist:byte list)) MOD 16 < 9)`) THEN ARITH_TAC;
        MP_TAC(SPECL[`val(EL p (inlist:byte list))`;`16`] MOD_LT_EQ) THEN ARITH_TAC]; ALL_TAC] THEN
    X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (9--12) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[R11_NIBBLE_VAL]) THEN DISCARD_OLDSTATE_TAC "s12" THEN
    ASM_CASES_TAC `val(EL p (inlist:byte list)) DIV 16 < 9` THENL
     [(* HI-only (low>=9, high<9): jae pc+383 not taken -> store at res+4*outlen0 -> pc+314 *)
      SUBGOAL_THEN `~(&(val(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32) (word 9):int32)))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (13--16) THEN
      SUBGOAL_THEN `val(word outlen0:int64) = outlen0` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `outlen0<256`) THEN ARITH_TAC; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (17--19) THEN DISCARD_OLDSTATE_TAC "s19" THEN
      FIRST_X_ASSUM(fun th -> let c=concl th in
         if is_eq c && can(find_term(fun t->t=`RAX`))c && can(find_term(fun t->t=`s19:x86state`))c
         then ASSUME_TAC(REWRITE_RULE[MATCH_MP RAX_INC (ASSUME `outlen0<256`)] th) else NO_TAC) THEN
      ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist):int32 list) = outlen0 + 1` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LEN_STEP_HI) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        DISCH_THEN(fun th->REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC); ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [RCX_INC_TAC;
        SUBGOAL_THEN `REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist) =
           APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                  [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) DIV 16))):int32]` SUBST1_TAC THENL
         [MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_HI) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `4 * (outlen0 + 1) = 4 * outlen0 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s19:x86state`;
           `REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list`;
           `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) DIV 16))):int32]`;
           `4*outlen0`; `4`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[DIMINDEX_32] THEN
          FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC) THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_WORDLIST_SINGLETON_INT32] THEN
        CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`s19:x86state`))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) DIV 16`))c
             then ASSUME_TAC(REWRITE_RULE[ASSUME `val(word outlen0:int64) = outlen0`; MATCH_MP HI_STORE_VAL (ASSUME `val(EL p (inlist:byte list)) DIV 16 < 9`)] th) else NO_TAC) THEN
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) DIV 16`))c && not(can(find_term is_cond)c)
             then MP_TAC th else NO_TAC) THEN
          STORE4_FROM_SPEC `s19:x86state` `word_add res (word(4 * outlen0)):int64`]];
      (* NONE (low>=9, high>=9): jae pc+383 taken -> pc+314, no store        *)
      SUBGOAL_THEN `&(val(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32) (word 9):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL
         [MP_TAC(ASSUME `~(val(EL p (inlist:byte list)) DIV 16 < 9)`) THEN ARITH_TAC;
          MP_TAC(ISPEC `EL p (inlist:byte list)` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
          MP_TAC(SPECL[`val(EL p (inlist:byte list))`;`16`] DIV_LE) THEN ARITH_TAC]; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (13--14) THEN DISCARD_OLDSTATE_TAC "s14" THEN
      ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist):int32 list) = outlen0` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LEN_STEP_NONE) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        DISCH_THEN(fun th->REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC); ALL_TAC] THEN
      SUBGOAL_THEN `REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist):int32 list = REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist)` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_NONE) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN RCX_INC_TAC]]);;

(* --- scalar_tail_run ---                                                   *)
(* ========================================================================= *)
(* SCALAR_TAIL_RUN: byte-loop-to-exit by strong induction on byte-budget d.  *)
(* Needs hyp LENGTH(REJ(SUB(0,p)))<=256 (the SIMD loop exits with outlen<=256, *)
(* so count-exit gives outlen=256 exactly = cap length). Load after main +   *)
(* .scalar_tail_lemmas + .scalar_tail_build + .scalar_body_lemma.            *)
(*                                                                           *)
(* . Induction on d; 4-way split                                             *)
(* per step: count-exit (outlen>=256), offset-exit (p=272), mid-byte exit    *)
(* (outlen=255 /\ low<9), clean-recursive (body trip then IH at p+1 via      *)
(* ENSURES_SEQUENCE_TAC + ENSURES_PRECONDITION/POSTCONDITION_THM).           *)
(* ========================================================================= *)

(* LENGTH(BUTLAST mldsa_rej_uniform_eta4_tmc) = 402 (tmc has length 403).    *)
let LENGTH_BUTLAST_TMC = prove
 (`LENGTH(BUTLAST mldsa_rej_uniform_eta4_tmc) = 402`,
  MP_TAC(ISPEC `mldsa_rej_uniform_eta4_tmc` LENGTH_BUTLAST_GEN) THEN
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_MLDSA_REJ_UNIFORM_ETA4_TMC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let SCALAR_TAIL_RUN = prove
 (`!d res buf table (inlist:byte list) pc (p:num) stackpointer.
        272 - p <= d /\
        LENGTH inlist = 272 /\
        nonoverlapping_modulo (2 EXP 64) (pc, 403) (val res,1024) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 403) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 403) (val table,2048) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val table,2048) /\
        p <= 272 /\
        LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) <= 256
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word(pc + 314) /\ read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list)) /\
                  read RCX s = word p /\
                  read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list))) s =
                    num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist)))
             (\s. read RIP s = word(pc + LENGTH(BUTLAST mldsa_rej_uniform_eta4_tmc)) /\
                  (let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES inlist) in
                   read RAX s = word(LENGTH outlist) /\
                   read(memory :> bytes(res, 4 * LENGTH outlist)) s = num_of_wordlist outlist))
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
              MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,,
              MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`,
  INDUCT_TAC THENL
   [(* ================= BASE CASE: d = 0 => p = 272 ================= *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `p = 272` SUBST_ALL_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> let c=concl th in c=`272 - p <= 0` || c=`p <= 272`))) THEN ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `inlist:byte list` SUB_LIST_BYTE_272) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `SUB_LIST(0,272) (inlist:byte list) = inlist`]) THEN
    REWRITE_TAC[ASSUME `SUB_LIST(0,272) (inlist:byte list) = inlist`] THEN
    ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = 256` THENL
     [(* --- BASE COUNT-EXIT: outlen = 256 --- *)
      MP_TAC(SPEC `REJ_SAMPLE_ETA4_BYTES inlist:int32 list` SUB_LIST_256_LE) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      REWRITE_TAC[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = 256`] THEN
      REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = REJ_SAMPLE_ETA4_BYTES inlist`] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `&(val(word_zx(word 256:int64):int32)):int - &256 = &(val(word_sub(word_zx(word 256:int64):int32) (word 256):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = 256`] THEN
      REWRITE_TAC[LENGTH_BUTLAST_TMC] THEN ASM_REWRITE_TAC[];
      (* --- BASE OFFSET-EXIT: outlen < 256, p = 272 ---                     *)
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) < 256` ASSUME_TAC THENL
       [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> let c=concl th in c=`LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) <= 256` || c=`~(LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = 256)`))) THEN ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `REJ_SAMPLE_ETA4_BYTES inlist:int32 list` SUB_LIST_256_LE) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = REJ_SAMPLE_ETA4_BYTES inlist`] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `~(&(val(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list)):int64):int32)):int - &256 = &(val(word_sub(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list)):int64):int32) (word 256):int32)))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      SUBGOAL_THEN `&(val(word_zx(word 272:int64):int32)):int - &272 = &(val(word_sub(word_zx(word 272:int64):int32) (word 272):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[LENGTH_BUTLAST_TMC] THEN ASM_REWRITE_TAC[]];
    (* ================= STEP CASE: SUC d =================                  *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_CASES_TAC `256 <= LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list)` THENL
     [(* --- STEP COUNT-EXIT: outlen >= 256 (=256 by invariant) --- *)
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) = 256` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`inlist:byte list`; `p:num`] SUB_LIST_256_PREFIX_GE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      MP_TAC(SPEC `REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list` SUB_LIST_256_LE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN DISCH_TAC THEN
      SUBGOAL_THEN `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist)`;
                  ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) = 256`] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `&(val(word_zx(word 256:int64):int32)):int - &256 = &(val(word_sub(word_zx(word 256:int64):int32) (word 256):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) = 256`; LENGTH_BUTLAST_TMC] THEN
      ASM_REWRITE_TAC[];
      (* --- not count-exit: outlen < 256 ---                                *)
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) < 256` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `p = 272` THENL
       [(* --- STEP OFFSET-EXIT: p = 272 --- *)
        FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `p = 272`)) THEN
        MP_TAC(SPEC `inlist:byte list` SUB_LIST_BYTE_272) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `SUB_LIST(0,272) (inlist:byte list) = inlist`]) THEN
        REWRITE_TAC[ASSUME `SUB_LIST(0,272) (inlist:byte list) = inlist`] THEN
        MP_TAC(SPEC `REJ_SAMPLE_ETA4_BYTES inlist:int32 list` SUB_LIST_256_LE) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
        REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = REJ_SAMPLE_ETA4_BYTES inlist`] THEN
        ENSURES_INIT_TAC "s0" THEN
        SUBGOAL_THEN `~(&(val(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list)):int64):int32)):int - &256 = &(val(word_sub(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list)):int64):int32) (word 256):int32)))` ASSUME_TAC THENL
         [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
        SUBGOAL_THEN `&(val(word_zx(word 272:int64):int32)):int - &272 = &(val(word_sub(word_zx(word 272:int64):int32) (word 272):int32))` ASSUME_TAC THENL
         [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
        X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--4) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        REWRITE_TAC[LENGTH_BUTLAST_TMC] THEN ASM_REWRITE_TAC[];
        (* --- p < 272 ---                                                   *)
        SUBGOAL_THEN `p < 272` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) = 255 /\ val(EL p (inlist:byte list)) MOD 16 < 9` THENL
         [(* --- STEP MID-BYTE EXIT: outlen=255, low<9 (accept low pushes to 256) --- *)
          FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (fun th -> is_conj(concl th) && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))(concl th))) THEN
          SUBGOAL_THEN `256 <= LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list)` ASSUME_TAC THENL
           [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_STEP_1) THEN
            ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `?rest. REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list =
             APPEND (APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                            [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]) rest`
           STRIP_ASSUME_TAC THENL
           [ASM_CASES_TAC `val(EL p (inlist:byte list)) DIV 16 < 9` THENL
             [EXISTS_TAC `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) DIV 16))):int32]` THEN
              MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_BOTH) THEN
              ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
              DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[APPEND; GSYM APPEND_ASSOC];
              EXISTS_TAC `[]:int32 list` THEN
              MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_LO) THEN
              ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
              DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[APPEND_NIL]]; ALL_TAC] THEN
          MP_TAC(SPECL [`inlist:byte list`; `p+1`] SUB_LIST_256_PREFIX_GE) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
          SUBGOAL_THEN `LENGTH(APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                            [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]:int32 list) = 256` ASSUME_TAC THENL
           [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) =
               APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                      [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]` ASSUME_TAC THENL
           [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && (try lhs(concl th) = `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list)` with _->false) then SUBST1_TAC th else NO_TAC) THEN
            FIRST_X_ASSUM(fun th -> if is_eq(concl th) && (try lhs(concl th) = `REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list` with _->false) then SUBST1_TAC th else NO_TAC) THEN
            W(fun (asl,gl) -> let lt = rhs gl in
               MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (mk_comb(`SUB_LIST(0,256):(int32)list->(int32)list`, lt)) THEN
               CONJ_TAC THENL
                [MATCH_MP_TAC SUB_LIST_APPEND_LEFT THEN ASM_REWRITE_TAC[LE_REFL];
                 MATCH_MP_TAC SUB_LIST_256_LE THEN ASM_REWRITE_TAC[LE_REFL]]); ALL_TAC] THEN
          REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) =
                APPEND (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist))
                [word_sx (word_sub (word 4:int16) (word (val (EL p (inlist:byte list)) MOD 16))):int32]`] THEN
          REWRITE_TAC[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) = 255`] THEN
          ENSURES_INIT_TAC "s0" THEN
          MP_TAC(ISPECL [`inlist:byte list`; `buf:int64`; `s0:x86state`; `p:num`; `272`] READ_1BYTE_EL) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
          SUBGOAL_THEN `~(&(val(word_zx(word 255:int64):int32)):int - &256 = &(val(word_sub(word_zx(word 255:int64):int32) (word 256):int32)))` ASSUME_TAC THENL
           [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
          SUBGOAL_THEN `~(&(val(word_zx(word p:int64):int32)):int - &272 = &(val(word_sub(word_zx(word p:int64):int32) (word 272):int32)))` ASSUME_TAC THENL
           [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
          X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--8) THEN
          SUBGOAL_THEN `word_add buf (word (1 * val (word p:int64))) = word_add buf (word p):int64` ASSUME_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
            MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `p < 272`) THEN ARITH_TAC; ALL_TAC] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `word_add buf (word (1 * val (word p:int64))) = word_add buf (word p):int64`;
                                      ASSUME `read (memory :> bytes8 (word_add buf (word p))) s4 = EL p (inlist:byte list)`;
                                      R10_NIBBLE_VAL]) THEN
          DISCARD_OLDSTATE_TAC "s8" THEN
          SUBGOAL_THEN `~(&(val(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32) (word 9):int32)))` ASSUME_TAC THENL
           [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (9--14) THEN
          DISCARD_OLDSTATE_TAC "s14" THEN
          SUBGOAL_THEN `&(val(word_zx(word 256:int64):int32)):int - &256 = &(val(word_sub(word_zx(word 256:int64):int32) (word 256):int32))` ASSUME_TAC THENL
           [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
          X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (15--16) THEN
          ENSURES_FINAL_STATE_TAC THEN
          REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) =
                APPEND (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist))
                [word_sx (word_sub (word 4:int16) (word (val (EL p (inlist:byte list)) MOD 16))):int32]`] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
          REWRITE_TAC[ASSUME `LENGTH(APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]:int32 list) = 256`] THEN
          REWRITE_TAC[LENGTH_BUTLAST_TMC] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
          (* memory fold: bytes(res,4*256) = APPEND prefix [lo]              *)
          SUBGOAL_THEN `4 * 256 = 4 * 255 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
          MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s16:x86state`;
             `REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list`;
             `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]`;
             `4*255`; `4`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
          ANTS_TAC THENL [REWRITE_TAC[DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_WORDLIST_SINGLETON_INT32] THEN
          CONJ_TAC THENL
           [ASM_REWRITE_TAC[];
            SUBGOAL_THEN `word(4 * 255):int64 = word 1020` SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
            FIRST_X_ASSUM(fun th -> let c=concl th in
               if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`s16:x86state`))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c
               then ASSUME_TAC(REWRITE_RULE[MATCH_MP LO_STORE_VAL (ASSUME `val(EL p (inlist:byte list)) MOD 16 < 9`)] th) else NO_TAC) THEN
            FIRST_X_ASSUM(fun th -> let c=concl th in
               if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c && not(can(find_term is_cond)c) && can(find_term(fun t->t=`s16:x86state`))c
               then MP_TAC th else NO_TAC) THEN
            STORE4_FROM_SPEC `s16:x86state` `word_add res (word 1020):int64`];
          (* --- STEP CLEAN-RECURSIVE: body trip then IH at p+1 ---          *)
          SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list) <= 256` ASSUME_TAC THENL
           [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_STEP_1) THEN ASM_REWRITE_TAC[] THEN
            DISCH_THEN SUBST1_TAC THEN
            REPEAT(FIRST_X_ASSUM(MP_TAC o check(fun th -> let c=concl th in
               c = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) < 256` ||
               c = `~(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) = 255 /\ val(EL p (inlist:byte list)) MOD 16 < 9)`))) THEN
            REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ARITH_TAC; ALL_TAC] THEN
          (* body lemma instance at (p, outlen(p))                           *)
          MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`p:num`;
             `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list)`;`stackpointer:int64`] SCALAR_TAIL_BODY) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(fun body_th ->
            let bodyQ = rand(rator(concl body_th)) in
            ENSURES_SEQUENCE_TAC `pc + 314` bodyQ THEN
            CONJ_TAC THENL
             [(* leg1: P -> bodyQ via the body lemma (precond/postcond weaken) *)
              MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
              EXISTS_TAC (rand(rator(concl body_th))) THEN CONJ_TAC THENL
               [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
                MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
                EXISTS_TAC (rand(rator(rator(concl body_th)))) THEN CONJ_TAC THENL
                 [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
                  ACCEPT_TAC body_th]];
              (* leg2: bodyQ -> R = IH at p+1                                *)
              ALL_TAC]) THEN
          (* leg2: weaken pre to IH's expanded pre, then apply IH@(p+1)      *)
          FIRST_X_ASSUM(fun ih -> if is_forall(concl ih) then
            (let ih_inst = SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`p+1`;`stackpointer:int64`] ih in
             let ih_pre = rand(rator(rator(snd(dest_imp(concl ih_inst))))) in
             MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC ih_pre THEN CONJ_TAC THENL
              [GEN_TAC THEN BETA_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
               MP_TAC ih_inst THEN ANTS_TAC THENL
                [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]])
            else NO_TAC)]]]]);;

(* ========================================================================= *)
(* SCALAR_TAIL_AT_P: the scalar-tail contract at an ARBITRARY exit position p *)
(* (not just 16*N). This is the form CORRECT's leg-2 uses: the SIMD region   *)
(* can exit at any sub-iter offset p (via a mid-guard), and at that exit     *)
(* niblen(p)<=256 always holds (OUTLEN0_LE_256_FROM_SUBITER: the guard 4 bytes *)
(* earlier ensured niblen(p-4)<=248, +<=8 = <=256), from RUN.                *)
(* ========================================================================= *)
let MLDSA_REJ_UNIFORM_ETA4_SCALAR_TAIL_AT_P = prove
 (`!res buf table (inlist:byte list) pc p stackpointer.
        LENGTH inlist = 272 /\
        nonoverlapping_modulo (2 EXP 64) (pc, 403) (val res,1024) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 403) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (pc, 403) (val table,2048) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val buf, 272) /\
        nonoverlapping_modulo (2 EXP 64) (val res,1024) (val table,2048) /\
        p <= 272 /\
        LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) <= 256
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word(pc + 314) /\ read RSP s = stackpointer /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
                  read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                  read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list)) /\
                  read RCX s = word p /\
                  read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list))) s =
                    num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist)))
             (\s. read RIP s = word(pc + LENGTH(BUTLAST mldsa_rej_uniform_eta4_tmc)) /\
                  (let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES inlist) in
                   read RAX s = word(LENGTH outlist) /\
                   read(memory :> bytes(res, 4 * LENGTH outlist)) s = num_of_wordlist outlist))
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
              MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(res,1024)])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`272 - p`; `res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`p:num`;`stackpointer:int64`] SCALAR_TAIL_RUN) THEN
  ASM_REWRITE_TAC[LE_REFL]);;

(* --- subiter_bridge_lemmas ---                                             *)
(* ========================================================================= *)
(* Sub-iteration spec bridges for the Phase-2 SIMD-loop RE-DECOMPOSITION.    *)
(* eta4's SIMD loop has per-sub-iteration `cmp eax,248; ja scalar` mid-guards *)
(* (file offsets 0xa0/0xd8/0x10d; the head 0x3c also has cmp ecx,256). To get *)
(* the TIGHT outlen0<=256 bound at scalar-tail entry (which the 16-byte-block *)
(* invariant only bounds <=280), the loop must be counted at 4-byte sub-iter *)
(* granularity. Each sub-iteration adds <=8 output coefficients, and the     *)
(* outlen<=256 bound follows from the per-sub-iter accounting below.         *)
(* ========================================================================= *)

(* A 4-byte sub-iteration contributes <= 8 output coefficients.              *)
let SUBITER_STEP_BOUND_8 = prove
 (`!(inlist:byte list) k.
     LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(k,4) inlist):int32 list) <= 8`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `SUB_LIST(k,4) (inlist:byte list)` LENGTH_REJ_SAMPLE_ETA4_BYTES_BOUND) THEN
  REWRITE_TAC[LENGTH_SUB_LIST] THEN ARITH_TAC);;

(* Processing 4 more input bytes appends their samples; length grows by <= 8. *)
let SUBITER_BRIDGE_ETA4 = prove
 (`!(inlist:byte list) p.
     p + 4 <= LENGTH inlist
     ==> REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+4) inlist):int32 list =
           APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                  (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(p,4) inlist)) /\
         LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+4) inlist):int32 list) =
           LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) +
           LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(p,4) inlist):int32 list) /\
         LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(p,4) inlist):int32 list) <= 8`,
  REPEAT STRIP_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `p + 4 = 0 + (p + 4)`] THEN
    MP_TAC(ISPECL [`inlist:byte list`;`p:num`;`4`;`0`] SUB_LIST_SPLIT) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES_APPEND];
    ONCE_REWRITE_TAC[ARITH_RULE `p + 4 = 0 + (p + 4)`] THEN
    MP_TAC(ISPECL [`inlist:byte list`;`p:num`;`4`;`0`] SUB_LIST_SPLIT) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REJ_SAMPLE_ETA4_BYTES_APPEND; LENGTH_APPEND];
    REWRITE_TAC[SUBITER_STEP_BOUND_8]]);;

(* The TIGHT bound: count <=248 before the last sub-iter guard => <=256 after *)
(* processing the 4 bytes. This discharges SCALAR_TAIL_FROM_RUN's            *)
(* `LENGTH(REJ(SUB(0,16N)))<=256` hypothesis from the sub-iter loop invariant. *)
let OUTLEN0_LE_256_FROM_SUBITER = prove
 (`!(inlist:byte list) p.
     p + 4 <= LENGTH inlist /\
     LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) <= 248
     ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+4) inlist):int32 list) <= 256`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`inlist:byte list`;`p:num`] SUBITER_BRIDGE_ETA4) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> let c=concl th in
    can (find_term (fun t -> t = `REJ_SAMPLE_ETA4_BYTES(SUB_LIST(p,4) inlist):int32 list`)) c
    || c = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) <= 248`))) THEN
  ARITH_TAC);;

(* Prefix monotonicity of the output count: a<=b => niblen(SUB(0,a))<=niblen(SUB(0,b)). *)
(* Used by the sub-iter loop invariant to show no mid-guard fires before the exit step *)
(* (if niblen(p+4)<256 then niblen at every earlier sub-iter offset is also <256). *)
let REJ_SAMPLE_ETA4_PREFIX_MONO = prove
 (`!(inlist:byte list) a b.
     a <= b
     ==> LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,a) inlist):int32 list) <=
         LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,b) inlist):int32 list)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `SUB_LIST(0,b) (inlist:byte list) = APPEND (SUB_LIST(0,a) inlist) (SUB_LIST(a,b-a) inlist)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`inlist:byte list`;`a:num`;`b-a`;`0`] SUB_LIST_SPLIT) THEN
    ASM_SIMP_TAC[ADD_CLAUSES; ARITH_RULE `a <= b ==> a + (b - a) = b`];
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES_APPEND_LE]]);;

(* JA (Condition_NBE, unsigned >) TAKEN when a>k: companion of s2n-bignum's  *)
(* JA_NOT_TAKEN_LE. Negates the not-taken disjunction. Used in the exit-block *)
(* proof to resolve the mid-guards `cmp eax,248; ja scalar` when the running *)
(* count exceeds 248 (the guard fires -> exit to pc+314).                    *)
let CORRECT_LOOPINV =
 `\i s. read RSP s = stackpointer /\
        read (memory :> bytes (buf, 272)) s = num_of_wordlist inlist /\
        read (memory :> bytes (table,2048)) s = num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
        read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
        read YMM2 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
        read YMM3 s = word 1816346497840254045859937019744124044757176230049263749638550337379029484548 /\
        read YMM4 s = word 4086779620140571603184858294424279100703646517610843436686738259102816340233 /\
        read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list)) /\
        read RCX s = word(16*i) /\
        read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list))) s =
          num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist))`;;

(* Phase 0/1/2 scaffold. After this, ONE goal remains = the exit-block obligation. *)
let CORRECT_SCAFFOLD_TAC : tactic =
  MAP_EVERY X_GEN_TAC [`res:int64`; `buf:int64`; `table:int64`; `inlist:byte list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES; LENGTH_MLDSA_REJ_UNIFORM_ETA4_TMC] THEN
  STRIP_TAC THEN GHOST_INTRO_TAC `stackpointer:int64` `read RSP` THEN
  (* Phase 1: WOP                                                            *)
  SUBGOAL_THEN `?i. 256 < 16 * i \/ 248 < LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16 * i) inlist):int16 list)` MP_TAC THENL
   [EXISTS_TAC `17:num` THEN ARITH_TAC; GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LT] th)) THEN
  SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES] THEN
    REWRITE_TAC[REJ_NIBBLES_ETA4_EMPTY; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  (* N=1 impossible: niblen(16)<=32<248 and 256<16 false                     *)
  ASM_CASES_TAC `N = 1` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = 1`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    REWRITE_TAC[ARITH_RULE `~(256 < 16 * 1)`] THEN
    MP_TAC(ISPECL [`inlist:byte list`; `16`] LENGTH_REJ_SAMPLE_ETA4_BYTES_SUB_LIST_BOUND) THEN
    ASM_REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
    REWRITE_TAC[ARITH_RULE `16 * 1 = 16`] THEN ARITH_TAC; ALL_TAC] THEN
  (* Phase 2: clean-block loop over N-1 iterations                           *)
  ENSURES_WHILE_UP_TAC `N - 1` `pc + 52` `pc + 52` CORRECT_LOOPINV THEN
  REPEAT CONJ_TAC THENL
   [(* G0 ~(N-1=0) *)
    REPEAT(FIRST_X_ASSUM(MP_TAC o check(fun th->concl th=`~(N=0)`||concl th=`~(N=1)`))) THEN ARITH_TAC;
    (* G1 init pc -> pc+52                                                   *)
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_ETA4_BYTES; REJ_NIBBLES_ETA4;
                NIBBLES_OF_BYTES; FILTER; MAP; LENGTH; num_of_wordlist] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_TRIVIAL] THEN CONV_TAC WORD_REDUCE_CONV;
    (* G2 body: CLEAN_BODY @ i + frame subsumption                           *)
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`N:num`;`i:num`;`stackpointer:int64`] MLDSA_REJ_UNIFORM_ETA4_CLEAN_BODY) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `i + 1 < N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i+1` o check(is_forall o concl)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN STRIP_TAC THEN
      REPEAT CONJ_TAC THEN (FIRST [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]); ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_FRAME_SUBSUMED) THEN
    REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN SUBSUMED_MAYCHANGE_TAC;
    (* G3 back-edge: refl                                                    *)
    REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    (* G4 exit obligation -- LEFT OPEN for the exit-block proof              *)
    ALL_TAC] THEN
  (* exit-block entry facts (hyp7 @ N-1)                                     *)
  SUBGOAL_THEN `16 * (N-1) <= 256 /\ LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*(N-1)) inlist):int16 list) <= 248` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `N-1` o check(is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(N-1)) inlist):int32 list) <= 248` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES]; ALL_TAC];;
(* Remaining after CORRECT_SCAFFOLD_TAC: the single exit-block goal at pc+52,
   pos=16(N-1), niblen<=248 -> CORRECT-post@pc+402. *)

(* --- exit_offset ---                                                       *)
(* EXIT_OFFSET development — offset arm of the exit block.                   *)
let exit_offset_tm = `
  !res buf table (inlist:byte list) pc N stackpointer.
       LENGTH inlist = 272 /\
       nonoverlapping_modulo (2 EXP 64) (pc, 403) (val res,1024) /\
       nonoverlapping_modulo (2 EXP 64) (pc, 403) (val buf, 272) /\
       nonoverlapping_modulo (2 EXP 64) (pc, 403) (val table,2048) /\
       nonoverlapping_modulo (2 EXP 64) (val res,1024) (val buf, 272) /\
       nonoverlapping_modulo (2 EXP 64) (val res,1024) (val table,2048) /\
       16 * N = 272 /\
       LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*N) inlist):int16 list) <= 248
       ==> ensures x86
            (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                 read RIP s = word(pc + 52) /\ read RSP s = stackpointer /\
                 read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                 read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
                 read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                 read YMM2 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
                 read YMM3 s = word 1816346497840254045859937019744124044757176230049263749638550337379029484548 /\
                 read YMM4 s = word 4086779620140571603184858294424279100703646517610843436686738259102816340233 /\
                 read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(N-1)) inlist):int32 list)) /\
                 read RCX s = word(16*(N-1)) /\
                 read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(N-1)) inlist):int32 list))) s =
                   num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(N-1)) inlist)))
            (\s. read RIP s = word(pc + LENGTH(BUTLAST mldsa_rej_uniform_eta4_tmc)) /\
                 (let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES inlist) in
                  read RAX s = word(LENGTH outlist) /\
                  read(memory :> bytes(res, 4 * LENGTH outlist)) s = num_of_wordlist outlist))
            (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
             MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(res,1024)])`;;

(* Q318: post-head-guard state at pc+314, pos=16N.                           *)
let q318 = `\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
      read RIP s = word(pc + 314) /\ read RSP s = stackpointer /\
      read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
      read(memory :> bytes(table,2048)) s = num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
      read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
      read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*N) inlist):int32 list)) /\
      read RCX s = word(16*N) /\
      read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*N) inlist):int32 list))) s =
        num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*N) inlist))`;;

let q56 = `\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
      read RIP s = word(pc + 52) /\ read RSP s = stackpointer /\
      read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
      read(memory :> bytes(table,2048)) s = num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
      read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
      read YMM2 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
      read YMM3 s = word 1816346497840254045859937019744124044757176230049263749638550337379029484548 /\
      read YMM4 s = word 4086779620140571603184858294424279100703646517610843436686738259102816340233 /\
      read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*N) inlist):int32 list)) /\
      read RCX s = word(16*N) /\
      read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*N) inlist):int32 list))) s =
        num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*N) inlist))`;;

let EXIT_OFFSET = prove(exit_offset_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*N) inlist):int16 list) <= 248` then ACCEPT_TAC th else NO_TAC); ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC q318 THEN
  CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [(* leg1: pc+52 -> Q318 : CLEAN_BLOCK@(N-1) [pc+52 pos16(N-1) -> pc+52 pos16N] then
       head guard cmp eax,248 (not taken, niblen(16N)<=248) + cmp ecx,256 (TAKEN, 16N=272>256) -> pc+314. *)
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC q56 THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN CONJ_TAC THENL
 [(* leg1a: CLEAN_BLOCK@(N-1), post pos=16N = q56 (modulo N-1+1 -> N)..
         Pre/post predicates match q56 exactly; only the MAYCHANGE frame differs
         (CLEAN_BLOCK has ZMM0;1;5;6, cframe has ZMM0..6) -> frame subsumption. *)
      SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL [UNDISCH_TAC `16 * N = 272` THEN ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`N:num`;`N-1`;`stackpointer:int64`] CLEAN_BLOCK) THEN
      SUBGOAL_THEN `N - 1 + 1 = N` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN (FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]); ALL_TAC] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_FRAME_SUBSUMED) THEN
      REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN SUBSUMED_MAYCHANGE_TAC;
 (* leg1b: q56 (pc+52 pos16N) -> Q318 via head guards..
         Guards stated in 272-form (16*N=272) because the stepper rewrites the flag
         predicates to 272-form, so the ja branch decision must match that form.
         cmp eax,248 (s1) not taken [niblen(272)<=248]; ja (s2); cmp ecx,256 (s3) TAKEN [272>256]; ja (s4)->pc+314. *)
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,272) inlist):int32 list) <= 248` ASSUME_TAC THENL
       [UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` THEN
        SUBST1_TAC(ASSUME `16 * N = 272`) THEN REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~(&(val(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,272) inlist):int32 list)):int64):int32)):int - &248 = &(val(word_sub(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,272) inlist):int32 list)):int64):int32) (word 248):int32))) \/ val(word_sub(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,272) inlist):int32 list)):int64):int32) (word 248):int32) = 0` ASSUME_TAC THENL
       [MATCH_MP_TAC JA_NOT_TAKEN_LE THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(~(&(val(word_zx(word(272):int64):int32)):int - &256 = &(val(word_sub(word_zx(word(272):int64):int32) (word 256):int32))) \/ val(word_sub(word_zx(word(272):int64):int32) (word 256):int32) = 0)` ASSUME_TAC THENL
       [MATCH_MP_TAC JA_TAKEN_GT THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--4) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `16 * N = 272`]) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];
    (* leg2: Q318 -> pc+402 : SCALAR_TAIL_AT_P @ p=16N. Weaken precond to AT_P's pre. *)
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
    EXISTS_TAC (rand(rator(rator(snd(dest_imp(concl(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`16*N`;`stackpointer:int64`] MLDSA_REJ_UNIFORM_ETA4_SCALAR_TAIL_AT_P))))))) THEN
    CONJ_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`16*N`;`stackpointer:int64`]
                   MLDSA_REJ_UNIFORM_ETA4_SCALAR_TAIL_AT_P) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN
        (FIRST [FIRST_ASSUM ACCEPT_TAC;
                ASM_ARITH_TAC;
                (FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` then MP_TAC th else NO_TAC) THEN ARITH_TAC)]);
        DISCH_THEN ACCEPT_TAC]]]);;

(* --- exit_block ---                                                        *)
(* ========================================================================= *)
(* EXIT_BLOCK: the single remaining goal after CORRECT_SCAFFOLD_TAC.         *)
(* Splits on niblen(SUB(0,16N))<=248:                                        *)
(*  - OFFSET arm (<=248): forces 16N=272 (N=17), apply EXIT_OFFSET.          *)
(*  - MID-EXIT arm (>248): a cmp eax,248;ja mid-guard fires inside the i=N-1 *)
(*    block at the first sub-iter offset p where niblen(p)>248 -> pc+314@p,  *)
(*    then SCALAR_TAIL_AT_P@p.                                               *)
(* Load after: full CLEAN_BODY chain, CLEAN_BLOCK, .exit_offset (EXIT_OFFSET), *)
(* .subiter_bridge_lemmas, .scalar_tail_run (AT_P), .correct_scaffold.       *)
(* ========================================================================= *)

(* let-free EXIT_OFFSET so its post matches the scaffold goal post verbatim. *)
let EXIT_OFFSET_NOLET = CONV_RULE(TOP_DEPTH_CONV let_CONV) EXIT_OFFSET;;

(* OFFSET arm: niblen(16N)<=248 in assumptions -> 16N=272 -> EXIT_OFFSET..   *)
let OFFSET_ARM_TAC : tactic =
  SUBGOAL_THEN `16 * N = 272` ASSUME_TAC THENL
   [SUBGOAL_THEN `256 < 16 * N` ASSUME_TAC THENL
     [UNDISCH_TAC `256 < 16 * N \/ 248 < LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (0,16 * N) inlist):int16 list)` THEN
      REWRITE_TAC[GSYM LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
      UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` THEN
      ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `N = 17` (fun th -> REWRITE_TAC[th] THEN CONV_TAC NUM_REDUCE_CONV) THEN
    UNDISCH_TAC `16 * (N-1) <= 256` THEN UNDISCH_TAC `256 < 16 * N` THEN
    UNDISCH_TAC `~(N=0)` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MATCH_MP_TAC EXIT_OFFSET_NOLET THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` THEN
  SUBST1_TAC(ASSUME `16 * N = 272`) THEN REWRITE_TAC[];;

(* --- midexit_prefix ---                                                    *)
(* PREFIX_TO_S21_TAC: the bound-independent body of PREFIX_G_FULL_TAC (gather/store s17 +
   counter steps 18-21 + SUBITER_BLOCK_BYTES + m8def rewrite), reaching s21 with
   RAX=acc-popcount, RCX, store(16i+4). Uses ONLY niblen(16i)<=248 (true in all exit cases).
   Shared by the clean (not-taken) and MID-EXIT (taken) guard resolutions. Extracted verbatim
   from .prefix_g_full_tac.ml lines 2-333. *)
(* Generator for the value + memory-safety twins of the prefix-to-s21 body     *)
(* stepping.  The two are identical except the MS variant strips the events     *)
(* existential right after ENSURES_INIT (STRIP_EXISTS_ASSUM_TAC), so it is a    *)
(* `memsafe` flag toggling that one step.                                       *)
let mk_prefix_to_s21 (memsafe:bool) : tactic =
  REPEAT GEN_TAC THEN
  (ALL_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `16 * i <= 256` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (i + 1) <= 272` THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_INIT_TAC "s0" THEN
  (if memsafe then STRIP_EXISTS_ASSUM_TAC else ALL_TAC) THEN
  MP_TAC(SPECL [`buf:int64`;`272`;`inlist:byte list`;`i:num`;`s0:x86state`] SUB_LIST_16_BYTES_FROM_INT128) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `16 * (i + 1) <= 272` THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `chunk0 = read(memory:>bytes128(word_add buf (word(16*i)))) s0` THEN DISCH_TAC THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) <= 248` ASSUME_TAC THENL
   [FIRST [FIRST_ASSUM ACCEPT_TAC;
           (* mid-exit: derive from a later sample bound niblen(16i+4k)<=248 via prefix monotonicity *)
           (FIRST_X_ASSUM(fun th -> match concl th with
              Comb(Comb(Const("<=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),k) when k=`248`
                -> MP_TAC th | _ -> NO_TAC) THEN
            MATCH_MP_TAC(ARITH_RULE `a <= b ==> b <= 248 ==> a <= 248`) THEN
            MATCH_MP_TAC REJ_SAMPLE_ETA4_PREFIX_MONO THEN ARITH_TAC);
           (REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
            TRANS_TAC LE_TRANS `LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16 * (i+1)) inlist):int16 list)` THEN
            ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NIBLEN_PREFIX_MONO THEN ARITH_TAC)]; ALL_TAC] THEN
  ABBREV_TAC `outlen0 = LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list)` THEN
  FIRST_ASSUM(fun th -> if concl th =
      `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list) = outlen0`
    then (RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) else NO_TAC) THEN
  MP_TAC(SPECL [`outlen0:num`;`248`] JA_NOT_TAKEN_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`16*i`;`256`] JA_NOT_TAKEN_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  VAL_INT64_TAC `outlen0:num` THEN
  X86_STEPS_TAC EXEC (1--2) THEN
  SUBGOAL_THEN `read RIP s2 = word(pc + 63):int64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && can(find_term((=)`&248:int`))(concl th)
                           then ASSUME_TAC(MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if can(find_term((=)`pc + 314`))(concl th) then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC; ALL_TAC] THEN
  X86_STEPS_TAC EXEC (3--4) THEN
  SUBGOAL_THEN `read RIP s4 = word(pc + 75):int64` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && can(find_term((=)`&256:int`))(concl th)
                           then ASSUME_TAC(MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))))) else NO_TAC) THEN
    FIRST_X_ASSUM(fun th -> if can(find_term((=)`pc + 314`))(concl th) then MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC; ALL_TAC] THEN
  X86_VSTEPS_TAC EXEC (5--5) THEN
  SUBGOAL_THEN `val(word(16*i):int64) = 16*i` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    UNDISCH_TAC `16*i <= 256` THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `val(word(16*i):int64) = 16*i`; ARITH_RULE `1 * x = x`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read (memory :> bytes128 (word_add buf (word (16 * i)))) s4 = chunk0`]) THEN
  SUBGOAL_THEN `read YMM0 s5 = usimd16 (\b:byte. word_zx b:int16) chunk0:int256` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can(find_term((=)`read YMM0 s5`))(lhand(concl th)) then SUBST1_TAC th else NO_TAC) THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DROP_WORDJOIN_TAC THEN PURGE_STALE_STATES_TAC ["s4"] THEN
  X86_VSTEPS_TAC EXEC (6--6) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s5 = usimd16 (\b:byte. word_zx b:int16) chunk0:int256`]) THEN
  X86_VSTEPS_TAC EXEC (7--7) THEN X86_VSTEPS_TAC EXEC (8--8) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM2 s5 =
    word 6811299366900952671974763824040465167839410862684739061144563765171360567055:int256`]) THEN
  SUBGOAL_THEN (mk_eq(`read YMM0 s8:int256`, F0NIB_CHUNK0)) ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && can(find_term((=)`read YMM0 s8`))(lhand(concl th)) then SUBST1_TAC th else NO_TAC) THEN
    REWRITE_TAC[usimd16;usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128] THEN
    CONV_TAC WORD_BLAST; ALL_TAC] THEN
  DROP_WORDJOIN_TAC THEN PURGE_STALE_STATES_TAC ["s5";"s6";"s7"] THEN
  ASSUME_TAC(SPEC `chunk0:int128` F0NIB_BYTES) THEN
  ASSUME_TAC(SPEC `chunk0:int128` F0NIB_BYTES_HI) THEN
  ABBREV_TAC `fn:int256 = read YMM0 s8` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(ASSUME(mk_eq(`fn:int256`, F0NIB_CHUNK0)))]) THEN
  X86_VSTEPS_TAC EXEC (9--9) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s8 = fn:int256`;
     ASSUME `read YMM4 s8 = word 4086779620140571603184858294424279100703646517610843436686738259102816340233:int256`]) THEN
  ABBREV_TAC `f1bnd:int256 = read YMM1 s9` THEN
  X86_VSTEPS_TAC EXEC (10--10) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s9 = fn:int256`;
     ASSUME `read YMM3 s9 = word 1816346497840254045859937019744124044757176230049263749638550337379029484548:int256`]) THEN
  ABBREV_TAC `f0sub:int256 = read YMM0 s10` THEN
  W(fun (asl,w) ->
      let f0d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f0sub:int256`) (map snd asl) in
      let gather_imp = prove
       (mk_imp(concl f0d,
        `!j. j < 8 ==>
           word_subword (word_subword (f0sub:int256) (0,128):int128) (8*j,8):byte =
           word_sub (word 4) (word(EL j [val(word_subword (chunk0:int128) (0,8):byte) MOD 16;
              val(word_subword chunk0 (0,8):byte) DIV 16; val(word_subword chunk0 (8,8):byte) MOD 16;
              val(word_subword chunk0 (8,8):byte) DIV 16; val(word_subword chunk0 (16,8):byte) MOD 16;
              val(word_subword chunk0 (16,8):byte) DIV 16; val(word_subword chunk0 (24,8):byte) MOD 16;
              val(word_subword chunk0 (24,8):byte) DIV 16]):byte)`),
        DISCH_THEN(fun f0eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN
          SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
          REWRITE_TAC[f0eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC)) in
      ASSUME_TAC (MP gather_imp f0d)) THEN
  (* bg2: sub-iter-2 gather forall over the >>64-shifted low-lane source g2 (lanes 8-15 /
     chunk0 nibbles 32,40,48,56). Derived early (f0sub word_join live); survives to s28.
     Built as the SUBITER_STORE_SPEC gather-hyp shape so SI2_FOLD discharges by MATCH_ACCEPT. *)
  W(fun (asl,w) ->
      let f0d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f0sub:int256`) (map snd asl) in
      let g2 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128) 64):int128):int128` in
      let bg2_concl = List.nth (conjuncts(lhand(concl(ISPECL [g2; `word (val (mask8b:int64) MOD 256):byte`;
           `word_subword (chunk0:int128) (32,8):byte`; `word_subword (chunk0:int128) (40,8):byte`;
           `word_subword (chunk0:int128) (48,8):byte`; `word_subword (chunk0:int128) (56,8):byte`] SUBITER_STORE_SPEC)))) 1 in
      let bg2_imp = prove(mk_imp(concl f0d, bg2_concl),
        DISCH_THEN(fun f0eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[SUBWORD_USHR] THEN CONV_TAC NUM_REDUCE_CONV THEN
          SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
          REWRITE_TAC[f0eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC)) in
      ASSUME_TAC (MP bg2_imp f0d)) THEN
  (* bg3: sub-iter-3 gather forall over the HIGH 128 lane g3 (lanes 16-23 / chunk0 nibbles 64,72,80,88).
     No shift (vextracti128 ,1 then vpshufb). Same JOIN-extract proof as bg1 (no SUBWORD_USHR). *)
  W(fun (asl,w) ->
      let f0d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f0sub:int256`) (map snd asl) in
      let g3 = `word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128` in
      let bg3_concl = List.nth (conjuncts(lhand(concl(ISPECL [g3; `word (val (mask8c:int64) MOD 256):byte`;
           `word_subword (chunk0:int128) (64,8):byte`; `word_subword (chunk0:int128) (72,8):byte`;
           `word_subword (chunk0:int128) (80,8):byte`; `word_subword (chunk0:int128) (88,8):byte`] SUBITER_STORE_SPEC)))) 1 in
      let bg3_imp = prove(mk_imp(concl f0d, bg3_concl),
        DISCH_THEN(fun f0eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN
          SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
          REWRITE_TAC[f0eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC)) in
      ASSUME_TAC (MP bg3_imp f0d)) THEN
  (* bg4: sub-iter-4 gather forall over the HIGH 128 lane >>64 (lanes 24-31 / chunk0 nibbles 96,104,112,120). *)
  W(fun (asl,w) ->
      let f0d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f0sub:int256`) (map snd asl) in
      let g4 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128) 64):int128):int128` in
      let bg4_concl = List.nth (conjuncts(lhand(concl(ISPECL [g4; `word (val (mask8d:int64) MOD 256):byte`;
           `word_subword (chunk0:int128) (96,8):byte`; `word_subword (chunk0:int128) (104,8):byte`;
           `word_subword (chunk0:int128) (112,8):byte`; `word_subword (chunk0:int128) (120,8):byte`] SUBITER_STORE_SPEC)))) 1 in
      let bg4_imp = prove(mk_imp(concl f0d, bg4_concl),
        DISCH_THEN(fun f0eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `j<8 ==> j=0\/j=1\/j=2\/j=3\/j=4\/j=5\/j=6\/j=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[WORD_ZX_TRIVIAL] THEN
          REWRITE_TAC[SUBWORD_USHR] THEN CONV_TAC NUM_REDUCE_CONV THEN
          SIMP_TAC[WORD_SUBWORD_SUBWORD;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
          REWRITE_TAC[f0eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REFL_TAC)) in
      ASSUME_TAC (MP bg4_imp f0d)) THEN
  (* MASKBIT forall derived NOW (f1bnd word_join def still present): bit 7(f1bnd lane k) <=>
     EL k[chunk0 nibbles]<9. ASSUME it — survives the DROP below + downstream purges. Used by
     counter stage 3b. *)
  W(fun (asl,w) ->
      let f1d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f1bnd:int256`) (map snd asl) in
      let maskbit_imp = prove
       (mk_imp(concl f1d,
        `!k. k < 8 ==> (bit 7 (word_subword (f1bnd:int256) (8*(k+16),8):byte) <=>
            EL k ([val(word_subword (chunk0:int128) (64,8):byte) MOD 16; val(word_subword chunk0 (64,8):byte) DIV 16;
                  val(word_subword chunk0 (72,8):byte) MOD 16; val(word_subword chunk0 (72,8):byte) DIV 16;
                  val(word_subword chunk0 (80,8):byte) MOD 16; val(word_subword chunk0 (80,8):byte) DIV 16;
                  val(word_subword chunk0 (88,8):byte) MOD 16; val(word_subword chunk0 (88,8):byte) DIV 16]:num list) < 9)`),
        DISCH_THEN(fun f1eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `k<8 ==> k=0\/k=1\/k=2\/k=3\/k=4\/k=5\/k=6\/k=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
          REWRITE_TAC[f1eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN
          W(fun (asl2,w2) ->
             let nibarg = find_term (fun u -> match u with
                Comb(Comb(Const("MOD",_),_),_) | Comb(Comb(Const("DIV",_),_),_) -> true | _ -> false) w2 in
             let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_subword" &&
               type_of u = `:byte` && can(find_term(fun v->v=`chunk0:int128`)) u with _->false) w2 in
             let valeq = prove(mk_eq(mk_comb(`val:byte->num`, mk_comb(`word:num->byte`, nibarg)), nibarg),
                REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let nlt16 = prove(mk_binop `(<):num->num->bool` nibarg `16`,
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let vp = REWRITE_RULE[valeq] (SPEC (mk_comb(`word:num->byte`, nibarg)) VPSUBB_SIGN_BIT_LT_9) in
             ACCEPT_TAC (MP vp nlt16)))) in
      ASSUME_TAC (MP maskbit_imp f1d)) THEN
  W(fun (asl,w) ->
      let f1d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f1bnd:int256`) (map snd asl) in
      let maskbit_imp = prove
       (mk_imp(concl f1d,
        `!k. k < 8 ==> (bit 7 (word_subword (f1bnd:int256) (8*(k+24),8):byte) <=>
            EL k ([val(word_subword (chunk0:int128) (96,8):byte) MOD 16; val(word_subword chunk0 (96,8):byte) DIV 16;
                  val(word_subword chunk0 (104,8):byte) MOD 16; val(word_subword chunk0 (104,8):byte) DIV 16;
                  val(word_subword chunk0 (112,8):byte) MOD 16; val(word_subword chunk0 (112,8):byte) DIV 16;
                  val(word_subword chunk0 (120,8):byte) MOD 16; val(word_subword chunk0 (120,8):byte) DIV 16]:num list) < 9)`),
        DISCH_THEN(fun f1eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `k<8 ==> k=0\/k=1\/k=2\/k=3\/k=4\/k=5\/k=6\/k=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
          REWRITE_TAC[f1eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN
          W(fun (asl2,w2) ->
             let nibarg = find_term (fun u -> match u with
                Comb(Comb(Const("MOD",_),_),_) | Comb(Comb(Const("DIV",_),_),_) -> true | _ -> false) w2 in
             let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_subword" &&
               type_of u = `:byte` && can(find_term(fun v->v=`chunk0:int128`)) u with _->false) w2 in
             let valeq = prove(mk_eq(mk_comb(`val:byte->num`, mk_comb(`word:num->byte`, nibarg)), nibarg),
                REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let nlt16 = prove(mk_binop `(<):num->num->bool` nibarg `16`,
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let vp = REWRITE_RULE[valeq] (SPEC (mk_comb(`word:num->byte`, nibarg)) VPSUBB_SIGN_BIT_LT_9) in
             ACCEPT_TAC (MP vp nlt16)))) in
      ASSUME_TAC (MP maskbit_imp f1d)) THEN
  W(fun (asl,w) ->
      let f1d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f1bnd:int256`) (map snd asl) in
      let maskbit_imp2 = prove
       (mk_imp(concl f1d,
        `!k. k < 8 ==> (bit 7 (word_subword (f1bnd:int256) (8*(k+8),8):byte) <=>
            EL k ([val(word_subword (chunk0:int128) (32,8):byte) MOD 16; val(word_subword chunk0 (32,8):byte) DIV 16;
                  val(word_subword chunk0 (40,8):byte) MOD 16; val(word_subword chunk0 (40,8):byte) DIV 16;
                  val(word_subword chunk0 (48,8):byte) MOD 16; val(word_subword chunk0 (48,8):byte) DIV 16;
                  val(word_subword chunk0 (56,8):byte) MOD 16; val(word_subword chunk0 (56,8):byte) DIV 16]:num list) < 9)`),
        DISCH_THEN(fun f1eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `k<8 ==> k=0\/k=1\/k=2\/k=3\/k=4\/k=5\/k=6\/k=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
          REWRITE_TAC[f1eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN
          W(fun (asl2,w2) ->
             let nibarg = find_term (fun u -> match u with
                Comb(Comb(Const("MOD",_),_),_) | Comb(Comb(Const("DIV",_),_),_) -> true | _ -> false) w2 in
             let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_subword" &&
               type_of u = `:byte` && can(find_term(fun v->v=`chunk0:int128`)) u with _->false) w2 in
             let valeq = prove(mk_eq(mk_comb(`val:byte->num`, mk_comb(`word:num->byte`, nibarg)), nibarg),
                REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let nlt16 = prove(mk_binop `(<):num->num->bool` nibarg `16`,
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let vp = REWRITE_RULE[valeq] (SPEC (mk_comb(`word:num->byte`, nibarg)) VPSUBB_SIGN_BIT_LT_9) in
             ACCEPT_TAC (MP vp nlt16)))) in
      ASSUME_TAC (MP maskbit_imp2 f1d)) THEN
  W(fun (asl,w) ->
      let f1d = find (fun th -> is_eq(concl th) && lhand(concl th) = `f1bnd:int256`) (map snd asl) in
      (* prove `f1bnd = wj ==> (!k...)` as a CLOSED implication (f1d discharged as antecedent,
         so the result has NO extra hyps), then MP with f1d. The DISCH'd eq is used to rewrite. *)
      let maskbit_imp = prove
       (mk_imp(concl f1d,
        `!k. k < 8 ==> (bit 7 (word_subword (f1bnd:int256) (8*k,8):byte) <=>
            EL k ([val(word_subword (chunk0:int128) (0,8):byte) MOD 16; val(word_subword chunk0 (0,8):byte) DIV 16;
                  val(word_subword chunk0 (8,8):byte) MOD 16; val(word_subword chunk0 (8,8):byte) DIV 16;
                  val(word_subword chunk0 (16,8):byte) MOD 16; val(word_subword chunk0 (16,8):byte) DIV 16;
                  val(word_subword chunk0 (24,8):byte) MOD 16; val(word_subword chunk0 (24,8):byte) DIV 16]:num list) < 9)`),
        DISCH_THEN(fun f1eq -> REPEAT STRIP_TAC THEN
          FIRST_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
            (ARITH_RULE `k<8 ==> k=0\/k=1\/k=2\/k=3\/k=4\/k=5\/k=6\/k=7`)) THEN
          CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
          REWRITE_TAC[f1eq] THEN
          REPEAT(CHANGED_TAC(SIMP_TAC[WORD_SUBWORD_JOIN_LOWER; WORD_SUBWORD_JOIN_UPPER;
                   DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256;ARITH] THEN
            CONV_TAC NUM_REDUCE_CONV)) THEN
          REWRITE_TAC[WORD_SUBWORD_BYTE_ID] THEN
          W(fun (asl2,w2) ->
             let nibarg = find_term (fun u -> match u with
                Comb(Comb(Const("MOD",_),_),_) | Comb(Comb(Const("DIV",_),_),_) -> true | _ -> false) w2 in
             let bt = find_term (fun u -> try fst(dest_const(fst(strip_comb u)))="word_subword" &&
               type_of u = `:byte` && can(find_term(fun v->v=`chunk0:int128`)) u with _->false) w2 in
             let valeq = prove(mk_eq(mk_comb(`val:byte->num`, mk_comb(`word:num->byte`, nibarg)), nibarg),
                REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN MATCH_MP_TAC MOD_LT THEN
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let nlt16 = prove(mk_binop `(<):num->num->bool` nibarg `16`,
                MP_TAC(REWRITE_RULE[DIMINDEX_8](ISPEC bt VAL_BOUND)) THEN ARITH_TAC) in
             let vp = REWRITE_RULE[valeq] (SPEC (mk_comb(`word:num->byte`, nibarg)) VPSUBB_SIGN_BIT_LT_9) in
             ACCEPT_TAC (MP vp nlt16)))) in
      ASSUME_TAC (MP maskbit_imp f1d)) THEN
  (* DROP f0sub/f1bnd word_join defs BEFORE vpmovmskb (s11).
     This keeps R8/R9's vpmovmskb+popcount over the OPAQUE `f1bnd` var (via the
     `read YMM1 s10 = f1bnd` fold) instead of the expanded word_join, so stage d's popeq / low8 /
     BOOL_CASES (over `word_subword f1bnd (8k,8)`) match the popcount term. Without this, R9 s21 =
     popcount(...word_join expanded...) and stage d leaves unsolved goals. *)
  REPEAT(FIRST_X_ASSUM(fun th ->
     if is_eq(concl th) && (lhand(concl th) = `f0sub:int256` || lhand(concl th) = `f1bnd:int256`)
     then ALL_TAC else failwith "keep")) THEN
  (* ---- STEP s11-s17 FIRST (vpmovmskb, vextracti128, movzbl R10 capture, vmovq, vpshufb,
     vpmovsxbd, vmovdqu store), keeping f0sub/f1bnd defs. The gather/mask SUBGOALs are proven
     AFTER stepping: their `EL j [...]`-shaped assumptions confuse X86_VSTEPS' simulator
     (vextracti128 at s12 fails with "mk_comb: types do not agree" if they're in context). ---- *)
  X86_VSTEPS_TAC EXEC (11--11) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM1 s10 = f1bnd:int256`]) THEN
  PURGE_STALE_STATES_TAC ["s10"] THEN
  X86_VSTEPS_TAC EXEC (12--12) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read YMM0 s11 = f0sub:int256`]) THEN
  PURGE_STALE_STATES_TAC ["s11"] THEN
  REABBREV_TAC `mask8 = read R8 s12` THEN
  X86_VERBOSE_STEP_TAC EXEC "s13" THEN
  MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s12 = mask8:int64`]) THEN
  (SUBGOAL_THEN maskbit_tgt ASSUME_TAC THENL [MASKBIT_TGT_TAC; ALL_TAC]) THEN
  X86_VSTEPS_TAC EXEC (14--14) THEN
  TAB1_TEQ_TAC THEN
  REABBREV_TAC `tab1 = read YMM6 s14` THEN
  X86_VSTEPS_TAC EXEC (15--15) THEN REABBREV_TAC `pshuf1 = read YMM6 s15` THEN
  PURGE_STALE_STATES_TAC ["s14"] THEN
  X86_VSTEPS_TAC EXEC (16--16) THEN REABBREV_TAC `sx1 = read YMM1 s16` THEN
  (* stepA: establish sx1 = usimd8 word_sx (word_zx(word_zx pshuf1)) (the vpmovsxbd lane form). *)
  SUBGOAL_THEN `sx1:int256 = usimd8 (\b:byte. word_sx b:int32) (word_zx(word_zx (pshuf1:int256):int128):int64)` ASSUME_TAC THENL
   [W(fun (asl,w) ->
       let sx1def = find (fun th -> is_eq(concl th) && rand(concl th)=`sx1:int256` &&
           can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
       SUBST1_TAC(SYM sx1def) THEN
       REWRITE_TAC[usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
       CONV_TAC WORD_BLAST);
    ALL_TAC] THEN
  PURGE_STALE_STATES_TAC ["s15"] THEN
  X86_STEPS_TAC EXEC (17--17) THEN
  PURGE_STALE_STATES_TAC ["s16"] THEN
  X86_STEPS_TAC EXEC (18--21) THEN
  MP_TAC(ISPECL[`inlist:byte list`;`i:num`;`chunk0:int128`] SUBITER_BLOCK_BYTES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `LENGTH(inlist:byte list) = 272` THEN
    UNDISCH_TAC `16 * i <= 256` THEN ARITH_TAC; STRIP_TAC] THEN
  W(fun (asl,w) ->
     let m8def = find (fun th -> match concl th with Comb(Comb(Const("=",_),_),Var("mask8",_)) -> true | _ -> false) (map snd asl) in
     RULE_ASSUM_TAC(fun th -> if concl th = maskbit_tgt ||
        can(find_term(fun u->match u with Const("TABLE_ENTRY",_)->true|_->false))(concl th)
        then th else REWRITE_RULE[GSYM m8def] th)) THEN
  ALL_TAC);;

let PREFIX_TO_S21_TAC : tactic = mk_prefix_to_s21 false;;


(* --- mg1_nt ---                                                            *)
(* MG1_NT_TAC: from s21 (pc+152, sub-iter-1 gather done, RAX=popcount-accumulate),
   resolve mid-guard-1 NOT-taken (niblen(16i+4)<=248 direct hyp) -> RIP s23 = pc+163.
   Assumes pop_len-style facts derivable; mirrors PREFIX_G_FULL tail but bound direct.
   Leaves pop_len, bridge, rax_red0 ASSUMEd for the subsequent SI1_FOLD_V2. *)
let mk_mg1_nt (memsafe:bool) : tactic =
  W(fun (asl,w) ->
    let r9 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("R9",_)),Var("s21",_))),_) -> true | _ -> false) asl in
    let goal_pc = find_term (fun t -> match t with Comb(Const("word_popcount",_),_) -> true | _ -> false) (concl(snd r9)) in
    let low8 = `bitval(bit 7 (word_subword (f1bnd:int256) (0,8):byte)) + bitval(bit 7 (word_subword f1bnd (8,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (16,8):byte)) + bitval(bit 7 (word_subword f1bnd (24,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (32,8):byte)) + bitval(bit 7 (word_subword f1bnd (40,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (48,8):byte)) + bitval(bit 7 (word_subword f1bnd (56,8):byte))` in
    let mr = CONV_RULE(DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV)
               (SPEC `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` MOD_RED) in
    let popeq = prove(mk_eq(goal_pc, low8),
      REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
      REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; MOD_MOD_EXP_MIN] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; mr] THEN
      MAP_EVERY (fun b -> BOOL_CASES_TAC b)
        [`bit 7 (word_subword (f1bnd:int256) (0,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (8,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (16,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (24,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (32,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (40,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (48,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (56,8):byte)`] THEN
      REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV) in
    let maskbit = snd(find (fun (_,th) -> let c=concl th in is_forall c &&
        can(find_term(fun u->u=`f1bnd:int256`))c && can(find_term(fun u->match u with Comb(Const("bit",_),_)->true|_->false))c &&
        not(can(find_term(fun u->match u with Const("word_zx",_)->true|_->false))c) &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (24,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (32,8):byte`))c)) asl) in
    let mb_tm = concl maskbit in
    let blk0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
           (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
    let blkeq = mk_eq(low8, `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list)`) in
    let blk0_tm = concl(snd blk0) in
    let bsum_raw = prove(mk_imp(mb_tm, mk_imp(blk0_tm, blkeq)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN DISCH_THEN(fun b -> REWRITE_TAC[b]) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER] THEN
      ASM_SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let bsum = MP (MP bsum_raw maskbit) (snd blk0) in
    let pop_len = TRANS popeq bsum in
    ASSUME_TAC pop_len) THEN
  (* bridge: outlen0 + niblen(SUB(16i,4)) = niblen_sample(16i+4)             *)
  SUBGOAL_THEN `outlen0 + LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list) = LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i`] SUBITER_BRIDGE_ETA4) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
    UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i) inlist):int32 list) = outlen0` THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  (* bnd1: outlen0 + niblen(SUB(16i,4)) <= 248  (= niblen_sample(16i+4) <= 248, direct hyp) *)
  SUBGOAL_THEN `outlen0 + LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list) <= 248` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),_)->true|_->false) then SUBST1_TAC th else NO_TAC) THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           (* mid-exit cases 3+: niblen(16i+4)<=248 follows from a later sample bound by monotonicity *)
           (FIRST_X_ASSUM(fun th -> match concl th with
              Comb(Comb(Const("<=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),k) when k=`248`
                -> MP_TAC th | _ -> NO_TAC) THEN
            MATCH_MP_TAC(ARITH_RULE `a <= b ==> b <= 248 ==> a <= 248`) THEN
            MATCH_MP_TAC REJ_SAMPLE_ETA4_PREFIX_MONO THEN ARITH_TAC)]; ALL_TAC] THEN
  W(fun (asl,w) ->
    let block0len = `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list)` in
    let sum = mk_binop `(+):num->num->num` `outlen0:num` block0len in
    let bnd = snd(find (fun (_,th) -> concl th = mk_binop `(<=):num->num->bool` sum `248`) asl) in
    let pop_len = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl) in
    let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let ja = MP (ISPECL[sum; `248`] JA_NOT_TAKEN_LE) (CONJ bnd (ARITH_RULE `248 < 2 EXP 32`)) in
    ASSUME_TAC pop_len THEN ASSUME_TAC bnd THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja) THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (22--23) THEN
  SUBGOAL_THEN `read RIP s23 = word (pc + 163):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let blk0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
             (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
      let rax_red0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
      let ja = find (fun (_,th) -> is_disj(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`248`))(concl th)) asl in
      rip_mp memsafe 163 23 THEN
      REWRITE_TAC[GSYM(snd blk0)] THEN REWRITE_TAC[snd rax_red0] THEN
      REWRITE_TAC[snd ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  (* fold RAX s23 read into clean word(acc1) form (mirrors PREFIX_G_FULL lines 426-431) so the
     subsequent SI2 store's memsafe can bound val(RAX)=acc1<=248. *)
  W(fun (asl,w) ->
    let pl = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl in
    let rr = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
    RULE_ASSUM_TAC(REWRITE_RULE[snd pl]) THEN RULE_ASSUM_TAC(REWRITE_RULE[snd rr]));;

let MG1_NT_TAC : tactic = mk_mg1_nt false;;
let MG1_NT_MS_TAC : tactic = mk_mg1_nt true;;

(* --- mg2_nt ---                                                            *)
(* MG2_NT_TAC: from s33, resolve mid-guard-2 NOT-taken (niblen(16i+8)<=248 direct) -> RIP s35=pc+215.
   = SI2_MG2_TAKEN's pop_len2/bridge2 build but JA_NOT_TAKEN_LE + RIP pc+215, ending with RAX-fold
   so the SI3 store memsafe at s41 discharges. *)
let mk_mg2_nt (memsafe:bool) : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
    let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
    let popcnt2 = REWRITE_RULE[m8b_def]
       (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE1)) in
    let lanesum8 = rand(concl popcnt2) in
    let mb2 = find_a (fun th -> let c=concl th in is_forall c &&
       can(find_term(fun u->u=`f1bnd:int256`))c &&
       can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),_) -> true | _ -> false))c) in
    let mb2_tm = concl mb2 in
    let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
    let blk16 = find_a (fun th -> is_eq(concl th) &&
       (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" &&
            length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le)) blk16) in
    let blk1_eq = el 1 (CONJUNCTS bb) in
    let block1 = `[word_subword (chunk0:int128) (32,8); word_subword chunk0 (40,8);
                   word_subword chunk0 (48,8); word_subword chunk0 (56,8)]:byte list` in
    let block1len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA4`, block1)) in
    let bsum2_raw = prove(mk_imp(mb2_tm, mk_eq(lanesum8, block1len_x)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV)
            (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER] THEN
      SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let pop_len2 = REWRITE_RULE[GSYM blk1_eq] (TRANS popcnt2 (MP bsum2_raw mb2)) in
    ASSUME_TAC pop_len2) THEN
  (* bridge2: acc1 + niblen(SUB(16i+4,4)) = niblen_sample(16i+8) = (acc2 conceptually) *)
  SUBGOAL_THEN `acc1 + LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+4,4) inlist):int16 list) = LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+4`] SUBITER_BRIDGE_ETA4) THEN
    ANTS_TAC THENL [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES; ARITH_RULE `(16*i+4)+4 = 16*i+8`] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) = acc1` then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  (* bnd: acc1 + block1len <= 248 (= niblen(16i+8)<=248 direct hyp)          *)
  SUBGOAL_THEN `acc1 + LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+4,4) inlist):int16 list) <= 248` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),_)->true|_->false) then SUBST1_TAC th else NO_TAC) THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           (* case-4: niblen(16i+8)<=248 follows from niblen(16i+12)<=248 by monotonicity *)
           (FIRST_X_ASSUM(fun th -> match concl th with
              Comb(Comb(Const("<=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),k) when k=`248`
                -> MP_TAC th | _ -> NO_TAC) THEN
            MATCH_MP_TAC(ARITH_RULE `a <= b ==> b <= 248 ==> a <= 248`) THEN
            MATCH_MP_TAC REJ_SAMPLE_ETA4_PREFIX_MONO THEN ARITH_TAC)]; ALL_TAC] THEN
  W(fun (asl,w) ->
    let block1len = `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+4,4) inlist):int16 list)` in
    let sum = mk_binop `(+):num->num->num` `acc1:num` block1len in
    let bnd = snd(find (fun (_,th) -> concl th = mk_binop `(<=):num->num->bool` sum `248`) asl) in
    let pop_len2 = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl) in
    let lt32 = MATCH_MP (ARITH_RULE `a + b <= 248 ==> a + b < 2 EXP 32`) bnd in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let ja = MP (ISPECL [sum; `248`] JA_NOT_TAKEN_LE) (CONJ bnd (ARITH_RULE `248 < 2 EXP 32`)) in
    ASSUME_TAC pop_len2 THEN ASSUME_TAC bnd THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja) THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (34--35) THEN
  SUBGOAL_THEN `read RIP s35 = word (pc + 215):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let pop_len2_old = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl in
      let zbe = MP (SPEC `val (mask8b:int64) MOD 256` zxbyte_eq) (ARITH_RULE `val (mask8b:int64) MOD 256 < 256`) in
      let pop_len2_typed = TRANS (AP_TERM `word_popcount:int32->num` zbe) (snd pop_len2_old) in
      let rax_red0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
      let ja = find (fun (_,th) -> is_disj(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`acc1:num`))(concl th)) asl in
      rip_mp memsafe 215 35 THEN
      REWRITE_TAC[pop_len2_typed] THEN REWRITE_TAC[snd rax_red0] THEN
      REWRITE_TAC[snd ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  (* RAX-fold so SI3 store memsafe discharges                                *)
  W(fun (asl,w) ->
    let pl = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl in
    let zbe = MP (SPEC `val (mask8b:int64) MOD 256` zxbyte_eq) (ARITH_RULE `val (mask8b:int64) MOD 256 < 256`) in
    let pl_typed = TRANS (AP_TERM `word_popcount:int32->num` zbe) (snd pl) in
    let rr = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
    RULE_ASSUM_TAC(REWRITE_RULE[pl_typed]) THEN RULE_ASSUM_TAC(REWRITE_RULE[snd rr]));;

let MG2_NT_TAC : tactic = mk_mg2_nt false;;
let MG2_NT_MS_TAC : tactic = mk_mg2_nt true;;

(* --- mg3_nt ---                                                            *)
(* MG3_NT_TAC: from s45, mid-guard-3 NOT-taken from direct niblen(16i+12)<=248 -> RIP s47=pc+268,
   with RAX-fold so the SI4 store memsafe at s53 discharges. Clone of SI3_MG3_TAKEN w/ JA_NOT_TAKEN_LE. *)
let mk_mg3_nt (memsafe:bool) : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let m8c_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8c:int64` | _ -> false) in
    let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
    let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
    let popcnt3 = REWRITE_RULE[m8b_def; m8c_def]
       (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE2)) in
    let lanesum = rand(concl popcnt3) in
    let mb3 = find_a (fun th -> let c=concl th in is_forall c &&
       can(find_term(fun u->u=`f1bnd:int256`))c &&
       can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),n) -> n=`16` | _ -> false))c) in
    let mb3_tm = concl mb3 in
    let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
    let blk16 = find_a (fun th -> is_eq(concl th) &&
       (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" &&
            length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le)) blk16) in
    let blk2_eq = el 2 (CONJUNCTS bb) in
    let block2 = `[word_subword (chunk0:int128) (64,8); word_subword chunk0 (72,8);
                   word_subword chunk0 (80,8); word_subword chunk0 (88,8)]:byte list` in
    let block2len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA4`, block2)) in
    let bsum3_raw = prove(mk_imp(mb3_tm, mk_eq(lanesum, block2len_x)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV)
            (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER] THEN
      SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let pop_len3 = REWRITE_RULE[GSYM blk2_eq] (TRANS popcnt3 (MP bsum3_raw mb3)) in
    ASSUME_TAC pop_len3) THEN
  (* bridge3: acc2 + niblen(SUB(16i+8,4)) = niblen_sample(16i+12)            *)
  SUBGOAL_THEN `acc2 + LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+8,4) inlist):int16 list) = LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+8`] SUBITER_BRIDGE_ETA4) THEN
    ANTS_TAC THENL [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES; ARITH_RULE `(16*i+8)+4 = 16*i+12`] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) = acc2` then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) < 2 EXP 32` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+8`] OUTLEN0_LE_256_FROM_SUBITER) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC;
        FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) = acc2` then SUBST1_TAC th else NO_TAC) THEN FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(16*i+8)+4 = 16*i+12`] THEN ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let block2len = `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+8,4) inlist):int16 list)` in
    let sum = mk_binop `(+):num->num->num` `acc2:num` block2len in
    let bridge3 = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc2",_)),_)),_) -> true | _ -> false) asl) in
    let lt32 = REWRITE_RULE[SYM bridge3] (snd(find (fun (_,th) -> concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) < 2 EXP 32`) asl)) in
    let pop_len3 = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl) in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let bnd = REWRITE_RULE[SYM bridge3] (snd(find (fun (_,th) -> concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) <= 248`) asl)) in
    let ja = MP (ISPECL [sum; `248`] JA_NOT_TAKEN_LE) (CONJ bnd (ARITH_RULE `248 < 2 EXP 32`)) in
    ASSUME_TAC pop_len3 THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja) THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (46--47) THEN
  SUBGOAL_THEN `read RIP s47 = word (pc + 268):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let asms = map snd asl in
      let find_a p = find p asms in
      let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
      let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
      let blk16 = find_a (fun th -> is_eq(concl th) &&
         (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" && length(dest_list(rand(concl th)))=16 with _->false)) in
      let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                  (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le)) blk16) in
      let blk2_eq = el 2 (CONJUNCTS bb) in
      let rax_red0 = find_a (fun th -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) ->
            can(find_term(fun u->u=`acc2:num`))(concl th) | _ -> false) in
      let ja = find_a (fun th -> is_disj(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`acc2:num`))(concl th)) in
      rip_mp memsafe 268 47 THEN
      REWRITE_TAC[GSYM blk2_eq] THEN REWRITE_TAC[rax_red0] THEN
      REWRITE_TAC[ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  (* RAX-fold so SI4 store memsafe discharges                                *)
  W(fun (asl,w) ->
    let pl = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl in
    let rr = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> can(find_term(fun u->u=`acc2:num`))(concl th) | _ -> false) asl in
    RULE_ASSUM_TAC(REWRITE_RULE[snd pl]) THEN RULE_ASSUM_TAC(REWRITE_RULE[snd rr]));;

let MG3_NT_TAC : tactic = mk_mg3_nt false;;
let MG3_NT_MS_TAC : tactic = mk_mg3_nt true;;

(* --- si4_body4 ---                                                         *)
(* SI4_BODY4_TAC: SI4_INTEGRATED body with forked SI4_PRE (acc3<=248 from direct niblen(16i+12)<=248).
   From s47/pc+268 (after MG3_NT) to s57/pc+52 at pos16(i+1) (back-edge), store folded to 16(i+1). *)
let SI4_BODY4_TAC : tactic =
  ABBREV_TAC `acc3 = acc2 + LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (16*i+8,4) inlist):int16 list)` THEN
  REABBREV_TAC `mask8d = read R8 s47` THEN
  SUBGOAL_THEN `acc3 <= 248` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),Var("acc3",_)),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_)))->true|_->false) then SUBST1_TAC th else NO_TAC) THEN
    FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  VAL_INT64_TAC `acc3:num` THEN
  ACC3_IDENT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) = acc3`]) THEN
  X86_VSTEPS_TAC EXEC (48--48) THEN
  X86_VERBOSE_STEP_TAC EXEC "s49" THEN MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s48 = mask8d:int64`]) THEN
  X86_VSTEPS_TAC EXEC (50--50) THEN TAB4_TEQ_TAC THEN REABBREV_TAC `tab4 = read YMM6 s50` THEN
  X86_VSTEPS_TAC EXEC (51--51) THEN REABBREV_TAC `pshuf4 = read YMM6 s51` THEN
  PURGE_STALE_STATES_TAC ["s50"] THEN
  X86_VSTEPS_TAC EXEC (52--52) THEN REABBREV_TAC `sx4 = read YMM1 s52` THEN
  VAL_INT64_TAC `acc3:num` THEN
  X86_STEPS_TAC EXEC (53--53) THEN
  SUBGOAL_THEN `sx4:int256 = usimd8 (\b:byte. word_sx b:int32) (word_zx(word_zx (pshuf4:int256):int128):int64)` ASSUME_TAC THENL
   [W(fun (asl,w) ->
       let sx4def = find (fun th -> is_eq(concl th) && rand(concl th)=`sx4:int256` &&
           can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
       SUBST1_TAC(SYM sx4def) THEN
       REWRITE_TAC[usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
       CONV_TAC WORD_BLAST);
    ALL_TAC] THEN
  (SUBGOAL_THEN maskbit_tgt_4 ASSUME_TAC THENL [MASKBIT_TGT_4_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN pf_target_4 ASSUME_TAC THENL [PF_PROOF_4; ALL_TAC]) THEN
  ACC3_IDENT_TAC THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let hasC nm th = can (find_term (fun u -> match u with Const(n,_) when n=nm -> true | _ -> false)) (concl th) in
    let bg4 = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f0sub:int256`))c &&
        can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (96,8):byte`))c &&
        can(find_term(fun u->u=`word_subword (f0sub:int256) (128,128):int128`))c) asms in
    let mthm4 = find (fun th -> concl th = maskbit_tgt_4) asms in
    let pfth4 = find (fun th -> concl th = pf_target_4) asms in
    let sx4u = find (fun th -> match concl th with Comb(Comb(Const("=",_),Var("sx4",_)),r)->can(find_term(fun u->match u with Const("usimd8",_)->true|_->false))r|_->false) asms in
    let storef0 = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),m),Var("s53",_))),Var("sx4",_)) -> can(find_term(fun u->match u with Const("bytes256",_)->true|_->false)) m |_->false) asms in
    let store_full = REWRITE_RULE[pfth4] (REWRITE_RULE[sx4u] storef0) in
    let g4 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128) 64):int128):int128` in
    let m = `word (val (mask8d:int64) MOD 256):byte` in
    let pc = ISPECL [`word_add res (word (4 * acc3)):int64`; `s53:x86state`; g4; m; `LENGTH(ACC_IDX (word (val (mask8d:int64) MOD 256):byte))`] SUBITER_STORE_POSTCOND in
    let res_th0 = MP pc (CONJ (SPEC m LACC8) store_full) in
    let spec = ISPECL [g4; m; `word_subword (chunk0:int128) (96,8):byte`; `word_subword (chunk0:int128) (104,8):byte`; `word_subword (chunk0:int128) (112,8):byte`; `word_subword (chunk0:int128) (120,8):byte`] SUBITER_STORE_SPEC in
    let rej_store = REWRITE_RULE[MP spec (CONJ mthm4 bg4)] res_th0 in
    let leninl = find (fun th -> concl th = `LENGTH(inlist:byte list)=272`) asms in
    let i116 = find (fun th -> concl th = `16 * (i + 1) <= 272`) asms in
    let blk16 = find (fun th -> is_eq(concl th) && hasC "SUB_LIST" th && (try length(dest_list(rand(concl th)))=16 with _->false)) asms in
    let bb = MP (ISPECL [`inlist:byte list`;`i:num`;`chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*(i+1)<=272 ==> 16*i+16<=272`) i116)) blk16) in
    let blk3_eq = el 3 (CONJUNCTS bb) in
    let lr0 = MP (ISPECL [m;`word_subword (chunk0:int128) (96,8):byte`;`word_subword (chunk0:int128) (104,8):byte`;`word_subword (chunk0:int128) (112,8):byte`;`word_subword (chunk0:int128) (120,8):byte`] LEN_RECONCILE_GEN) mthm4 in
    let lr = REWRITE_RULE[GSYM blk3_eq] lr0 in
    let rej_store1 = REWRITE_RULE[GSYM blk3_eq] rej_store in
    let acc3_ident = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),Var("acc3",_)) -> true | _ -> false) asms in
    let prefix_store0 = find (fun th -> (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s53",_))),_) -> true | _ -> false) &&
         hasC "num_of_wordlist" th && hasC "SUB_LIST" th && can(find_term(fun u->u=`acc3:num`))(lhand(concl th)) && not(hasC "ACC_IDX" th) && not(hasC "bytes256" th)) asms in
    let prefix_store = REWRITE_RULE[GSYM acc3_ident] prefix_store0 in
    let rej_store2 = REWRITE_RULE[GSYM acc3_ident] rej_store1 in
    let fold = MP (ISPECL [`res:int64`;`s53:x86state`;m;`SUB_LIST(16*i+12,4) (inlist:byte list)`;`SUB_LIST(0,16*i+12) (inlist:byte list)`] SUBITER_FOLD_STEP)
                  (CONJ lr (CONJ prefix_store rej_store2)) in
    let split = REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i+12`;`4`;`0`] SUB_LIST_SPLIT) in
    let clean = REWRITE_RULE[GSYM split; ARITH_RULE `(16*i+12)+4 = 16*i+16`] fold in
    ASSUME_TAC clean) THEN
  X86_STEPS_TAC EXEC (54--57);;
  ALL_TAC;;

(* --- midexit_subiter1 ---                                                  *)
(* MID_EXIT_SUBITER1: sub-iter-1 mid-guard fires TAKEN -> pc+314 at pos 16i+4.
   Entry pc+52/pos=16i (q56-style), niblen(16i)<=248, niblen(16i+4)>248, 16(i+1)<=272.
   Reaches pc+314 with RCX=16i+4, RAX=niblen(16i+4), store=REJ_SAMPLE(0,16i+4).
   Composes PREFIX_TO_S21_TAC (clean gather/store/counter to s21) + the mid-guard-1 TAKEN
   resolution (mirrors PREFIX's not-taken tail but uses JA_TAKEN_GT) + SI1_FOLD_V2 store fold.
   Load after: full CLEAN_BODY chain, .midexit_prefix (PREFIX_TO_S21_TAC), .subiter_bridge_lemmas. *)

(* midexit1_cframe: the MAYCHANGE frame shared by the mid-exit lemmas.       *)
let midexit1_cframe =
  `MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
   MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes (res,1024)]`;;

let midexit1_pre =
  `\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
       read RIP s = word(pc + 52) /\ read RSP s = stackpointer /\
       read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
       read(memory :> bytes(table,2048)) s = num_of_wordlist (mldsa_rej_uniform_table:byte list) /\
       read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
       read YMM2 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
       read YMM3 s = word 1816346497840254045859937019744124044757176230049263749638550337379029484548 /\
       read YMM4 s = word 4086779620140571603184858294424279100703646517610843436686738259102816340233 /\
       read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list)) /\
       read RCX s = word(16*i) /\
       read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist):int32 list))) s =
         num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i) inlist))`;;

let midexit1_post =
  `\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
       read RIP s = word(pc + 314) /\ read RSP s = stackpointer /\
       read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
       read(memory :> bytes(table,2048)) s = num_of_wordlist (mldsa_rej_uniform_table:byte list) /\
       read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
       read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i+4) inlist):int32 list)) /\
       read RCX s = word(16*i+4) /\
       read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i+4) inlist):int32 list))) s =
         num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i+4) inlist))`;;

let midexit1_tm =
  list_mk_forall([`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`i:num`;`stackpointer:int64`],
  mk_imp(list_mk_conj([`LENGTH (inlist:byte list) = 272`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 403) (val(res:int64),1024)`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 403) (val(buf:int64), 272)`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 403) (val(table:int64),2048)`;
    `nonoverlapping_modulo (2 EXP 64) (val(res:int64),1024) (val(buf:int64), 272)`;
    `nonoverlapping_modulo (2 EXP 64) (val(res:int64),1024) (val(table:int64),2048)`;
    `16 * (i + 1) <= 272`;
    `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i) inlist):int32 list) <= 248`;
    `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list)`]),
    list_mk_comb(`ensures x86`,[midexit1_pre; midexit1_post; midexit1_cframe])));;

let mk_midexit1 (memsafe:bool) (disch:tactic) : tactic =
(mk_prefix_to_s21 memsafe) THEN
  (* count facts                                                             *)
  SUBGOAL_THEN `16 * i + 4 <= LENGTH(inlist:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) <= 256` ASSUME_TAC THENL
   [MATCH_MP_TAC OUTLEN0_LE_256_FROM_SUBITER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) <= 256` THEN ARITH_TAC; ALL_TAC] THEN
  (* pop_len: word_popcount(...) = niblen(SUB(16i,4))                        *)
  W(fun (asl,w) ->
    let r9 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("R9",_)),Var("s21",_))),_) -> true | _ -> false) asl in
    let goal_pc = find_term (fun t -> match t with Comb(Const("word_popcount",_),_) -> true | _ -> false) (concl(snd r9)) in
    let low8 = `bitval(bit 7 (word_subword (f1bnd:int256) (0,8):byte)) + bitval(bit 7 (word_subword f1bnd (8,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (16,8):byte)) + bitval(bit 7 (word_subword f1bnd (24,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (32,8):byte)) + bitval(bit 7 (word_subword f1bnd (40,8):byte)) +
             bitval(bit 7 (word_subword f1bnd (48,8):byte)) + bitval(bit 7 (word_subword f1bnd (56,8):byte))` in
    let mr = CONV_RULE(DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV)
               (SPEC `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` MOD_RED) in
    let popeq = prove(mk_eq(goal_pc, low8),
      REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32; DIMINDEX_64] THEN
      REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`; MOD_MOD_EXP_MIN] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
      REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; mr] THEN
      MAP_EVERY (fun b -> BOOL_CASES_TAC b)
        [`bit 7 (word_subword (f1bnd:int256) (0,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (8,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (16,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (24,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (32,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (40,8):byte)`;
         `bit 7 (word_subword (f1bnd:int256) (48,8):byte)`;`bit 7 (word_subword (f1bnd:int256) (56,8):byte)`] THEN
      REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC WORD_REDUCE_CONV) in
    let maskbit = snd(find (fun (_,th) -> let c=concl th in is_forall c &&
        can(find_term(fun u->u=`f1bnd:int256`))c && can(find_term(fun u->match u with Comb(Const("bit",_),_)->true|_->false))c &&
        not(can(find_term(fun u->match u with Const("word_zx",_)->true|_->false))c) &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (24,8):byte`))c &&
        not(can(find_term(fun u->u=`word_subword (chunk0:int128) (32,8):byte`))c)) asl) in
    let mb_tm = concl maskbit in
    let blk0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
           (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
    let blkeq = mk_eq(low8, `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list)`) in
    let blk0_tm = concl(snd blk0) in
    let bsum_raw = prove(mk_imp(mb_tm, mk_imp(blk0_tm, blkeq)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN DISCH_THEN(fun b -> REWRITE_TAC[b]) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER] THEN
      ASM_SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let bsum = MP (MP bsum_raw maskbit) (snd blk0) in
    let pop_len = TRANS popeq bsum in
    ASSUME_TAC pop_len) THEN
  (* bridge: outlen0 + niblen(SUB(16i,4)) = niblen_sample(16i+4)             *)
  SUBGOAL_THEN `outlen0 + LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list) = LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i`] SUBITER_BRIDGE_ETA4) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
    UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i) inlist):int32 list) = outlen0` THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  (* lt32 + rax_red0 + ja_taken                                              *)
  SUBGOAL_THEN `outlen0 + LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list) < 2 EXP 32` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),_)->true|_->false) then SUBST1_TAC th else NO_TAC) THEN
    UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) < 2 EXP 32` THEN REWRITE_TAC[]; ALL_TAC] THEN
  W(fun (asl,w) ->
    let block0len = `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list)` in
    let sum = mk_binop `(+):num->num->num` `outlen0:num` block0len in
    let lt32 = snd(find (fun (_,th) -> concl th = mk_binop `(<):num->num->bool` sum `2 EXP 32`) asl) in
    let pop_len = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl) in
    let bridge = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),_) -> true | _ -> false) asl) in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let gt248 = REWRITE_RULE[SYM bridge] (snd(find (fun (_,th) -> concl th = `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list)`) asl)) in
    let ja_taken = MP (ISPECL [sum; `248`] JA_TAKEN_GT) (CONJ gt248 lt32) in
    ASSUME_TAC pop_len THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja_taken) THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (22--23) THEN
  (* resolve RIP s23 = pc+314 (mid-guard1 TAKEN)                             *)
  SUBGOAL_THEN `read RIP s23 = word (pc + 314):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let blk0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
             (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
      let rax_red0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
      let ja = find (fun (_,th) -> is_neg(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`248`))(concl th)) asl in
      rip_mp memsafe 314 23 THEN
      REWRITE_TAC[GSYM(snd blk0)] THEN REWRITE_TAC[snd rax_red0] THEN
      REWRITE_TAC[snd ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC] THEN
  SI1_FOLD_V2 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* discharge if-guard (taken), RAX collapse, RCX collapse                  *)
  W(fun (asl,w) ->
    let blk0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),l),_) -> (try let h,args=strip_comb l in fst(dest_const h)="SUB_LIST" &&
           (match args with [Comb(Comb(_,off),wid);_] -> wid=`4` && (match off with Comb(Comb(Const("*",_),_),_)->true|_->false) | _->false) with _->false) | _ -> false) asl in
    let rax_red0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
    let bridge = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("outlen0",_)),_)),_) -> true | _ -> false) asl in
    REWRITE_TAC[GSYM(snd blk0); snd rax_red0; snd bridge]) THEN
  W(fun (asl,w) ->
    let ntake = MP (ISPECL [`LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list)`;`248`] JA_TAKEN_GT)
                   (CONJ (ASSUME `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list)`)
                         (ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) < 2 EXP 32`)) in
    REWRITE_TAC[ntake]) THEN
  (* RCX collapse                                                            *)
  SUBGOAL_THEN `val(word(16*i):int64) = 16*i` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN UNDISCH_TAC `16*i<=256` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `16*i` RCX4_COLLAPSE) THEN
  ANTS_TAC THENL [UNDISCH_TAC `16*i<=256` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN disch;;
let MID_EXIT_SUBITER1 = prove(midexit1_tm, mk_midexit1 false ALL_TAC);;

(* --- midexit_subiter2 ---                                                  *)
(* MID_EXIT_SUBITER2: sub-iter-2 mid-guard fires TAKEN -> pc+314 at pos 16i+8.
   Entry pc+52/pos=16i (q56-style), niblen(16i+4)<=248 (mg1 not taken), niblen(16i+8)>248
   (mg2 taken), 16(i+1)<=272. Reaches pc+314 with RCX=16i+8, RAX=niblen(16i+8),
   store=REJ_SAMPLE(0,16i+8).
   Composes: prefix-monotonicity prelude (niblen(16i)<=248) + PREFIX_TO_S21 + MG1_NT (mg1 not
   taken -> pc+163) + SI1_FOLD_V2 + purge leftover COND-RIP-s23 + SI2_BODY (gather/store/counter
   to s33) + SI2_MG2_TAKEN (mg2 taken -> pc+314) + ENSURES_FINAL + RAX/RCX/guard discharge.
   Load after: full CLEAN_BODY chain, .midexit_prefix (PREFIX_TO_S21_TAC), .mg1_nt (MG1_NT_TAC),
 .subiter_bridge_lemmas, .midexit_subiter1 (RCX4_COLLAPSE).. *)

(* SI2_BODY_TAC: SI2_INTEGRATED body (gather/store-fold/counter to s33) w/o the not-taken mg2 resolve. *)
let SI2_BODY_TAC : tactic =
  REABBREV_TAC `mask8b = read R8 s23` THEN
  ABBREV_TAC `acc1 = outlen0 + LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST(16*i,4) inlist):int16 list)` THEN
  ACC1_IDENT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) = acc1`]) THEN
  X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (24--24) THEN
  X86_VERBOSE_STEP_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC "s25" THEN MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s24 = mask8b:int64`]) THEN
  X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (26--26) THEN TAB2_TEQ_TAC THEN REABBREV_TAC `tab2 = read YMM6 s26` THEN
  X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (27--27) THEN REABBREV_TAC `pshuf2 = read YMM6 s27` THEN
  PURGE_STALE_STATES_TAC ["s26"] THEN
  X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (28--28) THEN REABBREV_TAC `sx2 = read YMM1 s28` THEN
  VAL_INT64_TAC `acc1:num` THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (29--29) THEN
  SUBGOAL_THEN `sx2:int256 = usimd8 (\b:byte. word_sx b:int32) (word_zx(word_zx (pshuf2:int256):int128):int64)` ASSUME_TAC THENL
   [W(fun (asl,w) ->
       let sx2def = find (fun th -> is_eq(concl th) && rand(concl th)=`sx2:int256` &&
           can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
       SUBST1_TAC(SYM sx2def) THEN
       REWRITE_TAC[usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
       CONV_TAC WORD_BLAST);
    ALL_TAC] THEN
  (SUBGOAL_THEN maskbit_tgt_2 ASSUME_TAC THENL [MASKBIT_TGT_2_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN pf_target_2 ASSUME_TAC THENL [PF_PROOF_2; ALL_TAC]) THEN
  ACC1_IDENT_TAC THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let hasC nm th = can (find_term (fun u -> match u with Const(n,_) when n=nm -> true | _ -> false)) (concl th) in
    let bg2 = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f0sub:int256`))c &&
        can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))c &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (32,8):byte`))c) asms in
    let mthm2 = find (fun th -> concl th = maskbit_tgt_2) asms in
    let pfth2 = find (fun th -> concl th = pf_target_2) asms in
    let sx2u = find (fun th -> match concl th with Comb(Comb(Const("=",_),Var("sx2",_)),r)->can(find_term(fun u->match u with Const("usimd8",_)->true|_->false))r|_->false) asms in
    let storef0 = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),m),Var("s29",_))),Var("sx2",_)) -> can(find_term(fun u->match u with Const("bytes256",_)->true|_->false)) m |_->false) asms in
    let store_full = REWRITE_RULE[pfth2] (REWRITE_RULE[sx2u] storef0) in
    let g2 = `word_zx (word_zx (word_ushr (word_zx (word_zx (word_subword (f0sub:int256) (0,128):int128):int128):int128) 64):int128):int128` in
    let m = `word (val (mask8b:int64) MOD 256):byte` in
    let pc = ISPECL [`word_add res (word (4 * acc1)):int64`; `s29:x86state`; g2; m; `LENGTH(ACC_IDX (word (val (mask8b:int64) MOD 256):byte))`] SUBITER_STORE_POSTCOND in
    let res_th0 = MP pc (CONJ (SPEC m LACC8) store_full) in
    let spec = ISPECL [g2; m; `word_subword (chunk0:int128) (32,8):byte`; `word_subword (chunk0:int128) (40,8):byte`; `word_subword (chunk0:int128) (48,8):byte`; `word_subword (chunk0:int128) (56,8):byte`] SUBITER_STORE_SPEC in
    let rej_store = REWRITE_RULE[MP spec (CONJ mthm2 bg2)] res_th0 in
    let leninl = find (fun th -> concl th = `LENGTH(inlist:byte list)=272`) asms in
    let i116 = find (fun th -> concl th = `16 * (i + 1) <= 272`) asms in
    let blk16 = find (fun th -> is_eq(concl th) && hasC "SUB_LIST" th && (try length(dest_list(rand(concl th)))=16 with _->false)) asms in
    let bb = MP (ISPECL [`inlist:byte list`;`i:num`;`chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*(i+1)<=272 ==> 16*i+16<=272`) i116)) blk16) in
    let blk1_eq = el 1 (CONJUNCTS bb) in
    let lr0 = MP (ISPECL [m;`word_subword (chunk0:int128) (32,8):byte`;`word_subword (chunk0:int128) (40,8):byte`;`word_subword (chunk0:int128) (48,8):byte`;`word_subword (chunk0:int128) (56,8):byte`] LEN_RECONCILE_GEN) mthm2 in
    let lr = REWRITE_RULE[GSYM blk1_eq] lr0 in
    let rej_store1 = REWRITE_RULE[GSYM blk1_eq] rej_store in
    let acc1_ident = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),Var("acc1",_)) -> true | _ -> false) asms in
    let prefix_store0 = find (fun th -> (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s29",_))),_) -> true | _ -> false) &&
         hasC "num_of_wordlist" th && hasC "SUB_LIST" th && can(find_term(fun u->u=`acc1:num`))(lhand(concl th)) && not(hasC "ACC_IDX" th) && not(hasC "bytes256" th)) asms in
    let prefix_store = REWRITE_RULE[GSYM acc1_ident] prefix_store0 in
    let rej_store2 = REWRITE_RULE[GSYM acc1_ident] rej_store1 in
    let fold = MP (ISPECL [`res:int64`;`s29:x86state`;m;`SUB_LIST(16*i+4,4) (inlist:byte list)`;`SUB_LIST(0,16*i+4) (inlist:byte list)`] SUBITER_FOLD_STEP)
                  (CONJ lr (CONJ prefix_store rej_store2)) in
    let split = REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i+4`;`4`;`0`] SUB_LIST_SPLIT) in
    let clean = REWRITE_RULE[GSYM split; ARITH_RULE `(16*i+4)+4 = 16*i+8`] fold in
    ASSUME_TAC clean) THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (30--33);;

(* SI2_MG2_TAKEN_TAC: from s33, resolve mid-guard-2 TAKEN (niblen(16i+8)>248) -> RIP s35 = pc+314. *)
let mk_si2_mg2_taken (memsafe:bool) : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
    let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
    let popcnt2 = REWRITE_RULE[m8b_def]
       (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE1)) in
    let lanesum8 = rand(concl popcnt2) in
    let mb2 = find_a (fun th -> let c=concl th in is_forall c &&
       can(find_term(fun u->u=`f1bnd:int256`))c &&
       can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),_) -> true | _ -> false))c) in
    let mb2_tm = concl mb2 in
    let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
    let blk16 = find_a (fun th -> is_eq(concl th) &&
       (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" &&
            length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le)) blk16) in
    let blk1_eq = el 1 (CONJUNCTS bb) in
    let block1 = `[word_subword (chunk0:int128) (32,8); word_subword chunk0 (40,8);
                   word_subword chunk0 (48,8); word_subword chunk0 (56,8)]:byte list` in
    let block1len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA4`, block1)) in
    let bsum2_raw = prove(mk_imp(mb2_tm, mk_eq(lanesum8, block1len_x)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV)
            (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER] THEN
      SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let pop_len2 = REWRITE_RULE[GSYM blk1_eq] (TRANS popcnt2 (MP bsum2_raw mb2)) in
    ASSUME_TAC pop_len2) THEN
  SUBGOAL_THEN `acc1 + LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+4,4) inlist):int16 list) = LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+4`] SUBITER_BRIDGE_ETA4) THEN
    ANTS_TAC THENL [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES; ARITH_RULE `(16*i+4)+4 = 16*i+8`] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) = acc1` then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) < 2 EXP 32` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+4`] OUTLEN0_LE_256_FROM_SUBITER) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC;
        FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) = acc1` then SUBST1_TAC th else NO_TAC) THEN FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(16*i+4)+4 = 16*i+8`] THEN ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let block1len = `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+4,4) inlist):int16 list)` in
    let sum = mk_binop `(+):num->num->num` `acc1:num` block1len in
    let bridge2 = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),_) -> true | _ -> false) asl) in
    let lt32 = REWRITE_RULE[SYM bridge2] (snd(find (fun (_,th) -> concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) < 2 EXP 32`) asl)) in
    let pop_len2 = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl) in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let gt248 = REWRITE_RULE[SYM bridge2] (snd(find (fun (_,th) -> concl th = `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)`) asl)) in
    let ja_taken = MP (ISPECL [sum; `248`] JA_TAKEN_GT) (CONJ gt248 lt32) in
    ASSUME_TAC pop_len2 THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja_taken) THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (34--35) THEN
  SUBGOAL_THEN `read RIP s35 = word (pc + 314):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let pop_len2_old = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl in
      let zbe = MP (SPEC `val (mask8b:int64) MOD 256` zxbyte_eq) (ARITH_RULE `val (mask8b:int64) MOD 256 < 256`) in
      let pop_len2_typed = TRANS (AP_TERM `word_popcount:int32->num` zbe) (snd pop_len2_old) in
      let rax_red0 = find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
      let ja = find (fun (_,th) -> is_neg(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`acc1:num`))(concl th)) asl in
      rip_mp memsafe 314 35 THEN
      REWRITE_TAC[pop_len2_typed] THEN REWRITE_TAC[snd rax_red0] THEN
      REWRITE_TAC[snd ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC];;

let SI2_MG2_TAKEN_TAC : tactic = mk_si2_mg2_taken false;;
let SI2_MG2_TAKEN_MS_TAC : tactic = mk_si2_mg2_taken true;;

let me2_pre = midexit1_pre;;
let me2_post =
  `\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
       read RIP s = word(pc + 314) /\ read RSP s = stackpointer /\
       read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
       read(memory :> bytes(table,2048)) s = num_of_wordlist (mldsa_rej_uniform_table:byte list) /\
       read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
       read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i+8) inlist):int32 list)) /\
       read RCX s = word(16*i+8) /\
       read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i+8) inlist):int32 list))) s =
         num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i+8) inlist))`;;

let midexit2_tm =
  list_mk_forall([`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`i:num`;`stackpointer:int64`],
  mk_imp(list_mk_conj([`LENGTH (inlist:byte list) = 272`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 403) (val(res:int64),1024)`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 403) (val(buf:int64), 272)`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 403) (val(table:int64),2048)`;
    `nonoverlapping_modulo (2 EXP 64) (val(res:int64),1024) (val(buf:int64), 272)`;
    `nonoverlapping_modulo (2 EXP 64) (val(res:int64),1024) (val(table:int64),2048)`;
    `16 * (i + 1) <= 272`;
    `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+4) inlist):int32 list) <= 248`;
    `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)`]),
    list_mk_comb(`ensures x86`,[me2_pre; me2_post; midexit1_cframe])));;

let mk_midexit2 (memsafe:bool) (disch:tactic) : tactic =
(mk_prefix_to_s21 memsafe) THEN
  SUBGOAL_THEN `16 * i + 4 <= LENGTH(inlist:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC; ALL_TAC] THEN
  (mk_mg1_nt memsafe) THEN SI1_FOLD_V2 THEN
  FIRST_X_ASSUM(fun th -> match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),Var("s23",_))),r) when
      (match r with Comb(Comb(Comb(Const("COND",_),_),_),_)->true|_->false) -> ALL_TAC | _ -> NO_TAC) THEN
  SI2_BODY_TAC THEN
  (mk_si2_mg2_taken memsafe) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* discharge if-guard (taken), RAX collapse, RCX collapse                  *)
  W(fun (asl,w) ->
    let pop_len2 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl in
    let zbe = MP (SPEC `val (mask8b:int64) MOD 256` zxbyte_eq) (ARITH_RULE `val (mask8b:int64) MOD 256 < 256`) in
    let pop_len2_typed = TRANS (AP_TERM `word_popcount:int32->num` zbe) (snd pop_len2) in
    let rax_red0 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> true | _ -> false) asl in
    let bridge2 = find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc1",_)),_)),_) -> true | _ -> false) asl in
    REWRITE_TAC[pop_len2_typed; snd rax_red0; snd bridge2]) THEN
  W(fun (asl,w) ->
    let ntake = MP (ISPECL [`LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)`;`248`] JA_TAKEN_GT)
                   (CONJ (ASSUME `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list)`)
                         (ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) < 2 EXP 32`)) in
    REWRITE_TAC[ntake]) THEN
  (* RCX collapse: double +4 nest                                            *)
  MP_TAC(SPEC `16*i` RCX4_COLLAPSE) THEN ANTS_TAC THENL [UNDISCH_TAC `16*i<=256` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(SPEC `16*i+4` RCX4_COLLAPSE) THEN ANTS_TAC THENL [UNDISCH_TAC `16*i<=256` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `16*i+4+4 = 16*i+8`] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  (if memsafe then CONJ_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; disch] else AP_TERM_TAC THEN ARITH_TAC);;
let MID_EXIT_SUBITER2 = prove(midexit2_tm, mk_midexit2 false ALL_TAC);;

(* --- midexit_subiter3 ---                                                  *)
(* MID_EXIT_SUBITER3: sub-iter-3 mid-guard fires TAKEN -> pc+314 at pos 16i+12.
   Entry pc+52/pos=16i, niblen(16i+8)<=248 (mg1,mg2 not taken), niblen(16i+12)>248 (mg3 taken),
   16(i+1)<=272. Reaches pc+314 with RCX=16i+12, RAX=niblen(16i+12), store=REJ_SAMPLE(0,16i+12).
   Load after: full CLEAN_BODY chain, .midexit_prefix, .mg1_nt, .mg2_nt, .midexit_subiter2 (SI2_BODY_TAC),
   .midexit_subiter1 (RCX4_COLLAPSE), .subiter_bridge_lemmas, .si3_full/.si3_integrated/.si3_fold_pieces
   (SI3_TAIL uses ACC2_IDENT_TAC, TAB3_TEQ_TAC, MASKBIT_TGT_3_TAC, PF_PROOF_3, etc.).
. *)

let SI3_BODY3_TAC : tactic =
  ABBREV_TAC `acc2 = acc1 + LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (16*i+4,4) inlist):int16 list)` THEN
  REABBREV_TAC `mask8c = read R8 s35` THEN
  SUBGOAL_THEN `acc2 <= 248` ASSUME_TAC THENL
   [(* after ABBREV acc2, the bridge2 (acc1+niblen(16i+4,4)=niblen_sample(16i+8)) folds to
       (acc2 = niblen_sample(16i+8)); SUBST it then ACCEPT niblen(16i+8)<=248. *)
    FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),Var("acc2",_)),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_)))->true|_->false) then SUBST1_TAC th else NO_TAC) THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           (* case-4: niblen(16i+8)<=248 from niblen(16i+12)<=248 by monotonicity *)
           (FIRST_X_ASSUM(fun th -> match concl th with
              Comb(Comb(Const("<=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),k) when k=`248`
                -> MP_TAC th | _ -> NO_TAC) THEN
            MATCH_MP_TAC(ARITH_RULE `a <= b ==> b <= 248 ==> a <= 248`) THEN
            MATCH_MP_TAC REJ_SAMPLE_ETA4_PREFIX_MONO THEN ARITH_TAC)]; ALL_TAC] THEN
  VAL_INT64_TAC `acc2:num` THEN
  ACC2_IDENT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) = acc2`]) THEN
  X86_VSTEPS_TAC EXEC (36--36) THEN
  X86_VERBOSE_STEP_TAC EXEC "s37" THEN MOVZBL_R10_CAPTURE_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `read R8 s36 = mask8c:int64`]) THEN
  X86_VSTEPS_TAC EXEC (38--38) THEN TAB3_TEQ_TAC THEN REABBREV_TAC `tab3 = read YMM6 s38` THEN
  X86_VSTEPS_TAC EXEC (39--39) THEN REABBREV_TAC `pshuf3 = read YMM6 s39` THEN
  PURGE_STALE_STATES_TAC ["s38"] THEN
  X86_VSTEPS_TAC EXEC (40--40) THEN REABBREV_TAC `sx3 = read YMM1 s40` THEN
  VAL_INT64_TAC `acc2:num` THEN
  X86_STEPS_TAC EXEC (41--41) THEN
  SUBGOAL_THEN `sx3:int256 = usimd8 (\b:byte. word_sx b:int32) (word_zx(word_zx (pshuf3:int256):int128):int64)` ASSUME_TAC THENL
   [W(fun (asl,w) ->
       let sx3def = find (fun th -> is_eq(concl th) && rand(concl th)=`sx3:int256` &&
           can(find_term(fun u->match u with Const("word_join",_)->true|_->false))(concl th)) (map snd asl) in
       SUBST1_TAC(SYM sx3def) THEN
       REWRITE_TAC[usimd8;usimd4;usimd2;DIMINDEX_8;DIMINDEX_16;DIMINDEX_32;DIMINDEX_64;DIMINDEX_128;DIMINDEX_256] THEN
       CONV_TAC WORD_BLAST);
    ALL_TAC] THEN
  (SUBGOAL_THEN maskbit_tgt_3 ASSUME_TAC THENL [MASKBIT_TGT_3_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN pf_target_3 ASSUME_TAC THENL [PF_PROOF_3; ALL_TAC]) THEN
  ACC2_IDENT_TAC THEN
  W(fun (asl,w) ->
    let asms = map snd asl in
    let hasC nm th = can (find_term (fun u -> match u with Const(n,_) when n=nm -> true | _ -> false)) (concl th) in
    let bg3 = find (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f0sub:int256`))c &&
        not(can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))c) &&
        can(find_term(fun u->u=`word_subword (chunk0:int128) (64,8):byte`))c &&
        can(find_term(fun u->u=`word_subword (f0sub:int256) (128,128):int128`))c) asms in
    let mthm3 = find (fun th -> concl th = maskbit_tgt_3) asms in
    let pfth3 = find (fun th -> concl th = pf_target_3) asms in
    let sx3u = find (fun th -> match concl th with Comb(Comb(Const("=",_),Var("sx3",_)),r)->can(find_term(fun u->match u with Const("usimd8",_)->true|_->false))r|_->false) asms in
    let storef0 = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),m),Var("s41",_))),Var("sx3",_)) -> can(find_term(fun u->match u with Const("bytes256",_)->true|_->false)) m |_->false) asms in
    let store_full = REWRITE_RULE[pfth3] (REWRITE_RULE[sx3u] storef0) in
    let g3 = `word_zx (word_zx (word_subword (f0sub:int256) (128,128):int128):int128):int128` in
    let m = `word (val (mask8c:int64) MOD 256):byte` in
    let pc = ISPECL [`word_add res (word (4 * acc2)):int64`; `s41:x86state`; g3; m; `LENGTH(ACC_IDX (word (val (mask8c:int64) MOD 256):byte))`] SUBITER_STORE_POSTCOND in
    let res_th0 = MP pc (CONJ (SPEC m LACC8) store_full) in
    let spec = ISPECL [g3; m; `word_subword (chunk0:int128) (64,8):byte`; `word_subword (chunk0:int128) (72,8):byte`; `word_subword (chunk0:int128) (80,8):byte`; `word_subword (chunk0:int128) (88,8):byte`] SUBITER_STORE_SPEC in
    let rej_store = REWRITE_RULE[MP spec (CONJ mthm3 bg3)] res_th0 in
    let leninl = find (fun th -> concl th = `LENGTH(inlist:byte list)=272`) asms in
    let i116 = find (fun th -> concl th = `16 * (i + 1) <= 272`) asms in
    let blk16 = find (fun th -> is_eq(concl th) && hasC "SUB_LIST" th && (try length(dest_list(rand(concl th)))=16 with _->false)) asms in
    let bb = MP (ISPECL [`inlist:byte list`;`i:num`;`chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*(i+1)<=272 ==> 16*i+16<=272`) i116)) blk16) in
    let blk2_eq = el 2 (CONJUNCTS bb) in
    let lr0 = MP (ISPECL [m;`word_subword (chunk0:int128) (64,8):byte`;`word_subword (chunk0:int128) (72,8):byte`;`word_subword (chunk0:int128) (80,8):byte`;`word_subword (chunk0:int128) (88,8):byte`] LEN_RECONCILE_GEN) mthm3 in
    let lr = REWRITE_RULE[GSYM blk2_eq] lr0 in
    let rej_store1 = REWRITE_RULE[GSYM blk2_eq] rej_store in
    let acc2_ident = find (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),Var("acc2",_)) -> true | _ -> false) asms in
    let prefix_store0 = find (fun th -> (match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),Var("s41",_))),_) -> true | _ -> false) &&
         hasC "num_of_wordlist" th && hasC "SUB_LIST" th && can(find_term(fun u->u=`acc2:num`))(lhand(concl th)) && not(hasC "ACC_IDX" th) && not(hasC "bytes256" th)) asms in
    let prefix_store = REWRITE_RULE[GSYM acc2_ident] prefix_store0 in
    let rej_store2 = REWRITE_RULE[GSYM acc2_ident] rej_store1 in
    let fold = MP (ISPECL [`res:int64`;`s41:x86state`;m;`SUB_LIST(16*i+8,4) (inlist:byte list)`;`SUB_LIST(0,16*i+8) (inlist:byte list)`] SUBITER_FOLD_STEP)
                  (CONJ lr (CONJ prefix_store rej_store2)) in
    let split = REWRITE_RULE[ADD_CLAUSES] (ISPECL[`inlist:byte list`;`16*i+8`;`4`;`0`] SUB_LIST_SPLIT) in
    let clean = REWRITE_RULE[GSYM split; ARITH_RULE `(16*i+8)+4 = 16*i+12`] fold in
    ASSUME_TAC clean) THEN
  X86_STEPS_TAC EXEC (42--45) THEN
  ALL_TAC;;

(* SI3_MG3_TAKEN_TAC: from s45, resolve mid-guard-3 TAKEN (niblen(16i+12)>248) -> RIP s47=pc+314. *)
let mk_si3_mg3_taken (memsafe:bool) : tactic =
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let m8c_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8c:int64` | _ -> false) in
    let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
    let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
    let popcnt3 = REWRITE_RULE[m8b_def; m8c_def]
       (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE2)) in
    let lanesum = rand(concl popcnt3) in
    let mb3 = find_a (fun th -> let c=concl th in is_forall c &&
       can(find_term(fun u->u=`f1bnd:int256`))c &&
       can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),n) -> n=`16` | _ -> false))c) in
    let mb3_tm = concl mb3 in
    let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
    let blk16 = find_a (fun th -> is_eq(concl th) &&
       (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" &&
            length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le)) blk16) in
    let blk2_eq = el 2 (CONJUNCTS bb) in
    let block2 = `[word_subword (chunk0:int128) (64,8); word_subword chunk0 (72,8);
                   word_subword chunk0 (80,8); word_subword chunk0 (88,8)]:byte list` in
    let block2len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA4`, block2)) in
    let bsum3_raw = prove(mk_imp(mb3_tm, mk_eq(lanesum, block2len_x)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV)
            (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER] THEN
      SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let pop_len3 = REWRITE_RULE[GSYM blk2_eq] (TRANS popcnt3 (MP bsum3_raw mb3)) in
    ASSUME_TAC pop_len3) THEN
  (* bridge3: acc2 + niblen(SUB(16i+8,4)) = niblen_sample(16i+12)            *)
  SUBGOAL_THEN `acc2 + LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+8,4) inlist):int16 list) = LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+8`] SUBITER_BRIDGE_ETA4) THEN
    ANTS_TAC THENL [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES; ARITH_RULE `(16*i+8)+4 = 16*i+12`] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) = acc2` then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) < 2 EXP 32` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+8`] OUTLEN0_LE_256_FROM_SUBITER) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC;
        FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) = acc2` then SUBST1_TAC th else NO_TAC) THEN FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(16*i+8)+4 = 16*i+12`] THEN ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let block2len = `LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+8,4) inlist):int16 list)` in
    let sum = mk_binop `(+):num->num->num` `acc2:num` block2len in
    let bridge3 = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc2",_)),_)),_) -> true | _ -> false) asl) in
    let lt32 = REWRITE_RULE[SYM bridge3] (snd(find (fun (_,th) -> concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) < 2 EXP 32`) asl)) in
    let pop_len3 = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) asl) in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    let gt248 = REWRITE_RULE[SYM bridge3] (snd(find (fun (_,th) -> concl th = `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list)`) asl)) in
    let ja_taken = MP (ISPECL [sum; `248`] JA_TAKEN_GT) (CONJ gt248 lt32) in
    ASSUME_TAC pop_len3 THEN ASSUME_TAC rax_red0 THEN ASSUME_TAC ja_taken) THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (46--47) THEN
  SUBGOAL_THEN `read RIP s47 = word (pc + 314):int64` ASSUME_TAC THENL
   [W(fun (asl,w) ->
      let asms = map snd asl in
      let find_a p = find p asms in
      let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
      let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
      let blk16 = find_a (fun th -> is_eq(concl th) &&
         (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" && length(dest_list(rand(concl th)))=16 with _->false)) in
      let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                  (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le)) blk16) in
      let blk2_eq = el 2 (CONJUNCTS bb) in
      let rax_red0 = find_a (fun th -> match concl th with
          Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) ->
            can(find_term(fun u->u=`acc2:num`))(concl th) | _ -> false) in
      let ja = find_a (fun th -> is_neg(concl th) &&
          can(find_term(fun u->match u with Const("word_sub",_)->true|_->false))(concl th) &&
          can(find_term(fun u->u=`acc2:num`))(concl th)) in
      rip_mp memsafe 314 47 THEN
      REWRITE_TAC[GSYM blk2_eq] THEN REWRITE_TAC[rax_red0] THEN
      REWRITE_TAC[ja] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);
    ALL_TAC];;

let SI3_MG3_TAKEN_TAC : tactic = mk_si3_mg3_taken false;;
let SI3_MG3_TAKEN_MS_TAC : tactic = mk_si3_mg3_taken true;;

let me3_post =
  `\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
       read RIP s = word(pc + 314) /\ read RSP s = stackpointer /\
       read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
       read(memory :> bytes(table,2048)) s = num_of_wordlist (mldsa_rej_uniform_table:byte list) /\
       read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
       read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i+12) inlist):int32 list)) /\
       read RCX s = word(16*i+12) /\
       read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i+12) inlist):int32 list))) s =
         num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*i+12) inlist))`;;

let midexit3_tm =
  list_mk_forall([`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`i:num`;`stackpointer:int64`],
  mk_imp(list_mk_conj([`LENGTH (inlist:byte list) = 272`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 403) (val(res:int64),1024)`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 403) (val(buf:int64), 272)`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 403) (val(table:int64),2048)`;
    `nonoverlapping_modulo (2 EXP 64) (val(res:int64),1024) (val(buf:int64), 272)`;
    `nonoverlapping_modulo (2 EXP 64) (val(res:int64),1024) (val(table:int64),2048)`;
    `16 * (i + 1) <= 272`;
    `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+8) inlist):int32 list) <= 248`;
    `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list)`]),
    list_mk_comb(`ensures x86`,[midexit1_pre; me3_post; midexit1_cframe])));;

let mk_midexit3 (memsafe:bool) (disch:tactic) : tactic =
(mk_prefix_to_s21 memsafe) THEN
  SUBGOAL_THEN `16 * i + 4 <= LENGTH(inlist:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC; ALL_TAC] THEN
  (mk_mg1_nt memsafe) THEN SI1_FOLD_V2 THEN
  FIRST_X_ASSUM(fun th -> match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),Var("s23",_))),r) when
      (match r with Comb(Comb(Comb(Const("COND",_),_),_),_)->true|_->false) -> ALL_TAC | _ -> NO_TAC) THEN
  SI2_BODY_TAC THEN (mk_mg2_nt memsafe) THEN
  FIRST_X_ASSUM(fun th -> match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),Var("s35",_))),r) when
      (match r with Comb(Comb(Comb(Const("COND",_),_),_),_)->true|_->false) -> ALL_TAC | _ -> NO_TAC) THEN
  SI3_BODY3_TAC THEN (mk_si3_mg3_taken memsafe) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* discharge: RAX (block2 4-list -> SUB_LIST + pop_len3 + rax_red0 + bridge3), guard (JA_TAKEN_GT), RCX *)
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
    let blk16 = find_a (fun th -> is_eq(concl th) && (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" && length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le)) blk16) in
    let blk2_eq = el 2 (CONJUNCTS bb) in
    let pop_len3 = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> true | _ -> false) in
    let rax_red0 = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> can(find_term(fun u->u=`acc2:num`))(concl th) | _ -> false) in
    let bridge3 = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc2",_)),_)),_) -> can(find_term(fun u->match u with Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))->true|_->false))(concl th) | _ -> false) in
    REWRITE_TAC[GSYM blk2_eq] THEN REWRITE_TAC[pop_len3] THEN REWRITE_TAC[rax_red0; bridge3]) THEN
  W(fun (asl,w) ->
    let ntake = MP (ISPECL [`LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list)`;`248`] JA_TAKEN_GT)
                   (CONJ (ASSUME `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list)`)
                         (ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) < 2 EXP 32`)) in
    REWRITE_TAC[ntake]) THEN
  SUBGOAL_THEN `(16 * i + 4) MOD 2 EXP 32 = 16 * i + 4 /\ (16 * i + 4) MOD 2 EXP 64 = 16 * i + 4 /\
                (16 * i + 8) MOD 2 EXP 32 = 16 * i + 8 /\ (16 * i + 8) MOD 2 EXP 64 = 16 * i + 8 /\
                (16 * i + 12) MOD 2 EXP 32 = 16 * i + 12 /\ (16 * i + 12) MOD 2 EXP 64 = 16 * i + 12`
     STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `16*i<=256` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_64; DIMINDEX_32; VAL_WORD_ADD; VAL_WORD] THEN
  SUBGOAL_THEN `(16 * i) MOD 2 EXP 64 = 16 * i` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `16*i<=256` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC MOD_DOWN_CONV THEN
  ASM_REWRITE_TAC[ARITH_RULE `16*i+4+4 = 16*i+8`; ARITH_RULE `16*i+8+4 = 16*i+12`] THEN
  REWRITE_TAC[ARITH_RULE `(16*i+4)+4 = 16*i+8`] THEN
  ASM_REWRITE_TAC[ARITH_RULE `(16*i+8)+4 = 16*i+12`] THEN disch;;
let MID_EXIT_SUBITER3 = prove(midexit3_tm, mk_midexit3 false ALL_TAC);;

(* --- midexit_case4 ---                                                     *)
(* MID_EXIT_CASE4: all 4 sub-iters of the i=N-1-style block run clean (niblen(16i+4),16i+8,16i+12
   <=248), then at the loop back-edge pc+52/pos16(i+1) the head-guard1 (cmp eax,248) fires TAKEN
   since niblen(16(i+1))>248 -> pc+314 at pos16(i+1).
   Entry pc+52/pos=16i; hyps niblen(16i+12)<=248 (=> niblen(16i+4),16i+8 <=248 by mono),
   niblen(16(i+1))>248, 16(i+1)<=272. Reaches pc+314 with RCX=16(i+1), RAX=niblen(16(i+1)),
   store=REJ_SAMPLE(0,16(i+1)).
   Composes: PREFIX_TO_S21 + MG1_NT + SI1_FOLD + purge + SI2_BODY + MG2_NT + purge + SI3_BODY3
   + MG3_NT + purge + SI4_BODY4 (back-edge s57) + RAX-fold + head-guard1 eax-TAKEN (s58-59) +
   ENSURES_FINAL + RCX/store discharge. Load after .mg1_nt/.mg2_nt/.mg3_nt/.midexit_subiter2(SI2_BODY)
 /.midexit_subiter3(SI3_BODY3)/.si4_body4/.midexit_subiter1(RCX4_COLLAPSE).. *)

let me4_post =
  `\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
       read RIP s = word(pc + 314) /\ read RSP s = stackpointer /\
       read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
       read(memory :> bytes(table,2048)) s = num_of_wordlist (mldsa_rej_uniform_table:byte list) /\
       read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
       read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(i+1)) inlist):int32 list)) /\
       read RCX s = word(16*(i+1)) /\
       read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(i+1)) inlist):int32 list))) s =
         num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(i+1)) inlist))`;;

let midexit4_tm =
  list_mk_forall([`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`i:num`;`stackpointer:int64`],
  mk_imp(list_mk_conj([`LENGTH (inlist:byte list) = 272`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 403) (val(res:int64),1024)`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 403) (val(buf:int64), 272)`;
    `nonoverlapping_modulo (2 EXP 64) (pc, 403) (val(table:int64),2048)`;
    `nonoverlapping_modulo (2 EXP 64) (val(res:int64),1024) (val(buf:int64), 272)`;
    `nonoverlapping_modulo (2 EXP 64) (val(res:int64),1024) (val(table:int64),2048)`;
    `16 * (i + 1) <= 272`;
    `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) <= 248`;
    `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list)`]),
    list_mk_comb(`ensures x86`,[midexit1_pre; me4_post; midexit1_cframe])));;

let mk_midexit4 (memsafe:bool) (disch:tactic) : tactic =
(mk_prefix_to_s21 memsafe) THEN
  SUBGOAL_THEN `16 * i + 4 <= LENGTH(inlist:byte list)` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC; ALL_TAC] THEN
  (mk_mg1_nt memsafe) THEN SI1_FOLD_V2 THEN
  FIRST_X_ASSUM(fun th -> match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),Var("s23",_))),r) when
      (match r with Comb(Comb(Comb(Const("COND",_),_),_),_)->true|_->false) -> ALL_TAC | _ -> NO_TAC) THEN
  SI2_BODY_TAC THEN (mk_mg2_nt memsafe) THEN
  FIRST_X_ASSUM(fun th -> match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),Var("s35",_))),r) when
      (match r with Comb(Comb(Comb(Const("COND",_),_),_),_)->true|_->false) -> ALL_TAC | _ -> NO_TAC) THEN
  SI3_BODY3_TAC THEN (mk_mg3_nt memsafe) THEN
  FIRST_X_ASSUM(fun th -> match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),Var("s47",_))),r) when
      (match r with Comb(Comb(Comb(Const("COND",_),_),_),_)->true|_->false) -> ALL_TAC | _ -> NO_TAC) THEN
  SI4_BODY4_TAC THEN
  (* niblen(16(i+1))<=256                                                    *)
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list) <= 256` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+12`] OUTLEN0_LE_256_FROM_SUBITER) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC;
        FIRST_X_ASSUM(fun th -> if (match concl th with Comb(Comb(Const("=",_),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_))),Var("acc3",_))->true|_->false) then SUBST1_TAC th else NO_TAC) THEN FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(16*i+12)+4 = 16*(i+1)`; ARITH_RULE `16*i+16=16*(i+1)`]; ALL_TAC] THEN
  (* bridge4                                                                 *)
  SUBGOAL_THEN `acc3 + LENGTH(REJ_NIBBLES_ETA4 (SUB_LIST(16*i+12,4) inlist):int16 list) = LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`inlist:byte list`;`16*i+12`] SUBITER_BRIDGE_ETA4) THEN
    ANTS_TAC THENL [UNDISCH_TAC `16 * (i+1) <= 272` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES; ARITH_RULE `(16*i+12)+4 = 16*(i+1)`; ARITH_RULE `16*i+16 = 16*(i+1)`] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*i+12) inlist):int32 list) = acc3` then MP_TAC th else NO_TAC) THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN ARITH_TAC; ALL_TAC] THEN
  (* pop_len4 + rax_red0                                                     *)
  W(fun (asl,w) ->
    let asms = map snd asl in
    let find_a p = find p asms in
    let m8c_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8c:int64` | _ -> false) in
    let m8b_def = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8b:int64` | _ -> false) in
    let m8d_val = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),_),r) -> r = `mask8d:int64` && can(find_term(fun u->match u with Const("word_ushr",_)->true|_->false))(concl th) | _ -> false) in
    let pinst = `\k. bit 7 (word_subword (f1bnd:int256) (8*k,8):byte)` in
    let popcnt4 = REWRITE_RULE[m8d_val] (REWRITE_RULE[m8b_def; m8c_def]
       (CONV_RULE(DEPTH_CONV BETA_CONV THENC ONCE_DEPTH_CONV NUM_REDUCE_CONV) (SPEC pinst POPCNT_BYTE3))) in
    let lanesum = rand(concl popcnt4) in
    let mb4 = find_a (fun th -> let c=concl th in is_forall c && can(find_term(fun u->u=`f1bnd:int256`))c &&
       can(find_term(fun u-> match u with Comb(Comb(Const("+",_),Var("k",_)),n) -> n=`24` | _ -> false))c) in
    let mb4_tm = concl mb4 in
    let i_le = find_a (fun th -> concl th = `16 * i <= 256`) in
    let leninl = find_a (fun th -> concl th = `LENGTH(inlist:byte list) = 272`) in
    let blk16 = find_a (fun th -> is_eq(concl th) && (try fst(dest_const(fst(strip_comb(lhand(concl th)))))="SUB_LIST" && length(dest_list(rand(concl th)))=16 with _->false)) in
    let bb = MP (ISPECL [`inlist:byte list`; `i:num`; `chunk0:int128`] SUBITER_BLOCK_BYTES)
                (CONJ (REWRITE_RULE[GSYM leninl] (MP (ARITH_RULE `16*i<=256 ==> 16*i+16<=272`) i_le)) blk16) in
    let blk3_eq = el 3 (CONJUNCTS bb) in
    let block3 = `[word_subword (chunk0:int128) (96,8); word_subword chunk0 (104,8); word_subword chunk0 (112,8); word_subword chunk0 (120,8)]:byte list` in
    let block3len_x = mk_comb(`LENGTH:(int16)list->num`, mk_comb(`REJ_NIBBLES_ETA4`, block3)) in
    let bsum4_raw = prove(mk_imp(mb4_tm, mk_eq(lanesum, block3len_x)),
      DISCH_THEN(fun mbthm ->
        let mbs = map (fun k -> let th=SPEC(mk_small_numeral k) mbthm in
          CONV_RULE (NUM_REDUCE_CONV THENC ONCE_DEPTH_CONV EL_CONV) (MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th)))))) [0;1;2;3;4;5;6;7] in
        REWRITE_TAC mbs) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LENGTH_FILTER_BYTE_NIBBLES_4_BYTES] THEN
      REWRITE_TAC[GSYM BITVAL_SUM_8_EQ_LENGTH_FILTER] THEN
      SIMP_TAC[VAL_WORD_BYTE_LT256; BYTE_DIV16_LT; BYTE_MOD16_LT]) in
    let pop_len4 = REWRITE_RULE[GSYM blk3_eq] (TRANS popcnt4 (MP bsum4_raw mb4)) in
    let bridge4 = find_a (fun th -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc3",_)),_)),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_)))->true|_->false) in
    let le256 = find_a (fun th -> concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list) <= 256`) in
    let lt32 = REWRITE_RULE[SYM bridge4] (MATCH_MP (ARITH_RULE `a<=256 ==> a < 2 EXP 32`) le256) in
    let rax_red0 = MATCH_MP RAX_NEST_REDUCE lt32 in
    ASSUME_TAC pop_len4 THEN ASSUME_TAC rax_red0) THEN
  (* fold RAX s57 -> word(niblen(16(i+1)))                                   *)
  W(fun (asl,w) ->
    let pl4 = find (fun (_,th) -> match concl th with Comb(Comb(Const("=",_),Comb(Const("word_popcount",_),_)),_) -> can(find_term(fun u->u=`mask8d:int64`))(concl th) | _ -> false) asl in
    let rr = find (fun (_,th) -> match concl th with Comb(Comb(Const("=",_),Comb(Const("word_zx",_),Comb(Comb(Const("word_add",_),_),_))),_) -> can(find_term(fun u->u=`acc3:num`))(concl th) | _ -> false) asl in
    let bridge4 = find (fun (_,th) -> match concl th with Comb(Comb(Const("=",_),Comb(Comb(Const("+",_),Var("acc3",_)),_)),Comb(Const("LENGTH",_),Comb(Const("REJ_SAMPLE_ETA4_BYTES",_),_)))->true|_->false) asl in
    RULE_ASSUM_TAC(REWRITE_RULE[snd pl4]) THEN RULE_ASSUM_TAC(REWRITE_RULE[snd rr]) THEN RULE_ASSUM_TAC(REWRITE_RULE[snd bridge4])) THEN
  (* head-guard1 eax TAKEN -> pc+314                                         *)
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list) < 2 EXP 32` ASSUME_TAC THENL
   [UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list) <= 256` THEN ARITH_TAC; ALL_TAC] THEN
  W(fun (asl,w) ->
    let gt248 = find (fun (_,th) -> concl th = `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list)`) asl in
    let lt32 = find (fun (_,th) -> concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list) < 2 EXP 32`) asl in
    let ja_taken = MP (ISPECL [`LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(i+1)) inlist):int32 list)`; `248`] JA_TAKEN_GT) (CONJ (snd gt248) (snd lt32)) in
    ASSUME_TAC ja_taken) THEN
  X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (58--59) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `16*(i+1) = 16*i+16`] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(16 * i + 4) MOD 2 EXP 32 = 16 * i + 4 /\ (16 * i + 4) MOD 2 EXP 64 = 16 * i + 4 /\
                  (16 * i + 8) MOD 2 EXP 32 = 16 * i + 8 /\ (16 * i + 8) MOD 2 EXP 64 = 16 * i + 8 /\
                  (16 * i + 12) MOD 2 EXP 32 = 16 * i + 12 /\ (16 * i + 12) MOD 2 EXP 64 = 16 * i + 12 /\
                  (16 * i + 16) MOD 2 EXP 32 = 16 * i + 16 /\ (16 * i + 16) MOD 2 EXP 64 = 16 * i + 16`
       STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `16*i<=256` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM VAL_EQ] THEN
    REWRITE_TAC[VAL_WORD_ZX_GEN; DIMINDEX_64; DIMINDEX_32; VAL_WORD_ADD; VAL_WORD] THEN
    SUBGOAL_THEN `(16 * i) MOD 2 EXP 64 = 16 * i` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `16*i<=256` THEN ARITH_TAC; ALL_TAC] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    REPEAT(CHANGED_TAC(ASM_REWRITE_TAC[ARITH_RULE `(16*i+4)+4 = 16*i+8`; ARITH_RULE `(16*i+8)+4 = 16*i+12`;
                ARITH_RULE `(16*i+12)+4 = 16*i+16`; ARITH_RULE `16*i+4+4 = 16*i+8`; ARITH_RULE `16*i+8+4 = 16*i+12`;
                ARITH_RULE `16*i+12+4 = 16*i+16`]));
    ASM_REWRITE_TAC[]] THEN disch;;
let MID_EXIT_CASE4 = prove(midexit4_tm, mk_midexit4 false ALL_TAC);;

(* --- midexit_arm ---                                                       *)
(* MIDEXIT_ARM_TAC: closes the scaffold's MID-EXIT arm (the goal after CORRECT_SCAFFOLD_TAC +
   ASM_CASES niblen(16N)<=248, FALSE branch). Pre @ pc+52/pos16(N-1), niblen(16(N-1))<=248,
   niblen(16N)>248. Case-splits on the first crossover p in {16(N-1)+4,+8,+12,16N} and dispatches
   MID_EXIT_SUBITER{1,2,3}@(N-1) / MID_EXIT_CASE4@(N-1), then SCALAR_TAIL_AT_P@p -> pc+402.
   Load after the 4 MID_EXIT lemmas, SCALAR_TAIL_AT_P, OUTLEN0_LE_256_FROM_SUBITER. *)

let AT_P_NOLET = CONV_RULE(TOP_DEPTH_CONV let_CONV) MLDSA_REJ_UNIFORM_ETA4_SCALAR_TAIL_AT_P;;

(* dispatch one crossover case: midthm @ i:=N-1 reaches pc+314@pexpr; prevbound = niblen(pexpr-4)<=248
   (in context) used to derive niblen(pexpr)<=256; then SCALAR_TAIL_AT_P@pexpr. *)
let MIDEXIT_DISPATCH (midthm:thm) (pexpr:term) (prevpos:term) : tactic =
  let qpost = vsubst [`N-1`,`i:num`] (rand(rator(snd(dest_imp(snd(strip_forall(concl midthm))))))) in
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC qpost THEN
  CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [(* leg1: MID_EXIT lemma @ N-1 *)
    MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`N-1`;`stackpointer:int64`] midthm) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN (FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]); DISCH_THEN ACCEPT_TAC];
    (* leg2: niblen(pexpr)<=256 then SCALAR_TAIL_AT_P@pexpr                  *)
    SUBGOAL_THEN (mk_comb(mk_comb(`(<=):num->num->bool`,
        mk_comb(`LENGTH:(int32)list->num`, mk_comb(`REJ_SAMPLE_ETA4_BYTES:byte list->int32 list`,
          mk_comb(mk_comb(`SUB_LIST:num#num->byte list->byte list`,mk_pair(`0`,pexpr)),`inlist:byte list`)))), `256`)) ASSUME_TAC THENL
     [SUBGOAL_THEN (mk_eq(pexpr, mk_binop `(+):num->num->num` prevpos `4`)) SUBST1_TAC THENL
       [UNDISCH_TAC `~(N=0)` THEN UNDISCH_TAC `16 * N <= 272` THEN ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC OUTLEN0_LE_256_FROM_SUBITER THEN CONJ_TAC THENL
       [UNDISCH_TAC `16 * N <= 272` THEN UNDISCH_TAC `~(N=0)` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    MATCH_MP_TAC AT_P_NOLET THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];;

let MIDEXIT_ARM_TAC : tactic =
  (* setup facts (idempotent if already present)                             *)
  SUBGOAL_THEN `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,16 * N) inlist):int32 list) <= 248)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * N <= 272` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (N-1) <= 256` THEN UNDISCH_TAC `~(N=0)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * ((N-1)+1) <= 272` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * N <= 272` THEN UNDISCH_TAC `~(N=0)` THEN ARITH_TAC; ALL_TAC] THEN
  (* crossover case-split                                                    *)
  ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(N-1)+4) inlist):int32 list) <= 248` THENL
   [ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(N-1)+8) inlist):int32 list) <= 248` THENL
     [ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(N-1)+12) inlist):int32 list) <= 248` THENL
       [(* all 3 internal <=248 -> case-4, p = 16*((N-1)+1) *)
        SUBGOAL_THEN `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*((N-1)+1)) inlist):int32 list)` ASSUME_TAC THENL
         [SUBGOAL_THEN `16*((N-1)+1) = 16*N` SUBST1_TAC THENL
           [UNDISCH_TAC `~(N=0)` THEN ARITH_TAC; ALL_TAC] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MIDEXIT_DISPATCH MID_EXIT_CASE4 `16*((N-1)+1)` `16*(N-1)+12`;
        (* niblen(16(N-1)+12)>248 -> case-3, p=16(N-1)+12                    *)
        MIDEXIT_DISPATCH MID_EXIT_SUBITER3 `16*(N-1)+12` `16*(N-1)+8`];
      (* niblen(16(N-1)+8)>248 -> case-2, p=16(N-1)+8                        *)
      MIDEXIT_DISPATCH MID_EXIT_SUBITER2 `16*(N-1)+8` `16*(N-1)+4`];
    (* niblen(16(N-1)+4)>248 -> case-1, p=16(N-1)+4                          *)
    MIDEXIT_DISPATCH MID_EXIT_SUBITER1 `16*(N-1)+4` `16*(N-1)`];;

(* ========================================================================= *)
(* Main CORRECT theorem.                                                     *)
(* CORRECT_SCAFFOLD_TAC reduces to the i=N-1 exit block; OFFSET_ARM_TAC /    *)
(* MIDEXIT_ARM_TAC discharge the two niblen(16N) cases.                      *)
(* ========================================================================= *)
let MLDSA_REJ_UNIFORM_ETA4_CORRECT = prove
 (`!res buf table (inlist:byte list) pc.
        LENGTH inlist = 272 /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (res, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (buf, 272) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (table, 2048) /\
        nonoverlapping (res, 1024) (buf, 272) /\
        nonoverlapping (res, 1024) (table, 2048)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [res; buf; table] s /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s =
                    num_of_wordlist mldsa_rej_uniform_table)
             (\s. read RIP s = word(pc + LENGTH (BUTLAST mldsa_rej_uniform_eta4_tmc)) /\
                  let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES inlist) in
                  let outlen = LENGTH outlist in
                  C_RETURN s = word outlen /\
                  read(memory :> bytes(res,4 * outlen)) s =
                    num_of_wordlist outlist)
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`,
  CORRECT_SCAFFOLD_TAC THEN
  ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` THENL
   [OFFSET_ARM_TAC; MIDEXIT_ARM_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Subroutine correctness with array_abs_bound matching CBMC contract        *)
(* ensures(array_abs_bound(r, 0, return_value, MLDSA_ETA + 1)) for eta = 4.  *)
(* ------------------------------------------------------------------------- *)

(* NOTE: This must be kept in sync with the CBMC specification
 * in mldsa/src/native/x86_64/src/arith_native_x86_64.h *)

(* Bounded byte-shape core (CBMC array-abs-bound postcondition), exposed at   *)
(* top level so the Windows subroutine wrapper below can reuse it as its core *)
(* correctness theorem (the manual xmm6-spill splice needs the BUTLAST form). *)
let MLDSA_REJ_UNIFORM_ETA4_CORRECT_BOUND = prove
 (`!res buf table (inlist:byte list) pc.
    LENGTH inlist = 272 /\
    nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (res, 1024) /\
    nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (buf, 272) /\
    nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (table, 2048) /\
    nonoverlapping (res, 1024) (buf, 272) /\
    nonoverlapping (res, 1024) (table, 2048)
    ==> ensures x86
         (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
              read RIP s = word pc /\
              C_ARGUMENTS [res; buf; table] s /\
              read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
              read(memory :> bytes(table,2048)) s =
                num_of_wordlist mldsa_rej_uniform_table)
         (\s. read RIP s = word(pc + LENGTH (BUTLAST mldsa_rej_uniform_eta4_tmc)) /\
              (let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES inlist) in
               let outlen = LENGTH outlist in
               outlen <= 256 /\
               C_RETURN s = word outlen /\
               read(memory :> bytes(res,4 * outlen)) s =
                 num_of_wordlist outlist /\
               (!i. i < outlen
                    ==> ival(EL i outlist:int32) < &5 /\
                        -- &5 < ival(EL i outlist:int32))))
         (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
          MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
          MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
          MAYCHANGE [memory :> bytes(res,1024)])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ENSURES_STRENGTHEN_POST_X86 THEN
  EXISTS_TAC
   `\s:x86state.
      read RIP s = word(pc + LENGTH(BUTLAST mldsa_rej_uniform_eta4_tmc)) /\
      (let outlist = SUB_LIST(0,256) (REJ_SAMPLE_ETA4_BYTES (inlist:byte list)) in
       let outlen = LENGTH outlist in
       C_RETURN s = word outlen /\
       read(memory :> bytes(res:int64,4 * outlen)) s =
         num_of_wordlist outlist)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MLDSA_REJ_UNIFORM_ETA4_CORRECT THEN ASM_REWRITE_TAC[];
    BETA_TAC THEN GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_ACCEPT_TAC LENGTH_SUB_LIST_REJ_SAMPLE_ETA4_BYTES; ALL_TAC] THEN
    MATCH_ACCEPT_TAC REJ_SAMPLE_ETA4_BYTES_EL_BOUND]);;

let MLDSA_REJ_UNIFORM_ETA4_CORRECT_BOUND_CONCRETE =
  CONV_RULE(REWRITE_CONV[LENGTH_MLDSA_REJ_UNIFORM_ETA4_TMC;
                         fst MLDSA_REJ_UNIFORM_ETA4_EXEC])
    MLDSA_REJ_UNIFORM_ETA4_CORRECT_BOUND;;

let MLDSA_REJ_UNIFORM_ETA4_NOIBT_SUBROUTINE_CORRECT =
  let correct_bound_concrete = MLDSA_REJ_UNIFORM_ETA4_CORRECT_BOUND_CONCRETE in
  let saved_tic = !type_invention_error in
  type_invention_error := false;
  let th = prove
   (`!res buf table (inlist:byte list) pc stackpointer returnaddress.
        LENGTH inlist = 272 /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (res, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (buf, 272) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (table, 2048) /\
        nonoverlapping (res, 1024) (buf, 272) /\
        nonoverlapping (res, 1024) (table, 2048) /\
        nonoverlapping (stackpointer, 8) (res, 1024) /\
        nonoverlapping (stackpointer, 8) (buf, 272) /\
        nonoverlapping (stackpointer, 8) (table, 2048) /\
        nonoverlapping (stackpointer, 8) (word pc, LENGTH mldsa_rej_uniform_eta4_tmc)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_rej_uniform_eta4_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [res; buf; table] s /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s =
                    num_of_wordlist mldsa_rej_uniform_table)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (let outlist = SUB_LIST(0,256)
                      (REJ_SAMPLE_ETA4_BYTES inlist) in
                   let outlen = LENGTH outlist in
                   outlen <= 256 /\
                   C_RETURN s = word outlen /\
                   read(memory :> bytes(res,4 * outlen)) s =
                     num_of_wordlist outlist /\
                   (!i. i < outlen
                        ==> ival(EL i outlist:int32) < &5 /\
                            -- &5 < ival(EL i outlist:int32))))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(res,1024)])`,
    REWRITE_TAC[LENGTH_MLDSA_REJ_UNIFORM_ETA4_TMC] THEN
    X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_rej_uniform_eta4_tmc
      correct_bound_concrete) in
  type_invention_error := saved_tic;
  th;;

(* Full (untrimmed, IBT-prefixed) subroutine wrapper via ADD_IBT_RULE.       *)
(* This is the byte-shaped inner theorem (postcondition over the             *)
(* REJ_SAMPLE_ETA4_BYTES int16-path spec applied to a byte list); the public *)
(* spec below fronts it with the nibble-list REJ_SAMPLE_ETA4 spec.           *)
let MLDSA_REJ_UNIFORM_ETA4_SUBROUTINE_CORRECT_BYTES =
  ADD_IBT_RULE MLDSA_REJ_UNIFORM_ETA4_NOIBT_SUBROUTINE_CORRECT;;

(* ------------------------------------------------------------------------- *)
(* Public subroutine correctness, fronted with the nibble-list spec          *)
(* REJ_SAMPLE_ETA4 over inlist:(4 word) list (mirrors aarch64). The buffer is *)
(* a fixed 272 bytes, so the nibble input list has length 544. We bridge to  *)
(* the byte-shaped inner theorem: for any nibble list of even length there is *)
(* a byte list whose nibble decomposition matches it (BYTES_TO_NIBBLES_SURJ), *)
(* and REJ_SAMPLE_ETA4(BYTES_TO_NIBBLES bs) = REJ_SAMPLE_ETA4_BYTES bs       *)
(* (REJ_SAMPLE_ETA4_BYTES_EQ).                                               *)
(* ------------------------------------------------------------------------- *)
let MLDSA_REJ_UNIFORM_ETA4_SUBROUTINE_CORRECT = prove
 (`!res buf table (inlist:(4 word) list) pc stackpointer returnaddress.
      LENGTH inlist = 544 /\
      nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_mc) (res, 1024) /\
      nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_mc) (buf, 272) /\
      nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_mc) (table, 2048) /\
      nonoverlapping (res, 1024) (buf, 272) /\
      nonoverlapping (res, 1024) (table, 2048) /\
      nonoverlapping (stackpointer, 8) (res, 1024) /\
      nonoverlapping (stackpointer, 8) (buf, 272) /\
      nonoverlapping (stackpointer, 8) (table, 2048) /\
      nonoverlapping (stackpointer, 8) (word pc, LENGTH mldsa_rej_uniform_eta4_mc)
      ==> ensures x86
           (\s. bytes_loaded s (word pc) mldsa_rej_uniform_eta4_mc /\
                read RIP s = word pc /\
                read RSP s = stackpointer /\
                read (memory :> bytes64 stackpointer) s = returnaddress /\
                C_ARGUMENTS [res; buf; table] s /\
                read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                read(memory :> bytes(table,2048)) s =
                  num_of_wordlist mldsa_rej_uniform_table)
           (\s. read RIP s = returnaddress /\
                read RSP s = word_add stackpointer (word 8) /\
                (let outlist = SUB_LIST(0,256)
                    (REJ_SAMPLE_ETA4 inlist) in
                 let outlen = LENGTH outlist in
                 outlen <= 256 /\
                 C_RETURN s = word outlen /\
                 read(memory :> bytes(res,4 * outlen)) s =
                   num_of_wordlist outlist /\
                 (!i. i < outlen
                      ==> ival(EL i outlist:int32) < &5 /\
                          -- &5 < ival(EL i outlist:int32))))
           (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bytes(res,1024)])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPEC `inlist:(4 word) list` BYTES_TO_NIBBLES_SURJ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[EVEN_EXISTS] THEN EXISTS_TAC `272` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `bs:byte list` STRIP_ASSUME_TAC) THEN
  UNDISCH_THEN `BYTES_TO_NIBBLES (bs:byte list) = inlist`
    (SUBST_ALL_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH_BYTES_TO_NIBBLES]) THEN
  SUBGOAL_THEN `LENGTH (bs:byte list) = 272` ASSUME_TAC THENL
   [UNDISCH_TAC `2 * LENGTH (bs:byte list) = 544` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NUM_OF_BYTES_TO_NIBBLES; GSYM REJ_SAMPLE_ETA4_BYTES_EQ] THEN
  MP_TAC(SPECL
   [`res:int64`; `buf:int64`; `table:int64`; `bs:byte list`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`]
   MLDSA_REJ_UNIFORM_ETA4_SUBROUTINE_CORRECT_BYTES) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[]);;

(* ========================================================================= *)
(* Memory safety theorem                                                     *)
(* ========================================================================= *)

(* MEMSAFE helper tactics (DISCHARGE_MEMSAFE_TAC, DISCHARGE_MEMSAFE_ASM_TAC, *)
(* CONTAINED_ASM_TAC, ...) are defined here,                                 *)
(* after all CORRECT theorems, so the isolation freeze gate on the           *)
(* (expensive) CORRECT proof is unperturbed. They ride on the generic        *)
(* constant-time / memory-safety infrastructure in consttime.ml, which       *)
(* transitively pulls equiv.ml and supplies SIMPLIFY_MAYCHANGES_TAC /        *)
(* allowed_vars_e / EXISTS_E2_TAC / SAFE_META_EXISTS_TAC /                   *)
(* DISCHARGE_MEMACCESS_INBOUNDS_TAC, plus memaccess_inbounds,                *)
(* MEMACCESS_INBOUNDS_APPEND and the CONTAINED_MODULO_* lemmas.              *)
(* NOTE: this file sets type_invention_error := true globally (line 29) for  *)
(* the CORRECT proofs, but equiv.ml's MAYCHANGE-range helper only typechecks *)
(* under the HOL default (false).  On a cold load these deps have not been   *)
(* pulled by base.ml, so they load fresh HERE and would fail with            *)
(* "typechecking error ... MAYCHANGE" unless we restore the default around   *)
(* the needs.  The needs must stay a TOP-LEVEL statement (the line begins    *)
(* with the needs keyword) so it is inlined by the proof build, bringing     *)
(* allowed_vars_e /                                                          *)
(* EXISTS_E2_TAC / SAFE_META_EXISTS_TAC / DISCHARGE_MEMACCESS_INBOUNDS_TAC and *)
(* the CONTAINED_MODULO_* lemmas into scope for the tactics defined below.   *)
(* Toggle type_invention_error to the HOL default (false) around it, then    *)
(* restore this file's global setting (true).                                *)
type_invention_error := false;;
needs "x86/proofs/consttime.ml";;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Shared memory-safety discharge tactics (ride on consttime.ml).            *)
(* ------------------------------------------------------------------------- *)

let DISCHARGE_MEMSAFE_TAC:tactic =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(* Like SIMPLE_ARITH_TAC but allows `val` in assumptions since
   contained_modulo bounds may involve val terms. Filters out
   read/write/word simulation cruft that makes ASM_ARITH_TAC slow. *)
let (MEMSAFE_ARITH_TAC:tactic) =
  let numty = `:num` in
  let is_num_relop tm =
    exists (fun op -> is_binary op tm &&
                      (let x,_ = dest_binary op tm in type_of x = numty))
           ["=";"<";"<=";">";">="]
  and avoiders = ["lowdigits"; "highdigits"; "bigdigit";
                  "read"; "write"; "word"] in
  let avoiderp tm =
    match tm with Const(n,_) -> mem n avoiders | _ -> false in
  let filtered tm =
    (is_num_relop tm || (is_neg tm && is_num_relop (dest_neg tm))) &&
    not(can (find_term avoiderp) tm) in
  let tweak = GEN_REWRITE_RULE TRY_CONV [ARITH_RULE `~(n = 0) <=> 1 <= n`] in
  W(fun (asl,w) ->
    let asl' = filter (fun (_,th) -> filtered(concl th)) asl in
    MAP_EVERY (MP_TAC o tweak o snd) asl' THEN CONV_TAC ARITH_RULE);;

(* Bring `bitval p <= 1` as a MP_TAC hypothesis so MEMSAFE_ARITH_TAC's
   ARITH_RULE can derive bounds on bitval-sum expressions arising from
   VPMOVMSKPS-derived table indices. *)

let MEMSAFE_BITVAL_TAC:tactic =
  W(fun (asl,w) ->
    let bvs = find_terms (fun t ->
      try fst(dest_const(rator t)) = "bitval" with _ -> false) w in
    let bvs = setify bvs in
    MAP_EVERY (fun bv ->
      MP_TAC(SPEC (rand bv) BITVAL_BOUND)) bvs);;

(* ASM-aware version of CONTAINED_TAC for loop-body proofs where
   memory addresses involve symbolic loop variables. Uses MEMSAFE_ARITH_TAC
   which filters assumptions to avoid the performance issues of ASM_ARITH_TAC
   with hundreds of symbolic simulation assumptions. *)

let CONTAINED_ASM_TAC =
  GEN_REWRITE_TAC I [GSYM CONTAINED_MODULO_MOD2] THEN
  GEN_REWRITE_TAC (BINOP_CONV o LAND_CONV o LAND_CONV o TOP_DEPTH_CONV)
   [VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC(BINOP_CONV(LAND_CONV MOD_DOWN_CONV)) THEN
  REWRITE_TAC[CONTAINED_MODULO_MOD2; CONTAINED_MODULO_LMOD] THEN
  ((GEN_REWRITE_TAC I [CONTAINED_MODULO_REFL] THEN
    MEMSAFE_BITVAL_TAC THEN MEMSAFE_ARITH_TAC) ORELSE
   (MATCH_MP_TAC CONTAINED_MODULO_OFFSET_SIMPLE THEN
    MEMSAFE_BITVAL_TAC THEN MEMSAFE_ARITH_TAC) ORELSE
   (MATCH_MP_TAC CONTAINED_MODULO_SIMPLE THEN
    MEMSAFE_BITVAL_TAC THEN MEMSAFE_ARITH_TAC));;

(* ASM-aware version of DISCHARGE_MEMSAFE_TAC for loop bodies.
   Uses CONTAINED_ASM_TAC for contained_modulo proofs with symbolic bounds. *)

let DISCHARGE_MEMSAFE_ASM_TAC:tactic =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[memaccess_inbounds; ALL; EX; FST; SND] THEN
    REPEAT CONJ_TAC THEN
    TRY(REPEAT ((DISJ1_TAC THEN CONTAINED_ASM_TAC) ORELSE DISJ2_TAC ORELSE
                CONTAINED_ASM_TAC) THEN NO_TAC);
    REWRITE_TAC[APPEND; APPEND_NIL] THEN
    FIRST_ASSUM ACCEPT_TAC];;

(* ========================================================================= *)
(* MEMSAFE component: PREFIX_G_FULL_MS2_TAC                                  *)
(* ========================================================================= *)

(* PREFIX_G_FULL_MS2_TAC  : a VERBATIM copy of the value
   PREFIX_G_FULL_TAC with a single edit — STRIP_EXISTS_ASSUM_TAC right after
   ENSURES_INIT_TAC "s0". Purpose: anchor the precondition's events existential
   `read events s0 = APPEND e_acc e` (state-free RHS) so the stepper FLATTENS each
   `read events s(k+1)=CONS(ev)(read events sk)` to reference only the current
   state — surviving BOTH DISCARD_OLDSTATE_TAC and PURGE_STALE_STATES_TAC. This is
   the events-preservation mechanism applied to the existing
 value chain (no KEEPEV, no _MS rewrites). Confirmed by exp_flatten. *)

let TABLE_IDX_LT_256 = prove
 (`!K:num. val((word_zx:(M)word->int64)
              ((word_zx:(N)word->(M)word)
              ((word:num->(N)word)(K MOD 256)))) < 256`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD] THEN
  TRANS_TAC LET_TRANS `K MOD 256` THEN
  CONJ_TAC THENL
   [MESON_TAC[MOD_LE; LE_TRANS];
    SIMP_TAC[DIVISION; ARITH_EQ]]);;

(* idx < 256  ==>  the 8-byte gather load at table + 8*idx is contained in
   the 2048-byte table region (8*idx + 8 <= 8*255 + 8 = 2048). *)

let GATHER_CONTAINED = prove
 (`!(table:int64) idx:int64. val idx < 256
     ==> contained_modulo (2 EXP 64)
           (val(word_add table (word(8 * val idx))),8) (val table,2048)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [GSYM CONTAINED_MODULO_MOD2] THEN
  REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC(ONCE_DEPTH_CONV MOD_DOWN_CONV) THEN
  REWRITE_TAC[CONTAINED_MODULO_MOD2] THEN
  MATCH_MP_TAC CONTAINED_MODULO_OFFSET_SIMPLE THEN
  ASM_ARITH_TAC);;

(* Per-residual closer: pick the `(table,2048)` disjunct and apply the bounds.
   Works uniformly for all 4 (the 3 mask gathers and the f1bnd popcount nest). *)

let GATHER_BOUND_TAC : tactic =
  DISJ2_TAC THEN MATCH_MP_TAC GATHER_CONTAINED THEN MATCH_ACCEPT_TAC TABLE_IDX_LT_256;;

(* PREFIX_G_FULL_MS2_TAC: the memory-safety analogue of the prefix-gather    *)
(* body stepping — steps the SIMD block with the events existential carried  *)
(* and discharges the memaccess_inbounds obligation.                         *)
let PREFIX_G_FULL_MS2_TAC : tactic = mk_prefix_g_full true;;

(* ========================================================================= *)
(* MEMSAFE component: CLEAN_BODY_MEMSAFE + GATHER_BOUND_TAC                  *)
(* ========================================================================= *)

(* ========================================================================= *)
(* CLEAN_BODY_MEMSAFE: proves the eta4 SIMD loop body                        *)
(* (pc+52 -> pc+52) strengthened with the memory-safety events conjunct      *)
(* exists e_acc. read events s = APPEND e_acc e /\                           *)
(* memaccess_inbounds e_acc [buf,272;table,2048] [res,1024]                  *)
(* in BOTH pre and post — i.e. MLDSA_REJ_UNIFORM_ETA4_CLEAN_BODY_MEMSAFE.    *)
(*                                                                           *)
(* PATH A (events-preservation): the                                         *)
(* existing value chain (SI1_FOLD_V2; SI2/3/4_INTEGRATED; RAX/RCX_FINAL)     *)
(* is reused VERBATIM. The only changes vs CLEAN_BODY_FULL_TAC:              *)
(* 1. PREFIX_G_FULL_MS2_TAC instead of PREFIX_G_FULL_TAC: adds               *)
(* STRIP_EXISTS_ASSUM_TAC after ENSURES_INIT (anchors `read events s0 = APPEND *)
(* e_acc e`, a state-free RHS, so each step's events CONS fact flattens to   *)
(* reference only the current state and survives DISCARD_OLDSTATE/PURGE_STALE), *)
(* AND makes the s23 RIP-resolution events-aware.                            *)
(* 2. After RAX/RCX, DISCHARGE_MEMSAFE_ASM_TAC discharges the events existential *)
(* but leaves 4 `contained_modulo` table-gather disjuncts (the vpgatherdd loads *)
(* `[table + 8*idx, 8]`, idx a word_zx(word_zx(word(K MOD 256))) gather index). *)
(* These close with GATHER_BOUND_TAC below: pick the `(table,2048)` disjunct and *)
(* bound the index by 256 (so 8*idx+8 <= 2048).                              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Gather-index bound lemmas. The 4 residual disjuncts all carry a table index *)
(* of the shape  word_zx (word_zx (word (K MOD 256)))  for some K:num        *)
(* (K = val maskN for the 3 mask gathers; K = val(word_zx(word(popcount-sum))) *)
(* for the f1bnd nest). Since K is universally quantified, ONE lemma covers all *)
(* four. We avoid MEMSAFE_ARITH_TAC here because it filters out any assumption *)
(* containing a `word` constant — which is exactly what a raw `val IDX < 256` *)
(* for these word_zx-nested indices is — so the toolkit's auto-discharge cannot *)
(* close the table disjunct by itself.                                       *)
(* ------------------------------------------------------------------------- *)

let CLEAN_BODY_MS_FULL_TAC : tactic =
  PREFIX_G_FULL_MS2_TAC THEN SI1_FOLD_V2 THEN SI2_INTEGRATED THEN
  SI3_INTEGRATED THEN SI4_INTEGRATED THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `16*i+16 = 16*(i+1)`]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [RAX_FINAL_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [RCX_FINAL_TAC; ALL_TAC] THEN
  DISCHARGE_MEMSAFE_ASM_TAC THEN
  GATHER_BOUND_TAC;;

(* ------------------------------------------------------------------------- *)
(* Build the goal term (events existential in pre & post, layered onto the   *)
(* value CLEAN_BODY pre/post so Phase 5 can apply value+memsafe in lockstep) *)
(* and prove it.                                                             *)
(* ------------------------------------------------------------------------- *)
let clean_body_ms_tm =
  let qvars, body = strip_forall (concl MLDSA_REJ_UNIFORM_ETA4_CLEAN_BODY) in
  let hyps_tm, ens = dest_imp body in
  let ensc, ppf = strip_comb ens in
  let pre = el 1 ppf and post = el 2 ppf and frame = el 3 ppf in
  let sv, preb = dest_abs pre in
  let sv2, postb = dest_abs post in
  let evtempl = `exists e_acc:(uarch_event)list. read events (s:x86state) = APPEND e_acc (e:(uarch_event)list) /\ memaccess_inbounds e_acc [(buf:int64),272; (table:int64),2048] [(res:int64),1024]` in
  let pre' = mk_abs(sv, mk_conj(preb, vsubst[sv,`s:x86state`] evtempl)) in
  let post' = mk_abs(sv2, mk_conj(postb, vsubst[sv2,`s:x86state`] evtempl)) in
  let ens' = list_mk_comb(ensc,[el 0 ppf; pre'; post'; frame]) in
  list_mk_forall(qvars @ [`e:(uarch_event)list`], mk_imp(hyps_tm, ens'));;

let MLDSA_REJ_UNIFORM_ETA4_CLEAN_BODY_MEMSAFE =
  prove(clean_body_ms_tm, CLEAN_BODY_MS_FULL_TAC);;

(* ========================================================================= *)
(* MEMSAFE component: SCALAR_TAIL_BODY_MEMSAFE                               *)
(* ========================================================================= *)

(* ========================================================================= *)
(* SCALAR_TAIL_BODY_MEMSAFE: the eta4 scalar-tail per-byte                   *)
(* body (pc+314 -> pc+314) strengthened with the memory-safety events conjunct *)
(* exists e_acc. read events s = APPEND e_acc e /\                           *)
(* memaccess_inbounds e_acc [buf,272;table,2048] [res,1024]                  *)
(* in BOTH pre and post.                                                     *)
(*                                                                           *)
(* PATH A (events-preservation): the existing                                *)
(* value chain (SCALAR_BODY_SETUP + the 4 leaf closers RCX_INC_TAC / STORE4) is *)
(* reused VERBATIM. Two changes vs the value SCALAR_TAIL_BODY:               *)
(* 1. SCALAR_BODY_SETUP -> SCALAR_BODY_SETUP_MS: STRIP_EXISTS_ASSUM_TAC after *)
(* ENSURES_INIT anchors `read events s0 = APPEND e_acc e` (state-free RHS)   *)
(* so each step's events CONS fact survives DISCARD_OLDSTATE.                *)
(* 2. Each of the 4 leaf value closers is wrapped in an OUTER CONJ_TAC that  *)
(* peels the trailing events existential FIRST (the MS post is               *)
(* `(value_post) /\ events`, events the outermost conjunct), then            *)
(* DISCHARGE_MEMSAFE_ASM_TAC closes it. NO GATHER_BOUND_TAC: the scalar tail *)
(* has no vpgatherdd; the only memory accesses are res-stores, which         *)
(* CONTAINED_ASM_TAC (inside DISCHARGE) bounds directly from outlen0 < 256.  *)
(* ========================================================================= *)

(* Setup to s8 with the events existential anchored (= SCALAR_BODY_SETUP plus
   STRIP_EXISTS_ASSUM_TAC right after ENSURES_INIT_TAC "s0"). *)
let SCALAR_BODY_SETUP_MS =
  REPEAT GEN_TAC THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
  MP_TAC(ISPECL [`inlist:byte list`; `buf:int64`; `s0:x86state`; `p:num`; `272`] READ_1BYTE_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `outlen0 = LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list)` THEN
  FIRST_X_ASSUM(fun th -> if concl th = `L:num = outlen0` then SUBST_ALL_TAC th else NO_TAC) THEN
  SUBGOAL_THEN `~(&(val(word_zx(word outlen0:int64):int32)):int - &256 = &(val(word_sub(word_zx(word outlen0:int64):int32) (word 256):int32)))` ASSUME_TAC THENL
   [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(&(val(word_zx(word p:int64):int32)):int - &272 = &(val(word_sub(word_zx(word p:int64):int32) (word 272):int32)))` ASSUME_TAC THENL
   [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--8) THEN
  SUBGOAL_THEN `word_add buf (word (1 * val (word p:int64))) = word_add buf (word p):int64` ASSUME_TAC THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
    MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `p < 272`) THEN ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `word_add buf (word (1 * val (word p:int64))) = word_add buf (word p):int64`;
                              ASSUME `read (memory :> bytes8 (word_add buf (word p))) s4 = EL p (inlist:byte list)`;
                              R10_NIBBLE_VAL]) THEN
  DISCARD_OLDSTATE_TAC "s8";;

(* Build the MS goal term: events existential conjoined onto SCALAR_TAIL_BODY's
   pre & post (events the OUTERMOST conjunct), universally over the extra `e`. *)
let scalar_body_ms_tm =
  let qvars, body = strip_forall (concl SCALAR_TAIL_BODY) in
  let hyps_tm, ens = dest_imp body in
  let ensc, ppf = strip_comb ens in
  let pre = el 1 ppf and post = el 2 ppf and frame = el 3 ppf in
  let sv, preb = dest_abs pre in
  let sv2, postb = dest_abs post in
  let evtempl = `exists e_acc:(uarch_event)list. read events (s:x86state) = APPEND e_acc (e:(uarch_event)list) /\ memaccess_inbounds e_acc [(buf:int64),272; (table:int64),2048] [(res:int64),1024]` in
  let pre' = mk_abs(sv, mk_conj(preb, vsubst[sv,`s:x86state`] evtempl)) in
  let post' = mk_abs(sv2, mk_conj(postb, vsubst[sv2,`s:x86state`] evtempl)) in
  let ens' = list_mk_comb(ensc,[el 0 ppf; pre'; post'; frame]) in
  list_mk_forall(qvars @ [`e:(uarch_event)list`], mk_imp(hyps_tm, ens'));;

let SCALAR_TAIL_BODY_MEMSAFE = prove
 (scalar_body_ms_tm,

  SCALAR_BODY_SETUP_MS THEN
  ASM_CASES_TAC `val(EL p (inlist:byte list)) MOD 16 < 9` THENL
   [(* ===== ACCEPT-LOW (low<9): step to pc+364, store low, to pc+379 ===== *)
    SUBGOAL_THEN `~(&(val(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32) (word 9):int32)))` ASSUME_TAC THENL
     [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (9--14) THEN DISCARD_OLDSTATE_TAC "s14" THEN
    SUBGOAL_THEN `outlen0 + 1 < 256` ASSUME_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o check(fun th->let c=concl th in c=`outlen0<256`||c=`val(EL p (inlist:byte list)) MOD 16 < 9`||c=`~(outlen0=255/\val(EL p (inlist:byte list)) MOD 16 < 9)`))) THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> let c=concl th in
       if is_eq c && can(find_term(fun t->t=`RAX`))c && can(find_term(fun t->t=`s14:x86state`))c
       then ASSUME_TAC(REWRITE_RULE[MATCH_MP RAX_INC (ASSUME `outlen0<256`)] th) else NO_TAC) THEN
    SUBGOAL_THEN `~(&(val(word_zx(word(outlen0+1):int64):int32)):int - &256 = &(val(word_sub(word_zx(word(outlen0+1):int64):int32) (word 256):int32)))` ASSUME_TAC THENL
     [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (15--18) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[R11_NIBBLE_VAL]) THEN DISCARD_OLDSTATE_TAC "s18" THEN
    ASM_CASES_TAC `val(EL p (inlist:byte list)) DIV 16 < 9` THENL
     [(* ACCEPT-ACCEPT *)
      SUBGOAL_THEN `~(&(val(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32) (word 9):int32)))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (19--22) THEN
      SUBGOAL_THEN `val(word(outlen0+1):int64) = outlen0+1` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `outlen0+1<256`) THEN ARITH_TAC; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (23--25) THEN DISCARD_OLDSTATE_TAC "s25" THEN
      FIRST_X_ASSUM(fun th -> let c=concl th in
         if is_eq c && can(find_term(fun t->t=`RAX`))c && can(find_term(fun t->t=`s25:x86state`))c
         then ASSUME_TAC(REWRITE_RULE[MATCH_MP RAX_INC (ASSUME `outlen0+1<256`)] th) else NO_TAC) THEN
      ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist):int32 list) = outlen0 + 2` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LEN_STEP_BOTH) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        DISCH_THEN(fun th->REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC); ALL_TAC] THEN
      ASM_REWRITE_TAC[ARITH_RULE `(outlen0+1)+1 = outlen0+2`] THEN
      CONJ_TAC THENL
       [CONJ_TAC THENL
       [RCX_INC_TAC;
        SUBGOAL_THEN `REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist) =
           APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                  [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32;
                   word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) DIV 16))):int32]` SUBST1_TAC THENL
         [MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_BOTH) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `4 * (outlen0 + 2) = 4 * outlen0 + 8` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s25:x86state`;
           `REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list`;
           `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32;
             word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) DIV 16))):int32]`;
           `4*outlen0`; `8`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[DIMINDEX_32] THEN
          FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC) THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          (* 8-byte = [lo;hi]                                                *)
          GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM(REWRITE_CONV[APPEND] `APPEND [a:int32] [b:int32]`)] THEN
          SUBGOAL_THEN `(8:num) = 4 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
          MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `word_add res (word(4*outlen0)):int64`; `s25:x86state`;
             `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]`;
             `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) DIV 16))):int32]`;
             `4`; `4`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
          ANTS_TAC THENL [REWRITE_TAC[DIMINDEX_32; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_WORDLIST_SINGLETON_INT32] THEN
          SUBGOAL_THEN `val(word outlen0:int64) = outlen0` ASSUME_TAC THENL
           [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `outlen0<256`) THEN ARITH_TAC; ALL_TAC] THEN
          (* bridge both stores to spec form                                 *)
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`s25:x86state`))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c
             then ASSUME_TAC(REWRITE_RULE[ASSUME `val(word outlen0:int64) = outlen0`; MATCH_MP LO_STORE_VAL (ASSUME `val(EL p (inlist:byte list)) MOD 16 < 9`)] th) else NO_TAC) THEN
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`s25:x86state`))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) DIV 16`))c
             then ASSUME_TAC(REWRITE_RULE[MATCH_MP HI_STORE_VAL (ASSUME `val(EL p (inlist:byte list)) DIV 16 < 9`)] th) else NO_TAC) THEN
          CONJ_TAC THENL
           [FIRST_X_ASSUM(fun th -> let c=concl th in
               if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c && not(can(find_term is_cond)c)
               then MP_TAC th else NO_TAC) THEN
            STORE4_FROM_SPEC `s25:x86state` `word_add res (word(4 * outlen0)):int64`;
            SUBGOAL_THEN `word_add (word_add res (word (4 * outlen0))) (word 4):int64 = word_add res (word (4 * (outlen0+1)))` SUBST1_TAC THENL
             [CONV_TAC WORD_RULE; ALL_TAC] THEN
            FIRST_X_ASSUM(fun th -> let c=concl th in
               if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) DIV 16`))c && not(can(find_term is_cond)c)
               then MP_TAC th else NO_TAC) THEN
            STORE4_FROM_SPEC `s25:x86state` `word_add res (word(4 * (outlen0+1))):int64`]]];
        DISCHARGE_MEMSAFE_ASM_TAC];
      (* ===== LO-only (low<9, high>=9): jae pc+383 taken -> pc+314 =====    *)
      SUBGOAL_THEN `&(val(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32) (word 9):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL
         [MP_TAC(ASSUME `~(val(EL p (inlist:byte list)) DIV 16 < 9)`) THEN ARITH_TAC;
          MP_TAC(ISPEC `EL p (inlist:byte list)` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
          MP_TAC(SPECL[`val(EL p (inlist:byte list))`;`16`] DIV_LE) THEN ARITH_TAC]; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (19--20) THEN DISCARD_OLDSTATE_TAC "s20" THEN
      ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist):int32 list) = outlen0 + 1` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LEN_STEP_LO) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        DISCH_THEN(fun th->REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC); ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [CONJ_TAC THENL
       [RCX_INC_TAC;
        SUBGOAL_THEN `REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist) =
           APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                  [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]` SUBST1_TAC THENL
         [MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_LO) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `4 * (outlen0 + 1) = 4 * outlen0 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s20:x86state`;
           `REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list`;
           `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]`;
           `4*outlen0`; `4`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[DIMINDEX_32] THEN
          FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC) THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_WORDLIST_SINGLETON_INT32] THEN
        CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          SUBGOAL_THEN `val(word outlen0:int64) = outlen0` ASSUME_TAC THENL
           [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `outlen0<256`) THEN ARITH_TAC; ALL_TAC] THEN
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`s20:x86state`))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c
             then ASSUME_TAC(REWRITE_RULE[ASSUME `val(word outlen0:int64) = outlen0`; MATCH_MP LO_STORE_VAL (ASSUME `val(EL p (inlist:byte list)) MOD 16 < 9`)] th) else NO_TAC) THEN
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c && not(can(find_term is_cond)c)
             then MP_TAC th else NO_TAC) THEN
          STORE4_FROM_SPEC `s20:x86state` `word_add res (word(4 * outlen0)):int64`]];
        DISCHARGE_MEMSAFE_ASM_TAC]];
    (* ===== REJECT-LOW (low>=9): jae pc+347 taken -> pc+371 =====           *)
    SUBGOAL_THEN `&(val(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32) (word 9):int32))` ASSUME_TAC THENL
     [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL
       [MP_TAC(ASSUME `~(val(EL p (inlist:byte list)) MOD 16 < 9)`) THEN ARITH_TAC;
        MP_TAC(SPECL[`val(EL p (inlist:byte list))`;`16`] MOD_LT_EQ) THEN ARITH_TAC]; ALL_TAC] THEN
    X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (9--12) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[R11_NIBBLE_VAL]) THEN DISCARD_OLDSTATE_TAC "s12" THEN
    ASM_CASES_TAC `val(EL p (inlist:byte list)) DIV 16 < 9` THENL
     [(* HI-only (low>=9, high<9): jae pc+383 not taken -> store at res+4*outlen0 -> pc+314 *)
      SUBGOAL_THEN `~(&(val(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32) (word 9):int32)))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (13--16) THEN
      SUBGOAL_THEN `val(word outlen0:int64) = outlen0` ASSUME_TAC THENL
       [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `outlen0<256`) THEN ARITH_TAC; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (17--19) THEN DISCARD_OLDSTATE_TAC "s19" THEN
      FIRST_X_ASSUM(fun th -> let c=concl th in
         if is_eq c && can(find_term(fun t->t=`RAX`))c && can(find_term(fun t->t=`s19:x86state`))c
         then ASSUME_TAC(REWRITE_RULE[MATCH_MP RAX_INC (ASSUME `outlen0<256`)] th) else NO_TAC) THEN
      ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist):int32 list) = outlen0 + 1` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LEN_STEP_HI) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        DISCH_THEN(fun th->REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC); ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [CONJ_TAC THENL
       [RCX_INC_TAC;
        SUBGOAL_THEN `REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist) =
           APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                  [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) DIV 16))):int32]` SUBST1_TAC THENL
         [MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_HI) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `4 * (outlen0 + 1) = 4 * outlen0 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s19:x86state`;
           `REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list`;
           `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) DIV 16))):int32]`;
           `4*outlen0`; `4`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[DIMINDEX_32] THEN
          FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC) THEN ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_WORDLIST_SINGLETON_INT32] THEN
        CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`s19:x86state`))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) DIV 16`))c
             then ASSUME_TAC(REWRITE_RULE[ASSUME `val(word outlen0:int64) = outlen0`; MATCH_MP HI_STORE_VAL (ASSUME `val(EL p (inlist:byte list)) DIV 16 < 9`)] th) else NO_TAC) THEN
          FIRST_X_ASSUM(fun th -> let c=concl th in
             if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) DIV 16`))c && not(can(find_term is_cond)c)
             then MP_TAC th else NO_TAC) THEN
          STORE4_FROM_SPEC `s19:x86state` `word_add res (word(4 * outlen0)):int64`]];
        DISCHARGE_MEMSAFE_ASM_TAC];
      (* NONE (low>=9, high>=9): jae pc+383 taken -> pc+314, no store        *)
      SUBGOAL_THEN `&(val(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) DIV 16):int64):int32) (word 9):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL
         [MP_TAC(ASSUME `~(val(EL p (inlist:byte list)) DIV 16 < 9)`) THEN ARITH_TAC;
          MP_TAC(ISPEC `EL p (inlist:byte list)` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_8] THEN
          MP_TAC(SPECL[`val(EL p (inlist:byte list))`;`16`] DIV_LE) THEN ARITH_TAC]; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (13--14) THEN DISCARD_OLDSTATE_TAC "s14" THEN
      ENSURES_FINAL_STATE_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist):int32 list) = outlen0` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LEN_STEP_NONE) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
        DISCH_THEN(fun th->REWRITE_TAC[th]) THEN
        FIRST_ASSUM(fun th->if concl th=`LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist):int32 list) = outlen0` then REWRITE_TAC[th] else NO_TAC); ALL_TAC] THEN
      SUBGOAL_THEN `REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p+1) inlist):int32 list = REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist)` ASSUME_TAC THENL
       [MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_NONE) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_ACCEPT_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [RCX_INC_TAC; DISCHARGE_MEMSAFE_ASM_TAC]]]);;

(* ========================================================================= *)
(* MEMSAFE component: SCALAR_TAIL_RUN/AT_P_MEMSAFE                           *)
(* ========================================================================= *)

(* ========================================================================= *)
(* SCALAR_TAIL_RUN_MEMSAFE: the eta4 scalar-tail byte-loop                   *)
(* (pc+314 -> pc+402) strengthened with the memory-safety events conjunct in pre *)
(* & post.  Strong induction on the byte budget `d` (272 - p <= d), reusing the *)
(* value SCALAR_TAIL_RUN proof VERBATIM except:                              *)
(* 1. STRIP_EXISTS_ASSUM_TAC after each ENSURES_INIT_TAC (anchors events s0). *)
(* 2. exit leaves: DISCHARGE_MEMSAFE_ASM_TAC closes the trailing events goal. *)
(* 3. recursive leaf: SCALAR_TAIL_BODY -> SCALAR_TAIL_BODY_MEMSAFE (+`e` arg); *)
(* the IH is the MS IH, so ENSURES_SEQUENCE_TAC's intermediate bodyQ carries *)
(* events and the legs compose with a single shared `e`.                     *)
(* No GATHER_BOUND_TAC (scalar tail has no vpgatherdd; res-stores discharge via *)
(* CONTAINED_ASM_TAC).                                                       *)
(* Load after scalar_tail_ms.ml (binds SCALAR_TAIL_BODY_MEMSAFE).            *)
(* ========================================================================= *)

(* Thread the events existential DEEP-RIGHT on the conjunction spine so RUN's
   pre/post keep the canonical `bytes_loaded /\ read RIP = word.. /\ REST` shape
   that ENSURES_SEQUENCE_TAC's higher-order pattern (and ENSURES_INIT_TAC in the
   exit leaves) require. A naive (BIG)/\ev breaks the match (BIG, not
   bytes_loaded, would land in the program_decodes slot). The intermediate Q fed
   to ENSURES_SEQUENCE_TAC may be any shape, so the body lemma's outermost-events
   post is fine there. `e` is quantified LAST so INDUCT_TAC still inducts on d. *)
let rec conj_append_right t ev =
  if is_conj t then
    let l,r = dest_conj t in mk_conj(l, conj_append_right r ev)
  else mk_conj(t, ev);;
let scalar_run_ms_tm =
  let qvars, body = strip_forall (concl SCALAR_TAIL_RUN) in
  let hyps_tm, ens = dest_imp body in
  let ensc, ppf = strip_comb ens in
  let pre = el 1 ppf and post = el 2 ppf and frame = el 3 ppf in
  let sv, preb = dest_abs pre in
  let sv2, postb = dest_abs post in
  let evtempl = `exists e_acc:(uarch_event)list. read events (s:x86state) = APPEND e_acc (e:(uarch_event)list) /\ memaccess_inbounds e_acc [(buf:int64),272; (table:int64),2048] [(res:int64),1024]` in
  let pre' = mk_abs(sv, conj_append_right preb (vsubst[sv,`s:x86state`] evtempl)) in
  let post' = mk_abs(sv2, conj_append_right postb (vsubst[sv2,`s:x86state`] evtempl)) in
  let ens' = list_mk_comb(ensc,[el 0 ppf; pre'; post'; frame]) in
  list_mk_forall(qvars @ [`e:(uarch_event)list`], mk_imp(hyps_tm, ens'));;

let SCALAR_TAIL_RUN_MEMSAFE = prove
 (scalar_run_ms_tm,

  INDUCT_TAC THENL
   [(* ================= BASE CASE: d = 0 => p = 272 ================= *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `p = 272` SUBST_ALL_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> let c=concl th in c=`272 - p <= 0` || c=`p <= 272`))) THEN ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `inlist:byte list` SUB_LIST_BYTE_272) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `SUB_LIST(0,272) (inlist:byte list) = inlist`]) THEN
    REWRITE_TAC[ASSUME `SUB_LIST(0,272) (inlist:byte list) = inlist`] THEN
    ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = 256` THENL
     [(* --- BASE COUNT-EXIT: outlen = 256 --- *)
      MP_TAC(SPEC `REJ_SAMPLE_ETA4_BYTES inlist:int32 list` SUB_LIST_256_LE) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      REWRITE_TAC[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = 256`] THEN
      REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = REJ_SAMPLE_ETA4_BYTES inlist`] THEN
      ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
      SUBGOAL_THEN `&(val(word_zx(word 256:int64):int32)):int - &256 = &(val(word_sub(word_zx(word 256:int64):int32) (word 256):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = 256`] THEN
      REWRITE_TAC[LENGTH_BUTLAST_TMC] THEN ASM_REWRITE_TAC[] THEN DISCHARGE_MEMSAFE_ASM_TAC;
      (* --- BASE OFFSET-EXIT: outlen < 256, p = 272 ---                     *)
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) < 256` ASSUME_TAC THENL
       [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> let c=concl th in c=`LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) <= 256` || c=`~(LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = 256)`))) THEN ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `REJ_SAMPLE_ETA4_BYTES inlist:int32 list` SUB_LIST_256_LE) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = REJ_SAMPLE_ETA4_BYTES inlist`] THEN
      ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
      SUBGOAL_THEN `~(&(val(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list)):int64):int32)):int - &256 = &(val(word_sub(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list)):int64):int32) (word 256):int32)))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      SUBGOAL_THEN `&(val(word_zx(word 272:int64):int32)):int - &272 = &(val(word_sub(word_zx(word 272:int64):int32) (word 272):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[LENGTH_BUTLAST_TMC] THEN ASM_REWRITE_TAC[] THEN DISCHARGE_MEMSAFE_ASM_TAC];
    (* ================= STEP CASE: SUC d =================                  *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_CASES_TAC `256 <= LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list)` THENL
     [(* --- STEP COUNT-EXIT: outlen >= 256 (=256 by invariant) --- *)
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) = 256` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`inlist:byte list`; `p:num`] SUB_LIST_256_PREFIX_GE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      MP_TAC(SPEC `REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list` SUB_LIST_256_LE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN DISCH_TAC THEN
      SUBGOAL_THEN `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist)`;
                  ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) = 256`] THEN
      ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
      SUBGOAL_THEN `&(val(word_zx(word 256:int64):int32)):int - &256 = &(val(word_sub(word_zx(word 256:int64):int32) (word 256):int32))` ASSUME_TAC THENL
       [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
      X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) = 256`; LENGTH_BUTLAST_TMC] THEN
      ASM_REWRITE_TAC[] THEN DISCHARGE_MEMSAFE_ASM_TAC;
      (* --- not count-exit: outlen < 256 ---                                *)
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) < 256` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `p = 272` THENL
       [(* --- STEP OFFSET-EXIT: p = 272 --- *)
        FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `p = 272`)) THEN
        MP_TAC(SPEC `inlist:byte list` SUB_LIST_BYTE_272) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `SUB_LIST(0,272) (inlist:byte list) = inlist`]) THEN
        REWRITE_TAC[ASSUME `SUB_LIST(0,272) (inlist:byte list) = inlist`] THEN
        MP_TAC(SPEC `REJ_SAMPLE_ETA4_BYTES inlist:int32 list` SUB_LIST_256_LE) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
        REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) = REJ_SAMPLE_ETA4_BYTES inlist`] THEN
        ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
        SUBGOAL_THEN `~(&(val(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list)):int64):int32)):int - &256 = &(val(word_sub(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES inlist:int32 list)):int64):int32) (word 256):int32)))` ASSUME_TAC THENL
         [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
        SUBGOAL_THEN `&(val(word_zx(word 272:int64):int32)):int - &272 = &(val(word_sub(word_zx(word 272:int64):int32) (word 272):int32))` ASSUME_TAC THENL
         [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
        X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--4) THEN
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        REWRITE_TAC[LENGTH_BUTLAST_TMC] THEN ASM_REWRITE_TAC[] THEN DISCHARGE_MEMSAFE_ASM_TAC;
        (* --- p < 272 ---                                                   *)
        SUBGOAL_THEN `p < 272` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) = 255 /\ val(EL p (inlist:byte list)) MOD 16 < 9` THENL
         [(* --- STEP MID-BYTE EXIT: outlen=255, low<9 (accept low pushes to 256) --- *)
          FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (fun th -> is_conj(concl th) && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))(concl th))) THEN
          SUBGOAL_THEN `256 <= LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list)` ASSUME_TAC THENL
           [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_STEP_1) THEN
            ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `?rest. REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list =
             APPEND (APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                            [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]) rest`
           STRIP_ASSUME_TAC THENL
           [ASM_CASES_TAC `val(EL p (inlist:byte list)) DIV 16 < 9` THENL
             [EXISTS_TAC `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) DIV 16))):int32]` THEN
              MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_BOTH) THEN
              ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
              DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[APPEND; GSYM APPEND_ASSOC];
              EXISTS_TAC `[]:int32 list` THEN
              MP_TAC(SPECL[`inlist:byte list`;`p:num`] REJ_STEP_LO) THEN
              ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
              DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[APPEND_NIL]]; ALL_TAC] THEN
          MP_TAC(SPECL [`inlist:byte list`; `p+1`] SUB_LIST_256_PREFIX_GE) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
          SUBGOAL_THEN `LENGTH(APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                            [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]:int32 list) = 256` ASSUME_TAC THENL
           [REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) =
               APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                      [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]` ASSUME_TAC THENL
           [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && (try lhs(concl th) = `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list)` with _->false) then SUBST1_TAC th else NO_TAC) THEN
            FIRST_X_ASSUM(fun th -> if is_eq(concl th) && (try lhs(concl th) = `REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list` with _->false) then SUBST1_TAC th else NO_TAC) THEN
            W(fun (asl,gl) -> let lt = rhs gl in
               MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC (mk_comb(`SUB_LIST(0,256):(int32)list->(int32)list`, lt)) THEN
               CONJ_TAC THENL
                [MATCH_MP_TAC SUB_LIST_APPEND_LEFT THEN ASM_REWRITE_TAC[LE_REFL];
                 MATCH_MP_TAC SUB_LIST_256_LE THEN ASM_REWRITE_TAC[LE_REFL]]); ALL_TAC] THEN
          REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) =
                APPEND (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist))
                [word_sx (word_sub (word 4:int16) (word (val (EL p (inlist:byte list)) MOD 16))):int32]`] THEN
          REWRITE_TAC[ASSUME `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) = 255`] THEN
          ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
          MP_TAC(ISPECL [`inlist:byte list`; `buf:int64`; `s0:x86state`; `p:num`; `272`] READ_1BYTE_EL) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
          SUBGOAL_THEN `~(&(val(word_zx(word 255:int64):int32)):int - &256 = &(val(word_sub(word_zx(word 255:int64):int32) (word 256):int32)))` ASSUME_TAC THENL
           [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
          SUBGOAL_THEN `~(&(val(word_zx(word p:int64):int32)):int - &272 = &(val(word_sub(word_zx(word p:int64):int32) (word 272):int32)))` ASSUME_TAC THENL
           [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
          X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--8) THEN
          SUBGOAL_THEN `word_add buf (word (1 * val (word p:int64))) = word_add buf (word p):int64` ASSUME_TAC THENL
           [AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
            MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN MP_TAC(ASSUME `p < 272`) THEN ARITH_TAC; ALL_TAC] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `word_add buf (word (1 * val (word p:int64))) = word_add buf (word p):int64`;
                                      ASSUME `read (memory :> bytes8 (word_add buf (word p))) s4 = EL p (inlist:byte list)`;
                                      R10_NIBBLE_VAL]) THEN
          DISCARD_OLDSTATE_TAC "s8" THEN
          SUBGOAL_THEN `~(&(val(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32)):int - &9 = &(val(word_sub(word_zx(word(val(EL p (inlist:byte list)) MOD 16):int64):int32) (word 9):int32)))` ASSUME_TAC THENL
           [MATCH_MP_TAC JAE_NOT_TAKEN_LT THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (9--14) THEN
          DISCARD_OLDSTATE_TAC "s14" THEN
          SUBGOAL_THEN `&(val(word_zx(word 256:int64):int32)):int - &256 = &(val(word_sub(word_zx(word 256:int64):int32) (word 256):int32))` ASSUME_TAC THENL
           [MATCH_MP_TAC JAE_TAKEN_GE THEN CONJ_TAC THENL [ARITH_TAC; CONV_TAC NUM_REDUCE_CONV]; ALL_TAC] THEN
          X86_VSTEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (15--16) THEN
          ENSURES_FINAL_STATE_TAC THEN
          REWRITE_TAC[ASSUME `SUB_LIST(0,256)(REJ_SAMPLE_ETA4_BYTES inlist:int32 list) =
                APPEND (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,p) inlist))
                [word_sx (word_sub (word 4:int16) (word (val (EL p (inlist:byte list)) MOD 16))):int32]`] THEN
          CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
          REWRITE_TAC[ASSUME `LENGTH(APPEND (REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist))
                [word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]:int32 list) = 256`] THEN
          REWRITE_TAC[LENGTH_BUTLAST_TMC] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
          [REPEAT CONJ_TAC THEN
          (* memory fold: bytes(res,4*256) = APPEND prefix [lo]              *)
          SUBGOAL_THEN `4 * 256 = 4 * 255 + 4` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
          MP_TAC(ISPECL [`memory:(x86state,int64->byte)component`; `res:int64`; `s16:x86state`;
             `REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list`;
             `[word_sx(word_sub (word 4:int16) (word(val(EL p (inlist:byte list)) MOD 16))):int32]`;
             `4*255`; `4`] BYTES_EQ_NUM_OF_WORDLIST_APPEND) THEN
          ANTS_TAC THENL [REWRITE_TAC[DIMINDEX_32] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_WORDLIST_SINGLETON_INT32] THEN
          CONJ_TAC THENL
           [ASM_REWRITE_TAC[];
            SUBGOAL_THEN `word(4 * 255):int64 = word 1020` SUBST1_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
            FIRST_X_ASSUM(fun th -> let c=concl th in
               if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`s16:x86state`))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c
               then ASSUME_TAC(REWRITE_RULE[MATCH_MP LO_STORE_VAL (ASSUME `val(EL p (inlist:byte list)) MOD 16 < 9`)] th) else NO_TAC) THEN
            FIRST_X_ASSUM(fun th -> let c=concl th in
               if is_eq c && can(find_term(fun t->try fst(dest_const t)="bytes32" with _->false))c && can(find_term(fun t->t=`val(EL p (inlist:byte list)) MOD 16`))c && not(can(find_term is_cond)c) && can(find_term(fun t->t=`s16:x86state`))c
               then MP_TAC th else NO_TAC) THEN
            STORE4_FROM_SPEC `s16:x86state` `word_add res (word 1020):int64`];
           DISCHARGE_MEMSAFE_ASM_TAC];
          (* --- STEP CLEAN-RECURSIVE: body trip then IH at p+1 ---          *)
          SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p+1) inlist):int32 list) <= 256` ASSUME_TAC THENL
           [MP_TAC(SPECL[`inlist:byte list`;`p:num`] LENGTH_REJ_SAMPLE_STEP_1) THEN ASM_REWRITE_TAC[] THEN
            DISCH_THEN SUBST1_TAC THEN
            REPEAT(FIRST_X_ASSUM(MP_TAC o check(fun th -> let c=concl th in
               c = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) < 256` ||
               c = `~(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list) = 255 /\ val(EL p (inlist:byte list)) MOD 16 < 9)`))) THEN
            REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ARITH_TAC; ALL_TAC] THEN
          (* body lemma instance at (p, outlen(p))                           *)
          MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`p:num`;
             `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,p) inlist):int32 list)`;`stackpointer:int64`;`e:(uarch_event)list`] SCALAR_TAIL_BODY_MEMSAFE) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(fun body_th ->
            let bodyQ = rand(rator(concl body_th)) in
            ENSURES_SEQUENCE_TAC `pc + 314` bodyQ THEN
            CONJ_TAC THENL
             [(* leg1: P -> bodyQ via the body lemma (precond/postcond weaken) *)
              MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
              EXISTS_TAC (rand(rator(concl body_th))) THEN CONJ_TAC THENL
               [GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY(ASM_MESON_TAC[]);
                MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
                EXISTS_TAC (rand(rator(rator(concl body_th)))) THEN CONJ_TAC THENL
                 [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY(ASM_MESON_TAC[]);
                  ACCEPT_TAC body_th]];
              (* leg2: bodyQ -> R = IH at p+1                                *)
              ALL_TAC]) THEN
          (* leg2: weaken pre to IH's expanded pre, then apply IH@(p+1)      *)
          FIRST_X_ASSUM(fun ih -> if is_forall(concl ih) then
            (let ih_inst = SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`p+1`;`stackpointer:int64`;`e:(uarch_event)list`] ih in
             let ih_pre = rand(rator(rator(snd(dest_imp(concl ih_inst))))) in
             MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC ih_pre THEN CONJ_TAC THENL
              [GEN_TAC THEN BETA_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY(ASM_MESON_TAC[]);
               MP_TAC ih_inst THEN ANTS_TAC THENL
                [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]])
            else NO_TAC)]]]]);;

(* ========================================================================= *)
(* MLDSA_REJ_UNIFORM_ETA4_SCALAR_TAIL_AT_P_MEMSAFE:                          *)
(* the scalar-tail MEMSAFE contract at an arbitrary exit position p, a trivial *)
(* corollary of SCALAR_TAIL_RUN_MEMSAFE with budget d := 272 - p (so 272-p<=d *)
(* holds by LE_REFL). Events threaded deep-right (matching RUN_MEMSAFE); the *)
(* extra `e` arg is passed through and ASM_REWRITE closes the matching conjunct. *)
(* Mirrors the value MLDSA_REJ_UNIFORM_ETA4_SCALAR_TAIL_AT_P.                *)
(* ========================================================================= *)
let scalar_at_p_ms_tm =
  let qvars, body = strip_forall (concl MLDSA_REJ_UNIFORM_ETA4_SCALAR_TAIL_AT_P) in
  let hyps_tm, ens = dest_imp body in
  let ensc, ppf = strip_comb ens in
  let pre = el 1 ppf and post = el 2 ppf and frame = el 3 ppf in
  let sv, preb = dest_abs pre in
  let sv2, postb = dest_abs post in
  let evtempl = `exists e_acc:(uarch_event)list. read events (s:x86state) = APPEND e_acc (e:(uarch_event)list) /\ memaccess_inbounds e_acc [(buf:int64),272; (table:int64),2048] [(res:int64),1024]` in
  let pre' = mk_abs(sv, conj_append_right preb (vsubst[sv,`s:x86state`] evtempl)) in
  let post' = mk_abs(sv2, conj_append_right postb (vsubst[sv2,`s:x86state`] evtempl)) in
  let ens' = list_mk_comb(ensc,[el 0 ppf; pre'; post'; frame]) in
  list_mk_forall(qvars @ [`e:(uarch_event)list`], mk_imp(hyps_tm, ens'));;

let MLDSA_REJ_UNIFORM_ETA4_SCALAR_TAIL_AT_P_MEMSAFE = prove
 (scalar_at_p_ms_tm,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`272 - p`; `res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`p:num`;`stackpointer:int64`;`e:(uarch_event)list`] SCALAR_TAIL_RUN_MEMSAFE) THEN
  ASM_REWRITE_TAC[LE_REFL]);;

(* ========================================================================= *)
(* MEMSAFE component: MID_EXIT_*_MEMSAFE                                     *)
(* ========================================================================= *)

(* ========================================================================= *)
(* MID-EXIT MEMSAFE lemmas: the four mid-guard "taken"                       *)
(* exit cases of the eta4 SIMD loop body, each strengthened with the         *)
(* memory-safety events conjunct                                             *)
(* exists e_acc. read events s = APPEND e_acc e /\                           *)
(* memaccess_inbounds e_acc [buf,272;table,2048] [res,1024]                  *)
(* in BOTH pre and post. These are MID_EXIT_SUBITER1/2/3 and MID_EXIT_CASE4  *)
(* from x86/proofs/rej_uniform_eta4_avx2_asm.ml, lifted to MEMSAFE via PATH A. *)
(*                                                                           *)
(* PATH A (identical to CLEAN_BODY_MEMSAFE):                                 *)
(* reuse the existing value tactic verbatim, with three changes:             *)
(* 1. PREFIX_TO_S21_MS_TAC instead of PREFIX_TO_S21_TAC: inserts             *)
(* STRIP_EXISTS_ASSUM_TAC right after ENSURES_INIT_TAC "s0", anchoring the   *)
(* events precond to a state-free RHS so each step's CONS-events fact        *)
(* flattens and survives DISCARD_OLDSTATE/PURGE_STALE.                       *)
(* 2. The mid-guard RIP-resolution heuristics (FIRST_ASSUM grabbing the      *)
(* assumption containing `pc + K`) are made events-aware: with events        *)
(* anchored, the per-step `read events sN = CONS(EventJump(word(pc+K)),..)`  *)
(* fact ALSO matches `find_term (pc+K)`, so we additionally require          *)
(* `read RIP sN` on the LHS. (Same fix as in PREFIX_G_FULL_MS2_TAC.)         *)
(* This is why MG1_NT_MS_TAC, MG2_NT_MS_TAC, MG3_NT_MS_TAC,                  *)
(* SI2_MG2_TAKEN_MS_TAC, SI3_MG3_TAKEN_MS_TAC are defined below — verbatim   *)
(* copies of the value tactics with the RIP-LHS guard.                       *)
(* 3. After the value closers, DISCHARGE_MEMSAFE_ASM_TAC discharges the events *)
(* existential, leaving table-gather contained_modulo disjuncts that         *)
(* GATHER_BOUND_TAC closes (idx<256 => table+8*idx in [table,2048]).         *)
(* ========================================================================= *)

let PREFIX_TO_S21_MS_TAC : tactic = mk_prefix_to_s21 true;;






let midexit1_ms_tm =
  let qvars, body = strip_forall midexit1_tm in
  let hyps_tm, ens = dest_imp body in
  let ensc, ppf = strip_comb ens in
  let pre = el 1 ppf and post = el 2 ppf and frame = el 3 ppf in
  let sv, preb = dest_abs pre in
  let sv2, postb = dest_abs post in
  let evtempl = `exists e_acc:(uarch_event)list. read events (s:x86state) = APPEND e_acc (e:(uarch_event)list) /\ memaccess_inbounds e_acc [(buf:int64),272; (table:int64),2048] [(res:int64),1024]` in
  let pre' = mk_abs(sv, mk_conj(preb, vsubst[sv,`s:x86state`] evtempl)) in
  let post' = mk_abs(sv2, mk_conj(postb, vsubst[sv2,`s:x86state`] evtempl)) in
  let ens' = list_mk_comb(ensc,[el 0 ppf; pre'; post'; frame]) in
  list_mk_forall(qvars @ [`e:(uarch_event)list`], mk_imp(hyps_tm, ens'));;

let MID_EXIT_SUBITER1_MEMSAFE = prove(midexit1_ms_tm, mk_midexit1 true (DISCHARGE_MEMSAFE_ASM_TAC THEN GATHER_BOUND_TAC));;

let midexit2_ms_tm =
  let qvars, body = strip_forall midexit2_tm in
  let hyps_tm, ens = dest_imp body in
  let ensc, ppf = strip_comb ens in
  let pre = el 1 ppf and post = el 2 ppf and frame = el 3 ppf in
  let sv, preb = dest_abs pre in
  let sv2, postb = dest_abs post in
  let evtempl = `exists e_acc:(uarch_event)list. read events (s:x86state) = APPEND e_acc (e:(uarch_event)list) /\ memaccess_inbounds e_acc [(buf:int64),272; (table:int64),2048] [(res:int64),1024]` in
  let pre' = mk_abs(sv, mk_conj(preb, vsubst[sv,`s:x86state`] evtempl)) in
  let post' = mk_abs(sv2, mk_conj(postb, vsubst[sv2,`s:x86state`] evtempl)) in
  let ens' = list_mk_comb(ensc,[el 0 ppf; pre'; post'; frame]) in
  list_mk_forall(qvars @ [`e:(uarch_event)list`], mk_imp(hyps_tm, ens'));;

let MID_EXIT_SUBITER2_MEMSAFE = prove(midexit2_ms_tm, mk_midexit2 true (DISCHARGE_MEMSAFE_ASM_TAC THEN GATHER_BOUND_TAC));;

let midexit3_ms_tm =
  let qvars, body = strip_forall midexit3_tm in
  let hyps_tm, ens = dest_imp body in
  let ensc, ppf = strip_comb ens in
  let pre = el 1 ppf and post = el 2 ppf and frame = el 3 ppf in
  let sv, preb = dest_abs pre in
  let sv2, postb = dest_abs post in
  let evtempl = `exists e_acc:(uarch_event)list. read events (s:x86state) = APPEND e_acc (e:(uarch_event)list) /\ memaccess_inbounds e_acc [(buf:int64),272; (table:int64),2048] [(res:int64),1024]` in
  let pre' = mk_abs(sv, mk_conj(preb, vsubst[sv,`s:x86state`] evtempl)) in
  let post' = mk_abs(sv2, mk_conj(postb, vsubst[sv2,`s:x86state`] evtempl)) in
  let ens' = list_mk_comb(ensc,[el 0 ppf; pre'; post'; frame]) in
  list_mk_forall(qvars @ [`e:(uarch_event)list`], mk_imp(hyps_tm, ens'));;

let MID_EXIT_SUBITER3_MEMSAFE = prove(midexit3_ms_tm, mk_midexit3 true (DISCHARGE_MEMSAFE_ASM_TAC THEN GATHER_BOUND_TAC));;

let midexit4_ms_tm =
  let qvars, body = strip_forall midexit4_tm in
  let hyps_tm, ens = dest_imp body in
  let ensc, ppf = strip_comb ens in
  let pre = el 1 ppf and post = el 2 ppf and frame = el 3 ppf in
  let sv, preb = dest_abs pre in
  let sv2, postb = dest_abs post in
  let evtempl = `exists e_acc:(uarch_event)list. read events (s:x86state) = APPEND e_acc (e:(uarch_event)list) /\ memaccess_inbounds e_acc [(buf:int64),272; (table:int64),2048] [(res:int64),1024]` in
  let pre' = mk_abs(sv, mk_conj(preb, vsubst[sv,`s:x86state`] evtempl)) in
  let post' = mk_abs(sv2, mk_conj(postb, vsubst[sv2,`s:x86state`] evtempl)) in
  let ens' = list_mk_comb(ensc,[el 0 ppf; pre'; post'; frame]) in
  list_mk_forall(qvars @ [`e:(uarch_event)list`], mk_imp(hyps_tm, ens'));;

let MID_EXIT_CASE4_MEMSAFE = prove(midexit4_ms_tm, mk_midexit4 true (DISCHARGE_MEMSAFE_ASM_TAC THEN GATHER_BOUND_TAC));;

(* ========================================================================= *)
(* MEMSAFE component: MEMSAFE_SCAFFOLD + MLDSA_REJ_UNIFORM_ETA4_MEMSAFE_CORE *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Core MEMSAFE: the core MLDSA_REJ_UNIFORM_ETA4_MEMSAFE.                    *)
(* Mirrors the value CORRECT_SCAFFOLD_TAC / EXIT_OFFSET / MIDEXIT_ARM_TAC, with *)
(* the memory-safety events conjunct threaded through the loop invariant     *)
(* (DEEP-RIGHT, so ENSURES_WHILE_UP_TAC's canonical-spine HO match works) and *)
(* the per-block / exit lemmas swapped for their _MEMSAFE counterparts.      *)
(* ========================================================================= *)

(* Thread the events existential DEEP-RIGHT on the conjunction spine.        *)
let rec conj_append_right t ev =
  if is_conj t then let l,r = dest_conj t in mk_conj(l, conj_append_right r ev)
  else mk_conj(t, ev);;

let ev_existential =
  `exists e_acc:(uarch_event)list.
      read events (s:x86state) = APPEND e_acc (e:(uarch_event)list) /\
      memaccess_inbounds e_acc [(buf:int64),272; (table:int64),2048] [(res:int64),1024]`;;

(* MEMSAFE_LOOPINV = CORRECT_LOOPINV + events deep-right.                    *)
let MEMSAFE_LOOPINV =
  let iv,rest = dest_abs CORRECT_LOOPINV in
  let sv,body = dest_abs rest in
  mk_abs(iv, mk_abs(sv, conj_append_right body (vsubst[sv,`s:x86state`] ev_existential)));;

(* CLEAN_BLOCK_MEMSAFE: the relaxed-hyps body (drops ~(N=0) /\ i+1<N, relaxes to
   16*(i+1)<=272) with events outermost, for the OFFSET exit arm.  Proven by the
   same CLEAN_BODY_MS_FULL_TAC (the gather tactics never use the dropped hyps). *)
let clean_block_ms_tm =
  let qvars, body = strip_forall clean_block_tm in
  let hyps_tm, ens = dest_imp body in
  let ensc, ppf = strip_comb ens in
  let pre = el 1 ppf and post = el 2 ppf and frame = el 3 ppf in
  let sv, preb = dest_abs pre in
  let sv2, postb = dest_abs post in
  let pre' = mk_abs(sv, mk_conj(preb, vsubst[sv,`s:x86state`] ev_existential)) in
  let post' = mk_abs(sv2, mk_conj(postb, vsubst[sv2,`s:x86state`] ev_existential)) in
  let ens' = list_mk_comb(ensc,[el 0 ppf; pre'; post'; frame]) in
  list_mk_forall(qvars @ [`e:(uarch_event)list`], mk_imp(hyps_tm, ens'));;

let CLEAN_BLOCK_MEMSAFE = prove(clean_block_ms_tm, CLEAN_BODY_MS_FULL_TAC);;

(* ------------------------------------------------------------------------- *)
(* MEMSAFE_SCAFFOLD_TAC: mirror of the value CORRECT_SCAFFOLD_TAC.  After it, *)
(* ONE goal remains — the i=N-1 exit-block obligation (pc+52/pos16(N-1) ->   *)
(* pc+402, events).  G0 (~(N-1=0)) + G3 (back-edge refl) are pure; G1 (init  *)
(* pc->pc+52, 11 steps) discharges the i=0 events with the empty accumulator; *)
(* G2 (clean body, both edges) applies CLEAN_BODY_MEMSAFE@i with an events-  *)
(* associativity + ZMM-frame bridge (G2_BODY_BRIDGE_TAC).                    *)
(* ------------------------------------------------------------------------- *)

(* Bridge a loop-body goal (events deep-right, wide ZMM frame) to
   CLEAN_BODY_MEMSAFE@i (events outermost, narrow ZMM frame). *)
let G2_BODY_BRIDGE_TAC : tactic =
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`N:num`;`i:num`;`stackpointer:int64`;`e:(uarch_event)list`] MLDSA_REJ_UNIFORM_ETA4_CLEAN_BODY_MEMSAFE) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `i + 1 < N` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i+1` o check(is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THEN (FIRST [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]); ALL_TAC] THEN
  DISCH_THEN(fun bth ->
    W(fun (asl,gl) ->
      let lframe = rand(concl bth) in
      let lpost  = rand(rator(concl bth)) in
      let lpre   = rand(rator(rator(concl bth))) in
      let gframe = rand gl in
      let subsumed_tm = mk_binop `(subsumed):(x86state->x86state->bool)->(x86state->x86state->bool)->bool` lframe gframe in
      let subsumed_th = prove(subsumed_tm,
        REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN SUBSUMED_MAYCHANGE_TAC) in
      let bth' = MATCH_MP ENSURES_FRAME_SUBSUMED (CONJ subsumed_th bth) in
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC lpre THEN
      CONJ_TAC THENL
       [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY(ASM_MESON_TAC[]);
        MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC lpost THEN
        CONJ_TAC THENL
         [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY(ASM_MESON_TAC[]);
          ACCEPT_TAC bth']]));;

let MEMSAFE_SCAFFOLD_TAC : tactic =
  MAP_EVERY X_GEN_TAC [`res:int64`; `buf:int64`; `table:int64`; `inlist:byte list`; `e:(uarch_event)list`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES; LENGTH_MLDSA_REJ_UNIFORM_ETA4_TMC] THEN
  STRIP_TAC THEN GHOST_INTRO_TAC `stackpointer:int64` `read RSP` THEN
  SUBGOAL_THEN `?i. 256 < 16 * i \/ 248 < LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0, 16 * i) inlist):int16 list)` MP_TAC THENL
   [EXISTS_TAC `17:num` THEN ARITH_TAC; GEN_REWRITE_TAC LAND_CONV [num_WOP]] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LT] th)) THEN
  SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES] THEN
    REWRITE_TAC[REJ_NIBBLES_ETA4_EMPTY; LENGTH] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `N = 1` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `N = 1`)) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    REWRITE_TAC[ARITH_RULE `~(256 < 16 * 1)`] THEN
    MP_TAC(ISPECL [`inlist:byte list`; `16`] LENGTH_REJ_SAMPLE_ETA4_BYTES_SUB_LIST_BOUND) THEN
    ASM_REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
    REWRITE_TAC[ARITH_RULE `16 * 1 = 16`] THEN ARITH_TAC; ALL_TAC] THEN
  ENSURES_WHILE_UP_TAC `N - 1` `pc + 52` `pc + 52` MEMSAFE_LOOPINV THEN
  REPEAT CONJ_TAC THENL
   [(* G0 ~(N-1=0) *)
    REPEAT(FIRST_X_ASSUM(MP_TAC o check(fun th->concl th=`~(N=0)`||concl th=`~(N=1)`))) THEN ARITH_TAC;
    (* G1 init pc -> pc+52 (11 steps), i=0 events empty                      *)
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; SUB_LIST_CLAUSES; REJ_SAMPLE_ETA4_BYTES; REJ_NIBBLES_ETA4;
                NIBBLES_OF_BYTES; FILTER; MAP; LENGTH; num_of_wordlist] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_MEMORY_BYTES_TRIVIAL] THEN CONV_TAC WORD_REDUCE_CONV THEN
    EXISTS_TAC `[]:(uarch_event)list` THEN
    REWRITE_TAC[APPEND; memaccess_inbounds; ALL; EX; FST; SND];
    (* G2 forward body edge: CLEAN_BODY_MEMSAFE@i + bridge                   *)
    G2_BODY_BRIDGE_TAC;
    (* G3 re-entry body edge (0<i, pc+52->pc+52, inv i -> inv i): refl       *)
    REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    (* G4 exit obligation -- LEFT OPEN                                       *)
    ALL_TAC] THEN
  (* exit-block entry facts (hyp7 @ N-1), mirroring value CORRECT_SCAFFOLD_TAC *)
  SUBGOAL_THEN `16 * (N-1) <= 256 /\ LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*(N-1)) inlist):int16 list) <= 248` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `N-1` o check(is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(N-1)) inlist):int32 list) <= 248` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES]; ALL_TAC];;

(* ========================================================================= *)
(* G4 exit-block: the single goal left by MEMSAFE_SCAFFOLD_TAC               *)
(* (MEMSAFE_LOOPINV(N-1) @ pc+52 -> weak MEMSAFE post @ pc+402).  Mirrors the *)
(* value MLDSA_REJ_UNIFORM_ETA4_CORRECT's `ASM_CASES niblen(16N)<=248 THENL  *)
(* [OFFSET_ARM; MIDEXIT_ARM]`.  Intermediate ENSURES_TRANS predicates (q56_ms, *)
(* q318_ms) carry the events existential DEEP-RIGHT.                         *)
(*                                                                           *)
(* Both arms are proven below: the OFFSET arm via EXIT_OFFSET_MS and the     *)
(* MID-EXIT arm via MIDEXIT_ARM_MS_TAC (dispatching the MID_EXIT_*_MEMSAFE lemmas). *)
(* ========================================================================= *)

(* q56_ms / q318_ms: the value q56 / q318 intermediate predicates + events deep-right. *)
let q56_ms = `\s. (bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
      read RIP s = word(pc + 52) /\ read RSP s = stackpointer /\
      read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
      read(memory :> bytes(table,2048)) s = num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
      read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
      read YMM2 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
      read YMM3 s = word 1816346497840254045859937019744124044757176230049263749638550337379029484548 /\
      read YMM4 s = word 4086779620140571603184858294424279100703646517610843436686738259102816340233 /\
      read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*N) inlist):int32 list)) /\
      read RCX s = word(16*N) /\
      read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*N) inlist):int32 list))) s =
        num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*N) inlist))) /\
      (exists e_acc:(uarch_event)list. read events s = APPEND e_acc (e:(uarch_event)list) /\
        memaccess_inbounds e_acc [(buf:int64),272; (table:int64),2048] [(res:int64),1024])`;;

let q318_ms = `\s. (bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
      read RIP s = word(pc + 314) /\ read RSP s = stackpointer /\
      read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
      read(memory :> bytes(table,2048)) s = num_of_wordlist(mldsa_rej_uniform_table:byte list) /\
      read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
      read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*N) inlist):int32 list)) /\
      read RCX s = word(16*N) /\
      read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*N) inlist):int32 list))) s =
        num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*N) inlist))) /\
      (exists e_acc:(uarch_event)list. read events s = APPEND e_acc (e:(uarch_event)list) /\
        memaccess_inbounds e_acc [(buf:int64),272; (table:int64),2048] [(res:int64),1024])`;;

(* The OFFSET-arm lemma (16N=272 forced by niblen<=248), mirroring value EXIT_OFFSET. *)
let exit_offset_ms_tm = `
  !res buf table (inlist:byte list) pc N stackpointer e.
       LENGTH inlist = 272 /\
       nonoverlapping_modulo (2 EXP 64) (pc, 403) (val res,1024) /\
       nonoverlapping_modulo (2 EXP 64) (pc, 403) (val buf, 272) /\
       nonoverlapping_modulo (2 EXP 64) (pc, 403) (val table,2048) /\
       nonoverlapping_modulo (2 EXP 64) (val res,1024) (val buf, 272) /\
       nonoverlapping_modulo (2 EXP 64) (val res,1024) (val table,2048) /\
       16 * N = 272 /\
       LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*N) inlist):int16 list) <= 248
       ==> ensures x86
            (\s. (bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                 read RIP s = word(pc + 52) /\ read RSP s = stackpointer /\
                 read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                 read(memory :> bytes(table,2048)) s = num_of_wordlist mldsa_rej_uniform_table /\
                 read RDI s = res /\ read RSI s = buf /\ read RDX s = table /\
                 read YMM2 s = word 6811299366900952671974763824040465167839410862684739061144563765171360567055 /\
                 read YMM3 s = word 1816346497840254045859937019744124044757176230049263749638550337379029484548 /\
                 read YMM4 s = word 4086779620140571603184858294424279100703646517610843436686738259102816340233 /\
                 read RAX s = word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(N-1)) inlist):int32 list)) /\
                 read RCX s = word(16*(N-1)) /\
                 read(memory :> bytes(res, 4 * LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(N-1)) inlist):int32 list))) s =
                   num_of_wordlist(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0, 16*(N-1)) inlist))) /\
                 (exists e_acc:(uarch_event)list. read events s = APPEND e_acc e /\
                   memaccess_inbounds e_acc [buf,272; table,2048] [res,1024]))
            (\s. read RIP s = word(pc + LENGTH(BUTLAST mldsa_rej_uniform_eta4_tmc)) /\
                 (exists e2. read events s = APPEND e2 e /\
                   memaccess_inbounds e2 [buf,272; table,2048] [res,1024]))
            (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,, MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
             MAYCHANGE [CF; PF; AF; ZF; SF; OF] ,, MAYCHANGE [events] ,, MAYCHANGE [memory :> bytes(res,1024)])`;;

(* generic events-associativity + ZMM-frame bridge from a body/block lemma instance bth
   (events outermost) to the current goal (events deep-right). *)
let MS_BRIDGE_FROM (bth:thm) : tactic =
  W(fun (asl,gl) ->
    let lframe = rand(concl bth) in
    let lpost  = rand(rator(concl bth)) in
    let lpre   = rand(rator(rator(concl bth))) in
    let gframe = rand gl in
    let subsumed_tm = mk_binop `(subsumed):(x86state->x86state->bool)->(x86state->x86state->bool)->bool` lframe gframe in
    let subsumed_th = prove(subsumed_tm,
      REPEAT(MATCH_MP_TAC SUBSUMED_SEQ THEN REWRITE_TAC[SUBSUMED_REFL]) THEN SUBSUMED_MAYCHANGE_TAC) in
    let bth' = MATCH_MP ENSURES_FRAME_SUBSUMED (CONJ subsumed_th bth) in
    MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC lpre THEN
    CONJ_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY(ASM_MESON_TAC[]);
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC lpost THEN
      CONJ_TAC THENL
       [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY(ASM_MESON_TAC[]);
        ACCEPT_TAC bth']]);;

let EXIT_OFFSET_MS = prove(exit_offset_ms_tm,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_NIBBLES_ETA4(SUB_LIST(0,16*N) inlist):int16 list) <= 248` then ACCEPT_TAC th else NO_TAC); ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC q318_ms THEN
  CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [(* leg1: pc+52 -> q318_ms : CLEAN_BLOCK_MEMSAFE@(N-1) -> q56_ms, head guards -> q318_ms *)
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC q56_ms THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [(* leg1a: CLEAN_BLOCK_MEMSAFE@(N-1) -> q56_ms (pos 16N) *)
      SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL [UNDISCH_TAC `16 * N = 272` THEN ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`N:num`;`N-1`;`stackpointer:int64`;`e:(uarch_event)list`] CLEAN_BLOCK_MEMSAFE) THEN
      SUBGOAL_THEN `N - 1 + 1 = N` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN (FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]); ALL_TAC] THEN
      DISCH_THEN(fun bth -> MS_BRIDGE_FROM bth);
      (* leg1b: q56_ms -> q318_ms via head guards (cmp eax,248 nt; cmp ecx,256 taken) *)
      ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
      SUBGOAL_THEN `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,272) inlist):int32 list) <= 248` ASSUME_TAC THENL
       [UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` THEN
        SUBST1_TAC(ASSUME `16 * N = 272`) THEN REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~(&(val(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,272) inlist):int32 list)):int64):int32)):int - &248 = &(val(word_sub(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,272) inlist):int32 list)):int64):int32) (word 248):int32))) \/ val(word_sub(word_zx(word(LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,272) inlist):int32 list)):int64):int32) (word 248):int32) = 0` ASSUME_TAC THENL
       [MATCH_MP_TAC JA_NOT_TAKEN_LE THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(~(&(val(word_zx(word(272):int64):int32)):int - &256 = &(val(word_sub(word_zx(word(272):int64):int32) (word 256):int32))) \/ val(word_sub(word_zx(word(272):int64):int32) (word 256):int32) = 0)` ASSUME_TAC THENL
       [MATCH_MP_TAC JA_TAKEN_GT THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_EXEC (1--4) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `16 * N = 272`]) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCHARGE_MEMSAFE_ASM_TAC];
    (* leg2: q318_ms -> pc+402 : SCALAR_TAIL_AT_P_MEMSAFE @ p=16N, post-weaken to weak MEMSAFE post *)
    W(fun (asl,gl) ->
      let atp = SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`16*N`;`stackpointer:int64`;`e:(uarch_event)list`] MLDSA_REJ_UNIFORM_ETA4_SCALAR_TAIL_AT_P_MEMSAFE in
      let atp_ens = snd(dest_imp(concl atp)) in
      let _,ppf = strip_comb atp_ens in
      let atp_pre = el 1 ppf and atp_post = el 2 ppf in
      MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC atp_post THEN
      CONJ_TAC THENL
       [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC atp_pre THEN
        CONJ_TAC THENL
         [GEN_TAC THEN REWRITE_TAC[ASSUME `16 * N = 272`] THEN STRIP_TAC THEN
          ASM_REWRITE_TAC[ASSUME `16 * N = 272`] THEN TRY(ASM_MESON_TAC[]);
          MP_TAC atp THEN
          ANTS_TAC THENL
           [REPEAT CONJ_TAC THEN
            (FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC;
                    (FIRST_X_ASSUM(fun th -> if concl th = `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` then MP_TAC th else NO_TAC) THEN ARITH_TAC)]);
            DISCH_THEN ACCEPT_TAC]]])]);;

(* ------------------------------------------------------------------------- *)
(* MID-EXIT arm.  Mirrors the value MIDEXIT_DISPATCH / MIDEXIT_ARM_TAC.  For a *)
(* crossover at pexpr, leg1 = MID_EXIT_*_MEMSAFE @ N-1 (reaches pc+314@pexpr, *)
(* events outermost -> bridge to qpost_ms with events deep-right), leg2 =    *)
(* SCALAR_TAIL_AT_P_MEMSAFE @ pexpr (post-weakened to weak MEMSAFE post).    *)
(* ------------------------------------------------------------------------- *)

(* Generic leg2: from `<pc+314 @ p, value + events deep-right>` to the weak MEMSAFE post,
   via SCALAR_TAIL_AT_P_MEMSAFE @ p (post-weaken + pre-weaken). p is the exit position term. *)
let SCALAR_TAIL_LEG2_MS (p:term) : tactic =
  W(fun (asl,gl) ->
    let atp = SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;p;`stackpointer:int64`;`e:(uarch_event)list`] MLDSA_REJ_UNIFORM_ETA4_SCALAR_TAIL_AT_P_MEMSAFE in
    let atp_ens = snd(dest_imp(concl atp)) in
    let _,ppf = strip_comb atp_ens in
    let atp_pre = el 1 ppf and atp_post = el 2 ppf in
    MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN EXISTS_TAC atp_post THEN
    CONJ_TAC THENL
     [GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN EXISTS_TAC atp_pre THEN
      CONJ_TAC THENL
       [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN TRY(ASM_MESON_TAC[]);
        MP_TAC atp THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THEN (FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]);
          DISCH_THEN ACCEPT_TAC]]]);;

(* qpost_ms for a mid-exit lemma instance: its post (events outermost) re-threaded
   events deep-right, at i:=N-1.  midthm is the value-shape MEMSAFE lemma. *)
let midexit_qpost_ms (midthm:thm) : term =
  let post = rand(rator(snd(dest_imp(snd(strip_forall(concl midthm)))))) in
  let post = vsubst [`N-1`,`i:num`] post in
  let sv, body = dest_abs post in
  (* body = value_post /\ ev  (events outermost) -> re-thread deep-right     *)
  let value_post = lhand body in
  mk_abs(sv, conj_append_right value_post (vsubst[sv,`s:x86state`] ev_existential));;

let MIDEXIT_DISPATCH_MS (midthm:thm) (pexpr:term) (prevpos:term) : tactic =
  let qpost = midexit_qpost_ms midthm in
  MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN EXISTS_TAC qpost THEN
  CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [(* leg1: MID_EXIT lemma @ N-1, bridge events-outermost post -> qpost deep-right *)
    MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`N-1`;`stackpointer:int64`;`e:(uarch_event)list`] midthm) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN (FIRST [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]); ALL_TAC] THEN
    DISCH_THEN(fun bth -> MS_BRIDGE_FROM bth);
    (* leg2: niblen(pexpr)<=256 then SCALAR_TAIL_AT_P_MEMSAFE@pexpr          *)
    SUBGOAL_THEN (mk_comb(mk_comb(`(<=):num->num->bool`,
        mk_comb(`LENGTH:(int32)list->num`, mk_comb(`REJ_SAMPLE_ETA4_BYTES:byte list->int32 list`,
          mk_comb(mk_comb(`SUB_LIST:num#num->byte list->byte list`,mk_pair(`0`,pexpr)),`inlist:byte list`)))), `256`)) ASSUME_TAC THENL
     [SUBGOAL_THEN (mk_eq(pexpr, mk_binop `(+):num->num->num` prevpos `4`)) SUBST1_TAC THENL
       [UNDISCH_TAC `~(N=0)` THEN UNDISCH_TAC `16 * N <= 272` THEN ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC OUTLEN0_LE_256_FROM_SUBITER THEN CONJ_TAC THENL
       [UNDISCH_TAC `16 * N <= 272` THEN UNDISCH_TAC `~(N=0)` THEN UNDISCH_TAC `LENGTH(inlist:byte list)=272` THEN ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
    SCALAR_TAIL_LEG2_MS pexpr];;

(* ------------------------------------------------------------------------- *)
(* OFFSET arm: niblen(16N)<=248 in context -> force 16N=272 (N=17), apply EXIT_OFFSET_MS. *)
(* Mirrors value OFFSET_ARM_TAC.                                             *)
(* ------------------------------------------------------------------------- *)
let OFFSET_ARM_MS_TAC : tactic =
  SUBGOAL_THEN `16 * N = 272` ASSUME_TAC THENL
   [SUBGOAL_THEN `256 < 16 * N` ASSUME_TAC THENL
     [UNDISCH_TAC `256 < 16 * N \/ 248 < LENGTH (REJ_NIBBLES_ETA4 (SUB_LIST (0,16 * N) inlist):int16 list)` THEN
      REWRITE_TAC[GSYM LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN
      UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` THEN
      ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `N = 17` (fun th -> REWRITE_TAC[th] THEN CONV_TAC NUM_REDUCE_CONV) THEN
    UNDISCH_TAC `16 * (N-1) <= 256` THEN UNDISCH_TAC `256 < 16 * N` THEN
    UNDISCH_TAC `~(N=0)` THEN ARITH_TAC; ALL_TAC] THEN
  (* EXIT_OFFSET_MS pre is events-OUTERMOST; the scaffold goal pre is events-deep-right.
     Bridge via MS_BRIDGE_FROM (pre-assoc + post + frame all match by content). *)
  MP_TAC(SPECL [`res:int64`;`buf:int64`;`table:int64`;`inlist:byte list`;`pc:num`;`N:num`;`stackpointer:int64`;`e:(uarch_event)list`] EXIT_OFFSET_MS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM LENGTH_REJ_SAMPLE_ETA4_BYTES] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` THEN
    SUBST1_TAC(ASSUME `16 * N = 272`) THEN REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun bth -> MS_BRIDGE_FROM bth);;

let MIDEXIT_ARM_MS_TAC : tactic =
  SUBGOAL_THEN `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(LENGTH (REJ_SAMPLE_ETA4_BYTES (SUB_LIST (0,16 * N) inlist):int32 list) <= 248)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * N <= 272` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * (N-1) <= 256` THEN UNDISCH_TAC `~(N=0)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `16 * ((N-1)+1) <= 272` ASSUME_TAC THENL
   [UNDISCH_TAC `16 * N <= 272` THEN UNDISCH_TAC `~(N=0)` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(N-1)+4) inlist):int32 list) <= 248` THENL
   [ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(N-1)+8) inlist):int32 list) <= 248` THENL
     [ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*(N-1)+12) inlist):int32 list) <= 248` THENL
       [SUBGOAL_THEN `248 < LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*((N-1)+1)) inlist):int32 list)` ASSUME_TAC THENL
         [SUBGOAL_THEN `16*((N-1)+1) = 16*N` SUBST1_TAC THENL
           [UNDISCH_TAC `~(N=0)` THEN ARITH_TAC; ALL_TAC] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MIDEXIT_DISPATCH_MS MID_EXIT_CASE4_MEMSAFE `16*((N-1)+1)` `16*(N-1)+12`;
        MIDEXIT_DISPATCH_MS MID_EXIT_SUBITER3_MEMSAFE `16*(N-1)+12` `16*(N-1)+8`];
      MIDEXIT_DISPATCH_MS MID_EXIT_SUBITER2_MEMSAFE `16*(N-1)+8` `16*(N-1)+4`];
    MIDEXIT_DISPATCH_MS MID_EXIT_SUBITER1_MEMSAFE `16*(N-1)+4` `16*(N-1)`];;

(* ------------------------------------------------------------------------- *)
(* The complete exit-block tactic + the core MLDSA_REJ_UNIFORM_ETA4_MEMSAFE. *)
(* ------------------------------------------------------------------------- *)
let EXIT_BLOCK_MS_TAC : tactic =
  ASM_CASES_TAC `LENGTH(REJ_SAMPLE_ETA4_BYTES(SUB_LIST(0,16*N) inlist):int32 list) <= 248` THENL
   [OFFSET_ARM_MS_TAC; MIDEXIT_ARM_MS_TAC];;

let core_ms_tm = `!res buf table (inlist:byte list) e pc.
        LENGTH inlist = 272 /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (res, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (buf, 272) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (table, 2048) /\
        nonoverlapping (res, 1024) (buf, 272) /\
        nonoverlapping (res, 1024) (table, 2048)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [res; buf; table] s /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s =
                    num_of_wordlist mldsa_rej_uniform_table /\
                  read events s = e)
             (\s. read RIP s = word(pc + LENGTH (BUTLAST mldsa_rej_uniform_eta4_tmc)) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     memaccess_inbounds e2 [buf,272; table,2048] [res,1024]))
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`;;

let MLDSA_REJ_UNIFORM_ETA4_MEMSAFE_CORE = prove(core_ms_tm,
  MEMSAFE_SCAFFOLD_TAC THEN EXIT_BLOCK_MS_TAC);;

let MLDSA_REJ_UNIFORM_ETA4_MEMSAFE = prove
 (`!res buf table (inlist:byte list) e pc.
        LENGTH inlist = 272 /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (res, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (buf, 272) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (table, 2048) /\
        nonoverlapping (res, 1024) (buf, 272) /\
        nonoverlapping (res, 1024) (table, 2048)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) (BUTLAST mldsa_rej_uniform_eta4_tmc) /\
                  read RIP s = word pc /\
                  C_ARGUMENTS [res; buf; table] s /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s =
                    num_of_wordlist mldsa_rej_uniform_table /\
                  read events s = e)
             (\s. read RIP s = word(pc + LENGTH (BUTLAST mldsa_rej_uniform_eta4_tmc)) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                       [buf,272; table,2048]
                       [res,1024]))
             (MAYCHANGE [RIP; RAX; RCX; R8; R9; R10; R11] ,,
              MAYCHANGE [ZMM0; ZMM1; ZMM2; ZMM3; ZMM4; ZMM5; ZMM6] ,,
              MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events] ,,
              MAYCHANGE [memory :> bytes(res,1024)])`,
  MATCH_ACCEPT_TAC MLDSA_REJ_UNIFORM_ETA4_MEMSAFE_CORE);;

(* Concrete-length variant of the core MEMSAFE (exit RIP = word(pc+402)).    *)
let MLDSA_REJ_UNIFORM_ETA4_MEMSAFE_CORE_CONCRETE =
  CONV_RULE(REWRITE_CONV[LENGTH_MLDSA_REJ_UNIFORM_ETA4_TMC;
                         fst MLDSA_REJ_UNIFORM_ETA4_EXEC])
    MLDSA_REJ_UNIFORM_ETA4_MEMSAFE_CORE;;

(* ------------------------------------------------------------------------- *)
(* Memory safety of the subroutine form.                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_REJ_UNIFORM_ETA4_NOIBT_SUBROUTINE_SAFE =
  let saved_tic = !type_invention_error in
  type_invention_error := false;
  let th = prove
   (`!res buf table (inlist:byte list) e pc stackpointer returnaddress.
        LENGTH inlist = 272 /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (res, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (buf, 272) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_tmc) (table, 2048) /\
        nonoverlapping (res, 1024) (buf, 272) /\
        nonoverlapping (res, 1024) (table, 2048) /\
        nonoverlapping (stackpointer, 8) (res, 1024) /\
        nonoverlapping (stackpointer, 8) (buf, 272) /\
        nonoverlapping (stackpointer, 8) (table, 2048) /\
        nonoverlapping (stackpointer, 8) (word pc, LENGTH mldsa_rej_uniform_eta4_tmc)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_rej_uniform_eta4_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [res; buf; table] s /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s =
                    num_of_wordlist mldsa_rej_uniform_table /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                       [buf,272; table,2048; stackpointer,8]
                       [res,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(res,1024)])`,
    REWRITE_TAC[LENGTH_MLDSA_REJ_UNIFORM_ETA4_TMC] THEN
    X86_PROMOTE_RETURN_NOSTACK_TAC mldsa_rej_uniform_eta4_tmc
      MLDSA_REJ_UNIFORM_ETA4_MEMSAFE_CORE_CONCRETE THEN
    DISCHARGE_MEMSAFE_TAC) in
  type_invention_error := saved_tic;
  th;;

(* Full (untrimmed, IBT-prefixed) subroutine wrapper via ADD_IBT_RULE.       *)
let MLDSA_REJ_UNIFORM_ETA4_SUBROUTINE_SAFE =
  ADD_IBT_RULE MLDSA_REJ_UNIFORM_ETA4_NOIBT_SUBROUTINE_SAFE;;

(* ========================================================================= *)
(* Windows ABI variants.                                                     *)
(*                                                                           *)
(* The mldsa-native original ships no Windows theorems. We add them here     *)
(* following the template of x86/proofs/mlkem_rej_uniform_VARIABLE_TIME.ml   *)
(* (Windows CORRECT) and x86/proofs/mldsa_ntt.ml (manual xmm-spill splice).  *)
(*                                                                           *)
(* Unlike mlkem_rej_uniform (which deliberately avoids xmm6 so its Windows   *)
(* prologue only saves rdi/rsi and WINDOWS_X86_WRAP_STACK_TAC applies), the  *)
(* eta4 kernel uses xmm6 as a scratch register in the gather step. xmm6 is   *)
(* nonvolatile under the Microsoft x64 ABI, so the Windows entry point       *)
(* spills xmm6 (and rdi/rsi) to a 40-byte stack frame. The standard wrap     *)
(* tactics do not model this spill, so we splice the SysV core into the      *)
(* Windows prologue/epilogue by hand, exactly as mldsa_ntt.ml does.          *)
(* ========================================================================= *)

let mldsa_rej_uniform_eta4_windows_mc = define_from_elf
   "mldsa_rej_uniform_eta4_windows_mc"
   "x86/mldsa/mldsa_rej_uniform_eta4_VARIABLE_TIME.obj";;

let mldsa_rej_uniform_eta4_windows_tmc = define_trimmed
   "mldsa_rej_uniform_eta4_windows_tmc" mldsa_rej_uniform_eta4_windows_mc;;

let MLDSA_REJ_UNIFORM_ETA4_WINDOWS_TMC_EXEC =
  X86_MK_EXEC_RULE mldsa_rej_uniform_eta4_windows_tmc;;

(* The Windows entry spills xmm6 + rdi + rsi in an 8-instruction prologue     *)
(* (endbr64; sub rsp,40; movups [rsp],xmm6; mov [rsp+16],rdi;                 *)
(*  mov [rsp+24],rsi; mov rdi,rcx; mov rsi,rdx; mov rdx,r8), after which the  *)
(* SysV body begins at byte offset 0x1f = 31 (= LENGTH of that prologue).     *)
(* The epilogue restores xmm6/rdi/rsi and pops the frame in 5 instructions.   *)
let MLDSA_REJ_UNIFORM_ETA4_NOIBT_WINDOWS_SUBROUTINE_CORRECT =
  let saved_tic = !type_invention_error in
  type_invention_error := false;
  let th = prove
   (`!res buf table (inlist:byte list) pc stackpointer returnaddress.
        LENGTH inlist = 272 /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_windows_tmc) (res, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_windows_tmc) (buf, 272) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_windows_tmc) (table, 2048) /\
        nonoverlapping (res, 1024) (buf, 272) /\
        nonoverlapping (res, 1024) (table, 2048) /\
        nonoverlapping (word_sub stackpointer (word 40),48) (res, 1024) /\
        nonoverlapping (word_sub stackpointer (word 40),48) (buf, 272) /\
        nonoverlapping (word_sub stackpointer (word 40),48) (table, 2048) /\
        nonoverlapping (word_sub stackpointer (word 40),48)
                       (word pc, LENGTH mldsa_rej_uniform_eta4_windows_tmc)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_rej_uniform_eta4_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [res; buf; table] s /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s =
                    num_of_wordlist mldsa_rej_uniform_table)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (let outlist = SUB_LIST(0,256)
                      (REJ_SAMPLE_ETA4_BYTES inlist) in
                   let outlen = LENGTH outlist in
                   outlen <= 256 /\
                   WINDOWS_C_RETURN s = word outlen /\
                   read(memory :> bytes(res,4 * outlen)) s =
                     num_of_wordlist outlist /\
                   (!i. i < outlen
                        ==> ival(EL i outlist:int32) < &5 /\
                            -- &5 < ival(EL i outlist:int32))))
             (MAYCHANGE [RSP] ,,
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(res,1024)] ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 40),40)])`,
    REWRITE_TAC[fst MLDSA_REJ_UNIFORM_ETA4_WINDOWS_TMC_EXEC] THEN
    REPLICATE_TAC 5 GEN_TAC THEN
    WORD_FORALL_OFFSET_TAC 40 THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[fst MLDSA_REJ_UNIFORM_ETA4_WINDOWS_TMC_EXEC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[WINDOWS_C_ARGUMENTS; WINDOWS_C_RETURN] THEN
    REWRITE_TAC[WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
    ENSURES_PRESERVED_TAC "rsi_init" `RSI` THEN
    ENSURES_PRESERVED_TAC "init_xmm6" `ZMM6 :> bottomhalf :> bottomhalf` THEN
    REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER'] THEN
    REWRITE_TAC(map GSYM [YMM6]) THEN
    GHOST_INTRO_TAC `init_ymm6:int256` `read YMM6` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_WINDOWS_TMC_EXEC (1--7) THEN
    MP_TAC(SPECL [`res:int64`; `buf:int64`; `table:int64`; `inlist:byte list`;
                  `pc + 27`]
      MLDSA_REJ_UNIFORM_ETA4_CORRECT_BOUND_CONCRETE) THEN
    ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN NONOVERLAPPING_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    X86_BIGSTEP_TAC MLDSA_REJ_UNIFORM_ETA4_WINDOWS_TMC_EXEC "s8" THENL
     [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
       (BYTES_LOADED_SUBPROGRAM_RULE mldsa_rej_uniform_eta4_windows_tmc
       (REWRITE_RULE[BUTLAST_CLAUSES]
        (AP_TERM `BUTLAST:byte list->byte list` mldsa_rej_uniform_eta4_tmc))
       27));
      RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[C_RETURN]) THEN
    ABBREV_TAC `ymm6_epilog = read YMM6 s8` THEN
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_WINDOWS_TMC_EXEC (9--13) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o
         check (fun th -> is_eq(concl th) &&
                          rand(concl th) = `init_xmm6:int128`)) THEN
      CONV_TAC WORD_BLAST]) in
  type_invention_error := saved_tic;
  th;;

let MLDSA_REJ_UNIFORM_ETA4_WINDOWS_SUBROUTINE_CORRECT =
  ADD_IBT_RULE MLDSA_REJ_UNIFORM_ETA4_NOIBT_WINDOWS_SUBROUTINE_CORRECT;;

(* ------------------------------------------------------------------------- *)
(* Windows-ABI memory safety (SAFE).  Same manual xmm6-spill splice as the   *)
(* Windows CORRECT above, but wrapping the events/memaccess_inbounds core     *)
(* MLDSA_REJ_UNIFORM_ETA4_MEMSAFE_CORE_CONCRETE.  The safety witness e2 for   *)
(* the whole Windows body is the SysV core trace e2 framed by the spill       *)
(* prologue stores and epilogue loads (all inside the [stackpointer,48]/      *)
(* [stackpointer,40] frame), discharged by DISCHARGE_MEMACCESS_INBOUNDS_TAC.  *)
(* ------------------------------------------------------------------------- *)
let MLDSA_REJ_UNIFORM_ETA4_NOIBT_WINDOWS_SUBROUTINE_SAFE =
  let saved_tic = !type_invention_error in
  type_invention_error := false;
  let th = prove
   (`!res buf table (inlist:byte list) e pc stackpointer returnaddress.
        LENGTH inlist = 272 /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_windows_tmc) (res, 1024) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_windows_tmc) (buf, 272) /\
        nonoverlapping (word pc, LENGTH mldsa_rej_uniform_eta4_windows_tmc) (table, 2048) /\
        nonoverlapping (res, 1024) (buf, 272) /\
        nonoverlapping (res, 1024) (table, 2048) /\
        nonoverlapping (word_sub stackpointer (word 40),48) (res, 1024) /\
        nonoverlapping (word_sub stackpointer (word 40),48) (buf, 272) /\
        nonoverlapping (word_sub stackpointer (word 40),48) (table, 2048) /\
        nonoverlapping (word_sub stackpointer (word 40),48)
                       (word pc, LENGTH mldsa_rej_uniform_eta4_windows_tmc)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_rej_uniform_eta4_windows_tmc /\
                  read RIP s = word pc /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  WINDOWS_C_ARGUMENTS [res; buf; table] s /\
                  read(memory :> bytes(buf, 272)) s = num_of_wordlist inlist /\
                  read(memory :> bytes(table,2048)) s =
                    num_of_wordlist mldsa_rej_uniform_table /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     memaccess_inbounds e2
                       [buf,272; table,2048; word_sub stackpointer (word 40),48]
                       [res,1024; word_sub stackpointer (word 40),40]))
             (MAYCHANGE [RSP] ,,
              WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(res,1024)] ,,
              MAYCHANGE [memory :> bytes(word_sub stackpointer (word 40),40)])`,
    REWRITE_TAC[fst MLDSA_REJ_UNIFORM_ETA4_WINDOWS_TMC_EXEC] THEN
    REPLICATE_TAC 6 GEN_TAC THEN
    WORD_FORALL_OFFSET_TAC 40 THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[fst MLDSA_REJ_UNIFORM_ETA4_WINDOWS_TMC_EXEC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[WINDOWS_C_ARGUMENTS; WINDOWS_C_RETURN] THEN
    REWRITE_TAC[WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    ENSURES_PRESERVED_TAC "rdi_init" `RDI` THEN
    ENSURES_PRESERVED_TAC "rsi_init" `RSI` THEN
    ENSURES_PRESERVED_TAC "init_xmm6" `ZMM6 :> bottomhalf :> bottomhalf` THEN
    REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER'] THEN
    REWRITE_TAC(map GSYM [YMM6]) THEN
    GHOST_INTRO_TAC `init_ymm6:int256` `read YMM6` THEN
    GLOBALIZE_PRECONDITION_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_WINDOWS_TMC_EXEC (1--7) THEN
    MP_TAC(SPECL [`res:int64`; `buf:int64`; `table:int64`; `inlist:byte list`;
                  `read events s7`; `pc + 27`]
      MLDSA_REJ_UNIFORM_ETA4_MEMSAFE_CORE_CONCRETE) THEN
    ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN NONOVERLAPPING_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    X86_BIGSTEP_TAC MLDSA_REJ_UNIFORM_ETA4_WINDOWS_TMC_EXEC "s8" THENL
     [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
       (BYTES_LOADED_SUBPROGRAM_RULE mldsa_rej_uniform_eta4_windows_tmc
       (REWRITE_RULE[BUTLAST_CLAUSES]
        (AP_TERM `BUTLAST:byte list->byte list` mldsa_rej_uniform_eta4_tmc))
       27));
      RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN
    ABBREV_TAC `ymm6_epilog = read YMM6 s8` THEN
    X86_STEPS_TAC MLDSA_REJ_UNIFORM_ETA4_WINDOWS_TMC_EXEC (9--13) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [EXISTS_TAC
       `CONS (EventJump (word (pc + 448),returnaddress))
        (CONS (EventLoad (word_add stackpointer (word 40),8))
        (CONS (EventLoad (word_add stackpointer (word 24),8))
        (CONS (EventLoad (word_add stackpointer (word 16),8))
        (CONS (EventLoad (stackpointer,16))
        (APPEND e2
        (CONS (EventStore (word_add stackpointer (word 24),8))
        (CONS (EventStore (word_add stackpointer (word 16),8))
        (CONS (EventStore (stackpointer,16)) []))))))))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM APPEND_ASSOC; APPEND];
        DISCHARGE_MEMACCESS_INBOUNDS_TAC];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o
         check (fun th -> is_eq(concl th) &&
                          rand(concl th) = `init_xmm6:int128`)) THEN
      CONV_TAC WORD_BLAST]) in
  type_invention_error := saved_tic;
  th;;

let MLDSA_REJ_UNIFORM_ETA4_WINDOWS_SUBROUTINE_SAFE =
  ADD_IBT_RULE MLDSA_REJ_UNIFORM_ETA4_NOIBT_WINDOWS_SUBROUTINE_SAFE;;

(* NOTE: the mldsa-native original ends with a trailing                      *)
(*   needs "mldsa_native/x86_64/proofs/subroutine_signatures.ml"             *)
(* purely to register the subroutine signature in the constant-time harness. *)
(* In s2n-bignum that registration is not referenced by this proof (the      *)
(* SAFE theorems are derived from the MEMSAFE core, not via                   *)
(* PROVE_SAFETY_SPEC_TAC), so the load is dropped, matching                   *)
(* x86/proofs/mlkem_rej_uniform_VARIABLE_TIME.ml.                             *)
