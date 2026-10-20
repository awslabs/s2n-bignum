(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* Regression checks for shared context and abbreviation tactics.
   Run with `make -C common test_tactics`; no machine model is loaded. *)

needs "Library/integer.ml";;
needs "Library/words.ml";;
needs "Library/bitmatch.ml";;
needs "common/for_hollight.ml";;
needs "common/words2.ml";;
needs "common/misc.ml";;
needs "common/components.ml";;

let CLARIFY_DERIVED_LABEL = prove
 (`!p q. p /\ (p ==> q) ==> q`,
  REPEAT STRIP_TAC THEN
  LABEL_TAC "derived"
    (MATCH_MP (ASSUME `p ==> q`) (ASSUME `p:bool`)) THEN
  CLARIFY_TAC THEN
  USE_THEN "derived" ACCEPT_TAC);;

let CLARIFY_UNUSED_FACT = prove
 (`!p q. p /\ q ==> p`,
  REPEAT STRIP_TAC THEN CLARIFY_TAC THEN ASM_REWRITE_TAC[]);;

(* A labelled assumption is already independent. Its theorem need not be
   reapplied during justification, including after a metavariable changes. *)

let CLARIFY_ASSUMED_LABEL = prove
 (`!p:bool. p ==> p`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "assumed") THEN
  CLARIFY_TAC THEN USE_THEN "assumed" ACCEPT_TAC);;

let CLARIFY_CONJUNCTION_LABEL = prove
 (`!p q:bool. p /\ q ==> p /\ q`,
  REPEAT GEN_TAC THEN DISCH_THEN(LABEL_TAC "both") THEN
  CLARIFY_TAC THEN USE_THEN "both" ACCEPT_TAC);;

let CLARIFY_ASSUMED_INSTANTIATION = prove
 (`!a:num. a < 3 ==> ?x:num. x < 3 /\ a = x`,
  REPEAT STRIP_TAC THEN X_META_EXISTS_TAC `witness:num` THEN
  CLARIFY_TAC THEN CONJ_TAC THENL
   [ALL_TAC; UNIFY_REFL_TAC] THEN ASM_REWRITE_TAC[]);;

let CLARIFY_INSTANTIATION = prove
 (`!a:num. a < 3 ==> ?x:num. a = x`,
  REPEAT STRIP_TAC THEN
  META_EXISTS_TAC THEN CLARIFY_TAC THEN UNIFY_REFL_TAC);;

let CLARIFY_INSTANTIATED_FACT = prove
 (`!a:num. ?x:num. x < x + 1 /\ a = x`,
  GEN_TAC THEN X_META_EXISTS_TAC `witness:num` THEN
  LABEL_TAC "bound"
    (SPEC `witness:num` (ARITH_RULE `!n. n < n + 1`)) THEN
  CLARIFY_TAC THEN CONJ_TAC THENL
   [USE_THEN "bound" ACCEPT_TAC; UNIFY_REFL_TAC]);;
