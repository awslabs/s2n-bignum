(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* Regression checks for symbolic execution and shared context tactics. *)

needs "riscv/proofs/base.ml";;

let _ =
  let first = ASSUME `x:num = y`
  and second = ASSUME `x:num = z`
  and conjunction = ASSUME `p /\ q`
  and quantified = ASSUME `!n:num. f n = n + 1` in
  let gen = CACHED_GEN_REWRITE_CONV TOP_DEPTH_CONV
  and repeated = CACHED_CONTEXT_REWRITE_CONV
    true TOP_DEPTH_CONV basic_net in
  let check cached ordinary rules target =
    let expected = ordinary rules target
    and actual = cached rules target in
    if concl actual <> concl expected || hyp actual <> hyp expected then
      failwith "cached context rewriting changed the result or hypotheses" in
  List.iter (fun rules ->
    List.iter (fun target ->
      check gen (GEN_REWRITE_CONV TOP_DEPTH_CONV) rules target;
      check repeated REWRITE_CONV rules target)
     [`x:num`; `f 2:num`; `p /\ q`; `x + 0:num`])
   [[first;second;conjunction;quantified];
    [ASSUME(concl first);ASSUME(concl second);conjunction;quantified];
    [second;first;conjunction;quantified];
    [ADD_ASSUM `hidden:bool` first;conjunction;quantified];
    [conjunction;quantified]; []; [first;conjunction;quantified]];
  let contextual = ADD_ASSUM `hidden:bool` first in
  check gen (GEN_REWRITE_CONV TOP_DEPTH_CONV) [contextual] `x:num`;
  check gen (GEN_REWRITE_CONV TOP_DEPTH_CONV)
    [ADD_ASSUM `other:bool` first] `x:num`;
  check gen (GEN_REWRITE_CONV TOP_DEPTH_CONV) [first] `x:num`;
  check repeated REWRITE_CONV [first] `x + 0:num`;
  let saved = basic_rewrites() in
  set_basic_rewrites[];
  check repeated REWRITE_CONV [first] `x + 0:num`;
  set_basic_rewrites saved;
  check repeated REWRITE_CONV [first] `x + 0:num`;;

let CACHED_REWRITE_INSTANTIATION = prove
 (`!a:num. ?x:num. x < x + 1 /\ a = x`,
  GEN_TAC THEN X_META_EXISTS_TAC `witness:num` THEN
  ASSUME_TAC(SPEC `witness:num` (ARITH_RULE `!n. n < n + 1`)) THEN
  CONJ_TAC THENL
   [CACHED_ASM_REWRITE_TAC [];
    UNIFY_REFL_TAC]);;

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
