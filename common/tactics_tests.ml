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

let _ =
  let rule = ASSUME `!n:num. f n = n + 1` in
  let step = GEN_REWRITE_CONV I [rule] ORELSEC NUM_RED_CONV in
  let ordinary = TOP_DEPTH_CONV step
  and memoized = MEMOIZED_TOP_DEPTH_CONV step
  and bounded = MEMOIZED_TOP_DEPTH_CONV ~max_entries:2 step
  and disabled = MEMOIZED_TOP_DEPTH_CONV ~max_entries:0 step in
  List.iter (fun target ->
    let expected = ordinary target in
    List.iter (fun conv ->
      let actual = conv target in
      if not(aconv (concl actual) (concl expected)) ||
         hyp actual <> hyp expected then
        failwith "memoized depth changed its result or hypotheses")
      [memoized;bounded;disabled])
    [`f 0 + f 0:num`; `f 1:num`; `f 2:num`; `f 0:num`;
     `\n:num. f n`; `\j:num. f j`; `x:num`];
  if can (MEMOIZED_TOP_DEPTH_CONV ~max_entries:(-1)) step then
    failwith "memoized depth accepted a negative cache limit";;

let _ =
  let rule = ASSUME `!n:num. f n = n + 1` in
  let step = GEN_REWRITE_CONV I [rule] ORELSEC NUM_RED_CONV in
  let ordinary = TOP_DEPTH_CONV step
  and memoized = MEMOIZED_TOP_DEPTH_CONV step in
  let inputs = map (fun n ->
    mk_comb(`f:num->num`,mk_var("memo_symbol_" ^ string_of_int n,`:num`)))
    (0--31) in
  List.iter (fun target ->
    let actual = memoized target and expected = ordinary target in
    if concl actual <> concl expected || hyp actual <> hyp expected then
      failwith "memoized depth confused distinct symbolic variables")
    (inputs @ rev inputs);
  let calls = ref 0 in
  let atoms = [`f 0:num`; `f 1:num`; `f 2:num`] in
  let step tm =
    if mem tm atoms then incr calls;
    GEN_REWRITE_CONV I [rule] tm in
  let bounded = MEMOIZED_TOP_DEPTH_CONV ~max_entries:2 step in
  List.iter (fun tm -> ignore(bounded tm)) (atoms @ [hd atoms]);
  if !calls <> 4 then
    failwith "memoized depth did not respect its cache limit";;

let _ =
  let calls = ref 0 in
  let atom = `f 0:num` in
  let rule = ASSUME `f 0:num = 1` in
  let step tm =
    if tm = atom then incr calls;
    GEN_REWRITE_CONV I [rule] tm in
  let target = `f 0 + f 0:num` in
  ignore(TOP_DEPTH_CONV step target);
  if !calls <> 2 then failwith "memoized depth control fixture changed";
  calls := 0;
  let memoized = MEMOIZED_TOP_DEPTH_CONV step in
  let result = memoized target in
  if !calls <> 1 || hyp result <> hyp rule then
    failwith "memoized depth did not share a repeated contextual subterm";
  ignore(memoized target);
  if !calls <> 1 then failwith "memoized depth missed a repeated result";
  let changed = ADD_ASSUM `hidden:bool` rule in
  let fresh = MEMOIZED_TOP_DEPTH_CONV (GEN_REWRITE_CONV I [changed]) in
  let result = fresh target in
  if not(mem `hidden:bool` (hyp result)) then
    failwith "memoized depth reused a theorem from another context";;

let FRESH_ABBREV_SCOPE = prove
 (`!a:num. ?b:num. b = a + 1`,
  GEN_TAC THEN FRESH_ABBREV_TAC `fresh:num = a + 1` THEN
  EXISTS_TAC `fresh:num` THEN FIRST_ASSUM (ACCEPT_TAC o SYM));;

let FRESH_ABBREV_INSTANTIATION = prove
 (`!a:num. ?x:num. x < x + 1 /\ a = x`,
  GEN_TAC THEN X_META_EXISTS_TAC `witness:num` THEN
  FRESH_ABBREV_TAC `fresh:num = witness + 1` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fun definition ->
      CONV_TAC(RAND_CONV(GEN_REWRITE_CONV I [definition]))) THEN ASM_ARITH_TAC;
    UNIFY_REFL_TAC]);;

let _ =
  let fact = ASSUME `a + 1 = b:num` in
  let _,[(asl,w)],_ =
    FRESH_ABBREV_TAC `fresh:num = a + 1` (["original",fact],`a + 1 > a`) in
  if w <> `a + 1 > a` ||
     concl(snd(hd(tl asl))) <> concl fact ||
     concl(snd(hd asl)) <> `a + 1 = fresh:num`
  then failwith "FRESH_ABBREV_TAC rewrote the original context or goal";
  let hidden = ADD_ASSUM `fresh:num = 0` TRUTH in
  if can (FRESH_ABBREV_TAC `fresh:num = a + 1`) (["hidden",hidden],`T`) ||
     can (FRESH_ABBREV_TAC `fresh:num = fresh + 1`) ([],`T`) ||
     can (FRESH_ABBREV_TAC `fresh:num = a + 1`) ([],`fresh:num = 0`)
  then failwith "FRESH_ABBREV_TAC accepted a non-fresh name";;

(* Rewriting a separation premise to its modular form must retain the
   drivers for subregions, including their original hypotheses. *)

let _ =
  let cases =
   [`nonoverlapping (p:int32,96) (a,1024)`,
    `nonoverlapping (p:int32,96) (word_add a (word 16),16)`;
    `nonoverlapping (p:int64,96) (a,1024)`,
    `nonoverlapping (p:int64,96) (word_add a (word 16),16)`;
    `nonoverlapping (word pc:int64,96) (a,1024)`,
    `nonoverlapping (word pc:int64,96) (word_add a (word 16),16)`;
    `p:int32 = a \/ nonoverlapping (p,96) (a,1024)`,
    `nonoverlapping (p:int32,96) (word_add a (word 128),16)`;
    `p:int64 = a \/ nonoverlapping (p,96) (a,1024)`,
    `nonoverlapping (p:int64,96) (word_add a (word 128),16)`] in
  List.iter (fun (premise,target) ->
    List.iter (fun extra ->
      let original =
        if extra then ADD_ASSUM `hidden:bool` (ASSUME premise)
        else ASSUME premise in
      List.iter (fun fact ->
        let drivers = NONOVERLAPPING_DRIVERS
          [ASSUME `unused:bool`; fact;
           ASSUME `word_add (u:int64) (word 4) = v`] in
        if length drivers <> 3 then
          failwith "nonoverlap driver discarded a separation premise";
        List.iter (fun tm ->
          let proof = NONOVERLAPPING_RULE (drivers,[]) tm in
          if concl proof <> tm || hyp proof <> hyp original then
            failwith "nonoverlap driver changed premise dependencies")
          [target; rand(concl(PURE_ONCE_REWRITE_CONV
                            [NONOVERLAPPING_SYM] target))])
        [original;
         REWRITE_RULE[NONOVERLAPPING_CLAUSES_GEN] original;
         REWRITE_RULE[NONOVERLAPPING_CLAUSES] original])
      [false;true];
    if can (NONOVERLAPPING_RULE (NONOVERLAPPING_DRIVERS [],[])) target then
      failwith "nonoverlap driver proved separation without its premise")
    cases;;

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
