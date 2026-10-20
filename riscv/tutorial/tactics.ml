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

let ASSIGNS_ABSORB_CONTAINED = prove
 (`!a:int32.
    ASSIGNS (memory :> bytes(a,64)) ,,
    ASSIGNS (memory :> bytes32(word_add a (word 4))) =
    ASSIGNS (memory :> bytes(a,64))`,
  GEN_TAC THEN CONV_TAC(LAND_CONV ASSIGNS_ABSORB_CONV) THEN REFL_TAC);;

let _ =
  let frame = ASSUME
    `(MAYCHANGE [PC] ,, MAYCHANGE [memory :> bytes(a,64)])
       (s0:riscvstate) s` in
  let update = ASSUME
    `write PC pc
       (write (memory :> bytes32(word_add a (word 4))) v
          (s:riscvstate)) = s'` in
  let updated = MAYCHANGE_UPDATE_RULE update frame in
  if rator(rator(concl updated)) <> rator(rator(concl frame))
  then failwith "MAYCHANGE_UPDATE_RULE grew a frame for a contained write";;

let _ =
  if can ASSIGNS_ABSORB_CONV
    `ASSIGNS (memory :> bytes(a,64)) ,,
     ASSIGNS (memory :> bytes32(word_add (a:int32) (word 64)))`
  then failwith "ASSIGNS_ABSORB_CONV absorbed an out-of-range write";;

let CHECK_INITIAL_FRAME_TAC expected (asl,w as gl) =
  let frame = find (maychange_term o concl o snd) asl |> snd in
  if rator(rator(concl frame)) <> expected
  then failwith "ENSURES_INIT_TAC chose the wrong initial frame";
  ALL_TAC gl;;

let ENSURES_INIT_REQUESTED_FRAME = prove
 (`!a:int32.
    ensures (\s s':riscvstate. s' = s) (\s. T) (\s. T)
      (MAYCHANGE [PC] ,, MAYCHANGE [memory :> bytes(a,64)])`,
  GEN_TAC THEN ENSURES_INIT_TAC ~seed_frame:true "s0" THEN
  CHECK_INITIAL_FRAME_TAC
    `MAYCHANGE [PC] ,, MAYCHANGE [memory :> bytes(a,64)]` THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[]);;

let ENSURES_N_INIT_REQUESTED_FRAME = prove
 (`ensures_n (\s s':riscvstate. s' = s) (\s. T) (\s. T)
    (MAYCHANGE [PC]) (\s. 0)`,
  ENSURES_INIT_TAC ~seed_frame:true "s0" THEN
  CHECK_INITIAL_FRAME_TAC `MAYCHANGE [PC]` THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[]);;

let ENSURES_INIT_FALLBACK_FRAME = prove
 (`ensures (\s s':riscvstate. s' = s) (\s. T) (\s. T)
    (\s s'. s = s')`,
  ENSURES_INIT_TAC ~seed_frame:true "s0" THEN
  (fun (asl,w as gl) ->
    let frame = find (maychange_term o concl o snd) asl |> snd in
    let relation = rator(rator(concl frame)) in
    if name_of(fst(strip_comb relation)) <> "MAYCHANGE" ||
       dest_list(rand relation) <> []
    then failwith "ENSURES_INIT_TAC did not retain the empty-frame fallback";
    ALL_TAC gl) THEN
  ENSURES_FINAL_STATE_TAC THEN REWRITE_TAC[]);;
