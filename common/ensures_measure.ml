(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Code with an irregular control flow graph, proved by cut points and a     *)
(* measure: R n s says that s is at one of the cut points with the measure   *)
(* n (e.g. the potential of a model state that s corresponds to). If from    *)
(* every R n state the code reaches either the postcondition or a cut point  *)
(* with a smaller measure, within the frame C, then from every R n state it  *)
(* reaches the postcondition. This is the loop rule for code whose loops     *)
(* are not counted, e.g. a state machine with several loop headers.          *)
(* ========================================================================= *)

let ENSURES_MEASURE_INDUCT = prove
 (`!(step:A->A->bool) (R:num->A->bool) Q C.
        C ,, C = C /\
        (!n. ensures step (R n) (\s. Q s \/ ?m. m < n /\ R m s) C)
        ==> !n. ensures step (R n) Q C`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[FUN_EQ_THM; seq] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!a b c. (C:A->A->bool) a b /\ C b c ==> C a c` ASSUME_TAC
  THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[ensures] THEN X_GEN_TAC `s:A` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
    try fst(dest_const(fst(strip_comb(snd(dest_forall(concl th)))))) =
        "ensures"
    with Failure _ -> false)) THEN
  REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `s:A`) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[EVENTUALLY_IMP_EVENTUALLY]
   `(!s'. P s' ==> eventually (step:A->A->bool) Q s')
    ==> eventually step P s ==> eventually step Q s`) THEN
  X_GEN_TAC `s':A` THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC) THENL
   [ONCE_REWRITE_TAC[eventually_CASES] THEN DISJ1_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC)] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th ->
    try is_imp(snd(dest_forall(concl th))) with Failure _ -> false)) THEN
  ASM_REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `s':A`) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  X_GEN_TAC `s'':A` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
