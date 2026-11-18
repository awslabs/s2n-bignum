(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the combined correctness, constant-time and memory-safety       *)
(* ("FULL") theorems of the x86-64 mldsa-native proofs, as for AArch64 (see  *)
(* arm/proofs/utils/mldsa_native_full.ml, whose tools these are, for the     *)
(* x86 model).                                                               *)
(*                                                                           *)
(* Each function gets one FULL theorem, stating both correctness and the     *)
(* events, of the form                                                       *)
(*                                                                           *)
(*      ?f_events. !e args.                                                  *)
(*         H ==> ensures x86 (\s. P s /\ read events s = e)                  *)
(*                           (\s. Q s /\ ?e2. read events s = APPEND e2 e /\ *)
(*                                            e2 = f_events <public args> /\ *)
(*                                            memaccess_inbounds e2 R W)     *)
(*                           C                                               *)
(*                                                                           *)
(* and its correctness theorem (|- !args. H ==> ensures x86 P Q C) and its   *)
(* safety theorem (the FULL theorem without the data and without Q) follow   *)
(* from it, by CORRECT_OF_FULL_TAC and SAFE_OF_FULL_TAC.                     *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native.ml";;
needs "x86/proofs/consttime.ml";;
needs "common/fips204/properties/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* The combined contract implies the separate ones: the events in the        *)
(* precondition can be any, and the postconditions are weakened.             *)
(* ------------------------------------------------------------------------- *)

let ENSURES_ANY_EVENTS = prove
 (`!(P:x86state->bool) Q R.
        (!e. ensures x86 (\s. P s /\ read events s = e) Q R)
        ==> ensures x86 P Q R`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

let ENSURES_WEAKEN_PREPOST = MESON[ENSURES_PREPOSTCONDITION_THM]
 `ensures step P Q C
  ==> (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x)
      ==> ensures step P' Q' C`;;

(* ------------------------------------------------------------------------- *)
(* A call in a FULL proof. FULL_CALL_TAC mc execth name ilist vars n         *)
(* simulates the call at step n, after the CALL, in the image mc, with the   *)
(* FULL theorem of the callee in assumption name, as given by                *)
(* ASSUME_CALLEE_SAFETY_TAILED_TAC, instantiated with the events and ilist.  *)
(* The events before the call must be a function of the variables vars, the  *)
(* events of callees and the functions of the events template of the caller  *)
(* (f_ev_...), which FULL_EXISTS_E2_TAC checks as it proves the precondition *)
(* of the callee on the events, as EXISTS_E2_TAC does without the template.  *)
(* ------------------------------------------------------------------------- *)

let FULL_CALL_TAC mc execth name ilist vars n =
  REMOVE_THEN name (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (mc,execth,0x0,mc,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [FULL_EXISTS_E2_TAC (ref vars); LABEL_TAC name th]);;

(* ------------------------------------------------------------------------- *)
(* The parts of a FULL loop proof with ENSURES_EVENTS_WHILE_UP2_TAC, for the *)
(* loops of utils/mldsa_native.ml. FULL_INIT_TAC starts the simulation of a  *)
(* subgoal. VEC4_FULL_FINAL_TAC lanes tac ends a vectorized loop body, after *)
(* VEC4_LOOP_BODY_TAC and the steps of the loop test, as VEC4_LOOP_FINAL_TAC *)
(* does, with tac after the rewriting with the lane lemmas, and also proves  *)
(* the PC after the branch and the events of the iteration. FULL_FINAL_TAC   *)
(* ths does the same for a loop body whose outputs follow from the           *)
(* assumptions by rewriting with ths and WORD_RULE, as at the end of the     *)
(* scalar loops of the correctness proofs. FULL_EXIT_TAC execth n simulates  *)
(* the n instructions from the exit of a loop to the return, where the       *)
(* invariant gives the postcondition.                                        *)
(* ------------------------------------------------------------------------- *)

let FULL_EXIT_TAC execth n =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  X86_STEPS_TAC execth (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM(MATCH_ACCEPT_TAC o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The events of a loop whose iterations take one of several paths: the      *)
(* template is ENUMERATEL n (\i. if c i then f_ev_a .. i else f_ev_b .. i),  *)
(* with a meta-variable for each path, and each path of the proof of the     *)
(* body, with the case assumption c i or ~c i, picks its own (rewriting with *)
(* the case assumptions only), before discharging the safety property; the   *)
(* instantiated meta-variables are beta-reduced in the goal and in the       *)
(* assumptions, and negated comparisons put in one form, so that the events  *)
(* so far match the invariant syntactically.                                 *)
(* ------------------------------------------------------------------------- *)

(*** The return after such a loop, as FULL_EXIT_TAC ***)

let FULL_PATHS_EXIT_TAC execth n =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  X86_STEPS_TAC execth (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM(MATCH_ACCEPT_TAC o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN NO_TAC) THEN
  PATH_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The correctness and safety theorems from a FULL theorem. The goal of      *)
(* CORRECT_OF_FULL_TAC fullth is |- !args. H ==> ensures x86 P Q C, where P  *)
(* and Q are the precondition and the correctness part of the postcondition  *)
(* of fullth, with its quantified variables named as in fullth, in any       *)
(* order. The goal of SAFE_OF_FULL_TAC fullth is fullth with the data        *)
(* removed: its variables are e and some of the others, and the variables of *)
(* fullth that it does not have are the contents of memory, each fixed by a  *)
(* conjunct of P of the form !i. ... ==> read l s = x i or read l s = x,     *)
(* and its postcondition is that of fullth without Q.                        *)
(* ------------------------------------------------------------------------- *)

let CORRECT_OF_FULL_TAC fullth =
  let fv,fbody = dest_exists(concl fullth) in
  let ev,fvs = match fst(strip_forall fbody) with
                 ev::fvs -> ev,fvs
               | [] -> failwith "CORRECT_OF_FULL_TAC" in
  X_CHOOSE_THEN fv (fun th ->
    W(fun (asl,w) ->
      let vs = fst(strip_forall w) in
      let arg v =
        try find (fun u -> name_of u = name_of v) vs
        with Failure _ -> failwith("CORRECT_OF_FULL_TAC: "^name_of v) in
      MAP_EVERY X_GEN_TAC vs THEN DISCH_TAC THEN
      MATCH_MP_TAC ENSURES_ANY_EVENTS THEN X_GEN_TAC ev THEN
      MP_TAC(SPECL (ev::map arg fvs) th) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_PREPOST) THEN
      SIMP_TAC[])) fullth;;

let SAFE_OF_FULL_TAC fullth =
  let fv,fbody = dest_exists(concl fullth) in
  let s0 = `s0:x86state` in
  let witness ghost pre =
    let sv,body = dest_abs pre in
    let c = find (fun c -> free_in ghost c) (conjuncts body) in
    if is_forall c then
      let iv,b = dest_forall c in
      let l = lhs(snd(dest_imp b)) in
      mk_abs(iv,vsubst [s0,sv] l)
    else vsubst [s0,sv] (lhs c) in
  X_CHOOSE_THEN fv (fun th ->
    EXISTS_TAC fv THEN
    W(fun (asl,w) ->
      let vs = fst(strip_forall w) in
      let fvs = fst(strip_forall fbody) in
      let ghosts = filter (fun v ->
        not(exists (fun u -> name_of u = name_of v) vs)) fvs in
      let arg v =
        try find (fun u -> name_of u = name_of v) vs with Failure _ -> v in
      let sth = SPECL (map arg fvs) th in
      let ens = if is_imp(concl sth) then rand(concl sth) else concl sth in
      let pre = rand(rator(rator ens)) in
      let ws = map (fun g -> witness g pre, g) ghosts in
      MAP_EVERY X_GEN_TAC vs THEN DISCH_TAC THEN
      REWRITE_TAC[ensures] THEN X_GEN_TAC s0 THEN DISCH_TAC THEN
      MP_TAC(INST ws sth) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC s0) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC EVENTUALLY_MONO_AT THEN SIMP_TAC[])) fullth;;
