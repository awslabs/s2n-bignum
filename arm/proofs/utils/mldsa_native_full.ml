(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the combined correctness, constant-time and memory-safety       *)
(* ("FULL") theorems of the mldsa-native proofs.                             *)
(*                                                                           *)
(* The signing code branches on values its callees compute (the norm checks, *)
(* the hint count, the attempt counter), and the samplers loop until enough  *)
(* coefficients have been accepted. To show that the events of such a caller *)
(* depend only on what the code declassifies, its proof needs the results    *)
(* and the events of each call at the same point of the execution. Separate  *)
(* correctness and safety theorems are two ensures statements whose          *)
(* postconditions might hold at different points, so they cannot be combined *)
(* afterwards (see utils/mlkem_native_libc_full.ml). Each function therefore *)
(* gets one FULL theorem, stating both, of the form                          *)
(*                                                                           *)
(*      ?f_events. !e args.                                                  *)
(*         H ==> ensures arm (\s. P s /\ read events s = e)                  *)
(*                           (\s. Q s /\ ?e2. read events s = APPEND e2 e /\ *)
(*                                            e2 = f_events <public args> /\ *)
(*                                            memaccess_inbounds e2 R W)     *)
(*                           C                                               *)
(*                                                                           *)
(* and its correctness theorem (|- !args. H ==> ensures arm P Q C) and its   *)
(* safety theorem (the FULL theorem without the data and without Q) follow   *)
(* from it, by CORRECT_OF_FULL_TAC and SAFE_OF_FULL_TAC.                     *)
(* ========================================================================= *)

(* The part that depends on AArch64; the rest is in                          *)
(* common/fips204/properties/mldsa_native_full.ml.                           *)

needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/fips204/properties/mldsa_native_full.ml";;

let FULL_CALL_TAC mc execth name ilist vars n =
  REMOVE_THEN name (fun th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true (mc,execth,0x0,mc,th)
      (`e:(uarch_event)list`::ilist) n THENL
     [FULL_EXISTS_E2_TAC (ref vars); LABEL_TAC name th]);;

let FULL_EXIT_TAC execth n =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  ARM_STEPS_TAC execth (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM(MATCH_ACCEPT_TAC o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The return after such a loop, as FULL_EXIT_TAC ***)

let FULL_PATHS_EXIT_TAC execth n =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  ARM_STEPS_TAC execth (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM(MATCH_ACCEPT_TAC o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN NO_TAC) THEN
  PATH_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* The correctness and safety theorems from a FULL theorem. The goal of      *)
(* CORRECT_OF_FULL_TAC fullth is |- !args. H ==> ensures arm P Q C, where P  *)
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
  let s0 = `s0:armstate` in
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
