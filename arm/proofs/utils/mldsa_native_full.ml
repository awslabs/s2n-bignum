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

needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;

(* ------------------------------------------------------------------------- *)
(* The test of a loop counter in a FULL proof, as                            *)
(* ENSURES_EVENTS_WHILE_UP2_TAC leaves it: the PC after the branch is a      *)
(* conditional on the flags, to be shown equal to                            *)
(* word (if i + 1 < n then pc1 else pc2). The code tests the                 *)
(* counter c * (i + 1) after the increment, either as the sum of c * i and   *)
(* the complement 2^64 - c * (n - 1) (LOOP_TEST_TAC), or as a pointer with   *)
(* the same base as the bound it is compared with (PTR_LOOP_TEST_TAC). Each  *)
(* rewrites such tests in the goal to equations of numbers, using the bounds *)
(* in the assumptions, and LOOP_COND_TAC then rewrites each equation in i to *)
(* ~(i + 1 < n).                                                             *)
(* ------------------------------------------------------------------------- *)

let VAL_WORD_ADD_COMPLEMENT_EQ_0 = prove
 (`!m k. m < 2 EXP 64 /\ k < 2 EXP 64 /\ ~(k = 0)
         ==> (val(word_add (word m) (word k):int64) = 0 <=> m + k = 2 EXP 64)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; MOD_LT] THEN
  MP_TAC(SPECL [`m + k:num`; `2 EXP 64`] DIVISION) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  UNDISCH_TAC `m < 2 EXP 64` THEN UNDISCH_TAC `k < 2 EXP 64` THEN
  UNDISCH_TAC `~(k = 0)` THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`(m + k) DIV 18446744073709551616`,`q:num`) THEN
  SPEC_TAC(`(m + k) MOD 18446744073709551616`,`r:num`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `q = 0 \/ q = 1` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let VAL_WORD_SUB_ADD_EQ_0 = prove
 (`!a:int64 m n.
        m < 2 EXP 64 /\ n < 2 EXP 64
        ==> (val(word_sub (word_add a (word m)) (word_add a (word n))) = 0 <=>
             m = n)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; WORD_ADD_LCANCEL_EQ] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN ASM_SIMP_TAC[VAL_WORD; DIMINDEX_64; MOD_LT]);;

let LOOP_TEST_TAC =
  let pat = `val(word_add (word m) (word k):int64) = 0`
  and lth = SPECL [`m:num`; `k:num`] VAL_WORD_ADD_COMPLEMENT_EQ_0 in
  W(fun (asl,w) ->
    let tms = setify(find_terms (fun t -> can (term_match [] pat) t &&
                                 is_numeral(rand(rand(rand(lhand t))))) w) in
    MAP_EVERY (fun t ->
      let th = INSTANTIATE (term_match [] pat t) lth in
      MP_TAC th THEN ANTS_TAC THENL
       [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV]) tms);;

let PTR_LOOP_TEST_TAC =
  let pat = `val(word_sub (x:int64) y) = 0`
  and lth = SPECL [`a:int64`; `m:num`; `n:num`] VAL_WORD_SUB_ADD_EQ_0
  and pat' = `val(word_sub (word_add a (word m)) (word_add a (word n)):int64)
              = 0` in
  W(fun (asl,w) ->
    let tms = setify(find_terms (can (term_match [] pat)) w) in
    MAP_EVERY (fun t ->
      let th1 = REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] t in
      let t' = rand(concl th1) in
      try let th2 = INSTANTIATE (term_match [] pat' t') lth in
          MP_TAC th2 THEN ANTS_TAC THENL
           [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
            DISCH_THEN(fun th -> REWRITE_TAC[TRANS th1 th])]
      with Failure _ -> ALL_TAC) tms);;

let LOOP_COND_TAC =
  let lt = `i + 1 < n` in
  W(fun (asl,w) ->
    let lts = setify(find_terms (can (term_match [] lt)) w) in
    match lts with
      [l] ->
        let iv = lhand(lhand l) in
        let eqs = setify(find_terms (fun t -> is_eq t &&
                    type_of(lhs t) = `:num` && free_in iv t) w) in
        MAP_EVERY (fun e ->
          TRY(SUBGOAL_THEN (mk_eq(e,mk_neg l)) SUBST1_TAC THENL
               [SIMPLE_ARITH_TAC; ALL_TAC])) eqs THEN
        REWRITE_TAC[]
    | _ -> ALL_TAC);;

(* ------------------------------------------------------------------------- *)
(* A call in a FULL proof. FULL_CALL_TAC mc execth name ilist vars n         *)
(* simulates the call at step n, after the BL, in the image mc, with the     *)
(* FULL theorem of the callee in assumption name, as given by                *)
(* ASSUME_CALLEE_SAFETY_TAILED_TAC, instantiated with the events and ilist.  *)
(* The events before the call must be a function of the variables vars, the  *)
(* events of callees and the functions of the events template of the caller  *)
(* (f_ev_...), which FULL_EXISTS_E2_TAC checks as it proves the precondition *)
(* of the callee on the events, as EXISTS_E2_TAC does without the template.  *)
(* ------------------------------------------------------------------------- *)

let FULL_EXISTS_E2_TAC allowed_vars_e =
  let pfx = ref ["f_events_callee"; "f_ev_"] in
  (MATCH_MP_TAC NIL_IMPLIES_APPEND_EQ THEN CONJ_TAC THENL
    [REFL_TAC; SAFE_UNIFY_REFL_TAC allowed_vars_e pfx]) ORELSE
  (CONV_TAC (TRY_CONV (LAND_CONV CONS_TO_APPEND_CONV)) THEN
   TRY (GEN_REWRITE_TAC LAND_CONV [APPEND_ASSOC]) THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   SAFE_UNIFY_REFL_TAC allowed_vars_e pfx) ORELSE
  (CONV_TAC (TRY_CONV (LAND_CONV (ONCE_DEPTH_CONV CONS_TO_APPEND_CONV))) THEN
   CONV_TAC (TRY_CONV (LAND_CONV (ONCE_DEPTH_CONV CONS_TO_APPEND_CONV))) THEN
   GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV) [APPEND_ASSOC] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   SAFE_UNIFY_REFL_TAC allowed_vars_e pfx);;

let FULL_CALL_TAC mc execth name ilist vars n =
  REMOVE_THEN name (fun th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true (mc,execth,0x0,mc,th)
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

let FULL_INIT_TAC =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC;;

let VEC4_FULL_FINAL_TAC lanes tac =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC[CHUNK4_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      REWRITE_TAC[CHUNK4_ADDR; ADD_CLAUSES] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC lanes THEN tac THEN
      NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let FULL_FINAL_TAC ths =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC ths THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let FULL_EXIT_TAC execth n =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN
  ARM_STEPS_TAC execth (1--n) THEN
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

let PATH_DISCHARGE_TAC =
  let beta_all =
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) in
  let select_tac =
    W(fun (asl,w) ->
      let conds = map (fun t -> rand(rator(rator t)))
                      (find_terms is_cond w) in
      let ths = mapfilter (fun (_,th) ->
        let c = concl th in
        if mem c conds then EQT_INTRO th
        else if is_neg c && mem (rand c) conds then EQF_INTRO th
        else failwith "") asl in
      REWRITE_TAC ths) in
  REWRITE_TAC[ENUMERATEL_ADD1] THEN beta_all THEN select_tac THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    if is_conj w then CONJ_TAC THENL [FULL_UNIFY_F_EVENTS_TAC; ALL_TAC]
    else ALL_TAC) THEN
  beta_all THEN
  REWRITE_TAC[NOT_LT] THEN RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

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

let EVENTUALLY_MONO_AT = prove
 (`!(step:A->A->bool) P Q s0.
        (!s. P s ==> Q s) ==> eventually step P s0 ==> eventually step Q s0`,
  MESON_TAC[EVENTUALLY_MONO]);;

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
