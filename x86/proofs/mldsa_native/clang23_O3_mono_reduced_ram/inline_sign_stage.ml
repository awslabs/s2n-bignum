(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tactics for the stage lemmas of the clang 23 signature_internal proofs    *)
(* (signature_internal_44_stages.ml): the stack frame of an attempt at rsp0  *)
(* (RSP after the prologue, aligned to 32), with the callees below rsp0. The *)
(* memory-safety checks compare regions at offsets of rsp0, some below it:   *)
(* SI_FB_NORM_TAC d states every address from the lowest one, fb_si =      *)
(* rsp0 - d, so that the containment arithmetic has no offsets that wrap,    *)
(* as VM_RSP0_NORM_TAC of verify_internal_tools.ml does for verify.         *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/verify_internal_tools.ml";;
needs "x86/proofs/utils/mldsa_native_signing.ml";;

(*** rsp0 as fb_si + d in the goal and the assumptions ***)

let SI_FB_NORM_TAC d =
  let sub = WORD_RULE `word_sub (word_sub (x:int64) (word a)) (word b) =
                       word_sub x (word (a + b))` in
  let norm = REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) in
  let dt = mk_small_numeral d in
  RULE_ASSUM_TAC(CONV_RULE(REWRITE_CONV[sub] THENC DEPTH_CONV NUM_ADD_CONV)) THEN
  REWRITE_TAC[sub] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  ABBREV_TAC (mk_eq(`fb_si:int64`,mk_comb(mk_comb(`word_sub:int64->int64->int64`,`rsp0:int64`),
                                          mk_comb(`word:num->int64`,dt)))) THEN
  SUBGOAL_THEN (mk_eq(`rsp0:int64`,mk_comb(mk_comb(`word_add:int64->int64->int64`,`fb_si:int64`),
                                          mk_comb(`word:num->int64`,dt)))) SUBST_ALL_TAC THENL
   [EXPAND_TAC "fb_si" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE norm) THEN CONV_TAC norm;;
(*** The events at the end of a segment (VM_DISCHARGE_TAC with SI_FB_NORM_TAC d) ***)

let SI_DISCHARGE_TAC d =
  let beta_all =
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) in
  let select_tac =
    W(fun (asl,w) ->
      let conds = map (fun t -> rand(rator(rator t))) (find_terms is_cond w) in
      let ths = mapfilter (fun (_,th) ->
        let c = concl th in
        if mem c conds then EQT_INTRO th
        else if is_neg c && mem (rand c) conds then EQF_INTRO th
        else failwith "") asl in
      REWRITE_TAC ths) in
  let is_vdef th = let c = concl th in
    is_eq c && is_var(lhs c) && type_of(lhs c) = `:(uarch_event)list` in
  let is_meminb v th = let c = concl th in
    (match strip_comb c with
       Const("memaccess_inbounds",_),(e::_) -> e = v
     | _ -> false) in
  let split_tac =
    W(fun (asl,w) ->
      let defs = filter is_vdef (map snd asl) in
      MAP_EVERY (fun dth ->
        let v = lhs(concl dth) in
        MAP_EVERY (fun (_,mth) ->
          if is_meminb v mth then
            STRIP_ASSUME_TAC(REWRITE_RULE[MEMACCESS_INBOUNDS_APPEND] (REWRITE_RULE[dth] mth))
          else ALL_TAC) asl) defs) in
  REWRITE_TAC[ENUMERATEL_ADD1] THEN beta_all THEN select_tac THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    if is_conj w then
      CONJ_TAC THENL
       [(REWRITE_TAC[APPEND_ASSOC] THEN NO_TAC) ORELSE FULL_UNIFY_F_EVENTS_TAC;
        ALL_TAC]
    else ALL_TAC) THEN
  beta_all THEN
  REWRITE_TAC[NOT_LT] THEN RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  SI_FB_NORM_TAC d THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  split_tac THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   BYTE_IDX_DISCHARGE_TAC DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

(*** aligned 16 (rsp0 + n) for the offsets n, from aligned 32 rsp0 ***)

let SI_ALIGNED16_TAC offs =
  MAP_EVERY (fun off ->
    SUBGOAL_THEN (subst [mk_small_numeral off,`n:num`]
                    `aligned 16 (word_add (rsp0:int64) (word n))`) ASSUME_TAC THENL
     [MATCH_MP_TAC ALIGNED_WORD_ADD THEN CONJ_TAC THENL
       [MATCH_MP_TAC(MP (ISPECL [`16`;`32`;`rsp0:int64`] ALIGNED_WORD_WEAKEN)
                        (EQT_ELIM(DIVIDES_CONV `16 divides 32`))) THEN
        FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
        CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[]];
      ALL_TAC]) offs;;

(*** ASSUME_CALLEE_SAFETY_TAILED_TAC for a stage lemma with many variables: ***)
(*** the same assumption, with the quantifiers rotated by a derived rule   ***)
(*** rather than by MESON, which gives up ("Too deep") beyond about ten    ***)
(*** variables.                                                            ***)

let SI_ASSUME_CALLEE_TAILED_TAC =
  let append_lemma = MESON[SAFETY_APPEND_EXISTS]
    `(forall (e:((A)address_uarch_event)list). P e) <=>
      (forall e_tail e. P (APPEND e_tail e))` in
  fun (safety_th:thm) (name:string) ->
    let th1 = ONCE_REWRITE_RULE[append_lemma] safety_th in
    let f,body = dest_exists (concl th1) in
    let args,_ = strip_forall body in
    let rot = tl args @ [hd args] in
    let th2 = GENL rot (SPECL args (ASSUME body)) in
    let th3 = EXISTS (mk_exists(f,concl th2),f) th2 in
    ASSUME_CALLEE_SAFETY_TAC (CHOOSE (f,th1) th3) name;;
