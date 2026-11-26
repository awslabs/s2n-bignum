(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tactics and lemmas shared by the proofs of the inlined hint unpacking of  *)
(* verify_internal (inline_sign_hints44.ml for ML-DSA-44, inline_sign_hintsk *)
(* .ml for ML-DSA-65 and 87): the run of the hints as inline_hset, the       *)
(* decision of a branch on a condition the facts imply, the cases of the     *)
(* first row (i <= 0), the conditions of the events template.                *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign_hints.ml";;
needs "arm/proofs/utils/mldsa_native_wrap.ml";;

let HR_HSET_EQ = prove
 (`!(b:num->byte) s w q.
     s < w
     ==> inline_hset (\q. if val(b s) = q then word 1 else word 0) b s w q =
         (if ?j. s <= j /\ j < w /\ val(b j) = q then word 1 else word 0):int32`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INLINE_HSET] THEN
  SUBGOAL_THEN
   `(?j. s <= j /\ j < w /\ val((b:num->byte) j) = q) <=>
    (?j. s < j /\ j < w /\ val(b j) = q) \/ val(b s) = q`
  SUBST1_TAC THENL [ASM_MESON_TAC[LE_LT]; ALL_TAC] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]));;

let HR_LOG (name:string) (tac:tactic) : tactic = tac;;

let HR_PC_TAC =
  W(fun (asl,w) ->
    let pcth = snd(find (fun (_,th) -> let c = concl th in
      is_eq c && (try rand(rator(lhand c)) = `PC` with _ -> false) &&
      can (find_term is_cond) (rhs c)) asl) in
    let cnd = rand(rator(rator(find_term is_cond (rhs(concl pcth))))) in
    let rw cth = RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read PC s = x:int64`) (concl th)
      then REWRITE_RULE[cth] th else th) in
    (SUBGOAL_THEN cnd rw THENL
      [FIRST_ASSUM ACCEPT_TAC ORELSE GLUE_ARITH_TAC; ALL_TAC]) ORELSE
    (SUBGOAL_THEN (mk_neg cnd) rw THENL
      [FIRST_ASSUM ACCEPT_TAC ORELSE GLUE_ARITH_TAC; ALL_TAC]));;

let HR_I0_TAC =
  TRY(FIRST_ASSUM(fun th -> if concl th = `i <= 0` then
        ASSUME_TAC(MP (ARITH_RULE `i <= 0 ==> i = 0`) th) else NO_TAC));;

let HR_DECIDE_TAC =
  FIRST [GLUE_ARITH_TAC;
         REWRITE_TAC[DE_MORGAN_THM] THEN DISJ1_TAC THEN GLUE_ARITH_TAC;
         REWRITE_TAC[DE_MORGAN_THM] THEN DISJ2_TAC THEN GLUE_ARITH_TAC;
         CONJ_TAC THEN GLUE_ARITH_TAC;
         ASM_REWRITE_TAC[] THEN NO_TAC];;

let HR_COND_TAC =
  W(fun (asl,w) ->
    let conds = setify(map (fun t -> rand(rator(rator t))) (find_terms is_cond w)) in
    let known c = exists (fun (_,th) -> concl th = c || concl th = mk_neg c) asl in
    MAP_EVERY (fun c -> if known c then ALL_TAC else
       (SUBGOAL_THEN c ASSUME_TAC THENL [HR_DECIDE_TAC; ALL_TAC]) ORELSE
       (SUBGOAL_THEN (mk_neg c) ASSUME_TAC THENL [HR_DECIDE_TAC; ALL_TAC]) ORELSE
       ALL_TAC) conds);;

let HR_ZX_SMALL = prove
 (`!n. n < 256 ==> word_zx (word_zx (word n:int64):int32):int64 = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_zx; VAL_WORD; DIMINDEX_32; DIMINDEX_64] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `n MOD 2 EXP 64 = n /\ n MOD 2 EXP 32 = n` (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC);;

let HR_EQ1 = prove
 (`!k w. k + 1 < 2 EXP 64 /\ w < 2 EXP 64
         ==> (val (word_sub (word_add (word k:int64) (word 1)) (word w)) = 0 <=>
              k + 1 = w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; GSYM WORD_ADD] THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN ASM_SIMP_TAC[MOD_LT]);;

let HR_X9X10_TAC n =
  let s = mk_var("s"^string_of_int n,`:armstate`) in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if is_eq c && (lhs c = mk_comb(`read X9`,s) || lhs c = mk_comb(`read X10`,s))
    then CONV_RULE(RAND_CONV(REWRITE_CONV[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THENC
                             ONCE_DEPTH_CONV(fun t -> if is_comb t && is_comb(rator t) && lhand t = `1` && rator(rator t) = `(+):num->num->num` then REWR_CONV ADD_SYM t else failwith "") )) th
    else th);;
