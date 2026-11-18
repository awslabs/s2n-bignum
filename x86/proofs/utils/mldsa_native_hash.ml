(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the proofs of mld_H44, mld_H65 and mld_H87, which absorb up to *)
(* three inputs into one SHAKE256 context: absorbing two messages one after  *)
(* the other (mld_keccak_absorb of common/mldsa_native_fips202.ml, from the  *)
(* position the first one leaves) is absorbing their concatenation.          *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_absorb.ml";;
needs "x86/proofs/utils/keccak_fips202.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "common/fips204/properties/mldsa_native_hash.ml";;

(* ------------------------------------------------------------------------- *)
(* Tactics for the proofs of mld_H. MLD_H_CASES_TAC splits on whether in2len *)
(* and in3len are zero, substitutes the zero lengths, and selects the branch *)
(* of the events template for each case. MLD_H_BOUND_TAC a adds the bound    *)
(* x < 2 EXP (8 * n) for the bytes x of length n read at a, and              *)
(* MLD_H_VAL_LEN_TAC k a l adds val(word l) = l for the length l of the      *)
(* buffer at a, which does not overlap the k bytes at stackpointer.          *)
(* MLD_H_DISCHARGE_TAC is DISCHARGE_SAFETY_PROPERTY_TAC at the end of the    *)
(* part after a join whose events before it are a case of the template:      *)
(* memaccess_inbounds is split over each APPEND of the events, so that the   *)
(* events before the join, a conditional, are a conjunct of their own, to be *)
(* discharged by the assumption on them.                                     *)
(* ------------------------------------------------------------------------- *)

let MLD_H_READ_BYTES_BOUND = prove
 (`!a n (s:x86state) x.
        read (memory :> bytes(a,n)) s = x ==> x < 2 EXP (8 * n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]);;

let MLD_H_BOUND_TAC a =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if can (term_match [] `read (memory :> bytes(a,n)) s = x:num`) c &&
       fst(dest_pair(rand(rand(rand(rator(lhand c)))))) = a
    then ASSUME_TAC(MATCH_MP MLD_H_READ_BYTES_BOUND th) else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* MLD_H_BRANCH_TAC decides the condition c of the RIP after a conditional   *)
(* jump on a length, read RIP s = if c then a else b, which the simulation   *)
(* leaves as a test of the 64-bit word of the length against 0 (by TEST or   *)
(* CMP), from the value of the word and whether the length is 0, and         *)
(* rewrites the assumptions (the RIP and the events) with it; it does        *)
(* nothing if the simulation has decided the jump.                           *)
(* ------------------------------------------------------------------------- *)

let MLD_H_BRANCH_TAC =
  let is_rip_cond th =
    match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("RIP",_)),_)),r)
        -> is_cond r
    | _ -> false in
  let decide =
    REWRITE_TAC[WORD_SUB_0; WORD_AND_REFL] THEN ASM_REWRITE_TAC[] THEN
    NO_TAC in
  W(fun (asl,w) ->
    if not(exists (fun (_,th) -> is_rip_cond th) asl) then ALL_TAC else
    FIRST_X_ASSUM(fun th ->
      if not(is_rip_cond th) then NO_TAC else
      let c = rand(rator(rator(rand(concl th)))) in
      let use cth =
        ASSUME_TAC th THEN RULE_ASSUM_TAC(REWRITE_RULE[cth]) in
      (SUBGOAL_THEN c use THENL [decide; ALL_TAC]) ORELSE
      (SUBGOAL_THEN (mk_neg c) (use o EQF_INTRO) THENL [decide; ALL_TAC])));;
