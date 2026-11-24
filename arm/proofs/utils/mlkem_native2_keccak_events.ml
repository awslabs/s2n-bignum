(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tactics for the events in the loop proofs of the Keccak permutations, as  *)
(* in arm/proofs/sha3_keccak4_f1600_alt2.ml (which defines them for its own  *)
(* proofs), for the proof of the contract of sha3_keccak_f1600 that has the  *)
(* events together with the result: the events of each part are given by a   *)
(* metavariable, instantiated by unification after the simulation of the     *)
(* part.                                                                     *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

(*** Rewrite the condition of the branch to the PC in state st as cnd,   ***)
(*** proving the equivalence with tac, so that the PC and the event of   ***)
(*** the branch are in terms of the loop test                            ***)

let BRANCH_COND_TAC (st:term) (cnd:term) (tac:tactic) : tactic =
  W(fun (asl,w) ->
    let pcth = snd(find (fun (_,th) ->
      let c = concl th in
      is_eq c && lhand c = mk_comb(`read PC`,st)) asl) in
    let c = lhand(rator(rand(concl pcth))) in
    SUBGOAL_THEN (mk_eq(c,cnd))
     (fun eth -> RULE_ASSUM_TAC(PURE_REWRITE_RULE[eth])) THENL
     [tac; ALL_TAC]);;

(*** The events of the block before the loop, with ENUMERATEL (1 - 1) ***)

let KECCAK_EVENTS_INIT_TAC =
  REWRITE_TAC[SUB_REFL; ENUMERATEL; APPEND] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The events of the loop body for i, the iteration j = i - 1, with   ***)
(*** the new events written in terms of j for the unification          ***)

let KECCAK_EVENTS_BODY_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `i = j + 1` SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`i - 1 = j`; `1 <= i`] THEN ARITH_TAC;
      FULL_UNIFY_F_EVENTS_TAC];
    DISCHARGE_MEMACCESS_INBOUNDS_TAC];;
