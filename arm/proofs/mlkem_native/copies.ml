(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tactics for code in which the compiler has inlined several copies of the  *)
(* same loops one after the other, as clang does in                          *)
(* mlkem_keccakf1600x4_extract_bytes and mlkem_keccakf1600x4_xor_bytes, one *)
(* copy per Keccak state. The proof of the combined theorem with the events  *)
(* splits the code at the start of each copy with                            *)
(* ENSURES_EVENTS_SEQUENCE_TAC, so the goals for a copy after the first also *)
(* hold the events of the earlier copies: in the precondition, which becomes *)
(* an assumption e2 = ... after ENSURES_INIT_TAC, and in the postcondition.  *)
(* DISCHARGE_SAFETY_PROPERTY_TAC needs the two to be the same terms, so the   *)
(* proof must not rewrite one of them only. The tactics here rewrite the     *)
(* events of the postcondition alone where that is meant, and otherwise only *)
(* the state: the conjuncts of the goal other than the events, and the       *)
(* assumptions about components other than the events.                       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/consttime.ml";;

(*** In the postcondition only, e2 = APPEND (APPEND x y) z becomes        ***)
(*** e2 = APPEND x (APPEND y z), to split off the events of a loop or a   ***)
(*** sequence of the current copy from those of the earlier copies.       ***)

let COPIES_POST_REASSOC_TAC =
  let conv t =
    match t with
      Comb(Comb(Const("=",_),Var("e2",_)),_) ->
        RAND_CONV(REWR_CONV(GSYM APPEND_ASSOC)) t
    | _ -> failwith "COPIES_POST_REASSOC_TAC" in
  CONV_TAC(RATOR_CONV(RAND_CONV(ONCE_DEPTH_CONV conv)));;

(*** Rewriting only the assumptions about the state, read c s = x with c ***)
(*** other than events                                                   ***)

let copies_is_state th =
  match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),_)),_) ->
      not(is_const c && name_of c = "events")
  | _ -> false;;

let COPIES_STATE_RULE_TAC (rule:thm->thm) =
  RULE_ASSUM_TAC(fun th -> if copies_is_state th then rule th else th);;

(*** The goal of the events, exists e2. ..., and the final state with tac ***)
(*** proving each of the other conjuncts                                 ***)

let COPIES_SAFETY_TAC (asl,w) =
  if is_exists w then DISCHARGE_SAFETY_PROPERTY_TAC (asl,w)
  else NO_TAC (asl,w);;

let COPIES_FINISH_TAC (tac:tactic) =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN FIRST [COPIES_SAFETY_TAC; ALL_TAC] THEN tac;;

(*** An address word_add (word_add a (word m)) (word n) as word_add a     ***)
(*** (word(m + n)), the form that the simulation gives for an address     ***)
(*** with an immediate offset                                             ***)

let WORD_ADD_ADD_WORD = prove
 (`!a:int64 m n. word_add (word_add a (word m)) (word n) =
                 word_add a (word(m + n))`,
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]);;

(*** Equations of two such addresses, with arithmetic on the offsets ***)

let COPIES_ADDR_EQ x y =
  prove(mk_eq(x,y),
        REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;
