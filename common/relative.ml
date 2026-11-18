(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Proofs relative to the contracts of their callees.                        *)
(*                                                                           *)
(* The proofs of a build of mlkem-native or mldsa-native are split into two  *)
(* files per function f: f_spec.ml states the theorems (and has the          *)
(* definitions and tactics that the statements and proofs use) and           *)
(* f_proof.ml proves them. A spec file loads only the spec files of its      *)
(* callees, and states each theorem T with                                   *)
(*                                                                           *)
(*      let T_STMT = `...`;;                                                 *)
(*      let T = assume_spec T_STMT;;                                         *)
(*                                                                           *)
(* so T is the theorem T_STMT |- T_STMT. The proof file loads f_spec.ml and  *)
(* proves T_STMT with the tactic of T. The proofs of f                       *)
(* therefore run once, relative to the contracts of the callees: the result  *)
(* is A |- T_STMT, where A lists the statements of the callees (and of the   *)
(* lemmas of f_spec.ml) that the proof used.                                 *)
(*                                                                           *)
(* This file rebinds prove so that it accepts such a result when each        *)
(* assumption is (an instance of) a statement given to assume_spec, and      *)
(* behaves as HOL Light's prove otherwise. It also records every theorem it  *)
(* proves whose conclusion is such a statement. The link file of a build     *)
(* loads all proof files in one session, after which relative_close turns a  *)
(* theorem with assumptions into one without, by discharging each            *)
(* assumption with the recorded theorem for it, closed in the same way, and  *)
(* fails if some assumption has no proof.                                    *)
(*                                                                           *)
(* The file does not depend on the instruction set: arm/proofs/mlkem_native/ *)
(* relative.ml and x86/proofs/mlkem_native/relative.ml load it after the     *)
(* base.ml of their instruction set. Load it before any other file that uses *)
(* prove: code compiled before it calls HOL Light's prove.                   *)
(* ========================================================================= *)

needs "common/par.ml";;

(* ------------------------------------------------------------------------- *)
(* The stated contracts: the statement, the theorems proved for it, in the   *)
(* order they were proved, and the theorem without assumptions once          *)
(* relative_close has closed it. A contract can be proved more than once,    *)
(* and a proof can be circular: if the code of two functions is the same,    *)
(* the proof of one can be ACCEPT_TAC of the other's contract, which is the  *)
(* same statement. In a link file that runs the proof files one after the    *)
(* other, the real proof comes first; when they run at the same time (see    *)
(* common/par.ml) it may not, so relative_close tries them in turn. The      *)
(* list is changed under par_locked.                                         *)
(* ------------------------------------------------------------------------- *)

let relative_contracts =
  ref ([]:(term * thm list ref * thm option ref) list);;

let relative_find_contract tm =
  try Some(find (fun (s,_,_) -> aconv s tm) (!relative_contracts))
  with Failure _ ->
  try Some(find (fun (s,_,_) -> can (term_match [] s) tm)
                (!relative_contracts))
  with Failure _ -> None;;

(* ------------------------------------------------------------------------- *)
(* A statement with free variables, e.g. `x + 0 = x`, is recorded as the     *)
(* contract with them quantified, `!x. x + 0 = x`, and assume_spec gives     *)
(* the theorem !x. x + 0 = x |- x + 0 = x. The free variables of the         *)
(* conclusion are then not free in the assumption, so rules such as          *)
(* MATCH_MP and REWRITE_CONV can instantiate them, as they can in the        *)
(* proved theorem |- x + 0 = x. They would treat them as constants           *)
(* otherwise.                                                                *)
(* ------------------------------------------------------------------------- *)

let relative_contract_of tm = list_mk_forall(frees tm,tm);;

let assume_spec tm =
  if type_of tm <> bool_ty then failwith "assume_spec: not a proposition" else
  let vs = frees tm in
  let ctm = list_mk_forall(vs,tm) in
  (if type_vars_in_term tm <> [] then
    (Format.print_string "relative: warning: contract with type variables: ";
     print_qterm tm; Format.print_newline()));
  par_locked (fun () ->
    if not (exists (fun (s,_,_) -> aconv s ctm) (!relative_contracts)) then
      relative_contracts := (ctm,ref [],ref None)::(!relative_contracts));
  SPECL vs (ASSUME ctm);;

(* ------------------------------------------------------------------------- *)
(* assuming_proofs f evaluates f () with every prove(t,tac) replaced by      *)
(* assume_spec t. It is for the few phrases of the spec files that prove     *)
(* theorems through functions, e.g. one lemma per layer of the NTT, so that  *)
(* the spec file states them without proving them; the proof file has the    *)
(* same phrase without assuming_proofs. The flag is per domain, and a        *)
(* computation that a proof spawns starts with its value (see                *)
(* common/par.ml), so that it does not affect proofs on other domains.       *)
(* ------------------------------------------------------------------------- *)

let relative_assuming = par_local_ref (fun () -> false);;

let assuming_proofs f =
  let flag = relative_assuming () in
  let old = !flag in
  flag := true;
  try let r = f () in flag := old; r
  with e -> flag := old; raise e;;

(* ------------------------------------------------------------------------- *)
(* prove: as HOL Light's prove, except that the result may have assumptions  *)
(* that are stated contracts.                                                *)
(* ------------------------------------------------------------------------- *)

let prove(t,tac) =
  if !(relative_assuming ()) then assume_spec t else
  let th = TAC_PROOF(([],t),tac) in
  let asl,t' = dest_thm th in
  let bad = filter (fun a -> relative_find_contract a = None) asl in
  if bad <> [] then
    (Format.print_string "prove: assumptions that are not contracts:";
     Format.print_newline();
     do_list (fun a -> print_qterm a; Format.print_newline()) bad;
     failwith "prove: additional assumptions in result")
  else
  let th = if t' = t then th else
           try EQ_MP (ALPHA t' t) th
           with Failure _ ->
             failwith "prove: justification generated wrong theorem" in
  let ct = relative_contract_of t in
  (match relative_find_contract ct with
     Some(s,p,_) when aconv s ct ->
       let gth = GENL (frees t) th in par_locked (fun () -> p := !p @ [gth])
   | _ -> ());
  th;;

par_set_prove prove;;

(* ------------------------------------------------------------------------- *)
(* new_specification: as HOL Light's, but it also accepts a theorem with     *)
(* assumptions, which it keeps in the result. The constants are defined as   *)
(* by HOL Light's new_specification (the same definitions, which depend only *)
(* on the conclusion of the theorem), so when a spec file defines them from  *)
(* an assumed theorem, they are the constants that the proof file defines    *)
(* from the proved theorem. The specification is recorded in                 *)
(* the_specifications, so that the same phrase in the proof file, given the  *)
(* proved theorem, is a benign respecification that returns the result of    *)
(* the spec file.                                                            *)
(* ------------------------------------------------------------------------- *)

let new_specification =
  let hol_new_specification = new_specification in
  let code c = mk_small_numeral (Char.code (c.[0])) in
  let mk_code name =
      end_itlist (curry mk_pair) (map code (explode name)) in
  let check_distinct l =
    try itlist (fun t res -> if mem t res then fail() else t::res) l []; true
    with Failure _ -> false in
  let specify name th =
    let ntm = mk_code name in
    let gv = genvar(type_of ntm) in
    let th0 = CONV_RULE(REWR_CONV SKOLEM_THM) (GEN gv th) in
    let th1 = CONV_RULE(RATOR_CONV (REWR_CONV EXISTS_THM) THENC
                        BETA_CONV) th0 in
    let l,r = dest_comb(concl th1) in
    let rn = mk_comb(r,ntm) in
    let ty = type_of rn in
    let th2 = new_definition(mk_eq(mk_var(name,ty),rn)) in
    GEN_REWRITE_RULE ONCE_DEPTH_CONV [GSYM th2]
     (SPEC ntm (CONV_RULE BETA_CONV th1)) in
  let rec specifies names th =
    match names with
      [] -> th
    | name::onames -> let th' = specify name th in
                      specifies onames th' in
  fun names th ->
    let asl,c = dest_thm th in
    if asl = [] then hol_new_specification names th else
    if not (frees c = []) then
      failwith "new_specification: Free variables in predicate" else
    let avs = fst(strip_exists c) in
    if length names = 0 || length names > length avs then
      failwith "new_specification: Unsuitable number of constant names" else
    if not (check_distinct names) then
      failwith "new_specification: Constant names not distinct"
    else
      (* Looked up and made under one lock, so that proofs on several       *)
      (* domains (see common/par.ml) make each specification once.         *)
      par_locked (fun () ->
        try let sth = snd(find (fun ((names',th'),sth') ->
                                 names' = names && aconv (concl th') (concl th))
                               (!the_specifications)) in
            warn true ("Benign respecification"); sth
        with Failure _ ->
          let sth = specifies names th in
          the_specifications := ((names,th),sth)::(!the_specifications);
          sth);;

(* ------------------------------------------------------------------------- *)
(* Closing a theorem: discharge each assumption with a recorded theorem for  *)
(* its contract (instantiated if the assumption is an instance), closed      *)
(* first in the same way: the first recorded theorem that can be closed.     *)
(* ------------------------------------------------------------------------- *)

let relative_close =
  let rec close_hyp visiting h =
    let s,p,c =
      match relative_find_contract h with
        Some x -> x
      | None ->
          failwith("relative_close: no contract for "^string_of_term h) in
    let cth =
      match !c with
        Some cth -> cth
      | None ->
          if !p = [] then
            failwith("relative_close: contract not proved: "^string_of_term s)
          else if exists (aconv s) visiting then
            failwith("relative_close: circular contract: "^string_of_term s)
          else
          let rec first pths =
            match pths with
              [pth] -> close (s::visiting) pth
            | pth::opths ->
                (try close (s::visiting) pth with Failure _ -> first opths)
            | [] -> failwith "relative_close" in
          let cth = first !p in
          (c := Some cth; cth) in
    let ith = INSTANTIATE (term_match [] (concl cth) h) cth in
    if concl ith = h then ith else EQ_MP (ALPHA (concl ith) h) ith
  and close visiting th =
    itlist (fun h th -> PROVE_HYP (close_hyp visiting h) th) (hyp th) th in
  fun th ->
    let cth = close [] th in
    if hyp cth <> [] then failwith "relative_close: assumptions left"
    else cth;;

(* ------------------------------------------------------------------------- *)
(* The check at the end of a link file: every stated contract has been       *)
(* proved, and every proved one can be closed. It prints how many contracts  *)
(* were stated and fails, after listing them, if some were not proved.       *)
(* ------------------------------------------------------------------------- *)

let relative_report () =
  let l = rev(!relative_contracts) in
  let unproved = filter (fun (_,p,_) -> !p = []) l in
  do_list (fun (s,p,_) ->
    match !p with
      th::_ -> ignore(relative_close th)
    | [] -> ()) l;
  Format.print_string(Printf.sprintf
    "relative: %d contracts stated, %d proved and closed"
    (length l) (length l - length unproved));
  Format.print_newline();
  if unproved <> [] then
   (do_list (fun (s,_,_) ->
      Format.print_string "relative: not proved: "; print_qterm s;
      Format.print_newline()) unproved;
    failwith "relative_report: contracts not proved");;
