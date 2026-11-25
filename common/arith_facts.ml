(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The facts that linear arithmetic can use for a goal.                      *)
(*                                                                           *)
(* A proof that decides a condition by MAP_EVERY MP_TAC facts THEN ARITH_TAC *)
(* (or INT_ARITH_TAC) over all the facts of a symbolic execution pays for    *)
(* the facts that cannot help: ARITH_TAC splits the cases of every          *)
(* disequality ~(a = b), every disjunction and every iff among them, also of *)
(* those about terms the goal does not mention, and the iffs with atoms that *)
(* are not arithmetic (such as a model equation) double the cases.           *)
(*                                                                           *)
(*   arith_facts ths              the facts whose conclusion is a formula    *)
(*                                of arithmetic: relations (=, <, <=, >, >=) *)
(*                                on :num, :int or :real terms under ~, /\,  *)
(*                                \/, ==> and iff (no other atoms);          *)
(*   relevant_arith_facts ths tm  those of them connected to tm: they share *)
(*                                an arithmetic atom with tm or with another *)
(*                                connected fact (the closure).              *)
(*                                                                           *)
(* The atoms of an arithmetic term are its maximal subterms that are not     *)
(* built by the operators of linear arithmetic (numerals, +, -, *, SUC, PRE, *)
(* EXP, MIN, MAX, DIV and MOD, &, the int and real operations, conditionals) *)
(* or by those of arith_transparent (by default the word operations, so      *)
(* that val(word_add x (word k)) meets val x and k, as the conversions of     *)
(* the callers, e.g. VAL_NOWRAP_CONV, make them meet).                       *)
(* A linear arithmetic proof of tm needs only facts connected to tm, unless  *)
(* the facts are contradictory by themselves: callers that may meet that     *)
(* (dead branches) fall back to arith_facts or to all the facts.            *)
(* ========================================================================= *)

let arith_is_numty ty = ty = `:num` || ty = `:int` || ty = `:real`;;

let arith_is_rel t =
  match t with
    Comb(Comb(Const(("="|"<"|"<="|">"|">="),_),a),_) -> arith_is_numty(type_of a)
  | Comb(Comb(Const(("int_lt"|"int_le"|"int_gt"|"int_ge"|
                     "real_lt"|"real_le"|"real_gt"|"real_ge"),_),_),_) -> true
  | _ -> false;;

let rec arith_is_formula t =
  match t with
    Const(("T"|"F"),_) -> true
  | Comb(Const("~",_),a) -> arith_is_formula a
  | Comb(Comb(Const(("/\\"|"\\/"|"==>"),_),a),b) ->
      arith_is_formula a && arith_is_formula b
  | Comb(Comb(Const("=",_),a),b) when type_of a = bool_ty ->
      arith_is_formula a && arith_is_formula b
  | _ -> arith_is_rel t;;

let arith_facts (ths:thm list) =
  filter (fun th -> arith_is_formula(concl th)) ths;;

let arith_operators =
  ["NUMERAL"; "BIT0"; "BIT1"; "_0"; "+"; "-"; "*"; "SUC"; "PRE"; "EXP";
   "MIN"; "MAX"; "DIV"; "MOD"; "&"; "COND";
   "int_add"; "int_sub"; "int_mul"; "int_neg"; "int_of_num"; "int_pow";
   "int_min"; "int_max"; "int_abs";
   "real_add"; "real_sub"; "real_mul"; "real_neg"; "real_of_num"; "real_pow";
   "real_min"; "real_max"; "real_abs";
   "~"; "/\\"; "\\/"; "==>"; "="; "<"; "<="; ">"; ">=";
   "int_lt"; "int_le"; "int_gt"; "int_ge";
   "real_lt"; "real_le"; "real_gt"; "real_ge"; "T"; "F"];;

let arith_transparent =
  ref ["val"; "ival"; "word"; "iword"; "word_add"; "word_sub"; "word_neg";
       "word_mul"; "word_zx"; "word_sx"; "word_and"; "word_or"; "word_xor";
       "word_not"; "word_ushr"; "word_shl"; "word_ishr"; "word_join";
       "word_subword"; "bitval"];;

let rec arith_atoms t acc =
  match t with
    Const(c,_) -> if mem c arith_operators then acc else insert t acc
  | Var(_,_) -> insert t acc
  | Comb(_,_) ->
      let f,args = strip_comb t in
      (match f with
         Const(c,_) when mem c arith_operators || mem c !arith_transparent ->
           if c = "NUMERAL" then acc else
           itlist arith_atoms args acc
       | _ -> insert t acc)
  | Abs(_,_) -> insert t acc;;

let relevant_arith_facts (ths:thm list) (tm:term) =
  let facts = map (fun th -> th,arith_atoms (concl th) [])
                  (arith_facts ths) in
  let rec close atoms keep rest =
    let now,later = partition (fun (_,a) -> exists (fun x -> mem x atoms) a)
                              rest in
    if now = [] then keep else
    close (itlist (fun (_,a) acc -> union a acc) now atoms)
          (keep @ map fst now) later in
  let kept = close (arith_atoms tm []) [] facts in
  filter (fun th -> List.memq th kept) ths;;
