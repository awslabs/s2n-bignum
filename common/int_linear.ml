(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Linear integer congruence certificates.                                    *)
(* ========================================================================= *)

let INT_LINEAR_ADD_TM = `(+):int->int->int`
and INT_LINEAR_SUB_TM = `(-):int->int->int`
and INT_LINEAR_MUL_TM = `(*):int->int->int`
and INT_LINEAR_NEG_TM = `(--):int->int`;;

let INT_LINEAR_CONG_FROM_WITNESS = prove
 (`!a b q d:int.
     a - b = q * d
     ==> (a == b) (mod q)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[int_congruent] THEN
  DISCH_TAC THEN
  EXISTS_TAC `d:int` THEN
  ASM_REWRITE_TAC[]);;

let INT_LINEAR_EMPTY () =
  ref num_0,
  Hashtbl.create 521,
  ref [];;

let INT_LINEAR_ADD_ATOM (_,coefficients,order) tm coefficient =
  if coefficient <>/ num_0 then
    try
      let cell = Hashtbl.find coefficients tm in
      cell := !cell +/ coefficient
    with Not_found ->
      Hashtbl.add coefficients tm (ref coefficient);
      order := tm::!order;;

(* Treat products by concrete integers as scalar multiplication. Other
   products remain opaque atoms, so the rule also applies to expressions
   that are linear in larger syntactic subterms. *)

let rec INT_LINEAR_COLLECT
    ((constant,_,_) as linear) scale tm =
  if is_intconst tm then
    constant := !constant +/ scale */ dest_intconst tm
  else if is_binop INT_LINEAR_ADD_TM tm then
    let l,r = dest_binop INT_LINEAR_ADD_TM tm in
    INT_LINEAR_COLLECT linear scale l;
    INT_LINEAR_COLLECT linear scale r
  else if is_binop INT_LINEAR_SUB_TM tm then
    let l,r = dest_binop INT_LINEAR_SUB_TM tm in
    INT_LINEAR_COLLECT linear scale l;
    INT_LINEAR_COLLECT linear (minus_num scale) r
  else if is_comb tm && rator tm = INT_LINEAR_NEG_TM then
    INT_LINEAR_COLLECT linear (minus_num scale) (rand tm)
  else if is_binop INT_LINEAR_MUL_TM tm then
    let l,r = dest_binop INT_LINEAR_MUL_TM tm in
    if is_intconst l then
      INT_LINEAR_COLLECT linear (scale */ dest_intconst l) r
    else if is_intconst r then
      INT_LINEAR_COLLECT linear (scale */ dest_intconst r) l
    else
      INT_LINEAR_ADD_ATOM linear tm scale
  else
    INT_LINEAR_ADD_ATOM linear tm scale;;

let INT_LINEAR_TERM coefficient tm =
  if coefficient =/ num_1 then tm
  else if coefficient =/ minus_num num_1 then
    mk_comb(INT_LINEAR_NEG_TM,tm)
  else
    mk_binop INT_LINEAR_MUL_TM (mk_intconst coefficient) tm;;

let rec INT_LINEAR_RIGHT_ADD = function
    [] -> `(&0:int)`
  | [tm] -> tm
  | tm::tms ->
      mk_binop INT_LINEAR_ADD_TM tm (INT_LINEAR_RIGHT_ADD tms);;

let INT_LINEAR_DIVIDE modulus coefficient =
  if modulus =/ num_0 then
    if coefficient =/ num_0 then num_0
    else failwith "INT_LINEAR_DIVIDE: nonzero coefficient modulo zero"
  else if mod_num coefficient modulus =/ num_0 then
    quo_num coefficient modulus
  else
    failwith "INT_LINEAR_DIVIDE: coefficient is not divisible";;

let INT_LINEAR_DEST_CONG goal =
  let op,args = strip_comb goal in
  if not(is_const op && fst(dest_const op) = "==") ||
     length args <> 3
  then
    failwith "INT_LINEAR_DEST_CONG: not a congruence"
  else
    let lhs = List.nth args 0
    and rhs = List.nth args 1
    and modulus_tm = rand(List.nth args 2) in
    if type_of lhs <> `:int` || type_of rhs <> `:int` ||
       type_of modulus_tm <> `:int`
    then
      failwith "INT_LINEAR_DEST_CONG: not an integer congruence"
    else if not(is_intconst modulus_tm) then
      failwith "INT_LINEAR_DEST_CONG: nonconstant modulus"
    else
      lhs,rhs,modulus_tm,dest_intconst modulus_tm;;

let INT_LINEAR_CONG_WITNESS goal =
  let lhs,rhs,_,modulus = INT_LINEAR_DEST_CONG goal in
  let linear = INT_LINEAR_EMPTY () in
  let constant,coefficients,order = linear in
  INT_LINEAR_COLLECT linear num_1 lhs;
  INT_LINEAR_COLLECT linear (minus_num num_1) rhs;
  let terms =
    map
     (fun tm ->
        let coefficient = !(Hashtbl.find coefficients tm) in
        INT_LINEAR_TERM
          (INT_LINEAR_DIVIDE modulus coefficient) tm)
     (filter
       (fun tm -> !(Hashtbl.find coefficients tm) <>/ num_0)
       (rev(!order))) in
  let constant =
    INT_LINEAR_DIVIDE modulus !constant in
  INT_LINEAR_RIGHT_ADD
   (if constant =/ num_0 then terms
    else mk_intconst constant::terms);;

let INT_LINEAR_CONG_RULE goal =
  let lhs,rhs,modulus_tm,_ = INT_LINEAR_DEST_CONG goal in
  let witness = INT_LINEAR_CONG_WITNESS goal in
  let difference =
    mk_binop INT_LINEAR_SUB_TM lhs rhs
  and multiple =
    mk_binop INT_LINEAR_MUL_TM modulus_tm witness in
  (* The collector has already chosen the quotient. Normalize both sides
     only to check that certificate; no ideal or witness search is needed. *)
  let difference_th = INT_POLY_CONV difference
  and multiple_th = INT_POLY_CONV multiple in
  let equality_th =
    if aconv
        (rand(concl difference_th))
        (rand(concl multiple_th))
    then TRANS difference_th (SYM multiple_th)
    else
      failwith
        "INT_LINEAR_CONG_RULE: normalization mismatch" in
  let result =
    MP
     (SPECL
       [lhs;rhs;modulus_tm;witness]
       INT_LINEAR_CONG_FROM_WITNESS)
     equality_th in
  if aconv (concl result) goal then result
  else failwith "INT_LINEAR_CONG_RULE: conclusion mismatch";;

let INT_LINEAR_CONG_TAC (asl,goal) =
  ACCEPT_TAC(INT_LINEAR_CONG_RULE goal) (asl,goal);;
