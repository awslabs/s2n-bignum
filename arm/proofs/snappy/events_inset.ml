(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The events of a path in the set form (common/footprint.ml):              *)
(*                                                                           *)
(*   ?e2. read events s = APPEND e2 e /\ memaccess_inset e2 RS WS            *)
(*                                                                           *)
(* for RS and WS unions of memranges (and footprints). As SNAPPY_EVENTS_TAC  *)
(* of events.ml: each event of a step is within RS or WS by                  *)
(* snappy_subset_rule (the components of a union, a region within a region   *)
(* of the same base by arithmetic on the facts, else footprint_subset_rule), *)
(* and a list of a callee by its memaccess_inset fact (MEMACCESS_INSET_MONO) *)
(* or its memaccess_inbounds fact (MEMACCESS_INBOUNDS_INSET).               *)
(* ========================================================================= *)

needs "arm/proofs/snappy/events.ml";;
needs "common/footprint.ml";;

let SNAPPY_MEMRANGE_OFFSET_SUBSET = prove
 (`!(b:int64) x k y l.
        y <= x /\ x + k <= y + l
        ==> memrange(word_add b (word x),k) SUBSET memrange(word_add b (word y),l)`,
  REWRITE_TAC[GSYM CONTAINED_MEMRANGE; contained; DIMINDEX_64] THEN
  REWRITE_TAC[SNAPPY_CONTAINED_MODULO_OFFSET]);;

(* s SUBSET t for s and t unions of memranges and footprints.                *)
let snappy_subset_rule (asl:(string*thm) list) =
  let union_l = SPEC_ALL UNION_SUBSET
  and sub_ul = CONJUNCT1 SUBSET_UNION and sub_ur = CONJUNCT2 SUBSET_UNION in
  let trans2 th1 th2 = MATCH_MP SUBSET_TRANS (CONJ th1 th2) in
  let region s t =
    let a,k = dest_memrange s and b,l = dest_memrange t in
    let ba,x,tha = snappy_addr_split a and bb,y,thb = snappy_addr_split b in
    if compare ba bb <> 0 then failwith "base" else
    let c1 = mk_binary "<=" (y,x) and c2 = mk_binary "<=" (mk_binary "+" (x,k),
                                                         mk_binary "+" (y,l)) in
    let th1 = TAC_PROOF((asl,c1),SNAPPY_EV_ARITH_TAC)
    and th2 = TAC_PROOF((asl,c2),SNAPPY_EV_ARITH_TAC) in
    let th = MP (ISPECL [ba;x;k;y;l] SNAPPY_MEMRANGE_OFFSET_SUBSET) (CONJ th1 th2) in
    let th' = CONV_RULE(LAND_CONV(RAND_CONV(LAND_CONV(K(SYM tha)))) THENC
                        RAND_CONV(RAND_CONV(LAND_CONV(K(SYM thb))))) th in
    if aconv (concl th') (mk_icomb(mk_icomb(`(SUBSET):(int64->bool)->(int64->bool)->bool`,s),t))
    then th' else failwith "match" in
  let rec go s t =
    if compare s t = 0 then ISPEC s SUBSET_REFL else
    match s with
      Const("EMPTY",_) -> ISPEC t EMPTY_SUBSET
    | Comb(Comb(Const("UNION",_),x),y) ->
        EQ_MP (SYM(PART_MATCH lhand union_l (mk_icomb(mk_icomb(
                  `(SUBSET):(A->bool)->(A->bool)->bool`,s),t))))
              (CONJ (go x t) (go y t))
    | _ ->
    match t with
      Comb(Comb(Const("UNION",_),x),y) ->
        (try trans2 (go s x) (ISPECL [x;y] sub_ul)
         with Failure _ -> trans2 (go s y) (ISPECL [y;x] sub_ur))
    | _ ->
    try region s t with Failure _ -> footprint_subset_rule s t in
  fun s t ->
    snappy_ev_cur_asl () := asl;
    try go s t with Failure _ ->
      (if !snappy_ev_debug then
        (Format.print_string "snappy_subset_rule failed on: ";
         print_term s; Format.print_string "  SUBSET  "; print_term t;
         Format.print_newline());
       failwith "snappy_subset_rule");;

(* memaccess_inset l RS WS from the fact about l (set or list form).         *)
let SNAPPY_INSET_SUB_TAC : tactic = fun (asl,w) ->
  let l = rand(rator(rator w)) and rs = rand(rator w) and ws = rand w in
  let th = snd(find (fun (_,th) -> match concl th with
      Comb(Comb(Comb(Const(("memaccess_inset"|"memaccess_inbounds"),_),l'),_),_) ->
        l' = l
    | _ -> false) asl) in
  let th = match concl th with
      Comb(Comb(Comb(Const("memaccess_inbounds",_),_),_),_) ->
        REWRITE_RULE[MEMRANGES_CLAUSES; UNION_EMPTY]
          (MATCH_MP MEMACCESS_INBOUNDS_INSET th)
    | _ -> th in
  if concl th = w then ACCEPT_TAC th (asl,w) else
  let rs',ws' = rand(rator(concl th)),rand(concl th) in
  ACCEPT_TAC (MATCH_MP MEMACCESS_INSET_MONO
    (CONJ (snappy_subset_rule asl rs' rs)
          (CONJ (snappy_subset_rule asl ws' ws) th))) (asl,w);;

(* The goal ?e2. read events s = APPEND e2 e /\ memaccess_inset e2 RS WS.    *)
let SNAPPY_INSET_EVENTS_TAC : tactic = fun (asl,w) ->
  let _,bod = dest_exists w in
  let eqt = lhand bod in
  let t = lhs eqt and e = rand(rhs eqt) in
  let tv,rw =
    try let _,th = find (fun (_,th) -> is_eq(concl th) && lhs(concl th) = t) asl in
        rhs(concl th),GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o LAND_CONV) [th]
    with Failure _ -> t,ALL_TAC in
  set_component_assumptions (map snd asl);
  let one (asl,w) =
    match w with
      Comb(Comb(Const("SUBSET",_),s),t) ->
        ACCEPT_TAC (snappy_subset_rule asl s t) (asl,w)
    | _ -> SNAPPY_INSET_SUB_TAC (asl,w) in
  (rw THEN EXISTS_TAC (snappy_events_prefix e tv) THEN CONJ_TAC THENL
    [REWRITE_TAC[APPEND; GSYM APPEND_ASSOC];
     REWRITE_TAC[MEMACCESS_INSET_CLAUSES; MEMACCESS_INSET_APPEND;
                 event_loads; event_stores; EMPTY_SUBSET] THEN
     REPEAT CONJ_TAC THEN one]) (asl,w);;

(* As SNAPPY_EV_FIRST_TAC for the set form.                                  *)
let SNAPPY_INSET_FIRST_TAC : tactic = fun (asl,w) ->
  let fvs = freesl (w :: map (concl o snd) asl) in
  let is_ev t =
    is_exists t &&
    (let v,b = dest_exists t in
     (try match lhs(lhand b) with
            Comb(Comb(Const("read",_),Const("events",_)),_) -> true
          | _ -> false
      with Failure _ -> false) &&
     (try fst(dest_const(fst(strip_comb(rand b)))) = "memaccess_inset"
      with Failure _ -> false)) &&
    subset (frees t) fvs in
  let evs = setify(find_terms is_ev w) in
  MAP_EVERY (fun t -> SUBGOAL_THEN t (fun th -> REWRITE_TAC[th]) THENL
                       [SNAPPY_INSET_EVENTS_TAC; ALL_TAC]) evs (asl,w);;
