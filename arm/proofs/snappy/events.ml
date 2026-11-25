(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Memory safety of the snappy proofs by bstep: the events of a path in the  *)
(* list form ?e2. read events s = APPEND e2 e /\ memaccess_inbounds e2 R W  *)
(* (common/safety.ml), for R and W concrete lists of regions.                *)
(*                                                                           *)
(* At the end of a path, the events since the start are the events of the   *)
(* steps (CONS of EventLoad, EventStore, EventJump) and the lists of the     *)
(* lemmas and callees gone through (APPEND of the variables bstep_e<k>, with *)
(* their memaccess_inbounds facts), in front of the list of the start (e, or *)
(* APPEND e2 e with a fact memaccess_inbounds e2 R' W' at a cut point).      *)
(* SNAPPY_EVENTS_TAC proves the goal: the address of each step is split into *)
(* a base and a numeric offset (snappy_addr_split), and is in the region of  *)
(* R or W with the same base by arithmetic on the numeric facts that share   *)
(* atoms with the bound (SNAPPY_EV_ARITH_TAC); a list of a lemma or callee   *)
(* is in R and W if its own regions are (MEMACCESS_INBOUNDS_CONTAINED).      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(* Arithmetic facts: (in)equalities of numbers, without the state.          *)
let snappy_ev_is_num_fact tm =
  let rec ok t = match t with
      Comb(Comb(Const(("<"|"<="|"="),ty),a),b) when
          (try type_of a = `:num` with Failure _ -> false) -> true
    | Comb(Const("~",_),a) -> ok a
    | Comb(Comb(Const("/\\",_),a),b) -> ok a && ok b
    | _ -> false in
  ok tm && not(can (find_term (fun t -> match t with Const("read",_) -> true | _ -> false)) tm);;

(* ------------------------------------------------------------------------- *)
(* Lemmas and the tactics.                                                  *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_CONTAINED_MODULO_OFFSET = prove
 (`!(b:int64) x k y l.
        y <= x /\ x + k <= y + l
        ==> contained_modulo (2 EXP 64) (val(word_add b (word x)),k)
                                        (val(word_add b (word y)),l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[contained_modulo] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN EXISTS_TAC `(x - y) + i:num` THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[CONG; VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC MOD_DOWN_CONV THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let SNAPPY_WORD_ADD_ADD_NUM = prove
 (`!(b:int64) x n. word_add (word_add b (word x)) (word n) = word_add b (word(x + n))`,
  REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]);;

let SNAPPY_WORD_ADD_0_SYM = prove
 (`!b:int64. b = word_add b (word 0)`,
  REWRITE_TAC[WORD_ADD_0]);;

let SNAPPY_MEMACCESS_INBOUNDS_CLAUSES = prove
 (`(!rr wr. memaccess_inbounds ([]:uarch_event list) rr wr) /\
   (!a k t rr wr.
       memaccess_inbounds (CONS (EventLoad(a,k):uarch_event) t) rr wr <=>
       EX (\r. contained_modulo (2 EXP 64) (val a,k) (val (FST r),SND r)) rr /\
       memaccess_inbounds t rr wr) /\
   (!a k t rr wr.
       memaccess_inbounds (CONS (EventStore(a,k):uarch_event) t) rr wr <=>
       EX (\r. contained_modulo (2 EXP 64) (val a,k) (val (FST r),SND r)) wr /\
       memaccess_inbounds t rr wr) /\
   (!x y t rr wr.
       memaccess_inbounds (CONS (EventJump(x,y):uarch_event) t) rr wr <=>
       memaccess_inbounds t rr wr)`,
  REWRITE_TAC[memaccess_inbounds; ALL]);;

(* The list in front of e in t (CONS and APPEND).                            *)
let rec snappy_events_prefix e t =
  if t = e then mk_const("NIL",[hd(snd(dest_type(type_of e))),`:A`])
  else match t with
    Comb(Comb(Const(("CONS"|"APPEND"),_) as c,h),t') ->
      mk_comb(mk_comb(c,h),snappy_events_prefix e t')
  | _ -> failwith "snappy_events_prefix: the events are not on e";;

(* Arithmetic from the numeric facts that share atoms with the goal, twice   *)
(* transitively, without the facts with DIV or MOD unless the goal has one   *)
(* of their DIV/MOD terms; then with the facts with DIV or MOD that share    *)
(* an atom with the goal (as in compress_fragment_seg4_proof.ml).            *)
let snappy_ev_atoms tm =
  let tm' = subst [`n_len_atom:num`,`LENGTH(inp:byte list)`] tm in
  filter (fun v -> not(fst(dest_var v) = "inp")) (frees tm');;

let snappy_ev_divmods tm =
  find_terms (fun t -> is_binary "DIV" t || is_binary "MOD" t) tm;;

(* Facts for the terms of a goal (as bounds of functions), from the proofs   *)
(* that use this file: each function of the list gives facts for a goal. A   *)
(* proof sets them for itself (par_local_ref, common/par.ml): the proofs run *)
(* at the same time on several domains of the link.                         *)
let snappy_ev_bounds = par_local_ref (fun () -> ([]:(term -> thm list) list));;

let SNAPPY_EV_ARITH_TAC : tactic = fun (asl,w) ->
  let w' = rand(concl((NUM_REDUCE_CONV THENC REWRITE_CONV[ADD_CLAUSES]) w)) in
  if w' = `T` then ACCEPT_TAC(EQT_ELIM((NUM_REDUCE_CONV THENC
                     REWRITE_CONV[ADD_CLAUSES]) w)) (asl,w) else
  let extra = flat (map (fun f -> try f w with Failure _ -> []) !(snappy_ev_bounds ())) in
  let asl = asl @ map (fun th -> ("",th)) extra in
  let facts0 = filter (fun th -> snappy_ev_is_num_fact(concl th)) (map snd asl) in
  let gdm = snappy_ev_divmods w in
  let facts = filter (fun th -> let dm = snappy_ev_divmods(concl th) in
      dm = [] || exists (fun t -> mem t gdm) dm) facts0 in
  let ga = snappy_ev_atoms w in
  let grow vs = itlist (fun th acc ->
      let a = snappy_ev_atoms(concl th) in
      if intersect a vs <> [] then union a acc else acc) facts vs in
  let sharing vs = filter (fun th -> intersect (snappy_ev_atoms(concl th)) vs <> []) facts in
  (* stages: the facts within the atoms of the goal, then those sharing an  *)
  (* atom with it, then twice transitively, then with DIV and MOD facts     *)
  let within = filter (fun th -> subset (snappy_ev_atoms(concl th)) ga) facts in
  let s1 = sharing ga in
  let s2 = sharing (grow(grow ga)) in
  let attempt ths = try Some((MAP_EVERY MP_TAC ths THEN ARITH_TAC) ([],w))
                    with Failure _ -> None in
  let rec go l = match l with
      [] -> failwith "SNAPPY_EV_ARITH_TAC"
    | ths::rest -> (match attempt ths with Some r -> r | None -> go rest) in
  let ths2 = filter (fun th -> let c = concl th in
      snappy_ev_divmods c <> [] && not(mem th s2) &&
      intersect (snappy_ev_atoms c) ga <> []) facts0 in
  let stages = [within] @ (if length s1 > length within then [s1] else []) @
               (if length s2 > length s1 then [s2] else []) @
               (if ths2 = [] then [] else [s2 @ ths2]) in
  go stages;;

(* The assumptions of the goal, for the side conditions of a split: set by   *)
(* SNAPPY_CONTAINED_TAC and snappy_subset_rule and read by snappy_addr_split *)
(* in the same call, per domain (common/par_domains.ml): proofs that run at  *)
(* the same time on other domains set their own.                             *)
let snappy_ev_cur_asl = par_local_ref (fun () -> ([]:(string*thm) list));;

(* word_add (word_add b (word x)) (word n) = word_add b (word (x - m)) for   *)
(* the numerals m and n = 2^64 - m, if m <= x.                               *)
let snappy_neg_offset_thm =
  let cache = ref [] in
  fun m n ->
    try assoc (m,n) !cache with Failure _ ->
    let tm = subst [m,`m:num`; n,`n:num`]
      `!(b:int64) x. m <= x
          ==> word_add (word_add b (word x)) (word n) = word_add b (word (x - m))` in
    let th = prove(tm,
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN (subst [m,`m:num`] `x = (x - m) + m`)
       (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV) [th])
      THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC] THEN
      CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[WORD_ADD_0]) in
    cache := ((m,n),th) :: !cache; th;;

(* An address a as base + offset: (b, x, |- a = word_add b (word x)), with   *)
(* word (p + n) as word p + n.                                               *)
let rec snappy_addr_split a =
  match a with
    Comb(Comb(Const("word_add",_),t),Comb(Const("word",_),n))
      when is_numeral n && dest_numeral n >=/ pow2 63 &&
           dest_numeral n </ pow2 64 ->
      let m = mk_numeral(pow2 64 -/ dest_numeral n) in
      (try
        let b,x,th = snappy_addr_split t in
        if x = `0` then failwith "zero" else
        let lth = TAC_PROOF((!(snappy_ev_cur_asl ()), mk_binary "<=" (m,x)),
                            SNAPPY_EV_ARITH_TAC) in
        let eq = MP (ISPECL [b;x] (snappy_neg_offset_thm m n)) lth in
        b, mk_binary "-" (x,m),
        TRANS (AP_THM (AP_TERM (rator(rator a)) th) (rand a)) eq
       with Failure _ ->
      let b = mk_comb(mk_comb(`word_sub:int64->int64->int64`,t),
                      mk_comb(`word:num->int64`,m)) in
      let th = WORD_RULE (mk_eq(a,b)) in
      b, `0`, TRANS th (ISPEC b SNAPPY_WORD_ADD_0_SYM))
  | Comb(Comb(Const("word_add",_),t),Comb(Const("word",_),n)) ->
      let b,x,th = snappy_addr_split t in
      if x = `0` && b = t then t, n, REFL a else
      b, mk_binary "+" (x,n),
      TRANS (AP_THM (AP_TERM (rator(rator a)) th) (rand a))
            (ISPECL [b;x;n] SNAPPY_WORD_ADD_ADD_NUM)
  | Comb(Const("word",_),Comb(Comb(Const("+",_),p),n)) ->
      let b = mk_comb(rator a,p) in
      b, n, ISPECL [p;n] (INST_TYPE [`:64`,`:N`] WORD_ADD)
  | _ -> a, `0`, ISPEC a SNAPPY_WORD_ADD_0_SYM;;

let snappy_ev_debug = ref true;;

(* A goal contained_modulo (2 EXP 64) (val a,k) (val b1,l1) \/ ... : the     *)
(* first region with the base of a that contains it.                         *)
let SNAPPY_CONTAINED_TAC : tactic = fun (asl,w) ->
  snappy_ev_cur_asl () := asl;
  let ds = disjuncts w in
  let parse d = match d with
      Comb(Comb(Comb(Const("contained_modulo",_),_),
           Comb(Comb(Const(",",_),Comb(Const("val",_),a)),k)),
           Comb(Comb(Const(",",_),Comb(Const("val",_),b)),l)) -> (a,k,b,l)
    | _ -> (if !snappy_ev_debug then
              (Format.print_string "SNAPPY_CONTAINED_TAC: not contained_modulo: ";
               print_term d; Format.print_newline()));
           failwith "SNAPPY_CONTAINED_TAC: not contained_modulo" in
  let (a,k,_,_) = parse (hd ds) in
  let ba,x,tha = snappy_addr_split a in
  let try_one d =
    let (_,_,b,l) = parse d in
    let bb,y,thb = snappy_addr_split b in
    if bb <> ba then failwith "base" else
    let c1 = mk_binary "<=" (y,x) and c2 = mk_binary "<=" (mk_binary "+" (x,k),
                                                         mk_binary "+" (y,l)) in
    let th1 = TAC_PROOF((asl,c1),SNAPPY_EV_ARITH_TAC)
    and th2 = TAC_PROOF((asl,c2),SNAPPY_EV_ARITH_TAC) in
    let th = MP (ISPECL [ba;x;k;y;l] SNAPPY_CONTAINED_MODULO_OFFSET) (CONJ th1 th2) in
    let th' = CONV_RULE(LAND_CONV(LAND_CONV(RAND_CONV(K(SYM tha)))) THENC
                        RAND_CONV(LAND_CONV(RAND_CONV(K(SYM thb))))) th in
    if aconv (concl th') d then EQ_MP (ALPHA (concl th') d) th'
    else failwith "match" in
  let rec prove_disj tm th =
    if tm = concl th then th else
    let l,r = dest_disj tm in
    if l = concl th then DISJ1 th r else DISJ2 l (prove_disj r th) in
  let rec first l = match l with
      [] -> if !snappy_ev_debug then
              (Format.print_string "SNAPPY_CONTAINED_TAC failed on: ";
               print_term w; Format.print_newline());
            failwith "SNAPPY_CONTAINED_TAC"
    | d::r -> (try prove_disj w (try_one d) with Failure _ -> first r) in
  ACCEPT_TAC (first ds) (asl,w);;

(* memaccess_inbounds l R W from an assumption memaccess_inbounds l R' W'.   *)
let SNAPPY_INBOUNDS_SUB_TAC : tactic = fun (asl,w) ->
  let l = rand(rator(rator w)) in
  let th = snd(find (fun (_,th) -> match concl th with
      Comb(Comb(Comb(Const("memaccess_inbounds",_),l'),_),_) -> l' = l
    | _ -> false) asl) in
  if concl th = w then ACCEPT_TAC th (asl,w) else
  (MP_TAC th THEN MATCH_MP_TAC MEMACCESS_INBOUNDS_CONTAINED THEN
   REWRITE_TAC[ALL; EX; contained; DIMINDEX_64] THEN
   REPEAT CONJ_TAC THEN SNAPPY_CONTAINED_TAC) (asl,w);;

(* The goal ?e2. read events s = APPEND e2 e /\ memaccess_inbounds e2 R W.   *)
let SNAPPY_EVENTS_TAC : tactic = fun (asl,w) ->
  let _,bod = dest_exists w in
  let eqt = lhand bod in
  let t = lhs eqt and e = rand(rhs eqt) in
  let tv,rw =
    try let _,th = find (fun (_,th) -> is_eq(concl th) && lhs(concl th) = t) asl in
        rhs(concl th),GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o LAND_CONV) [th]
    with Failure _ -> t,ALL_TAC in
  (rw THEN EXISTS_TAC (snappy_events_prefix e tv) THEN CONJ_TAC THENL
    [REWRITE_TAC[APPEND; GSYM APPEND_ASSOC];
     REWRITE_TAC[SNAPPY_MEMACCESS_INBOUNDS_CLAUSES; MEMACCESS_INBOUNDS_APPEND;
                 EX] THEN
     BETA_TAC THEN REWRITE_TAC[FST; SND] THEN
     REPEAT CONJ_TAC THEN
     FIRST [SNAPPY_INBOUNDS_SUB_TAC; SNAPPY_CONTAINED_TAC]]) (asl,w);;

(* The events of the current state (the goal eventually arm P s).            *)
let snappy_current_events (asl,w) =
  let s = rand w in
  rhs(concl(snd(find (fun (_,th) -> is_eq(concl th) &&
     lhs(concl th) = mk_comb(`read (events:(armstate,uarch_event list)component)`,s)) asl)));;

(* After ENSURES_INIT_TAC: the events of the precondition, chosen as e2.    *)
let SNAPPY_EV_CHOOSE_TAC : tactic =
  REPEAT(FIRST_X_ASSUM(X_CHOOSE_THEN `e2:uarch_event list` STRIP_ASSUME_TAC o
    check (fun th -> is_exists(concl th) &&
                     fst(dest_var(fst(dest_exists(concl th)))) = "e2")));;

(* At the end of a path of a lemma: the conjuncts                            *)
(* ?e2. read events s = APPEND e2 e /\ ... of the goal that do not depend on *)
(* its bound variables, proved first (SNAPPY_EVENTS_TAC) and rewritten to T. *)
let SNAPPY_EV_FIRST_TAC : tactic = fun (asl,w) ->
  let fvs = freesl (w :: map (concl o snd) asl) in
  let is_ev t =
    is_exists t &&
    (let v,b = dest_exists t in
     fst(dest_var v) = "e2" &&
     (try match lhs(lhand b) with
            Comb(Comb(Const("read",_),Const("events",_)),_) -> true
          | _ -> false
      with Failure _ -> false)) &&
    subset (frees t) fvs in
  let evs = setify(find_terms is_ev w) in
  MAP_EVERY (fun t -> SUBGOAL_THEN t (fun th -> REWRITE_TAC[th]) THENL
                       [SNAPPY_EVENTS_TAC; ALL_TAC]) evs (asl,w);;


(* In a path (the goal eventually arm P s): the events since the last        *)
(* checkpoint, CONS of the steps and lists of callees in front of APPEND v e0 *)
(* with a fact memaccess_inbounds v R W, proved in R and W now and replaced  *)
(* by a new variable with the same facts, so that the events of a long path  *)
(* stay small terms.                                                         *)

let SNAPPY_EV_CHECKPOINT_TAC : tactic = fun (asl,w) ->
  let s = rand w in
  let evq = mk_comb(`read (events:(armstate,uarch_event list)component)`,s) in
  let _,evth = find (fun (_,th) -> is_eq(concl th) && lhs(concl th) = evq) asl in
  let t = rhs(concl evth) in
  let ibfact v = snd(find (fun (_,th) -> match concl th with
      Comb(Comb(Comb(Const("memaccess_inbounds",_),v'),_),_) -> v' = v
    | _ -> false) asl) in
  let rec tail t = match t with
      Comb(Comb(Const("CONS",_),_),t') -> tail t'
    | Comb(Comb(Const("APPEND",_),v),e0) when is_var v && is_var e0 &&
        can ibfact v -> v,e0
    | Comb(Comb(Const("APPEND",_),_),t') -> tail t'
    | _ -> failwith "SNAPPY_EV_CHECKPOINT_TAC" in
  let v,e0 = tail t in
  if t = list_mk_icomb "APPEND" [v;e0] then
    failwith "SNAPPY_EV_CHECKPOINT_TAC: nothing new" else
  let ib = concl(ibfact v) in
  let r = rand(rator ib) and wr = rand ib in
  let e3 = variant (frees w @ freesl (map (concl o snd) asl))
                   (mk_var("e_ck",type_of v)) in
  let goal = mk_exists(e3, mk_conj(mk_eq(evq, list_mk_icomb "APPEND" [e3;e0]),
               list_mk_comb(rator(rator(rator ib)),[e3;r;wr]))) in
  let th = TAC_PROOF((asl,goal), SNAPPY_EVENTS_TAC) in
  (* the facts about the lists now inside e3 are not needed any more *)
  let olds = filter (fun (_,th) -> match concl th with
      Comb(Comb(Comb(Const(("memaccess_inbounds"|"memaccess_inset"),_),l),_),_) ->
        is_var l && vfree_in l t
    | _ -> false) asl in
  (UNDISCH_THEN (concl evth) (K ALL_TAC) THEN
   MAP_EVERY (fun (_,th) -> UNDISCH_THEN (concl th) (K ALL_TAC)) olds THEN
   X_CHOOSE_THEN e3 (CONJUNCTS_THEN ASSUME_TAC) th) (asl,w);;
