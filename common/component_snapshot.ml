(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* Opt-in parent snapshots for forward execution. Instead of carrying
   read (parent :> view) s = x through every change to s, retain
   read parent s = snapshot and read view snapshot = x. Only writes to
   parent create a new snapshot and transport its view facts.

   Snapshot equations and every transported fact are kernel theorems.
   The option records components, not context proofs or assumed frames. *)

needs "common/components.ml";;

let component_snapshot_parents = ref ([]:term list);;

let COMPONENT_SNAPSHOT_READ_CONV ths =
  let parents = mapfilter (fun th ->
    match concl th with
    | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s)),v)
      when is_var v && not(vfree_in s c) && not(vfree_in s v) ->
        (c,s,th)
    | _ -> failwith "not a parent equation") ths in
  fun tm ->
    match tm with
    | Comb(Comb(Const("read",_),
         Comb(Comb(Const(":>",_),c),d)),s) ->
        let _,_,parent = find (fun (c',s',_) -> c = c' && s = s') parents in
        let composed = GEN_REWRITE_CONV I [READ_COMPONENT_COMPOSE] tm in
        TRANS composed (AP_TERM (list_mk_icomb "read" [d]) parent)
    | _ -> failwith "COMPONENT_SNAPSHOT_READ_CONV";;

let COMPONENT_SNAPSHOT_VIEWS_TAC parent state parent_th =
  W(fun (asl,_) ->
    let convert th =
      match concl th with
      | Comb(Comb(Const("=",_),
          Comb(Comb(Const("read",_),
            Comb(Comb(Const(":>",_),c),d)),s)),_)
        when c = parent && s = state && not(vfree_in state d) ->
          let th = CONV_RULE
            (LAND_CONV(GEN_REWRITE_CONV I [READ_COMPONENT_COMPOSE])) th in
          CONV_RULE
            (LAND_CONV(RAND_CONV(GEN_REWRITE_CONV I [parent_th]))) th
      | _ -> failwith "not a view of this parent" in
    let converted = mapfilter (fun (_,th) -> th,convert th) asl in
    DISCARD_ASSUMPTIONS_TAC(fun th ->
      exists (fun (old,_) -> aconv (concl old) (concl th)) converted) THEN
    MAP_EVERY ASSUME_TAC(map snd converted));;

let COMPONENT_SNAPSHOT_INNER_READ snapshot th =
  match concl th with
  | Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),s)),_)
      -> s = snapshot
  | _ -> false;;

let COMPONENT_SNAPSHOT_INIT_TAC parent name =
  W(fun (asl,w) ->
    let state = rand w in
    let read_parent = list_mk_icomb "read" [parent;state] in
    let avoid = w::flat(map (fun (_,th) -> concl th::hyp th) asl) in
    let snapshot = variant avoid (mk_var(name,type_of read_parent)) in
    FRESH_ABBREV_TAC(mk_eq(snapshot,read_parent)) THEN
    W(fun (asl,_) ->
      let parent_th =
        find (fun (_,th) -> concl th = mk_eq(read_parent,snapshot)) asl
        |> snd in
      COMPONENT_SNAPSHOT_VIEWS_TAC parent state parent_th));;

let COMPONENT_SNAPSHOT_UPDATE_TAC uth =
  if !component_snapshot_parents = [] then ALL_TAC else
  let utm,state' = dest_eq(concl uth) in
  let state = repeat rand utm in
  MAP_EVERY (fun parent ->
    W(fun (asl,w) ->
      let ths = map snd asl in
      let old_read = list_mk_icomb "read" [parent;state] in
      let old_parent =
        find (fun th -> is_eq(concl th) && lhs(concl th) = old_read) ths in
      let old_snapshot = rhs(concl old_parent) in
      if not(is_var old_snapshot) then
        failwith "COMPONENT_SNAPSHOT_UPDATE_TAC: not a named snapshot";
      let current_read = list_mk_icomb "read" [parent;state'] in
      (* Ordinary propagation has already proved this equation for an
         unchanged parent. Avoid constructing another rewrite table. *)
      if exists (fun th ->
        concl th = mk_eq(current_read,old_snapshot)) ths then ALL_TAC else
      let read_conv = !extra_context_read_CONV ths in
      let equations =
        !extra_context_read_filter ths
        |> filter (fun th -> not(is_eq(concl th)) ||
                            lhs(concl th) <> rhs(concl th)) in
      let new_parent =
        AP_TERM (list_mk_icomb "read" [parent]) (SYM uth)
        |> CONV_RULE(RAND_CONV
            (TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC
             TOP_DEPTH_CONV read_conv THENC
             GEN_REWRITE_CONV TOP_DEPTH_CONV equations)) in
      let value = rhs(concl new_parent) in
      (* A store can normalize to the old snapshot even when ordinary
         propagation could not preserve the machine-state parent. Keep
         the derived current-parent equation for later reads and updates. *)
      if value = old_snapshot then ASSUME_TAC new_parent else
      (* Never abbreviate a parent which still depends on the machine state.
         Such updates need the ordinary execution representation. *)
      let () = if vfree_in state value then
        failwith "COMPONENT_SNAPSHOT_UPDATE_TAC: unresolved parent" in
      let avoid = w::flat(map (fun th -> concl th::hyp th) ths) in
      let snapshot = variant avoid (genvar(type_of value)) in
      FRESH_ABBREV_TAC(mk_eq(snapshot,value)) THEN
      W(fun (asl,_) ->
        let definition =
          find (fun (_,th) -> concl th = mk_eq(value,snapshot)) asl |> snd in
        let parent_th = TRANS new_parent definition in
        let inner_facts =
          filter (COMPONENT_SNAPSHOT_INNER_READ old_snapshot) ths in
        let cxt =
          NONOVERLAPPING_DRIVERS ths,FILTER_CANONIZE_ASSUMPTIONS ths in
        let updated =
          mapfilter (STATE_UPDATE_RULE cxt definition) inner_facts in
        let written = STATE_UPDATE_NEW_RULE definition in
        ASSUME_TAC parent_th THEN
        COMPONENT_SNAPSHOT_VIEWS_TAC parent state' parent_th THEN
        DISCARD_ASSUMPTIONS_TAC(fun th ->
          concl th = concl definition || concl th = concl old_parent ||
          COMPONENT_SNAPSHOT_INNER_READ old_snapshot th) THEN
        MAP_EVERY ASSUME_TAC updated THEN
        W(fun (asl,_) ->
          MAP_EVERY ASSUME_TAC (filter (fun th ->
            not(exists (fun (_,known) -> concl known = concl th) asl))
            written)))))
    !component_snapshot_parents;;

let WITH_COMPONENT_SNAPSHOTS_TAC snapshots tac gl =
  let saved = !component_snapshot_parents in
  component_snapshot_parents := map fst snapshots;
  match (MAP_EVERY (fun (parent,name) ->
           COMPONENT_SNAPSHOT_INIT_TAC parent name) snapshots THEN tac) gl with
  | result -> component_snapshot_parents := saved; result
  | exception error -> component_snapshot_parents := saved; raise error;;

(* Keep guarded-read rules first: immutable views need not consult a mutable
   snapshot. The ordinary assumption-rewrite phase resolves the inner view. *)
let _ =
  let previous = !extra_context_read_CONV in
  extra_context_read_CONV := (fun ths ->
    if !component_snapshot_parents = [] then previous ths else
    previous ths ORELSEC COMPONENT_SNAPSHOT_READ_CONV ths);;
