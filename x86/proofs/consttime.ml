(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "common/consttime.ml";;

let mk_safety_spec
    ?(coda_pc_range:(int*int) option) (* when coda is used: (begin, len) *)
    ~(keep_maychanges:bool)
    (fnargs,xx,meminputs,memoutputs,memtemps)
    (subroutine_correct_th:thm) exec: term*(term list) =
  let read_sth_eq (f:term->bool):term->bool =
    fun t -> is_eq t && let l = lhs t in is_binary "read" l &&
      let l' = fst (dest_binary "read" l) in f l' in
  gen_mk_safety_spec ?coda_pc_range ~keep_maychanges
    (fnargs,xx,meminputs,memoutputs,memtemps)
    subroutine_correct_th exec
    (read_sth_eq (fun t -> t = `RSP`))
    (can (fun t ->
            let l = fst (dest_eq t) in
            let l' = fst (dest_binary "read" l) in
            let mem,b64_sp = dest_binary ":>" l' in
            let b64,sp = dest_comb b64_sp in
            check (fun () ->
              name_of mem = "memory" && name_of b64 = "bytes64" &&
              name_of sp = "stackpointer") ()));;

let EXPAND_MAYCHANGE_YMM_REGS_TAC:tactic =
  let ymms = [
    (`YMM0`,`ZMM0`);   (`YMM1`,`ZMM1`);   (`YMM2`,`ZMM2`); (`YMM3`,`ZMM3`);
    (`YMM4`,`ZMM4`);   (`YMM5`,`ZMM5`);   (`YMM6`,`ZMM6`); (`YMM7`,`ZMM7`);
    (`YMM8`,`ZMM8`);   (`YMM9`,`ZMM9`);   (`YMM10`,`ZMM10`); (`YMM11`,`ZMM11`);
    (`YMM12`,`ZMM12`); (`YMM13`,`ZMM13`); (`YMM14`,`ZMM14`); (`YMM15`,`ZMM15`);
  ] in
  let rec collect_maychange_components (t:term): term list =
    try
      let lhs,rhs = dest_binary ",," t in
      (collect_maychange_components lhs) @ (collect_maychange_components rhs)
    with _ ->
      if is_comb t && name_of (rator t) = "MAYCHANGE" then
        let args = rand t in
        dest_list args
      else failwith ("Unknown term: " ^ (string_of_term t)) in

  FIRST_X_ASSUM (fun th ->
    let _ = check (maychange_term o concl) th in
    (* t s s' where t is (MAYCHANGE .. ,, MAYCHANGE .. ,, .. *)
    let t,s' = dest_comb (concl th) in
    let t,s = dest_comb t in
    let maychange_comps = collect_maychange_components t in
    (* map YMM to ZMM *)
    let maychange_comps = List.map (fun t ->
      try assoc t ymms with _ -> t) maychange_comps in
    (* unique it *)
    let maychange_comps = uniq (sort (<) maychange_comps) in

    let new_maychanges = List.map (fun t ->
        let unary_list = mk_list ([t],type_of t) in
        mk_icomb (`MAYCHANGE`,unary_list))
      maychange_comps in
    let new_maychange_seq = List.fold_right (fun mayc t ->
        mk_icomb(mk_icomb (`,,`,mayc),t))
      (butlast new_maychanges) (last new_maychanges) in
    let new_maychange_full = mk_icomb(mk_icomb(new_maychange_seq,s),s') in
    SUBGOAL_THEN new_maychange_full MP_TAC THENL [
      MP_TAC th; ALL_TAC
  ]) THENL [
    DISCH_TAC THEN PRINT_GOAL_TAC THEN MONOTONE_MAYCHANGE_TAC;
    DISCH_TAC
  ];;

let PROVE_SAFETY_SPEC_TAC ?(public_vars:term list option) exec:tactic =
  GEN_PROVE_SAFETY_SPEC_TAC ?public_vars:public_vars exec
    ?tac_before_maychange_simp:(Some EXPAND_MAYCHANGE_YMM_REGS_TAC)
    [BYTES_LOADED_APPEND_CLAUSE]
    X86_SINGLE_STEP_TAC;;

