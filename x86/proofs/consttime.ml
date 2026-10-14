(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(*   Tactics for proving constant-time and memory-safety properties in x86.  *)
(* ========================================================================= *)

needs "common/consttime.ml";;

(* Sanity check for architecture *)
let _ = match `:armstate`,`:x86state` with
  | (Tyvar _),(Tyapp (_, [])) -> ()
  | (Tyapp (_, [])),(Tyvar _) -> failwith "this file cannot be loaded from arm"
  | _,_ -> failwith "Unknown case";;

let mk_safety_spec
    ?(readonly_objects=([]:(term * term)list))
    ?(extra_public_vars=([]:term list))
    ~(keep_maychanges:bool)
    (fnargs,xx,meminputs,memoutputs,memtemps)
    (subroutine_correct_th:thm) exec: term*(term list) =
  let read_sth_eq (f:term->bool):term->bool =
    fun t -> is_eq t && let l = lhs t in is_binary "read" l &&
      let l' = fst (dest_binary "read" l) in f l' in
  gen_mk_safety_spec ~readonly_objects ~extra_public_vars ~keep_maychanges
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
    with Failure _ ->
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
    let maychange_comps = map (fun t ->
      try assoc t ymms with Failure _ -> t) maychange_comps in
    (* unique it *)
    let maychange_comps = uniq (sort (<) maychange_comps) in

    let new_maychanges = map (fun t ->
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

(* Symbolic simulation of steps snums of a leg of a safety proof. *)

let X86_SAFETY_SIM_TAC exec snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  X86_STEPS_TAC exec snums THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];;

(* Prove a safety property following the skeleton sk (SAFETY_SKELETON_TAC),
   introducing the variables (W64_GEN_TAC for the word variables named in
   w64) and rewriting with ths and the usual x86 definitions. *)

let X86_SAFETY_SKELETON_TAC ?(ths=[]) ?(rename=[]) w64 sk =
  SAFETY_SKELETON_TAC
    (GEN_SAFETY_INTRO_TAC ~rename ([C_ARGUMENTS; C_RETURN; SOME_FLAGS] @ ths) w64)
    sk;;

(* Prove the safety of the Windows entry point of a function using AVX2: the
   Windows code saves the registers gprs (among RDI and RSI) and the low
   halves of the callee-saved vector registers numbered xmms (from 6 to 15),
   moves the arguments, runs the standard code tmc at offset off, whose
   safety theorem is core_th, and restores the registers. pre and post are
   the numbers of steps before and after the standard code; pre_ants is run
   before discharging the preconditions of core_th. *)

let X86_WINDOWS_XMM_WRAP_SAFETY_TAC ?(pre_ants=ALL_TAC) (wintmc,winexec)
    (tmc,core_th) ~gprs ~xmms ~off ~pre ~post =
  let ymm_th i =
    el i [YMM0; YMM1; YMM2; YMM3; YMM4; YMM5; YMM6; YMM7;
          YMM8; YMM9; YMM10; YMM11; YMM12; YMM13; YMM14; YMM15] in
  let reg_tm s i = parse_term (Printf.sprintf s i) in
  let bigstate = "s" ^ string_of_int (pre + 1) in
  fun (asl,w) ->
    let vs = fst(strip_forall(snd(dest_exists w))) in
    let ngen = index `stackpointer:int64` vs in
    let stackoff =
      let t = find_term (fun t -> is_binary "word_sub" t &&
                                  lhand t = `stackpointer:int64`) w in
      dest_small_numeral (rand(rand t)) in
    let core_vs = fst(strip_forall(snd(dest_exists(concl core_th)))) in
    let args = tl (fst(chop_list (index `pc:num` core_vs) core_vs)) in
    let pcoff = mk_binary "+" (`pc:num`,mk_small_numeral off) in
    (ASSUME_CALLEE_SAFETY_TAC core_th "H_subth" THEN
     META_EXISTS_TAC THEN
     REPLICATE_TAC ngen GEN_TAC THEN
     WORD_FORALL_OFFSET_TAC stackoff THEN
     REPEAT GEN_TAC THEN
     REWRITE_TAC[fst winexec] THEN
     REPEAT STRIP_TAC THEN REWRITE_TAC[WINDOWS_C_ARGUMENTS] THEN
     REWRITE_TAC[WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
     MAP_EVERY (fun r ->
       ENSURES_PRESERVED_TAC (String.lowercase_ascii(fst(dest_const r))^"_init") r)
       gprs THEN
     MAP_EVERY (fun i ->
       ENSURES_PRESERVED_TAC ("init_xmm" ^ string_of_int i)
         (reg_tm "ZMM%d :> bottomhalf :> bottomhalf" i)) xmms THEN
     REWRITE_TAC[READ_ZMM_BOTTOM_QUARTER'] THEN
     REWRITE_TAC(map (GSYM o ymm_th) xmms) THEN
     MAP_EVERY (fun i ->
       GHOST_INTRO_TAC (mk_var("init_ymm" ^ string_of_int i,`:int256`))
         (reg_tm "read YMM%d" i)) xmms THEN
     GLOBALIZE_PRECONDITION_TAC THEN
     REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
     ENSURES_INIT_TAC "s0" THEN
     X86_STEPS_TAC winexec (1--pre) THEN
     W(fun (asl,w) ->
       let current_events = filter_map (fun (_,ath) -> let t = concl ath in
         if is_eq t && is_read_events (lhs t) then Some (rhs t)
         else None) asl in
       if length current_events <> 1
       then failwith "More than 'read events .. = ..?'"
       else
         REMOVE_THEN "H_subth"
           (MP_TAC o SPECL (hd current_events :: args @ [pcoff]))) THEN
     ASM_REWRITE_TAC[C_ARGUMENTS; SOME_FLAGS] THEN
     pre_ants THEN
     ANTS_TAC THENL [NONOVERLAPPING_TAC; ALL_TAC] THEN
     X86_BIGSTEP_TAC winexec bigstate THENL
      [FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP
        (BYTES_LOADED_SUBPROGRAM_RULE wintmc
          (REWRITE_RULE[BUTLAST_CLAUSES]
            (AP_TERM `BUTLAST:byte list->byte list` tmc))
          off));
       RULE_ASSUM_TAC(CONV_RULE(TRY_CONV RIP_PLUS_CONV))] THEN
     MAP_EVERY (fun i ->
       ABBREV_TAC (parse_term (Printf.sprintf "ymm%d_epilog = read YMM%d %s"
                                 i i bigstate))) xmms THEN
     X86_STEPS_TAC winexec ((pre+2)--(pre+1+post)) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_ZMM_QUARTER]) THEN
     RULE_ASSUM_TAC(REWRITE_RULE[MAYCHANGE_YMM_SSE_QUARTER]) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     CONJ_TAC THENL [DISCHARGE_SAFETY_PROPERTY_TAC; ALL_TAC] THEN
     (* the preserved vector registers *)
     REPEAT CONJ_TAC THEN CONV_TAC WORD_BLAST) (asl,w);;
