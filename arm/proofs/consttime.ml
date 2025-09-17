needs "arm/proofs/equiv.ml";;

let find_stack_access_size (subroutine_correct_term:term): int option =
  try
    let t = find_term (fun t -> is_binary "word_sub" t &&
        let a,b = dest_binary "word_sub" t in
        a = mk_var("stackpointer",`:int64`)) subroutine_correct_term in
    let sz = snd (dest_comb t) in
    Some (dest_small_numeral (snd (dest_comb sz)))
  with _ -> None;;


(* Create a safety spec. This returns a safety spec using ensures. *)
let mk_safety_spec
    ?(coda_pc_range:(int*int) option) (* when coda is used: (begin, len) *)
    (fnargs,_,meminputs,memoutputs,memtemps)
    (subroutine_correct_th:thm) exec: term =

  let fnspec:term = concl subroutine_correct_th in
  let fnspec_quants,t = strip_forall fnspec in
  if name_of (last fnspec_quants) <> "returnaddress"
  then failwith "spec's last forall quantifier isn't 'returnaddress'?"
  else begin
  let (fnspec_globalasms:term),(fnspec_ensures:term) =
      if is_imp t then dest_imp t else `true`,t in

  let c_args = find_term
    (fun t -> is_comb t && let c,a = dest_comb t in
      name_of c = "C_ARGUMENTS")
      fnspec_ensures in
  let c_var_to_hol (var_c:string): string =
    let c_to_hol_vars = zip fnargs (dest_list (rand c_args)) in
    let c_to_hol_names = map (fun ((x,_,_),yvar) -> x,name_of yvar) c_to_hol_vars in
    try
      assoc var_c c_to_hol_names
    with _ -> failwith ("c_var_to_hol: unknown var in C: " ^ var_c) in

  let aligned_bytes_term = find_term
    (fun t -> is_comb t && fst (strip_comb t) = `aligned_bytes_loaded`)
      fnspec_ensures in
  let readsp: term option = try
      Some (find_term
        (fun t -> is_eq t && let l = fst (dest_eq t) in
          is_binary "read" l &&
          fst (dest_binary "read" l) = `SP`)
        fnspec_ensures)
    with _ -> None in
  let stack_access_size: int option = find_stack_access_size fnspec in
  assert ((readsp = None) = (stack_access_size = None));

  let elemsz_to_int (s:string): int =
    let s = if String.starts_with ~prefix:">=" s
      then String.sub s 2 (String.length s - 2) else s in
    try int_of_string s
    with _ -> failwith ("Don't know how to convert to int: " ^ s) in

  (* rename C variable names in meminputs, memoutputs and memtemps
     to the HOL Light vars in specs *)
  let (meminputs_hol:(string * string * int)list),
       memoutputs_hol, memtemps_hol =
    map (fun x,y,bsz -> c_var_to_hol x, y, bsz) meminputs,
    map (fun x,y,bsz -> c_var_to_hol x, y, bsz) memoutputs,
    map (fun x,y,bsz -> c_var_to_hol x, y, bsz) memtemps in
  let fnargs_hol : (string*string*string) list = map
    (fun x,y,z -> c_var_to_hol x, y, z) fnargs in

  (* memreads/writes without stackpointer and pc. *)
  let memreads:(term*term)list = map
      (fun (varname,range,elemty_size) ->
        find (fun t -> name_of t = varname) fnspec_quants,
        mk_small_numeral(elemsz_to_int range * elemty_size))
    (meminputs_hol @ memoutputs_hol @ memtemps_hol) in
  let memwrites = map (fun
      (varname,range,elemty_size) ->
        find (fun t -> name_of t = varname) fnspec_quants,
        mk_small_numeral(elemsz_to_int range * elemty_size))
    (memoutputs_hol @ memtemps_hol) in

  let usedvars = itlist (fun (t,_) l ->
    let vars = find_terms is_var t in union vars l) (memreads @ memwrites) [] in

  let f_events_args = usedvars @
    (match stack_access_size with
     | None -> [`pc:num`;`returnaddress:int64`]
     | Some sz ->
       let baseptr = subst [mk_small_numeral sz,`n:num`] `word_sub stackpointer (word n):int64` in
       [`pc:num`;baseptr;`returnaddress:int64`]) in
  let f_events = mk_var("f_events",
    itlist mk_fun_ty (map type_of f_events_args) `:(armevent)list`) in

  (* memreads,memwrites with stackpointer as well as pc :) *)
  let memreads,memwrites =
    match stack_access_size with
    | None -> memreads,memwrites
    | Some sz ->
      let baseptr = subst [mk_small_numeral sz,`n:num`] `word_sub stackpointer (word n):int64` in
      (memreads @ [baseptr,mk_small_numeral sz],
       memwrites @ [baseptr,mk_small_numeral sz]) in
  let memreads,memwrites =
    match coda_pc_range with
    | None -> memreads,memwrites
    | Some (pos,sz) ->
      let baseptr = subst [mk_small_numeral pos,`n:num`] `word_add (word pc) (word n):int64` in
      (memreads @ [baseptr,mk_small_numeral sz],
       memwrites @ [baseptr,mk_small_numeral sz]) in

  let s = mk_var("s",`:armstate`) in
  let precond = mk_gabs(s,
    list_mk_conj ([
      vsubst [s,`s:armstate`] aligned_bytes_term;
      `read PC s = word pc`;
      `read X30 s = returnaddress`;
    ] @
    (match readsp with
     | None -> []
     | Some t -> [
        vsubst [s,`s:armstate`] t;
     ]) @
    [ mk_comb (c_args, s);
      `read events s = e`;
    ])) in

  let postcond = mk_gabs(s,
    let mr = mk_list (map mk_pair memreads,`:int64#num`) in
    let mw = mk_list (map mk_pair memwrites,`:int64#num`) in
    let e2 = mk_var("e2",`:(armevent)list`) in
    mk_exists(e2,
      list_mk_conj [
        `read PC s = returnaddress`;
        `read events s = APPEND e2 e`;
        mk_eq(e2, list_mk_comb (f_events,f_events_args));
        mk_comb(mk_comb(mk_comb (`memaccess_inbounds`,e2),mr),mw)
      ])) in

  (* Filter unused forall vars *)
  let spec_without_quantifiers =
    let body = list_mk_icomb "ensures"
        [`arm`;precond;postcond;
        `\(s:armstate) (s':armstate). true`
        ] in
    if fnspec_globalasms = `true` then body
    else mk_imp(fnspec_globalasms,body) in
  let fnspec_quants_filtered =
    let fvars = frees spec_without_quantifiers in
    List.filter (fun t -> mem t fvars) fnspec_quants in
  mk_exists(f_events,
    list_mk_forall(fnspec_quants_filtered, spec_without_quantifiers))
  end;;

let REPEAT_GEN_AND_OFFSET_STACKPTR_TAC =
  W (fun (asl,w) ->
    (match find_stack_access_size w with
    | None -> REPEAT GEN_TAC
    | Some sz -> (REPEAT (W (fun (asl,w) ->
      let x,_ = dest_forall w in
      if name_of x = "stackpointer" then NO_TAC else GEN_TAC)) THEN
      WORD_FORALL_OFFSET_TAC sz THEN
      REPEAT GEN_TAC)) THEN
    REPEAT GEN_TAC);;

let DISCHARGE_MEMACCESS_INBOUNDS_TAC =
  ASM_REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN
  REWRITE_TAC[memaccess_inbounds;ALL;EX] THEN
    REPEAT CONJ_TAC THEN
      (REPEAT ((DISJ1_TAC THEN CONTAINED_TAC) ORELSE DISJ2_TAC ORELSE
              CONTAINED_TAC));;

let mk_freshvar =
  let n = ref 0 in
  fun ty ->
    let s = "trace_" ^ (string_of_int !n) in
    n := 1 + !n;
    mk_var(s,ty);;

let ABBREV_TRACE_TAC (stored_abbrevs:thm list ref)=
  let pat = `read events s = APPEND rhs e` in
  let PROVE_MEMORY_INBOUNDS_TAC (trace:term):tactic =
    fun (asl,w) ->
      let mem_inbounds_term =
        find_term
          (fun t -> name_of (fst (strip_comb t)) = "memaccess_inbounds")
          w in
      let c,_::readranges::writeranges::[] = strip_comb mem_inbounds_term in
      let new_mem_inbounds =
          list_mk_comb(c,trace::readranges::writeranges::[]) in
      (SUBGOAL_THEN new_mem_inbounds MP_TAC THENL [
        DISCHARGE_MEMACCESS_INBOUNDS_TAC THEN
        FAIL_TAC "could not prove memaccess_inbounds";
        ALL_TAC
      ] THEN DISCARD_MATCHING_ASSUMPTIONS [`memaccess_inbounds x rr wr`] THEN
      DISCH_TAC) (asl,w) in

  let CORE_ABBREV_TRACE_TAC (trace:term):tactic =
    fun (asl,w) ->
      let f_events_term =
        find_term
          (fun t -> name_of (fst (strip_comb t)) = "f_events")
          w in
      let fv,args = strip_comb f_events_term in
      let fv = mk_freshvar (type_of fv) in
      let newvarth = ref TRUTH in
       (ABBREV_TAC (mk_eq (fv,list_mk_abs(args,trace))) THEN
        POP_ASSUM (fun th ->
          newvarth := th; stored_abbrevs := th::!stored_abbrevs; ALL_TAC) THEN
        SUBGOAL_THEN (mk_eq (trace, list_mk_comb(fv,args))) MP_TAC THENL [
          (fun (asl,w) -> REWRITE_TAC[GSYM !newvarth] (asl,w)) THEN NO_TAC;
          ALL_TAC
        ] THEN
        DISCH_THEN SUBST_ALL_TAC)
      (asl,w) in

  (* Pick `read events .. = rhs`, show `memaccess_inbounds rhs [..] []`,
      and abbreviate it. *)
  RULE_ASSUM_TAC (CONV_RULE (TRY_CONV (
    (fun t -> check is_eq t; ALL_CONV t) THENC
    RAND_CONV CONS_TO_APPEND_CONV))) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [APPEND_ASSOC]) THEN
  fun (asl,w) ->
    let read_events = filter (fun (_,th) ->
      can (term_match [] pat) (concl th)) asl in
    match read_events with
    | [] -> failwith "No read events"
    | (_,read_event_th)::_ ->
      let trace_append,trace::_::[] = strip_comb (rhs (concl read_event_th)) in
      if name_of trace_append <> "APPEND" then failwith "unknown form" else
      (PROVE_MEMORY_INBOUNDS_TAC trace THEN
       CORE_ABBREV_TRACE_TAC trace)
      (asl,w);;

let PROVE_SAFETY_SPEC exec:tactic =
  W (fun (asl,w) ->
    let f_events = fst (dest_exists w) in
    let quantvars,forall_body = strip_forall(snd(dest_exists w)) in

    (* The destination PC *)
    let dest_pc_addr =
      let triple = if is_imp forall_body
        then snd (dest_imp forall_body) else forall_body in
      let _,(sem::pre::post::frame::[]) = strip_comb triple in
      let read_pc_eq = find_term (fun t -> is_eq t && is_read_pc (lhs t)) post in
      snd (dest_eq read_pc_eq) in

    X_META_EXISTS_TAC f_events THEN
    REWRITE_TAC[C_ARGUMENTS;ALL;ALLPAIRS;NONOVERLAPPING_CLAUSES;fst exec] THEN
    REWRITE_TAC[ALIGNED_BYTES_LOADED_APPEND_CLAUSE] THEN
    REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
    TRY DISCH_TAC THEN
    REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN

    ENSURES_INIT_TAC "s0" THEN

    let chunksize = 50 in
    let stored_abbrevs = ref [] in
    let i = ref 0 in
    let successful = ref true and finished = ref false in
    REPEAT (W (fun (asl,w) ->
      if !finished then NO_TAC else

      REPEAT_N chunksize (W (fun (asl,w) ->
        (* find 'read PC ... = ..' and check it reached at dest_pc_addr *)
        match List.find_opt (fun (_,th) ->
            is_eq (concl th) && is_read_pc (lhs (concl th)))
            asl with
        | None ->
          successful := false; finished := true; ALL_TAC
        | Some (_,read_pc_th) ->
          if rhs (concl read_pc_th) = dest_pc_addr
          then (* Successful! *) (finished := true; ALL_TAC)
          else (* Proceed *)
            let _ = i := !i + 1 in
            ARM_SINGLE_STEP_TAC exec ("s" ^ string_of_int !i)))
      THEN

      SIMPLIFY_MAYCHANGES_TAC THEN
      ABBREV_TRACE_TAC stored_abbrevs THEN CLARIFY_TAC)) THEN

    W (fun (asl,w) ->
      if not !successful
      then FAIL_TAC ("could not reach to the destination pc (" ^ (string_of_term dest_pc_addr) ^ ")")
      else ALL_TAC) THEN

    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    W (fun (asl,w) -> REWRITE_TAC(map GSYM !stored_abbrevs)) THEN

    X_META_EXISTS_TAC `e2:(armevent)list` THEN
    CONJ_TAC THENL [
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[APPEND] THEN UNIFY_REFL_TAC;
      ALL_TAC
    ] THEN
    (* e2 = f_events <public info> *)
    CONJ_TAC THENL [UNIFY_REFL_TAC; ALL_TAC] THEN
    (* memaccess_inbounds *)
    POP_ASSUM MP_TAC THEN
    W (fun (asl,w) -> REWRITE_TAC(APPEND :: (map GSYM !stored_abbrevs))) THEN
    NO_TAC);;

let ASSERT_GOAL_TAC (t:term): tactic =
  fun (asl,w) ->
    if t <> w then failwith "ASSERT_GOAL_TAC"
    else ALL_TAC (asl,w);;
