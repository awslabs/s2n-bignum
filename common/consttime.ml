(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(*   Common tactics for proving constant-time and memory-safety properties.  *)
(*  Assumes that this file will be loaded after necessary assembly semantics *)
(*  is loaded ({arm,x86}/proofs/...), as common/bignum.ml does).             *)
(* ========================================================================= *)

needs "common/equiv.ml";;
needs "common/safety.ml";;

(* Find the base pointer and access size. *)
let find_stack_access_size (fnspec_maychange:term): (term * int) option =
  try
    let stackptr = mk_var("stackpointer",`:int64`) in

    let t = find_term (fun t -> is_pair t &&
        let baseptr, sz = dest_pair t in
        baseptr = stackptr ||
        (is_binary "word_sub" baseptr &&
         let a,b = dest_binary "word_sub" baseptr in
         a = stackptr)) fnspec_maychange in
    let baseptr,sz = dest_pair t in
    Some (baseptr, dest_small_numeral sz)
  with Failure _ -> None;;

find_stack_access_size `MAYCHANGE [memory :> bytes (stackpointer,264)]`;;
find_stack_access_size `MAYCHANGE [memory :> bytes(z,8 * 8);
                    memory :> bytes(word_sub stackpointer (word 224),224)]`;;

(* Create a safety spec. This returns a safety spec using ensures, as well
   as the unversally quantified variables that are public information.

   NOTE: the output may need further edit if the variable for program counter
   is named other than 'pc' in subroutine_correct_th.
*)
let gen_mk_safety_spec
    ?(readonly_objects=([]:(term * term)list)) (* address(int64), size(num) list *)
    ?(extra_public_vars=([]:term list)) (* public scalars that are not sizes *)
    ~(keep_maychanges:bool)
    (fnargs,_,meminputs,memoutputs,memtemps)
    (subroutine_correct_th:thm) exec
    (find_eq_stackpointer:term->bool)
    (find_eq_returnaddress:term->bool): term*(term list) =

  (* The stack pointer variable is assumed to be called stackpointer below,
     so rename it if the correctness theorem calls it differently. *)
  let subroutine_correct_th =
    try
      let vs,body = strip_forall (concl subroutine_correct_th) in
      let ens = if is_imp body then snd(dest_imp body) else body in
      let pre = snd(dest_abs(el 1 (snd(strip_comb ens)))) in
      let v = rhs (find_term find_eq_stackpointer pre) in
      if is_var v && mem v vs && name_of v <> "stackpointer" then
        let vs' = map (fun u -> if u = v then mk_var("stackpointer",type_of u)
                                else u) vs in
        GENL vs' (SPECL vs' subroutine_correct_th)
      else subroutine_correct_th
    with Failure _ -> subroutine_correct_th in

  (* Likewise the program counter is assumed to be called pc, so rename it if
     the correctness theorem calls it differently, e.g. pc2 in a core. *)
  let subroutine_correct_th =
    try
      let vs,body = strip_forall (concl subroutine_correct_th) in
      let ens = if is_imp body then snd(dest_imp body) else body in
      let pre = snd(dest_abs(el 1 (snd(strip_comb ens)))) in
      let pc_of t =
        let c,args = strip_comb t in
        if is_const c &&
           mem (name_of c) ["bytes_loaded"; "aligned_bytes_loaded"] &&
           length args = 3 then rand(el 1 args) else failwith "pc_of" in
      let v = pc_of (find_term (can pc_of) pre) in
      let pcv = mk_var("pc",type_of v) in
      if is_var v && mem v vs && starts_with "pc" (name_of v) &&
         name_of v <> "pc" && not(mem pcv vs) then
        let vs' = map (fun u -> if u = v then pcv else u) vs in
        GENL vs' (SPECL vs' subroutine_correct_th)
      else subroutine_correct_th
    with Failure _ -> subroutine_correct_th in

  (* Decompose the functional correctness. *)
  let fnspec:term = concl subroutine_correct_th in
  let fnspec_quants,t = strip_forall fnspec in
  let (fnspec_globalasms:term),(fnspec_ensures:term) =
      if is_imp t then dest_imp t else `true`,t in
  let arch_const::fnspec_precond::fnspec_postcond::fnspec_maychanges::[] =
      snd (strip_comb fnspec_ensures) in
  let fnspec_precond_bvar,fnspec_precond = dest_abs fnspec_precond in
  let fnspec_postcond_bvar,fnspec_postcond = dest_abs fnspec_postcond in
  (* :x86state or :armstate *)
  let state_ty = fst (dest_fun_ty (type_of arch_const)) in

  let c_args = find_term
    (fun t -> is_comb t && let c,a = dest_comb t in
      name_of c = "C_ARGUMENTS")
      fnspec_precond in
  let c_var_to_hol (var_c:string): term =
    let c_to_hol_vars = zip fnargs (dest_list (rand c_args)) in
    let c_to_hol_vars = map (fun ((x,_,_),yvar) -> x,yvar) c_to_hol_vars in
    try
      assoc var_c c_to_hol_vars
    with Failure _ -> failwith ("c_var_to_hol: unknown var in C: " ^ var_c) in

  let bytes_loaded_terms = find_terms
    (fun t -> is_comb t &&
        let bytes_loaded,args = strip_comb t in
        let name = name_of bytes_loaded in
        (name = "bytes_loaded" || name = "aligned_bytes_loaded") &&
        List.length args = 3)
      fnspec_precond in
  let (bytes_loaded_mc::[]),bytes_loaded_others = List.partition (fun t ->
      let _::pc::_ = snd (strip_comb t) in
      let word_const,pc_var = dest_comb pc in
      starts_with "pc" (name_of pc_var))
    bytes_loaded_terms in
  let read_sp_eq: term option = try
      Some (find_term find_eq_stackpointer fnspec_precond)
    with Failure _ -> None in
  let stack_access_size: (term*int) option =
      find_stack_access_size fnspec_maychanges in
  assert ((read_sp_eq = None) = (stack_access_size = None));

  let returnaddress_var:term option =
    List.find_opt (fun t -> name_of t = "returnaddress") fnspec_quants in
  let read_x30_eq: term option = try
      Some (find_term find_eq_returnaddress fnspec_precond)
    with Failure _ -> None in

  (* An expression s to a term of :num type. Besides numerals, variables and
     max(a,b), it may use parentheses and the binary operators + - * and /
     (as DIV), with the precedences and left associativity of C. *)
  let rec elemsz_to_hol (s:string): term =
    let s = String.trim s in
    let s = if starts_with ">=" s
      then String.trim (String.sub s 2 (String.length s - 2)) else s in
    let l = String.length s in

    (* The index of the last of the characters cs in str outside parentheses *)
    let find_op (str:string) cs =
      let rec go i depth =
        if i < 0 then None else
        match String.get str i with
        | ')' -> go (i - 1) (depth + 1)
        | '(' -> go (i - 1) (depth - 1)
        | c -> if depth = 0 && mem c cs then Some i else go (i - 1) depth in
      go (String.length str - 1) 0 in

    let op_idx = match find_op s ['+';'-'] with
      | None -> find_op s ['*';'/']
      | idx -> idx in

    match op_idx with
    | Some idx ->
      let expr_lhs = String.sub s 0 idx in
      let expr_rhs = String.sub s (idx+1) (l - idx - 1) in
      let op = match String.get s idx with
        | '/' -> "DIV"
        | c -> String.make 1 c in
      mk_binary op (elemsz_to_hol expr_lhs, elemsz_to_hol expr_rhs)
    | None ->
     if l > 2 && String.get s 0 = '(' && String.get s (l - 1) = ')' then
       elemsz_to_hol (String.sub s 1 (l - 2))
     else if starts_with "max(" s && l > 5 && String.get s (l - 1) = ')' then
       let args = String.sub s 4 (l - 5) in
       (match find_op args [','] with
        | Some i ->
          let a = String.sub args 0 i
          and b = String.sub args (i + 1) (String.length args - i - 1) in
          mk_binary "MAX" (elemsz_to_hol a, elemsz_to_hol b)
        | None -> failwith ("elemsz_to_hol: cannot parse " ^ s))
     else
     (try mk_small_numeral (int_of_string s)
      with Failure _ ->
        let v = c_var_to_hol s in
        match dest_type (type_of v) with
        | ("num",_) -> v
        | _ -> (* word ty *) mk_icomb (`val:(N)word->num`,v)) in

  (* memreads/writes without stackpointer and pc; (base pointer, size) list. *)
  let (memreads:(term*term)list), (memwrites:(term*term)list) =
    let fn =
      (fun (c_varname,range,elemty_size) ->
        c_var_to_hol c_varname,
        (try mk_small_numeral (elemty_size * int_of_string range)
         with Failure _ ->
           mk_binary "*" (elemsz_to_hol range, mk_small_numeral elemty_size))) in

    map fn (meminputs @ memoutputs @ memtemps),
    map fn (memoutputs @ memtemps) in

  (* Variables describing public information. *)
  let public_vars = itlist (fun (baseptr,sz) l ->
    let pvars = find_terms is_var baseptr in
    let szvars = find_terms is_var sz in
    union (union pvars l) szvars) (memreads @ memwrites) [] in
  let public_vars = public_vars @ subtract extra_public_vars public_vars in

  (* Create the f_events var as well as expressions (not necessarily var)
     as args of f_events containing public information *)
  let f_events_public_args = public_vars @
    ((* If _mc takes extra arguments, which can happen when it is taking
        the addresses of readonly objects, add them *)
      let the_mc = rand bytes_loaded_mc in
      if is_const the_mc then []
      else begin
        let the_mc_fn, addr_args = strip_comb the_mc in
        filter (fun t -> is_var t && name_of t <> "pc") addr_args
      end
    ) @
    (match stack_access_size with
     | None -> [`pc:num`] @ (match returnaddress_var with Some v -> [v] | None -> [])
     | Some (baseptr,sz) ->
       [`pc:num`;baseptr] @ (match returnaddress_var with Some v -> [v] | None -> [])) in
  let f_events = mk_var("f_events",
    itlist mk_fun_ty (map type_of f_events_public_args) `:(uarch_event)list`) in

  (* memreads,memwrites with stackpointer as well as pc :)
    These will be the arguments of memaccess_inbounds.
  *)
  let memreads,memwrites =
    match stack_access_size with
    | None -> memreads,memwrites
    | Some (baseptr,sz) ->
      (* Further regions at fixed offsets from the stack pointer, e.g. a slot
         of the frame of the caller of a core *)
      let stackptr = mk_var("stackpointer",`:int64`) in
      let others = setify (find_terms (fun t -> is_pair t &&
          let b,_ = dest_pair t in
          is_binary "word_add" b && fst(dest_binary "word_add" b) = stackptr)
        fnspec_maychanges) in
      let others = map dest_pair others in
      (memreads @ [baseptr,mk_small_numeral sz] @ others,
       memwrites @ [baseptr,mk_small_numeral sz] @ others) in
  (* coda *)
  let memreads,memwrites =
    let the_mc = rand bytes_loaded_mc in
    if is_binary "APPEND" the_mc then
      let code_mc,data_mc = dest_binary "APPEND" the_mc in
      let baseptr = subst [code_mc,`b:((8)word)list`]
        `word (pc + LENGTH (b:((8)word)list)):int64` in
      let len = subst [data_mc,`b:((8)word)list`] `LENGTH (b:((8)word)list)` in
      (memreads @ [baseptr,len], memwrites)
    else
      memreads,memwrites in
  (* rodata *)
  let memreads,memwrites =
    let _ = List.iter (fun (addr,sz) ->
        if not (can dest_word_ty (type_of addr)) then
          failwith ("rodata: not a int64 ty: " ^ (string_of_term addr)))
        readonly_objects in
    (memreads @ readonly_objects),memwrites in
  (* Remove duplicates *)
  let memreads,memwrites =
    let rec dedup l =
      match l with
      | h::t -> if mem h t then dedup t else h::(dedup t)
      | h::[] -> [h]
      | [] -> []
    in
    rev (dedup (rev memreads)),
    rev (dedup (rev memwrites)) in

  let s = mk_var("s",state_ty) in
  let precond =
    let read_pc_eq = find_term (fun t -> is_eq t && is_read_pc (lhs t))
        fnspec_precond in
    let read_pc_eq = vsubst [s,fnspec_precond_bvar] read_pc_eq in
    mk_gabs(s,
      list_mk_conj ([
        vsubst [s,s] bytes_loaded_mc;
        read_pc_eq;
      ] @
      bytes_loaded_others @
      (match read_sp_eq with | None -> [] | Some t -> [ vsubst [s,s] t ]) @
      (match read_x30_eq with | None -> [] | Some t -> [ vsubst [s,s] t ]) @
      [ mk_comb (c_args, s); `read events s = e`; ])) in

  let postcond = mk_gabs(s,
    let mr = mk_list (map mk_pair memreads,`:int64#num`) in
    let mw = mk_list (map mk_pair memwrites,`:int64#num`) in
    let e2 = mk_var("e2",`:(uarch_event)list`) in
    let read_pc_eq = find_term (fun t -> is_eq t && is_read_pc (lhs t))
        fnspec_postcond in
    (* Keep a disjunction of the possible final PCs, as for a program with
       several exits (without repetitions, as all exits of a subroutine
       return to the same address). *)
    let read_pc_eq =
      try let c = find (fun c -> is_disj c &&
                    forall (fun d -> is_eq d && is_read_pc (lhs d))
                      (disjuncts c))
                    (conjuncts fnspec_postcond) in
          let rec nodups l =
            match l with [] -> [] | h::t -> h::nodups (filter ((<>) h) t) in
          let ds = disjuncts c in
          let ds' = nodups ds in
          if length ds' = length ds then c else list_mk_disj ds'
      with Failure _ -> read_pc_eq in
    let read_pc_eq = vsubst [s,fnspec_postcond_bvar] read_pc_eq in
    mk_conj (
      read_pc_eq, (* put read_pc_eq out, so that specialized Hoare rule tactics
                     can work well *)
      mk_exists(e2,
        list_mk_conj [
          `read events s = APPEND e2 e`;
          mk_eq(e2, list_mk_comb (f_events,f_events_public_args));
          mk_comb(mk_comb(mk_comb (`memaccess_inbounds`,e2),mr),mw)
        ]))) in

  (* Filter unused forall vars *)
  let spec_without_quantifiers =
    let maychanges = if keep_maychanges then fnspec_maychanges
      else mk_abs(mk_var("s",state_ty), mk_abs(mk_var("s'",state_ty), `true`))
      in
    let body = list_mk_icomb "ensures"
        [arch_const;precond;postcond;maychanges] in
    (* Drop the assumptions that only constrain variables the safety property
       does not mention, such as a < n for the input values a and n *)
    let asms = filter (fun c ->
        let vs = intersect (frees c) fnspec_quants in
        vs = [] || intersect vs (frees body) <> [])
      (conjuncts fnspec_globalasms) in
    if fnspec_globalasms = `true` || asms = [] then body
    else mk_imp(list_mk_conj asms,body) in
  let the_e_var = mk_var("e", `:(uarch_event)list`) in
  let fnspec_quants_filtered =
    let fvars = frees spec_without_quantifiers in
      the_e_var::List.filter (fun t -> mem t fvars) fnspec_quants in

  (* Return the spec, as well as the HOL Light variables having public info *)
  (mk_exists(f_events,
    list_mk_forall(fnspec_quants_filtered, spec_without_quantifiers)),
   the_e_var::`pc:num`::public_vars @ (match returnaddress_var with Some v -> [v] | None -> []) @
      (if read_sp_eq = None then [] else [`stackpointer:int64`]));;

let REPEAT_GEN_AND_OFFSET_STACKPTR_TAC =
  W (fun (asl,w) ->
    (match find_stack_access_size w with
    | None -> REPEAT GEN_TAC
    | Some (baseptr,sz) ->
      if is_binary "word_sub" baseptr then
        (REPEAT (W (fun (asl,w) ->
        let x,_ = dest_forall w in
        if name_of x = "stackpointer" then NO_TAC else GEN_TAC)) THEN
        WORD_FORALL_OFFSET_TAC sz THEN
        REPEAT GEN_TAC)
      else if is_var baseptr then GEN_TAC
      else failwith
        ("Don't know how to rebase offset of stackptr " ^
         (string_of_term baseptr))) THEN
    REPEAT GEN_TAC);;

(* Given a conclusion which is
  memaccess_inbounds [..(events)..] [..] [] where events is a list of
  Event* constructors (EventJump, EventLoad, ...), discharge the goal.
*)
let DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC =
  REWRITE_TAC[MESON[APPEND]`APPEND ([]:(A)list) [] = []`] THEN
  REWRITE_TAC[memaccess_inbounds;ALL;EX] THEN
  (* CONTAINED_TAC works for contained_modulo *)
  REWRITE_TAC[contained;DIMINDEX_64] THEN
  REPEAT CONJ_TAC THEN
    (TRY
      (REPEAT ((DISJ1_TAC THEN CONTAINED_TAC) ORELSE DISJ2_TAC ORELSE
            CONTAINED_TAC) THEN NO_TAC));;

let DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC:tactic =
  let try_discharge (meminb_th:thm):tactic =
    UNDISCH_TAC (concl meminb_th) THEN
    ASM_REWRITE_TAC[] THEN (* to expand "e2" *)
    (* this is sometimes needed *)
    REWRITE_TAC[APPEND;APPEND_NIL] THEN
    (* at this point, simple goals must have been already proven *)
    (* A more general case *)
    ((MATCH_MP_TAC MEMACCESS_INBOUNDS_MEM THEN
      REWRITE_TAC[ALL;MEM] (* this must resolve all ALL (\x. MEM ..) goals *)
      THEN
      NO_TAC) ORELSE
    (* Even more general case *)
    (MATCH_MP_TAC MEMACCESS_INBOUNDS_CONTAINED THEN
      DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN
      NO_TAC)) in

  (* try for each memaccess_inbounds assumption *)
  W (fun (asl,w) ->
    let meminbounds = map snd (filter (fun (_,th) ->
          let cth = concl th in
          is_comb cth &&
          name_of (fst (strip_comb cth)) = "memaccess_inbounds")
        asl) in
    if meminbounds = [] then
      failwith "No memaccess_inbounds assumption" else
    end_itlist (fun tac1 tac2 -> tac1 ORELSE tac2)
      (map try_discharge meminbounds));;

let DISCHARGE_MEMACCESS_INBOUNDS_TAC =
  let cons_to_append_th =
      MESON[APPEND]
        `memaccess_inbounds (CONS a b) = memaccess_inbounds (APPEND [a] b)` in
  let append_nil_th =
      MESON[APPEND]
        `memaccess_inbounds (APPEND [] b) = memaccess_inbounds b /\
         memaccess_inbounds (APPEND (APPEND [] []) b) = memaccess_inbounds b` in

  let rec main_tac (asl,w) =
    (* Case 1. If the exactly same memaccess_inbounds exists as assumption,
      just use it. *)
    ((DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC) ORELSE

    (* Case 2. if the goal is simply a concrete list of events, use an
      existing tactic. *)
    (DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC) ORELSE

    (* Case 3. If the goal consist of memaccess_inbounds of a previous trace which
      can be discharged by assumption, followed by a concrete events list,
      apply MEMACCESS_INBOUNDS_APPEND and prove it *)
      (* Move the inner CONS to the outermost place *)
    (REWRITE_TAC[CONJUNCT2 APPEND] THEN
      (* Convert the CONS sequence in the first argument of memaccess_inbounds to
        APPEND *)
      CONV_TAC ((RATOR_CONV o RATOR_CONV o RAND_CONV) CONS_TO_APPEND_CONV) THEN

      GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN
      CONJ_TAC THENL [
        (* The new, concrete event trace. *)
        DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN
        (if !safety_print_log then
          PRINT_TAC
            "DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC left this, retracting..."
          THEN PRINT_GOAL_TAC
        else ALL_TAC) THEN NO_TAC;
        (* The existing event trace. *)
        REWRITE_TAC[append_nil_th] THEN
        main_tac (* recursively call *)
        THEN NO_TAC
      ]) ORELSE

      (* Case 4. Reverse of case3 :
        memaccess_inbounds (APPEND f_events <concrete events>) ... *)
    (GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN
      CONJ_TAC THENL [
        (* The existing event trace. *)
        main_tac THEN NO_TAC; (* recursively call *)
        (* The new, concrete event trace. *)
        DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN
        (if !safety_print_log then
          PRINT_TAC
            "DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC left this, retracting..."
          THEN PRINT_GOAL_TAC
        else ALL_TAC) THEN NO_TAC;
      ]) ORELSE

    (* Case 5: memaccess_inbounds (APPEND e1 e2) ... where e1 and e2 are
       somewhat complex. Restrict to the case when e1 could be discharged with
       DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC. Kind of case 3+4. *)
    (GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN
      CONJ_TAC THENL [
        (* The existing event trace. *)
        DISCHARGE_MEMACCESS_INBOUNDS_USING_ASM_TAC; (* recursively call *)
        (* The new, concrete event trace. *)
        main_tac;
      ] THEN NO_TAC)) (asl,w)
  in
  (* Remove all vacuous appends *)
  REWRITE_TAC[CONJUNCT1 APPEND; APPEND_NIL] THEN
  (* start! *)
  (main_tac ORELSE
   (PRINT_GOAL_TAC THEN
    FAIL_TAC
      ("DISCHARGE_MEMACCESS_INBOUNDS_TAC could not identify the pattern. " ^
      "Please check whether the event list in assumption matches the event " ^
      "list in the conclusion")));;

let mk_freshvar =
  let n = ref 0 in
  fun ty ->
    let s = "trace_" ^ (string_of_int !n) in
    n := 1 + !n;
    mk_var(s,ty);;

let ABBREV_TRACE_TAC (stored_abbrevs:thm list ref)=
  let pat = `read events s = e` in

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
      let r = rhs (concl read_event_th) in
      (if is_comb r then
        let trace_append,trace::_::[] = strip_comb r in
        if name_of trace_append <> "APPEND" then failwith "unknown form" else
        (PROVE_MEMORY_INBOUNDS_TAC trace THEN
        CORE_ABBREV_TRACE_TAC trace)
      else
        (* It seems the event list is already well-abbreviated; return *)
        ALL_TAC)
      (asl,w);;

let rec WHILE_TAC (flag:bool ref) tac w =
  (if !flag then tac THEN WHILE_TAC flag tac else ALL_TAC) w;;

(* public_vars describe the HOL Light variables that will contain public
   information. This is for faster symbolic simulation. *)
let GEN_PROVE_SAFETY_SPEC_TAC =
  let pth =
    prove(`forall (e:(uarch_event)list) e2.
        e = APPEND e2 e <=> APPEND [] e = APPEND e2 e`,
    MESON_TAC[APPEND]) in
  let qth =
    prove(`memaccess_inbounds [] [] []`, MESON_TAC[memaccess_inbounds;ALL]) in

  let mainfn ?(public_vars:term list option)
    ?(tac_before_maychange_simp:tactic option) exec
    (extra_unpack_thms:thm list) single_step_tac
    :tactic =

    REWRITE_TAC[C_ARGUMENTS;ALL;ALLPAIRS;SOME_FLAGS;fst exec] THEN
    REWRITE_TAC extra_unpack_thms THEN

    W (fun (asl,w) ->
      let f_events = fst (dest_exists w) in
      let quantvars,forall_body = strip_forall(snd(dest_exists w)) in
      let stored_abbrevs = ref [] in

      if quantvars = [] || hd quantvars <> `e:(uarch_event)list`
      then failwith "The goal must be `exists f_events. forall e ...`" else

      (* The destination PC *)
      let dest_pc_addr =
        let triple = if is_imp forall_body
          then snd (dest_imp forall_body) else forall_body in
        let _,(sem::pre::post::frame::[]) = strip_comb triple in
        let read_pc_eq = find_term (fun t -> is_eq t && is_read_pc (lhs t)) post in
        snd (dest_eq read_pc_eq) in

      X_META_EXISTS_TAC f_events THEN
      REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
      TRY DISCH_TAC THEN
      REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN

      ENSURES_INIT_TAC "s0" THEN
      (* Drop any 'read .. = ..' statement that does not have any public_var *)
      (match public_vars with
      | None -> ALL_TAC
      | Some public_vars ->
        DISCARD_ASSUMPTIONS_TAC (fun th ->
            let t = concl th in
            is_eq t && is_binary "read" (lhs t) &&
            intersect (frees t) public_vars = [])) THEN

      let chunksize = 50 in
      let i = ref 0 in
      let successful = ref true and hasnext = ref true in
      WHILE_TAC hasnext (W (fun (_,_) ->
        REPEAT_N chunksize (W (fun (asl,w) ->
          (* find 'read RIP/PC ... = ..' and check it reached at dest_pc_addr *)
          match List.find_opt (fun (_,th) ->
              is_eq (concl th) && is_read_pc (lhs (concl th)))
              asl with
          | None ->
            successful := false; hasnext := false; ALL_TAC
          | Some (_,read_pc_th) ->
            if rhs (concl read_pc_th) = dest_pc_addr
            then (* Successful! *) (hasnext := false; ALL_TAC)
            else (* Proceed *)
              let _ = i := !i + 1 in
              single_step_tac exec ("s" ^ string_of_int !i)))
        THEN

        (match tac_before_maychange_simp with
         | Some tac -> tac | None -> ALL_TAC) THEN
        SIMPLIFY_MAYCHANGES_TAC THEN
        ABBREV_TRACE_TAC stored_abbrevs THEN CLARIFY_TAC)) THEN

      W (fun (asl,w) ->
        if not !successful
        then FAIL_TAC ("could not reach to the destination pc (" ^ (string_of_term dest_pc_addr) ^ ")")
        else ALL_TAC) THEN

      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[] THEN
      W (fun (asl,w) -> REWRITE_TAC(map GSYM !stored_abbrevs)) THEN

      (* e2 can be []! *)
      REWRITE_TAC[pth] THEN
      (X_META_EXISTS_TAC `e2:(uarch_event)list` ORELSE
       (PRINT_GOAL_TAC THEN FAIL_TAC "Not `exists e2. ...`?")) THEN
      CONJ_TAC THENL [
        AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[APPEND] THEN UNIFY_REFL_TAC;
        ALL_TAC
      ] THEN
      (* e2 = f_events <public info> *)
      CONJ_TAC THENL [UNIFY_REFL_TAC; ALL_TAC] THEN
      (* memaccess_inbounds *)
      (ACCEPT_TAC qth ORELSE
      (POP_ASSUM MP_TAC THEN
       W (fun (asl,w) -> REWRITE_TAC(APPEND :: (map GSYM !stored_abbrevs))) THEN
       PRINT_GOAL_TAC THEN FAIL_TAC "Could not prove memaccess_inbounds")))
  in mainfn;;

let ASSERT_CONCL_TAC (t:term): tactic =
  PRINT_GOAL_TAC THEN
  fun (asl,w) ->
    if t <> w then
      (let _ = Printf.printf "%s\n" (string_of_term t) in
       failwith "ASSERT_CONCL_TAC") (asl,w)
    else ALL_TAC (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Tactics corresponding to Hoare rules.                                     *)
(* ------------------------------------------------------------------------- *)

(*monomorphic type annotation to avoid value-restriction weak vars in generated files*)
let allowed_vars_e : term list ref = ref [];;

let NIL_IMPLIES_APPEND_EQ =
  prove(`forall (l:(A)list) m m'. m = m' /\ [] = l ==> m = APPEND l m'`,
    MESON_TAC[APPEND]);;

(* Given a goal `|- ... = APPEND e2 e` where e2 is a meta variable,
   try to unify e2 with the (part of) LHS. *)
let EXISTS_E2_TAC allowed_vars_e =
  (* it could be NIL *)
  (MATCH_MP_TAC NIL_IMPLIES_APPEND_EQ THEN CONJ_TAC THENL [
    REFL_TAC;
    SAFE_UNIFY_REFL_TAC allowed_vars_e
      (ref ["f_events_callee"(* allow callee's f_events *)])
  ]) ORELSE
  (* Apply CONS_TO_APPEND_CONV to the heads of the events *)
  (CONV_TAC (TRY_CONV (LAND_CONV CONS_TO_APPEND_CONV)) THEN
   TRY (GEN_REWRITE_TAC LAND_CONV [APPEND_ASSOC]) THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   SAFE_UNIFY_REFL_TAC allowed_vars_e
     (ref ["f_events_callee"(* allow callee's f_events *)])) ORELSE
  (* When the goal is
     CONS(CONS(...(APPEND a (CONS(CONS(... e)))))) = APPEND e2 e
     May appear when dealing with register spills in subroutines
  *)
  (CONV_TAC (TRY_CONV (LAND_CONV (ONCE_DEPTH_CONV CONS_TO_APPEND_CONV))) THEN
   CONV_TAC (TRY_CONV (LAND_CONV (ONCE_DEPTH_CONV CONS_TO_APPEND_CONV))) THEN
   GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV) [APPEND_ASSOC] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   SAFE_UNIFY_REFL_TAC allowed_vars_e
    (ref ["f_events_callee"(* allow callee's f_events *)]));;

(* Given a goal
  `|- exists f_events. forall ...
        ensures .. (..) (\s. exists e2. expr(f_events)) ..`
  Come up with a new subgoal
  `|- exists f_ev1 f_ev2 f_ev3 ....
      forall ...
        ensures .. (..) (\s. exists e2. expr(concrete_f_events)) ..`
  where concrete_f_events is an argument and f_evN are free variables having
  function types in concrete_f_events,
  and prove the original goal, leaving only one subgoal.
*)
let CONCRETIZE_F_EVENTS_TAC (concrete_f_events:term): tactic =
  fun (asl,w) ->
    let old_f_events,body = dest_exists w in
    let f_events_ty = type_of old_f_events in
    if f_events_ty <> type_of concrete_f_events
    then failwith
      ("type of old f_events and new f_events mismatch:" ^
        (string_of_type f_events_ty) ^ " vs. " ^
        (string_of_type (type_of concrete_f_events)))
      else
    (* The f_events vars; they will be existentially quantified *)
    let free_f_events = frees concrete_f_events in
    (* Do sanity check *)
    let _ = List.iter (fun t ->
        if not (starts_with "f_ev" (name_of t))
        then failwith
          ("This free variable does not start with 'f_ev'; is it a function " ^
           "that returns a list of uarch_events?") else
        let tty = type_of t in
        try let _ = dest_fun_ty tty in ()
        with Failure _ -> failwith "This is not a function type")
      free_f_events in
    let new_goal = subst [concrete_f_events,old_f_events] body in
    let new_goal = list_mk_exists (free_f_events, new_goal) in
    (SUBGOAL_THEN new_goal MP_TAC THENL [
      BETA_TAC;
      STRIP_TAC THEN EXISTS_TAC concrete_f_events THEN ASM_REWRITE_TAC[] THEN
      PRINT_GOAL_TAC THEN NO_TAC
    ]) (asl,w);;

(* Given a goal
  `.. |- ensures _
          (\s. .. /\ exists e2.
              read events s = APPEND e2 e /\
              e2 = e_tail /\
              memaccess_inbounds e2 [..])
          (\s. .. /\ exists e2.
              read events s = APPEND e2 e /\
              e2 = APPEND e_back (APPEND e_front e_tail) /\
              memaccess_inbounds e2 [...])
          (..)`,
  apply ENSURES_SEQUENCE_TAC by creating a new invariant from inv such that
  if inv is `\s. P s`, the new invariant is
  `\s. P s /\
       exists e2.
         read events s = APPEND e2 e /\
         e2 = APPEND e_front e_tail /\
         memaccess_inbounds e2 [...]`
*)
let ENSURES_EVENTS_SEQUENCE_TAC (pc:term) (inv:term): tactic =
  let var_e2 = mk_var("e2",`:(uarch_event)list`) in
  let find_e2_def (pred:term) : term*term*term =
    let t_exists_e2 = find_term
      (fun t -> is_exists t && fst (dest_exists t) = var_e2)
      pred in
    let clause1,e2_equals,clause3 =
      match conjuncts (snd (dest_exists t_exists_e2)) with
        [clause1;e2_equals;clause3] -> clause1,e2_equals,clause3
      | _ -> failwith "find_e2_def: expected three conjuncts" in

    if not (is_eq e2_equals)
    then failwith ("expected `e2 = ...`, but got " ^
                   (string_of_term e2_equals)) else
    let the_def = rhs e2_equals in
    (clause1,the_def,clause3)
  and is_nil (t:term): bool = is_const t && name_of t = "NIL" in

  fun (asl,w) ->
    let t_ensures,args = strip_comb w in
    if name_of t_ensures <> "ensures" then failwith "not ensures" else
    let t_arm,precond,postcond =
      match args with
        t_arm::precond::postcond::_::[] -> t_arm,precond,postcond
      | _ -> failwith "expected ensures with four arguments" in

    (* extract the 'e2 = APPEND ...' subterm, from 'exists e2. ...'. *)
    let clause1,e2_def_post,clause3 = find_e2_def postcond in

    if not (is_comb e2_def_post) ||
        name_of (fst (strip_comb e2_def_post)) <> "APPEND"
    then failwith ("expected `e2 = APPEND ..`, but got " ^
        (string_of_term e2_def_post)) else

    let e_back,e_front_tail =
      match snd (strip_comb e2_def_post) with
        [e_back;e_front_tail] -> e_back,e_front_tail
      | _ -> failwith "ENSURES_EVENTS_SEQUENCE_TAC: expected APPEND _ _" in

    let e2_def_pre = try Some (find_e2_def precond) with Failure _ -> None in
    let _ = match e2_def_pre with
      | Some (_,e2_def_pre,_) ->
        if not (is_nil e2_def_pre ||
          (is_binary "APPEND" e_front_tail && rand e_front_tail = e2_def_pre))
        then failwith ("e2 in postcond must start with e2 in precond!")
      | None -> () in

    (* Let's discard e_back, and use e_front to reconstruct 'exists e2. ...'! *)
    let new_exists_e2 = mk_exists (var_e2,
      list_mk_conj [clause1;mk_eq(var_e2,e_front_tail);clause3]) in
    let new_inv = let bvar,body = dest_abs inv in
      mk_abs(bvar,mk_conj(body,new_exists_e2)) in
    ENSURES_SEQUENCE_TAC pc new_inv (asl,w);;

(* Given a goal
  `.. |- ensures _ (\s. ..)
          (\s. .. /\ exists e2.
              read events s = APPEND e2 e /\
              e2 = APPEND
                (APPEND e_back
                  (APPEND (ENUMERATEL n e_loop)
                          (APPEND e_front))
                e_prev) /\
              memaccess_inbounds e2 [...])
          (..)`,
  where
  (1) e_back is the event trace from conditional branch to the postcondition,
  (2) e_front is the event trace from precondition to the first instruction of
      loop body,
  (3) e_loop is the event trace of the loop body, and
  (4) e_prev is the event trace until the precondition (e_prev can be omitted)
  apply ENSURES_WHILE_{A}UP2_TAC by creating a new loop invariant from loop_inv
  such that, if loop_inv is `\i s. P i s`, the new invariant is
  `\i s. P i s /\
       exists e2.
         read events s = APPEND e2 e /\
         e2 = APPEND (ENUMERATEL i e_loop) (APPEND e_front e_prev) /\
         memaccess_inbounds e2 [...]`

  NOTE: For WHILE tactics involving events, only one version is provided:
  ENSURES_EVENTS_WHILE_UP2_TAC . This is because automated constant-time tactics
  are tailored to the output of ENSURES_EVENTS_WHILE_UP2_TAC.
  Proofs that use other variants like ENSURES_WHILE_AUP_TAC,
  ENSURES_WHILE_ADOWN_TAC must be slightly modified to use
  ENSURES_EVENTS_WHILE_UP2_TAC.
*)
let ENSURES_EVENTS_WHILE_UP2_TAC =
  let mk_new_inv loop_inv (itrbegin:term option) (numitr:term option) (asl,w) =
    let t_ensures,args = strip_comb w in
    if name_of t_ensures <> "ensures" then failwith "not ensures" else
    let t_arm,precond,postcond =
      match args with
        t_arm::precond::postcond::_::[] -> t_arm,precond,postcond
      | _ -> failwith "expected ensures with four arguments" in

    (* extract the 'e2 = APPEND ...' subterm, from 'exists e2. ...'. *)
    let var_e2 = mk_var("e2",`:(uarch_event)list`) in
    let t_exists_e2 = find_term
      (fun t -> is_exists t && fst (dest_exists t) = var_e2)
      postcond in
    let t_exists_e2_in_pre = can (find_term
      (fun t -> is_exists t && fst (dest_exists t) = var_e2)) precond in
    let clause1,e2_equals,clause3 =
      match conjuncts (snd (dest_exists t_exists_e2)) with
        [clause1;e2_equals;clause3] -> clause1,e2_equals,clause3
      | _ -> failwith "find_e2_def: expected three conjuncts" in

    let failmsg () =
      if t_exists_e2_in_pre then
        failwith
          ("expected `e2 = APPEND (APPEND <epilogue> (APPEND (ENUMERATEL n " ^
           "<loopiter>) <prologue>)) ...`, but got " ^
           (string_of_term e2_equals))
      else failwith
        ("expected `e2 = APPEND <epilogue> (APPEND (ENUMERATEL n <loopiter>) " ^
         "<prologue>)`, but got " ^
            (string_of_term e2_equals)) in

    let the_enumeratel,counter,e_loop,e_front,(e_prev_trace:term option) =
      try
        let the_append = snd (dest_eq e2_equals) in
        let the_append,e_prev_trace =
          if t_exists_e2_in_pre then
            let e,e_prev_trace = dest_binary "APPEND" the_append in
            (e,Some e_prev_trace)
          else the_append,None in
        let e_back,e_middle = dest_binary "APPEND" the_append in
        let e_enumeratel,e_front = dest_binary "APPEND" e_middle in
        (* e_enumeratel is supposed to be 'ENUMERATEL n ...' *)
        let the_enumeratel,counter,e_loop =
          match strip_comb e_enumeratel with
            the_enumeratel,[counter;e_loop] -> the_enumeratel,counter,e_loop
          | _ -> failwith "expected ENUMERATEL with two arguments" in
        (* discard e_back! *)
        the_enumeratel,counter,e_loop,e_front,e_prev_trace
      with Failure _ -> failmsg() in

    let _ = match numitr with
     | None -> ()
     | Some numitr ->
      if counter <> numitr then
        failwith ("Counter mismatch: " ^ (string_of_term numitr) ^ " <> " ^
          (string_of_term counter)) in

    (* Let's discard e_back, and use e_loop and counter to reconstruct
      'exists e2. ...'! *)
    let new_exists_e2 =
      let loop_i = hd (fst (strip_abs loop_inv)) in (* 'i' *)
      (* if there is lowerbound, like ENSURES_WHILE_AUP, subtract it *)
      let loop_i = match itrbegin with
        | None -> loop_i
        | Some lb -> mk_binary "-" (loop_i,lb) in
      let new_enumeratel = list_mk_comb (the_enumeratel, [loop_i;e_loop]) in
      let new_e2_expr =
        let atm = `APPEND:(uarch_event)list->(uarch_event)list->(uarch_event)list` in
        match e_prev_trace with
        | None -> mk_binop atm new_enumeratel e_front
        | Some e_prev_trace ->
          mk_binop atm new_enumeratel (mk_binop atm e_front e_prev_trace) in
      mk_exists (var_e2,
        list_mk_conj [clause1;mk_eq(var_e2,new_e2_expr);clause3]) in
    let new_inv = let bvars,body = strip_abs loop_inv in
      list_mk_abs(bvars,mk_conj(body,new_exists_e2)) in
    new_inv in
  (* ENSURES_EVENTS_WHILE_UP2_TAC *)
  (fun (k:term) (pc1:term) (pc2:term) (loop_inv:term) (asl,w) ->
    let new_inv = mk_new_inv loop_inv None (Some k) (asl,w) in
    ENSURES_WHILE_UP2_TAC k pc1 pc2 new_inv (asl,w));;

let UNIFY_F_EVENTS_TAC =
  (* If rhs is "f_events e1 e2 .." and there exists en which is "word k",
     abbreviate "word k" to wk and replace k with "val wk". *)
  W (fun (asl,w) ->
    let _,the_rhs = dest_eq w in
    let f_events,args = strip_comb the_rhs in
    if not (is_var f_events) then failwith "Not a var" else
    let word_args = List.filter (fun t ->
      if not (is_comb t) then false else
      let w,a = dest_comb t in
      if not (is_const w && name_of w = "word") then false else
      is_var a) args in
    (* unique *)
    let word_args = sort (<) word_args in
    let word_args = uniq word_args in
    MAP_EVERY (fun t -> (* t is "word x" *)
      let _,x = dest_comb t in
      let new_v = genvar (type_of t) in
      let eq_val = mk_eq (x,mk_icomb(`val:(N)word->num`,new_v)) in (* wx = val (x) *)
      ABBREV_TAC (mk_eq (new_v,t)) THEN
      SUBGOAL_THEN eq_val SUBST_ALL_TAC THENL
      [ (ASM_SIMP_TAC[WORD_VAL] THEN NO_TAC) ORELSE
        (EXPAND_TAC (name_of new_v) THEN EXPAND_TAC (name_of x) THEN
         REWRITE_TAC[WORD_VAL] THEN NO_TAC) ORELSE
        (PRINT_GOAL_TAC THEN
         FAIL_TAC ("This variable may not fit in bitwidth of word: " ^
            (string_of_term x)));
        ALL_TAC ]) word_args)
  THEN
  (SAFE_UNIFY_REFL_TAC (ref [])
      (ref ["f_events_callee"(* allow callee's f_events *)]) ORELSE
    (PRINT_GOAL_TAC THEN FAIL_TAC "UNIFY_F_EVENTS_TAC"));;

(* An extra wrapper on top of UNIFY_F_EVENTS_TAC. Canonicalizes
   APPEND and ENUMERATEL before trying UNIFY_F_EVENTS_TAC. *)
let CANONICALIZE_UNIFY_F_EVENTS_TAC:tactic =
  PURE_REWRITE_TAC[APPEND_NIL;CONJUNCT1 APPEND] THEN
  GEN_REWRITE_TAC (ONCE_DEPTH_CONV o LAND_CONV) [ENUMERATEL_ADD1] THEN
  GEN_REWRITE_TAC REDEPTH_CONV [APPEND_ASSOC] THEN
  REPEAT (AP_THM_TAC THEN AP_TERM_TAC) THEN
  CONV_TAC (REPEATC (RAND_CONV BETA_CONV)) THEN
  UNIFY_F_EVENTS_TAC;;

(* When the goal has conclusion
    ... = f_events ...  or
    ... = (APPEND or CONS) ... f_events ...,
  unify f_events with the concrete expression in LHS. *)
let FULL_UNIFY_F_EVENTS_TAC:tactic =
  (* If t is `APPEND a b`, return Some (a,b) *)
  let dest_append (t:term):(term*term) option =
    let c,args = strip_comb t in
    if name_of c = "APPEND" then let l::r::[] = args in Some (l,r) else None
  (* If t is `ENUMERATEL a b`, return Some (a,b) *)
  and dest_enumeratel (t:term):(term*term) option =
    let c,args = strip_comb t in
    if name_of c = "ENUMERATEL"
    then let l::r::[] = args in Some (l,r) else None
  (* If t is `f_events a b c ...`, return true *)
  and is_f_events_comb (t:term): bool =
    let c,args = strip_comb t in
    is_var c && find_substring (name_of c) ("f_events_callee") = None in

  let do_fail msg =
    failwith ("FULL_UNIFY_F_EVENTS_TAC: could not instantiate f_ev*: " ^ msg)
    in

  PURE_REWRITE_TAC[APPEND_NIL;CONJUNCT1 APPEND] THEN
  (fun (asl,w) ->
    let l,r = dest_eq w in
    (* When the goal is `x = f_events ...` *)
    if is_f_events_comb r then UNIFY_F_EVENTS_TAC (asl,w) else

    (* Simple case: when RHS is APPEND, and LHS can be anything *)
    try match (dest_append r) with
    | None -> do_fail "simple case failed."
    | Some (r1,r2) ->
      begin match (dest_enumeratel r1, dest_append r2) with
      | None, _ when is_f_events_comb r1 && l = r2 ->
        (* l = APPEND (f_events_.. ..) l.
           f_ev must be [] *)
        (MATCH_MP_TAC NIL_IMPLIES_APPEND_EQ THEN CONJ_TAC THENL
        [REFL_TAC; UNIFY_F_EVENTS_TAC])

      | Some (cnt,_), Some (r21,r22) when
          cnt = `0` && is_f_events_comb r21 && r22 = l ->
        (* l = APPEND (ENUMERATEL 0 ..) (APPEND f_ev l).
           f_ev must be [] *)
        (REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN
        MATCH_MP_TAC NIL_IMPLIES_APPEND_EQ THEN CONJ_TAC THENL
        [REFL_TAC; UNIFY_F_EVENTS_TAC])

      | Some (cnt,_), None when cnt = `0` && is_f_events_comb r2 ->
        (* l = APPEND (ENUMERATEL 0 ..) f_ev` *)
        (REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN UNIFY_F_EVENTS_TAC)

      | _, _ -> failwith "simple case failed"
      end (asl,w)
    with Failure _ ->

    (* If LHS is 'APPEND _ _', do more. *)
    (match (dest_append l, dest_append r) with
    | None, _ -> do_fail "LHS is not APPEND whereas RHS is APPEND"
    | Some (l1,l2), None ->
      begin match (dest_enumeratel l2, dest_enumeratel r) with
      | Some (lcnt,lbody), Some (rcnt,rbody) when
          lbody = rbody && rcnt = mk_binary "+" (lcnt,`1`) ->
        (* APPEND l1 (APPEND (ENUMERATEL i loop) l22) =
          ENUMERATEL (i + 1) loop
        *)
        GEN_REWRITE_TAC RAND_CONV [ENUMERATEL_ADD1] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC (RAND_CONV BETA_CONV) THEN
        UNIFY_F_EVENTS_TAC
      | _, _ -> do_fail "Unknown 'APPEND _ _ = _' case"
      end

    (* The main case. *)
    | Some (l1,l2), Some (r1,r2) ->
      if l2 = r2 && is_f_events_comb r1 then
        (* APPEND t x = APPEND (f_events_.. ..) x *)
        (AP_THM_TAC THEN AP_TERM_TAC THEN UNIFY_F_EVENTS_TAC)

      else
        (* APPEND [..] x = APPEND (ENUMERATEL 0 ..) (APPEND f_ev x) *)
        begin match (dest_enumeratel r1, dest_append r2) with
        | Some (cnt,_), Some (r21,r22) when
            cnt = `0` && is_f_events_comb r21 && r22 = l2 ->
          (REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN AP_THM_TAC THEN
          AP_TERM_TAC THEN UNIFY_F_EVENTS_TAC)
        | _, _ ->

        begin match (dest_append l2, dest_append r1) with
        | Some (l21, l22), Some (r11, r12) ->
          if is_f_events_comb r11 && dest_append r12 = Some (l1, l21) &&
            r2 = l22 then
            (* APPEND l1 (APPEND l21 l22) =
              APPEND (APPEND f_ev (APPEND l1 l21)) l22
              f_ev = []!
            *)
            (REWRITE_TAC[GSYM APPEND_ASSOC] THEN
            MATCH_MP_TAC NIL_IMPLIES_APPEND_EQ THEN CONJ_TAC THENL
            [REFL_TAC; UNIFY_F_EVENTS_TAC])
          else if is_f_events_comb r11 && r12 = l21 && r2 = l22 then
            (* APPEND l1 (APPEND l21 l22) = APPEND (APPEND f_ev l21) l22
              f_ev = l1
            *)
            (REWRITE_TAC[GSYM APPEND_ASSOC] THEN
            AP_THM_TAC THEN AP_TERM_TAC THEN UNIFY_F_EVENTS_TAC)
          else if is_f_events_comb r11 &&
              (match dest_append l22 with
               | None -> false
               | Some (l221,l222) -> dest_append r12 = Some (l21,l221)
                  && l222 = r2) then
            (* APPEND l1 (APPEND l21 (APPEND l221 l222)) =
               APPEND (APPEND f_ev (APPEND l21 l221)) l222
              f_ev = l1
            *)
            (REWRITE_TAC[GSYM APPEND_ASSOC] THEN
            AP_THM_TAC THEN AP_TERM_TAC THEN UNIFY_F_EVENTS_TAC)
          else
            do_fail "Unknown 'APPEND _ (APPEND _ _) = APPEND (APPEND _ _) _' case"

        | Some (l21, l22), None ->
          begin match (dest_enumeratel l21, dest_enumeratel r1) with
          | Some (lcnt,lbody), Some (rcnt,rbody) ->
            if rcnt = mk_binary "+" (lcnt,`1`) && lbody = rbody &&
              l22 = r2 then
              (* APPEND l1 (APPEND (ENUMERATEL i loop) l22) =
                APPEND (ENUMERATEL (i + 1) loop) l22
                loop is l1
              *)
              (GEN_REWRITE_TAC LAND_CONV [APPEND_ASSOC] THEN
              AP_THM_TAC THEN AP_TERM_TAC THEN
              REWRITE_TAC[ENUMERATEL_ADD1] THEN
              AP_THM_TAC THEN AP_TERM_TAC THEN
              UNIFY_F_EVENTS_TAC)
            else do_fail "Unknown 'APPEND _ (APPEND _ _) = APPEND _ _' case"
          | _, _ -> do_fail "Unknown 'APPEND _ (APPEND _ _) = APPEND _ _' case"
          end

        | _, _ ->
          do_fail "Unknown case"
        end
      end) (asl,w)) ORELSE CANONICALIZE_UNIFY_F_EVENTS_TAC;;

(* The input goal:
  exists e2.
    read events s = APPEND e2 e /\
    e2 = f_events <public args> /\     <--- this clause is optional.
    memaccess_inbounds e2 ...'
*)
(* pre_memaccess_tac runs just before the memaccess_inbounds predicates are
   proved, e.g. to abbreviate terms that would get in the way of arithmetic. *)
let GEN_DISCHARGE_SAFETY_PROPERTY_TAC (pre_memaccess_tac:tactic) =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  W (fun (asl,w) ->
    (if is_conj w then
      (CONJ_TAC THENL [ FULL_UNIFY_F_EVENTS_TAC; ALL_TAC ])
    else ALL_TAC) THEN
    pre_memaccess_tac THEN
    (* Prove memaccess_inbounds predicates *)
    DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let DISCHARGE_SAFETY_PROPERTY_TAC = GEN_DISCHARGE_SAFETY_PROPERTY_TAC ALL_TAC;;

(* ------------------------------------------------------------------------- *)
(* Helpers for safety proofs written by hand, e.g. for programs with loops.  *)
(* ------------------------------------------------------------------------- *)

(* Close the conjuncts of a postcondition before its event part, such as the
   values of registers and of the PC, after symbolic simulation. *)

let SAFETY_PEEL_TAC =
  REPEAT(W(fun (asl,w) ->
    if is_conj w then
      CONJ_TAC THENL
       [FIRST[(REWRITE_TAC[COND_ID] THEN NO_TAC);
              (GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN ASM_REWRITE_TAC[] THEN
               NO_TAC);
              (ASM_REWRITE_TAC[] THEN NO_TAC);
              (ASM_REWRITE_TAC[ADD_CLAUSES; SUB_0] THEN NO_TAC);
              (REWRITE_TAC[WORD_SHL_WORD] THEN CONV_TAC NUM_REDUCE_CONV THEN
               CONV_TAC WORD_RULE THEN NO_TAC);
              (REWRITE_TAC[SUB_0] THEN CONV_TAC WORD_RULE)];
        ALL_TAC]
    else NO_TAC));;

let SAFETY_CLOSE_TAC = SAFETY_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

(* Remove the assumptions t = (\x. ...) a with t not a variable, such as the
   instantiated event traces of earlier iterations. *)

let SAFETY_DROP_BETA_EQS_TAC =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    let c = concl th in is_eq c && not (is_var (lhs c)) &&
    is_abs (fst (strip_comb (rhs c))))));;

(* Reduce the conditionals `if p then a else b` of the goal according to p or
   ~p, proved by prove_tac (for SAFETY_COND_TAC, from an assumption), without
   rewriting with p itself. *)

let GEN_SAFETY_COND_TAC (prove_tac:tactic) (p:term) =
  let prove_tac = REWRITE_TAC[EQ_CLAUSES] THEN prove_tac in
  (SUBGOAL_THEN (mk_iff(p,`T`)) (fun th -> REWRITE_TAC[th; COND_CLAUSES]) THENL
    [prove_tac THEN NO_TAC; ALL_TAC]) ORELSE
  (SUBGOAL_THEN (mk_iff(p,`F`)) (fun th -> REWRITE_TAC[th; COND_CLAUSES]) THENL
    [prove_tac THEN NO_TAC; ALL_TAC]);;

let SAFETY_COND_TAC = GEN_SAFETY_COND_TAC (FIRST_ASSUM ACCEPT_TAC);;

(* Facts for an up-counting loop with index register word e (e an expression
   in the loop variable v), whose backward branch compares e + 1 with bnd;
   cnt is the iteration count. *)

let SAFETY_UPCOUNT_FACTS_TAC (v:term) (e:term) (bnd:term) (cnt:term) =
  let e1 = mk_binary "+" (e,`1`) in
  let wd t = mk_comb(`word:num->int64`,t) in
  let mkval t = mk_eq(mk_icomb(`val:int64->num`,wd t),t) in
  SUBGOAL_THEN (list_mk_conj
    [mkval e; mkval e1;
     mk_eq(list_mk_comb(`word_add:int64->int64->int64`,[wd e; `word 1:int64`]),
           wd e1);
     mk_iff(mk_binary "<" (e1,bnd), mk_binary "<" (mk_binary "+" (v,`1`),cnt))])
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SIMPLE_ARITH_TAC;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SIMPLE_ARITH_TAC;
      CONV_TAC WORD_RULE;
      SIMPLE_ARITH_TAC];
    ALL_TAC];;

(* Facts for a down-counting register holding word (c - v), decremented
   before a test of zero. *)

let SAFETY_DOWNCOUNT_FACTS_TAC (v:term) (c:term) =
  let sub t = subst [c,`c:num`; v,`j:num`] t in
  SUBGOAL_THEN (sub `word_sub (word (c - j)) (word 1):int64 = word (c - (j + 1)) /\
                     val (word (c - j):int64) = c - j /\
                     val (word (c - (j + 1)):int64) = c - (j + 1) /\
                     (~(c - (j + 1) = 0) <=> j + 1 < c)`)
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN (sub `c - j = (c - (j + 1)) + 1`) SUBST1_TAC THENL
       [SIMPLE_ARITH_TAC; CONV_TAC WORD_RULE];
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SIMPLE_ARITH_TAC;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN SIMPLE_ARITH_TAC;
      SIMPLE_ARITH_TAC];
    ALL_TAC];;

(* Regroup the postcondition trace e2 = APPEND (APPEND x y) z as
   APPEND x (APPEND y z). *)

let SAFETY_POST_REASSOC_TAC =
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ONCE_DEPTH_CONV)
   [METIS[APPEND_ASSOC]
     `(exists e2. P e2 /\ e2 = APPEND (APPEND (x:(uarch_event)list) y) z /\ Q e2) <=>
      (exists e2. P e2 /\ e2 = APPEND x (APPEND y z) /\ Q e2)`];;

(* Rewrite the postcondition trace to APPEND <head> <precondition trace> when
   a loop is entered from the post-leg of the previous loop. *)

let SAFETY_CARRY_REASSOC_TAC : tactic = fun (asl,w) ->
  let _,args = strip_comb w in
  let pre = el 1 args and post = el 2 args in
  let e2v = `e2:(uarch_event)list` in
  let find_rhs t = rhs (find_term (fun u -> is_eq u && lhs u = e2v) t) in
  let pre_rhs = find_rhs pre and post_rhs = find_rhs post in
  let x0 = lhand (lhand post_rhs) in
  let eq = mk_eq(post_rhs,
    mk_binop `APPEND:(uarch_event)list->(uarch_event)list->(uarch_event)list`
      x0 pre_rhs) in
  let th = prove(eq, REWRITE_TAC[APPEND_ASSOC]) in
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ONCE_DEPTH_CONV) [th] (asl,w);;

(* Reorder the postcondition conjuncts so that the trace part comes last
   (after ENSURES_PRESERVED_TAC / ENSURES_EXISTING_PRESERVED_TAC add more). *)

let SAFETY_EXISTS_LAST_TAC =
  let conv tm =
    let cs = conjuncts tm in
    let ex,others = partition is_exists cs in
    if ex = [] || others = [] then REFL tm
    else CONJ_ACI_RULE (mk_eq(tm,list_mk_conj(others @ ex))) in
  CONV_TAC(RATOR_CONV(RAND_CONV(ABS_CONV conv)));;

(* Discharge a goal `exists e2. ... e2 = <trace> ...` whose witness is given
   explicitly, e.g. for a leg of zero steps, after simplifying with the
   assumptions `val x = x` and `~(x = y)`. *)

let SAFETY_CONCRETE_DISCHARGE_TAC : tactic =
  let is_valfact th =
    let c = concl th in
    is_eq c &&
    (try let v,a = dest_comb (lhs c) in
         name_of v = "val" && rand a = rhs c with Failure _ -> false) in
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  W(fun (a,w) ->
      let e2v, body = dest_exists w in
      let wit = rhs (find (fun c -> is_eq c && lhs c = e2v) (conjuncts body)) in
      EXISTS_TAC wit) THEN
  REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[APPEND; APPEND_NIL; GSYM APPEND_ASSOC] THEN NO_TAC;
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) THEN
    ASSUM_LIST(fun ths ->
      let vths = filter is_valfact ths in
      let nths = filter (fun th -> let c = concl th in
                           is_neg c && is_eq (dest_neg c)) ths in
      let rws = vths @ nths @ [COND_CLAUSES; APPEND_NIL; CONJUNCT1 APPEND;
                               GSYM APPEND_ASSOC] in
      RULE_ASSUM_TAC(REWRITE_RULE rws) THEN REWRITE_TAC rws) THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC];;

(* Lift the word constructor out of a conditional, e.g. in a branch target. *)

let SAFETY_COND_WORD_LIFT = prove
 (`!(b:bool) (a:num) (c:num).
     (if b then word a:int64 else word c) = word (if b then a else c)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

(* Beta-reduce an application of an abstraction whose bound variable is
   called v, e.g. to unfold one particular instantiated event trace. *)

let BETA_VAR_CONV v tm =
  if is_comb tm && is_abs (rator tm) && name_of (bndvar (rator tm)) = v
  then BETA_CONV tm else failwith "BETA_VAR_CONV";;

(* Rewrite with ths only the assumptions `read c s = ...` for the components
   c whose names are in names, e.g. to normalize a pointer or a PC. *)

let SAFETY_REWRITE_READS_TAC names ths =
  let reads_comp tm =
    try let c = rand(rator(lhs tm)) in
        is_const c && mem (fst(dest_const c)) names
    with Failure _ -> false in
  RULE_ASSUM_TAC (fun th ->
    if reads_comp (concl th) then REWRITE_RULE ths th else th);;

(* ------------------------------------------------------------------------- *)
(* Safety proofs following the control flow of the program.                  *)
(* ------------------------------------------------------------------------- *)

(* The skeleton of a safety proof follows the control flow of the program:
     Leg(name,tac)    a straight-line piece, proved by tac, whose events are
                      given by a fresh f_ev_<name> applied to the public
                      variables and to the indices of the enclosing loops;
     Seq(pc,inv,a,b)  a and then b, meeting at pc where inv holds;
     Loop(n,pc1,pc2,inv,pre,body,post)
                      a loop of n iterations with head pc1, exit pc2 and
                      invariant inv = \i s. ..., entered by pre and left by
                      post (ENSURES_EVENTS_WHILE_UP2_TAC); the body starts
                      with the assumptions about i;
     Cases(p,a,b)     a when p holds and b otherwise;
     Then(tac,a)      a after tac, e.g. to establish facts for several legs.
   The terms n and p are about the variables of the proof, in which the word
   variables generalized by W64_GEN_TAC are numbers. *)

type safety_skeleton =
    Leg of string * tactic
  | Seq of term * term * safety_skeleton * safety_skeleton
  | Loop of term * term * term * term *
            safety_skeleton * safety_skeleton * safety_skeleton
  | Cases of term * safety_skeleton * safety_skeleton
  | Then of tactic * safety_skeleton;;

let rec safety_skeleton_is_leg sk =
  match sk with
    Leg _ -> true
  | Then(_,a) -> safety_skeleton_is_leg a
  | _ -> false;;

(* The f_events witness of a skeleton, as a function of the public variables
   args; the numbers k of the proof are val k for word variables k in args. *)

let safety_skeleton_witness (args:term list) (sk:safety_skeleton) : term =
  let ety = `:(uarch_event)list` in
  let app = `APPEND:(uarch_event)list->(uarch_event)list->(uarch_event)list`
  and enum = `ENUMERATEL:num->(num->(uarch_event)list)->(uarch_event)list` in
  let theta = mapfilter (fun a ->
    if type_of a = `:int64`
    then mk_comb(`val:int64->num`,a),mk_var(name_of a,`:num`)
    else fail()) args in
  let rec wit idxs sk =
    match sk with
      Leg(name,_) ->
        let vs = args @ idxs in
        let f = mk_var("f_ev_" ^ name,itlist (mk_fun_ty o type_of) vs ety) in
        list_mk_comb(f,vs)
    | Seq(_,_,a,b) -> mk_binop app (wit idxs b) (wit idxs a)
    | Loop(n,_,_,inv,pre,body,post) ->
        let i = fst(dest_abs inv) in
        let bw = wit (idxs @ [i]) body in
        let bw = if safety_skeleton_is_leg body then rator bw else mk_abs(i,bw) in
        mk_binop app (wit idxs post)
          (mk_binop app (list_mk_comb(enum,[subst theta n; bw])) (wit idxs pre))
    | Cases(p,a,b) -> mk_cond(subst theta p,wit idxs a,wit idxs b)
    | Then(_,a) -> wit idxs a in
  list_mk_abs(args,wit [] sk);;

(* Whether the precondition of an ensures goal has a trace exists e2. ... *)

let safety_pre_has_trace w =
  let e2 = `e2:(uarch_event)list` in
  can (find_term (fun t -> is_exists t && fst(dest_exists t) = e2))
      (el 1 (snd(strip_comb w)));;

(* Rewrite the trace D of the postcondition of an ensures goal (e2 = D) by
   conv. Only D is changed, not the instantiated f_ev of the precondition. *)

let SAFETY_POST_TRACE_CONV_TAC (conv:conv) : tactic = fun (asl,w) ->
  let e2 = `e2:(uarch_event)list` in
  let d = rhs(find_term (fun t -> is_eq t && lhs t = e2)
                        (el 2 (snd(strip_comb w)))) in
  let at_d t = if t = d then conv t else failwith "SAFETY_POST_TRACE_CONV_TAC" in
  CONV_TAC(RATOR_CONV(RAND_CONV(ONCE_DEPTH_CONV at_d))) (asl,w);;

let SAFETY_APPEND_ASSOC_CONV = REWR_CONV(GSYM APPEND_ASSOC);;

(* Rewrite with the assumptions val(word x) = x, which keeps the traces of
   the precondition and of the postcondition alike when an instantiated f_ev
   brings val(word x) back. *)

let SAFETY_VAL_WORD_TAC : tactic =
  let is_valfact th =
    let c = concl th in
    is_eq c &&
    (try let v,a = dest_comb (lhs c) in
         name_of v = "val" && rand a = rhs c with Failure _ -> false) in
  ASSUM_LIST(fun ths ->
    let vths = filter is_valfact ths in
    if vths = [] then ALL_TAC else REWRITE_TAC vths);;

(* Prove an ensures goal following a skeleton, where the trace of its
   postcondition is the witness of the skeleton (followed by the trace of
   the precondition if any). Legs see the goals of the ENSURES_EVENTS tactics
   after SAFETY_VAL_WORD_TAC; the other nodes regroup the trace first. As in
   the usual ENSURES_EVENTS_WHILE_UP2_TAC ... THEN ASM_REWRITE_TAC[] idiom,
   the goals of a loop are rewritten with the assumptions. The straight-line
   legs of a node are proved before its loops, so that the events of a loop
   body are mostly instantiated when the body is proved (as in the usual
   pre, post, body order). *)

let is_ensures t = try fst(dest_const(fst(strip_comb t))) = "ensures"
                    with Failure _ -> false;;

let rec SAFETY_SKELETON_WALK_TAC (sk:safety_skeleton) : tactic =
  match sk with
    Leg(_,tac) -> SAFETY_VAL_WORD_TAC THEN tac
  | Then(tac,a) -> tac THEN SAFETY_SKELETON_WALK_TAC a
  | Cases(p,a,b) ->
      ASM_CASES_TAC p THENL
       [SAFETY_COND_TAC p THEN SAFETY_SKELETON_WALK_TAC a;
        SAFETY_COND_TAC p THEN SAFETY_SKELETON_WALK_TAC b]
  | Seq(pc,inv,a,b) ->
      W(fun (_,w) ->
        if safety_pre_has_trace w
        then SAFETY_POST_TRACE_CONV_TAC SAFETY_APPEND_ASSOC_CONV
        else ALL_TAC) THEN
      ENSURES_EVENTS_SEQUENCE_TAC pc inv THEN
      (if safety_skeleton_is_leg b && not(safety_skeleton_is_leg a) then
         CONJ_TAC THENL [ALL_TAC; SAFETY_SKELETON_WALK_TAC b] THEN
         SAFETY_SKELETON_WALK_TAC a
       else
         CONJ_TAC THENL [SAFETY_SKELETON_WALK_TAC a; SAFETY_SKELETON_WALK_TAC b])
  | Loop(n,pc1,pc2,inv,pre,body,post) -> W(fun (_,w) ->
      let i = fst(dest_abs inv) and nested = safety_pre_has_trace w in
      ENSURES_EVENTS_WHILE_UP2_TAC n pc1 pc2 inv THEN ASM_REWRITE_TAC[] THEN
      W(fun (_,w) ->
        if is_ensures (lhand w) then ALL_TAC else
        CONJ_TAC THENL [SIMPLE_ARITH_TAC ORELSE ASM_ARITH_TAC; ALL_TAC]) THEN
      CONJ_TAC THENL
       [(if safety_skeleton_is_leg pre then ALL_TAC
         else SAFETY_POST_TRACE_CONV_TAC
                (REWR_CONV(CONJUNCT1 ENUMERATEL_APPEND_ZERO))) THEN
        SAFETY_SKELETON_WALK_TAC pre;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [ALL_TAC;
        (if safety_skeleton_is_leg post || not nested then ALL_TAC
         else SAFETY_POST_TRACE_CONV_TAC
                (SAFETY_APPEND_ASSOC_CONV THENC
                 RAND_CONV SAFETY_APPEND_ASSOC_CONV)) THEN
        SAFETY_SKELETON_WALK_TAC post] THEN
      X_GEN_TAC i THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
      (if safety_skeleton_is_leg body then ALL_TAC else
       SAFETY_POST_TRACE_CONV_TAC
        (LAND_CONV(REWR_CONV ENUMERATEL_ADD1) THENC
         SAFETY_APPEND_ASSOC_CONV THENC LAND_CONV BETA_CONV)) THEN
      SAFETY_SKELETON_WALK_TAC body);;

(* Prove a goal `exists f_events. ...` following the skeleton sk: introduce
   the witness given by the skeleton, then do intro (which should generalize
   by W64_GEN_TAC the word variables used as numbers in sk) and the steps of
   the skeleton. *)

let SAFETY_SKELETON_TAC (intro:tactic) (sk:safety_skeleton) : tactic =
  fun (asl,w) ->
    let fev,body = dest_exists w in
    let app = find_term (fun t -> is_comb t && fst(strip_comb t) = fev) body in
    let wit = safety_skeleton_witness (snd(strip_comb app)) sk in
    (CONCRETIZE_F_EVENTS_TAC wit THEN REPEAT META_EXISTS_TAC THEN intro THEN
     SAFETY_SKELETON_WALK_TAC sk) (asl,w);;

(* Introduce the variables of a safety goal, by W64_GEN_TAC for the word
   variables named in w64 and renaming them by the list rename of pairs of
   names, rewrite with ths and assume the hypotheses. *)

let GEN_SAFETY_INTRO_TAC ?(rename=([]:(string*string)list)) (ths:thm list)
    (w64:string list) : tactic =
  REPEAT(W(fun (asl,w) ->
    let v,_ = dest_forall w in
    let n = name_of v in
    let n' = try assoc n rename with Failure _ -> n in
    if mem n w64 && type_of v = `:int64`
    then W64_GEN_TAC (mk_var(n',`:num`)) else X_GEN_TAC (mk_var(n',type_of v)))) THEN
  REWRITE_TAC ths THEN
  TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC));;
