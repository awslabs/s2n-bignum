(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ------------------------------------------------------------------------- *)
(* A useful function to generate the specification of NOIBT_SUBROUTINE_SAFE  *)
(* safety property for x86, from *_SAFE and *_NOIBT_SUBROUTINE_CORRECT       *)
(* ------------------------------------------------------------------------- *)

let mk_noibt_subroutine_safe_spec
    (safe_th:thm) (noibt_subroutine_correct_th:thm) =
  let mk_word (t:int) = mk_comb (`word:num->int64`,mk_small_numeral t) in
  let safe_t = concl safe_th in
  let correct_t = concl noibt_subroutine_correct_th in

  let uvs,body = strip_forall correct_t in
  let retaddr::stackptr::_ = rev uvs in
  let new_assum,body = if is_imp body then dest_imp body else `T`,body in
  (* ^^^ use these new_uvs and new_assum..! *)
  (* get the subtracted offset ('word ..') from stackpointer. *)
  let stackofs:term option =
    try
      let ofs = find_term (fun t -> is_binary "word_sub" t &&
          fst (dest_binary "word_sub" t) = stackptr) new_assum in
      Some (rand ofs)
    with _ ->
      let _ = Printf.printf "(* Has no \"word_sub stackpointer (word ..)\"; stackofs is None *)\n" in
      None in

  let _::pre_fn::post_fn::new_frame::[] = snd (strip_comb body) in
  (* ^^^ use new_frame *)
  let pre_fn_var,pre_fn_clauses = dest_abs pre_fn in
  let pre_bytes_loaded::pre_rip::pre_rsp::pre_retaddr::pre_c_args::_ =
    conjuncts pre_fn_clauses in
  let post_fn_var,post_fn_clauses = dest_abs post_fn in
  let post_rip::post_rsp::_ = conjuncts post_fn_clauses in

  let old_f_ev,sbody = dest_exists safe_t in
  let s_uvs,sbody = strip_forall sbody in
  let already_has_stackptr = last s_uvs = stackptr in
  let new_uvs =
    if already_has_stackptr then s_uvs @ [retaddr]
    else s_uvs @ [stackptr;retaddr] in

  let safe_ensures =
    let sbody_noq = snd (strip_forall sbody) in
    if is_imp sbody_noq then snd (dest_imp sbody_noq) else sbody_noq in
  let ensures_const,(x86_const::pre::post::_) = strip_comb safe_ensures in
  let pre_read_events::_ = rev (conjuncts (snd (dest_abs pre))) in
  let post_e2_pred::_ = rev (conjuncts (snd (dest_abs post))) in
  (* post_e2_pred is:
    `exists e2.
        read events s = APPEND e2 e /\
        e2 = f_events ... /\
        memaccess_inbounds ...` *)
  (* prepare new f_events, with stackpointer and returnaddress *)
  let new_f_ev_ty =
    let ty = type_of old_f_ev in
    let rec f (t:hol_type) =
      try let a,t' = dest_fun_ty t in
          let args,t0 = f t' in
          (a::args),t0
      with _ -> [],t in
    let args,retty = f ty in
    let new_args = args @
      (if already_has_stackptr then [type_of retaddr]
       else [type_of stackptr;type_of retaddr]) in
    itlist mk_fun_ty new_args retty in
  let new_f_events = mk_var("f_events",new_f_ev_ty) in
  let new_post_e2_pred =
    (* word_sub stackpointer (ofs) *)
    let stackptr_with_ofs =
      match stackofs with
      | None -> stackptr
      | Some ofs -> list_mk_icomb "word_sub" [stackptr;ofs] in
    let e2,ebody = dest_exists post_e2_pred in
    let read_events::old_e2_eq::old_meminb::[] = conjuncts ebody in
    let new_e2_eq =
      let old_f_ev_expr = rhs old_e2_eq in
      let _,old_f_ev_args = strip_comb old_f_ev_expr in
      let new_f_ev_args =
        (if already_has_stackptr then butlast old_f_ev_args
         else old_f_ev_args) @ [stackptr_with_ofs;retaddr] in
      mk_eq(lhs old_e2_eq, list_mk_comb(new_f_events,new_f_ev_args)) in
    let new_meminb =
      let meminb_const,_::readlist::writelist::[] = strip_comb old_meminb in
      let old_readlist,old_writelist = (dest_list readlist),(dest_list writelist) in
      let stackofs_num = match stackofs with
        | Some so -> snd (dest_comb so) | None -> `0` in
      let new_readlist,new_writelist =
        if already_has_stackptr then
          let ofs_int = dest_small_numeral stackofs_num in
          (* stack+8 is read because it is where returnaddress is stored *)
          let range_read = mk_pair (stackptr_with_ofs,mk_small_numeral(ofs_int+8)) in
          let range_write = mk_pair (stackptr_with_ofs,stackofs_num) in
          (* remove the old stack range *)
          let old_readlist_nosp = filter (fun t ->
              not (can (find_term (fun t' -> t' = stackptr)) t)) old_readlist in
          let old_writelist_nosp = filter (fun t ->
              not (can (find_term (fun t' -> t' = stackptr)) t)) old_writelist in
          (old_readlist_nosp @ [range_read]),
          (old_writelist_nosp @ [range_write])
        else
          let stackofs_num_plus_8 =
            mk_small_numeral((dest_small_numeral stackofs_num) + 8) in
          let range_read = mk_pair (stackptr_with_ofs, stackofs_num_plus_8) in
          let range_write = mk_pair (stackptr_with_ofs, stackofs_num) in
          (old_readlist @ [range_read]),
          (old_writelist @ [range_write]) in
      list_mk_comb (meminb_const,[e2;mk_flist new_readlist; mk_flist new_writelist]) in
    mk_exists (e2, list_mk_conj [read_events; new_e2_eq; new_meminb]) in

  let new_pre = mk_abs(pre_fn_var,
    list_mk_conj [pre_bytes_loaded;pre_rip;pre_rsp;pre_retaddr;pre_c_args;pre_read_events]) in
  let new_post = mk_abs(post_fn_var,
    list_mk_conj [post_rip;post_rsp;new_post_e2_pred]) in

  let new_body = list_mk_comb(ensures_const,[x86_const;new_pre;new_post;new_frame]) in
  mk_exists(new_f_events,
    list_mk_forall(new_uvs,mk_imp(new_assum,new_body)));;

(* Usage:
  generate_four_variants_of_x86_safety_specs
      "p384_montjadd_alt"
      P384_MONTJADD_ALT_CORRECT
      P384_MONTJADD_ALT_EXEC
      P384_MONTJADD_ALT_NOIBT_SUBROUTINE_CORRECT
      P384_MONTJADD_ALT_NOIBT_WINDOWS_SUBROUTINE_CORRECT;;

  Needs these two files already loaded:
    x86/proofs/consttime.ml
    x86/proofs/subroutine_signatures.ml

  NOTE: the assumptions of generated *_SUBROUTINE_SAFE (no IBT) may have wrong
  nonoverlapping ranges on (pc,<program length>) if the program lengths are
  hard-coded as integer constants. It must be corrected by adding 4.
  An example is edwards25519_scalarmuldouble which has coda mc.
*)
let generate_four_variants_of_x86_safety_specs (fnname:string)
    correct_th exec_th
    noibt_subroutine_correct_th noibt_windows_subroutine_correct_th =
  let fnname_u = String.uppercase_ascii fnname in
  (* 0. preamble *)
  print_endline ("(* ------------------------------------------------------------------------- *)");
  print_endline ("(* Constant-time and memory safety proof.                                    *)");
  print_endline ("(* (specs generated with generate_four_variants_of_x86_safety_specs)         *)");
  print_endline ("(* ------------------------------------------------------------------------- *)");
  print_endline ("");

  (* 1. generate the spec of the 'core' part *)
  print_endline ("needs \"x86/proofs/consttime.ml\";;");
  print_endline ("needs \"x86/proofs/subroutine_signatures.ml\";;");
  print_endline ("");
  print_endline ("let full_spec,public_vars = mk_safety_spec");
  print_endline ("    ~keep_maychanges:true");
  print_endline ("    (assoc \"" ^ fnname ^ "\" subroutine_signatures)");
  print_endline ("    " ^ fnname_u ^ "_CORRECT");
  print_endline ("    " ^ fnname_u ^ "_EXEC;;");
  print_endline ("");

  (* 2. write its proof *)
  print_endline ("let " ^ fnname_u ^ "_SAFE = time prove");

  let full_spec,_ = mk_safety_spec
    ~keep_maychanges:true
    (assoc fnname subroutine_signatures)
    correct_th
    exec_th in
  Format.printf " (%a,\n" pp_print_qterm full_spec;
  Format.printf "  ASSERT_CONCL_TAC full_spec THEN\n";
  Format.printf "  PROVE_SAFETY_SPEC_TAC ~public_vars:public_vars %s_EXEC);;\n\n"
      fnname_u;

  (* 3. NOIBT_SUBROUTINE_SAFE and SUBROUTINE_SAFE *)
  let noibt_subroutine_safe_spec = mk_noibt_subroutine_safe_spec
    (ASSUME (full_spec)) noibt_subroutine_correct_th in
  Format.printf "let %s_NOIBT_SUBROUTINE_SAFE = time prove\n" fnname_u;
  Format.printf " (%a,\n" pp_print_qterm noibt_subroutine_safe_spec;
  Format.printf "  <TACTIC> THEN DISCHARGE_SAFETY_PROPERTY_TAC);;\n\n";

  let subroutine_safe_spec =
    let t = find_term (fun t -> is_const t && name_of t = fnname ^ "_tmc")
      noibt_subroutine_safe_spec in
    subst [mk_var(fnname ^ "_mc",type_of t),t] noibt_subroutine_safe_spec in
  Format.printf "let %s_SUBROUTINE_SAFE = time prove\n" fnname_u;
  Format.printf " (%a,\n" pp_print_qterm subroutine_safe_spec;
  Format.printf "  MATCH_ACCEPT_TAC(ADD_IBT_RULE %s_NOIBT_SUBROUTINE_SAFE));;\n\n" fnname_u;

  (* 4. NOIBT_WINDOWS_SUBROUTINE_SAFE and WINDOWS_SUBROUTINE_SAFE *)
  print_endline "(* ------------------------------------------------------------------------- *)";
  print_endline "(* Constant-time and memory safety proof of Windows ABI version.             *)";
  print_endline "(* ------------------------------------------------------------------------- *)\n";

  (* Replace `<fnname>_tmc` with `<fnname>_windows_tmc` *)
  let full_spec_w =
    let the_tmc = find_term
        (fun t -> is_const t && name_of t = fnname ^ "_tmc") full_spec in
    let windows_tmc = mk_mconst (fnname ^ "_windows_tmc", type_of the_tmc) in
    let data_tmc = match find_terms
        (fun t -> is_const t && name_of t = fnname ^ "_data") full_spec with
      | [] -> []
      | the_tmc::[] ->
        [mk_mconst (fnname ^ "_windows_data", type_of the_tmc), the_tmc] in
    subst ((windows_tmc,the_tmc)::data_tmc) full_spec in
  let noibt_windows_subroutine_safe_spec = mk_noibt_subroutine_safe_spec
    (ASSUME (full_spec_w)) noibt_windows_subroutine_correct_th in
  Format.printf "let %s_NOIBT_WINDOWS_SUBROUTINE_SAFE = time prove\n" fnname_u;
  Format.printf " (%a,\n" pp_print_qterm noibt_windows_subroutine_safe_spec;
  Format.printf "  <TACTIC> THEN DISCHARGE_SAFETY_PROPERTY_TAC);;\n\n";

  let windows_subroutine_safe_spec =
    let t = find_term (fun t -> is_const t && name_of t = fnname ^ "_windows_tmc")
      noibt_windows_subroutine_safe_spec in
    subst [mk_var(fnname ^ "_windows_mc",type_of t),t] noibt_windows_subroutine_safe_spec in
  Format.printf "let %s_WINDOWS_SUBROUTINE_SAFE = time prove\n" fnname_u;
  Format.printf " (%a,\n" pp_print_qterm windows_subroutine_safe_spec;
  Format.printf "  MATCH_ACCEPT_TAC(ADD_IBT_RULE %s_NOIBT_WINDOWS_SUBROUTINE_SAFE));;\n\n" fnname_u;;
