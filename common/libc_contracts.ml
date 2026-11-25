(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Contracts for external functions, such as those of the C library, that   *)
(* compiled code calls (through the PLT of a shared object), independent of  *)
(* the instruction set. arm/proofs/libc.ml has the AArch64 instances (memcpy, *)
(* memmove, memset) and the tactics for the calls.                           *)
(*                                                                           *)
(* The code of such a function is not part of the image, so its behaviour is *)
(* assumed. A contract is about the function at an address f (which a caller *)
(* reads from its GOT) in any state where a region (ea,el) of memory, which  *)
(* holds its code and any data it uses, has fixed contents ev; callers do    *)
(* not write that region. The function may change what the calling          *)
(* convention lets it change (given by the ABI below, with the registers     *)
(* that the linker and the platform may use, such as X16, X17 and X18 on     *)
(* AArch64), and of memory only its outputs.                                 *)
(*                                                                           *)
(* Each function has five contracts, all made by libc_contracts from one     *)
(* description. With the arguments args (the C arguments), the ghosts (the   *)
(* values of the inputs), the link (the return address, and the stack        *)
(* pointer where the ABI needs it) and the hypothesis H on them:             *)
(*                                                                           *)
(*  <f>_contract f ea el ev           correctness:                           *)
(*     !args ghosts link. H ==> ensures (call, inputs) (return, outputs)     *)
(*                                                                           *)
(*  <f>_safe_contract f ea el ev      memory safety:                         *)
(*     !e args link. H ==> ensures (call, events = e)                        *)
(*       (return, ?e2. events = APPEND e2 e /\                               *)
(*                      memaccess_inbounds e2 (reads @ [ea,el]) writes)      *)
(*     The events exist and are in bounds; nothing is said about what they   *)
(*     depend on, so it fits code whose accesses depend on the data.         *)
(*                                                                           *)
(*  <f>_correct_safe_contract f ea el ev    both in one ensures:             *)
(*     !e args ghosts link. H ==> ensures (call, inputs, events = e)         *)
(*       (return, outputs, ?e2. ... memaccess_inbounds e2 ...)               *)
(*     A caller whose own accesses depend on the outputs of a call needs the *)
(*     outputs and the events of that call together. Two ensures facts       *)
(*     cannot be combined afterwards (their postconditions may hold at       *)
(*     different points of an execution), so this is a contract of its own; *)
(*     it implies the first two.                                             *)
(*                                                                           *)
(*  <f>_safety_contract f ea el ev    constant time and memory safety:       *)
(*     ?f_events. !e args link. H ==> ensures (call, events = e)             *)
(*       (return, ?e2. events = APPEND e2 e /\ e2 = f_events args link /\    *)
(*                     memaccess_inbounds e2 ...)                            *)
(*     as in the proofs of mlkem-native: the events are a function of the    *)
(*     arguments (addresses and lengths, assumed public), not of the data.   *)
(*                                                                           *)
(*  <f>_full_contract f ea el ev      all of these in one ensures; it        *)
(*     implies the other four.                                               *)
(*                                                                           *)
(* The theorems <F>_FULL_CONTRACT, <F>_CORRECT_SAFE_CONTRACT and             *)
(* <F>_SAFETY_CONTRACT state the implications, so a caller can assume the   *)
(* strongest contract it needs and derive the others for its callees.       *)
(* ========================================================================= *)

needs "common/safety.ml";;

(* ------------------------------------------------------------------------- *)
(* The calling convention: how a call starts and ends, as conjuncts of the   *)
(* pre- and postcondition, with the variables of the link quantified in the  *)
(* contracts; the C arguments and the result; and what a callee may change  *)
(* besides its outputs.                                                      *)
(* ------------------------------------------------------------------------- *)

type libc_abi =
  { abi_step : term;                (* arm *)
    abi_memory : term;              (* memory *)
    abi_events : term;              (* events *)
    abi_link : term list;           (* [returnaddress] *)
    abi_call : term -> term -> term list;  (* f s |-> [read PC s = f; ...] *)
    abi_return : term -> term;         (* s |-> read PC s = returnaddress *)
    abi_args : term list -> term -> term;     (* C_ARGUMENTS args s *)
    abi_result : term -> term -> term;        (* s r |-> C_RETURN s = r *)
    abi_frame : term;               (* the registers that may change *)
  };;

(* A function: its name, its C arguments (variables), the ghosts (values of *)
(* its inputs, variables), the hypothesis on them (state-free, besides the   *)
(* disjointness of the outputs from (ea,el), which is added), the input and  *)
(* output conjuncts (terms in the state variable s), the result (if the      *)
(* contract states it), and the regions that it reads (besides (ea,el) and   *)
(* its outputs) and writes.                                                  *)

type libc_function =
  { lf_name : string;
    lf_args : term list;
    lf_ghosts : term list;
    lf_hyp : term list;
    lf_pre : term list;
    lf_post : term list;
    lf_result : term option;
    lf_reads : term list;
    lf_writes : term list;
  };;

(* The statements of the five contracts, as terms, for a function at f with  *)
(* the region (ea,el) holding ev.                                            *)

let libc_contract_terms (abi:libc_abi) (lf:libc_function) =
  let sty = hd(snd(dest_type(type_of abi.abi_step))) in
  let s = mk_var("s",sty) in
  let f = `f:int64` and ea = `ea:int64` and el = `el:num` and ev = `ev:num` in
  let rd c = list_mk_icomb "read" [c;s] in
  let mem_bytes w =
    mk_icomb(mk_icomb(mk_const(":>",[]),abi.abi_memory),
             mk_comb(`bytes:int64#num->(int64->byte,num)component`,w)) in
  let e = mk_var("e",type_of(rd abi.abi_events)) in
  let e2 = mk_var("e2",type_of e) in
  let reads = lf.lf_reads @ [mk_pair(ea,el)] and writes = lf.lf_writes in
  let hyps =
    map (fun w -> list_mk_comb(`nonoverlapping:int64#num->int64#num->bool`,
                               [w; mk_pair(ea,el)])) writes @ lf.lf_hyp in
  let ea_fact = mk_eq(rd(mem_bytes(mk_pair(ea,el))),ev) in
  let events_fact = mk_eq(rd abi.abi_events,e) in
  let call = abi.abi_call f s @ [abi.abi_args lf.lf_args s; ea_fact] in
  let ret = abi.abi_return s ::
            (match lf.lf_result with
               Some r -> [abi.abi_result s r] | None -> []) in
  let frame =
    if writes = [] then abi.abi_frame else
    let ml = mk_list(map mem_bytes writes,type_of(mem_bytes(hd writes))) in
    let rec seq f g = match f with
        Comb(Comb(Const(",,",_) as c,a),b) -> mk_comb(mk_comb(c,a),seq b g)
      | _ -> list_mk_icomb ",," [f;g] in
    seq abi.abi_frame (mk_icomb(`MAYCHANGE`,ml)) in
  let region_ty = `:int64#num` in
  let inb = list_mk_icomb "memaccess_inbounds"
              [e2; mk_list(reads,region_ty); mk_list(writes,region_ty)] in
  let fev_ty = itlist (fun v ty -> mk_fun_ty (type_of v) ty)
                      (lf.lf_args @ abi.abi_link) (type_of e) in
  let fev = mk_var("f_events",fev_ty) in
  let fev_app = list_mk_comb(fev,lf.lf_args @ abi.abi_link) in
  let ev_post ct =
    mk_exists(e2,list_mk_conj
      ([mk_eq(rd abi.abi_events,list_mk_icomb "APPEND" [e2;e])] @
       (if ct then [mk_eq(e2,fev_app)] else []) @ [inb])) in
  let ens pre post =
    list_mk_icomb "ensures"
      [abi.abi_step; mk_abs(s,list_mk_conj pre); mk_abs(s,list_mk_conj post);
       frame] in
  let stmt vars pre post =
    let body = ens pre post in
    list_mk_forall(vars,if hyps = [] then body
                        else mk_imp(list_mk_conj hyps,body)) in
  let correct = stmt (lf.lf_args @ lf.lf_ghosts @ abi.abi_link)
                  (call @ lf.lf_pre) (ret @ lf.lf_post)
  and safe = stmt (e :: lf.lf_args @ abi.abi_link)
               (call @ [events_fact]) (ret @ [ev_post false])
  and correct_safe = stmt (e :: lf.lf_args @ lf.lf_ghosts @ abi.abi_link)
                       (call @ lf.lf_pre @ [events_fact])
                       (ret @ lf.lf_post @ [ev_post false])
  and safety = mk_exists(fev,stmt (e :: lf.lf_args @ abi.abi_link)
                 (call @ [events_fact]) (ret @ [ev_post true]))
  and full = mk_exists(fev,stmt (e :: lf.lf_args @ lf.lf_ghosts @ abi.abi_link)
               (call @ lf.lf_pre @ [events_fact])
               (ret @ lf.lf_post @ [ev_post true])) in
  [f;ea;el;ev],[correct; safe; correct_safe; safety; full];;

(* ------------------------------------------------------------------------- *)
(* The implications between the contracts, proved generically: from the     *)
(* stronger contract instantiated with the events of the state for e (when  *)
(* the weaker one does not have them), and the postcondition weakened.       *)
(* ------------------------------------------------------------------------- *)

let EVENTUALLY_MONO_IMP = prove
 (`!(step:S->S->bool) P Q s.
        (!s'. P s' ==> Q s') ==> eventually step P s ==> eventually step Q s`,
  MESON_TAC[EVENTUALLY_MONO]);;

let LIBC_CONTRACT_IMP_TAC (abi:libc_abi) =
  let fvar tm = try Some(fst(dest_exists tm)) with Failure _ -> None in
  fun (asl,w) ->
    let src,tgt = dest_imp w in
    let src_f = fvar src and tgt_f = fvar tgt in
    let src_body = match src_f with Some _ -> snd(dest_exists src) | None -> src
    and tgt_body = match tgt_f with Some _ -> snd(dest_exists tgt) | None -> tgt in
    let svars,_ = strip_forall src_body and tvars,tb = strip_forall tgt_body in
    let ens = if is_imp tb then rand tb else tb in
    let pre = lhand(rator ens) in
    let s = fst(dest_abs pre) in
    let ev_read = mk_icomb(mk_icomb(`read`,abi.abi_events),s) in
    (* A ghost of the source that the target does not have is the value   *)
    (* that the source's precondition gives it, read c s = x.               *)
    let src_pre =
      let sb = snd(strip_forall src_body) in
      let sens = if is_imp sb then rand sb else sb in
      let sv,sp = dest_abs(lhand(rator sens)) in
      conjuncts(vsubst [s,sv] sp) in
    let inst = map (fun v ->
        if mem v tvars then v
        else if name_of v = "e" then ev_read
        else try lhs(find (fun c -> is_eq c && rhs c = v) src_pre)
             with Failure _ ->
               failwith ("LIBC_CONTRACT_IMP_TAC: no value for " ^ name_of v))
      svars in
    ((match src_f with
        Some f -> DISCH_THEN(X_CHOOSE_TAC f)
      | None -> DISCH_TAC) THEN
     (match tgt_f,src_f with
        Some _,Some f -> EXISTS_TAC f
      | Some _,None -> failwith "LIBC_CONTRACT_IMP_TAC: no events function"
      | _ -> ALL_TAC) THEN
     MAP_EVERY X_GEN_TAC tvars THEN
     (if is_imp(snd(strip_forall tgt_body)) then DISCH_TAC else ALL_TAC) THEN
     REWRITE_TAC[ensures] THEN X_GEN_TAC s THEN BETA_TAC THEN STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPECL inst) THEN ASM_REWRITE_TAC[ensures] THEN
     DISCH_THEN(MP_TAC o SPEC s) THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC EVENTUALLY_MONO_IMP THEN REWRITE_TAC[] THEN MESON_TAC[])
    (asl,w);;

(* libc_contracts abi lf defines the five contracts of lf and proves the     *)
(* implications; it returns the definitions in the order above and the      *)
(* theorems                                                                  *)
(*   <F>_FULL_CONTRACT: full ==> correct /\ safe /\ correct_safe /\ safety   *)
(*   <F>_CORRECT_SAFE_CONTRACT: correct_safe ==> correct /\ safe             *)
(*   <F>_SAFETY_CONTRACT: safety ==> safe                                    *)
(* all for !f ea el ev.                                                      *)

let libc_contracts (abi:libc_abi) (lf:libc_function) =
  let params,stmts = libc_contract_terms abi lf in
  let names = map (fun k -> lf.lf_name ^ k)
    ["_contract"; "_safe_contract"; "_correct_safe_contract";
     "_safety_contract"; "_full_contract"] in
  let defs = map2 (fun n tm ->
      let ty = itlist (mk_fun_ty o type_of) params bool_ty in
      new_definition(mk_eq(list_mk_comb(mk_var(n,ty),params),tm)))
    names stmts in
  let lhs_of th = lhs(snd(strip_forall(concl th))) in
  let c = map lhs_of defs in
  let imp src tgts =
    let tm = list_mk_forall(params,mk_imp(src,list_mk_conj tgts)) in
    prove(tm,
      REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN
      FIRST_X_ASSUM(MP_TAC) THEN PURE_REWRITE_TAC defs THEN
      LIBC_CONTRACT_IMP_TAC abi) in
  match c,defs with
    [correct;safe;correct_safe;safety;full],_ ->
      let up = String.uppercase_ascii lf.lf_name in
      let fullth = imp full [correct;safe;correct_safe;safety]
      and csth = imp correct_safe [correct;safe]
      and sth = imp safety [safe] in
      defs,[up ^ "_FULL_CONTRACT",fullth;
            up ^ "_CORRECT_SAFE_CONTRACT",csth;
            up ^ "_SAFETY_CONTRACT",sth]
  | _ -> failwith "libc_contracts";;

(* ------------------------------------------------------------------------- *)
(* Reductions that the tactics for calls use.                                *)
(* ------------------------------------------------------------------------- *)

let VAL_WORD_NUMERAL_CONV tm =
  match tm with
    Comb(Const("val",_),Comb(Const("word",_),n)) when is_numeral n ->
      WORD_REDUCE_CONV tm
  | _ -> failwith "VAL_WORD_NUMERAL_CONV";;

(* ------------------------------------------------------------------------- *)
(* After memset with c = 0: the bytes, as the contract gives them, make a    *)
(* region of zeros. The address of byte i of a destination word_add a        *)
(* (word k) may have been normalized to word_add a (word(k + i)).            *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES_OF_BYTES8 = prove
 (`!(m:(S,int64->byte)component) a n x s.
        (!j. j < n
             ==> read (m :> bytes8(word_add a (word j))) s =
                 word((x DIV 2 EXP (8 * j)) MOD 256))
        ==> read (m :> bytes(a,n)) s = x MOD 2 EXP (8 * n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1];
    REPEAT STRIP_TAC] THEN
  REWRITE_TAC[ADD1; READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE;
              READ_BYTES_BYTES8] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`; `s:S`]) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `j < n ==> j < SUC n`];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[LT] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL; LEFT_ADD_DISTRIB; MULT_CLAUSES; EXP_ADD] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 8 = 256`; MOD_MULT_MOD] THEN ARITH_TAC);;

let MEMSET_ZERO_BYTES = prove
 (`!(m:(S,int64->byte)component) a n s.
        (!i. i < n
             ==> read (m :> bytes8(word_add a (word i))) s =
                 word_zx(word 0:int64))
        ==> read (m :> bytes(a,n)) s = 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(S,int64->byte)component`; `a:int64`; `n:num`; `0`;
                 `s:S`] READ_MEMORY_BYTES_OF_BYTES8) THEN
  ASM_SIMP_TAC[DIV_0; MOD_0] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONV_TAC WORD_REDUCE_CONV);;

let MEMSET_ZERO_BYTES_OFFSET = prove
 (`!(m:(S,int64->byte)component) a k n s.
        (!i. i < n
             ==> read (m :> bytes8(word_add a (word(k + i)))) s =
                 word_zx(word 0:int64))
        ==> read (m :> bytes(word_add a (word k),n)) s = 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEMSET_ZERO_BYTES THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN ASM_SIMP_TAC[]);;

let MEMSET_ZERO_BYTES_TAC =
  FIRST_ASSUM(fun th ->
    ASSUME_TAC(try MATCH_MP MEMSET_ZERO_BYTES_OFFSET th
               with Failure _ -> MATCH_MP MEMSET_ZERO_BYTES th));;
