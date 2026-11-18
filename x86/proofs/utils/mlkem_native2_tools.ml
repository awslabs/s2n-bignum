(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs about an image of x86 functions that call one        *)
(* another, as for the AArch64 mlkem_native2 (see                            *)
(* arm/proofs/mlkem_native2_image.ml): the symbols of a linked ELF file as   *)
(* layout names, decoding theorems for given ranges of the image, data in    *)
(* the image, a driver that simulates code whose control flow is fixed by    *)
(* its parameters, with hooks at given offsets, calls by the theorems of     *)
(* the callees, ghost functions for the buffers that they write, and the     *)
(* SAFE theorems of leaf functions in the form that their callers need.      *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/layout.ml";;

(* ------------------------------------------------------------------------- *)
(* The symbols of the section .text of an ELF64 file, as (name, value, size) *)
(* for the functions and other symbols with names, excluding those of the    *)
(* assembler's numeric labels. The labels inside the functions have names    *)
(* starting with L, which keeps them local to the object on Mach-O; that     *)
(* prefix is dropped where the name without it is not another symbol's.      *)
(* ------------------------------------------------------------------------- *)

let load_elf64_text_symbols =
  let u16 bs a = get_int_le bs a 2 and u32 bs a = get_int_le bs a 4
  and u64 bs a = get_int_le bs a 8 in
  fun (filename:string) ->
    let file = load_file filename in
    if not (is_elf file) || get_int_list file 0x4 2 <> [2;1] then
      failwith "load_elf64_text_symbols: not a little-endian ELF64 file" else
    let shoff = u64 file 0x28 and shentsize = u16 file 0x3a
    and shnum = u16 file 0x3c and shstrndx = u16 file 0x3e in
    let header i = shoff + i * shentsize in
    let offset i = u64 file (header i + 0x18)
    and size i = u64 file (header i + 0x20)
    and typ i = u32 file (header i + 0x4)
    and link i = u32 file (header i + 0x28) in
    let name_of i = get_string file (offset shstrndx + u32 file (header i)) in
    let find p = let rec go i = if i >= shnum then failwith
                   "load_elf64_text_symbols: missing section"
                 else if p i then i else go (i + 1) in go 0 in
    let text = find (fun i -> name_of i = ".text")
    and symtab = find (fun i -> typ i = 2) in
    let strtab = link symtab in
    let unlocal n = String.sub n 1 (String.length n - 1) in
    let rec syms k acc =
      if k < 0 then acc else
      let e = offset symtab + 24 * k in
      let name = get_string file (offset strtab + u32 file e)
      and shndx = u16 file (e + 6) in
      let acc' =
        if shndx = text && name <> "" && String.get name 0 <> '$' &&
           not (String.contains name '.')
        then (name,u64 file (e + 8),u64 file (e + 16))::acc
        else acc in
      syms (k - 1) acc' in
    let l = syms (size symtab / 24 - 1) [] in
    let names = map (fun (n,_,_) -> n) l in
    map (fun (n,v,sz as sym) ->
           if String.length n > 1 && String.get n 0 = 'L' &&
              not (mem (unlocal n) names)
           then (unlocal n,v,sz) else sym) l;;

(* ------------------------------------------------------------------------- *)
(* An image: the code of a linked ELF file as one byte list mc, the theorem  *)
(* for its length, and the layout names: f for the address of each function  *)
(* or label f, f_size for the size of a function, and <image>_size for the   *)
(* size of the image, where <image> is the name of mc without a final "_mc". *)
(* ------------------------------------------------------------------------- *)

let x86_image name filename =
  let mc = define_from_elf name filename in
  let lenth = CONV_RULE(RAND_CONV LENGTH_CONV)
                (AP_TERM `LENGTH:byte list->num` mc) in
  let n = String.length name in
  let base = if n > 3 && String.sub name (n - 3) 3 = "_mc"
             then String.sub name 0 (n - 3) else name in
  install_layout
   ((base ^ "_size",dest_small_numeral(rhs(concl lenth))) ::
    List.concat
     (map (fun (n,v,sz) -> if sz = 0 then [n,v] else [n,v; n ^ "_size",sz])
          (load_elf64_text_symbols filename)));
  mc,lenth;;

(* ------------------------------------------------------------------------- *)
(* Decoding all the code of an image would take a long time, and data in it  *)
(* are not instructions, so the decoding theorems for the simulation are     *)
(* only made for the given ranges of addresses [lo,hi), those of the code    *)
(* being simulated. Otherwise this is the same as X86_MK_EXEC_RULE. (From    *)
(* the proofs of mlkem-native's compiled code for x86.)                      *)
(* ------------------------------------------------------------------------- *)

let X86_MK_EXEC_RANGES_RULE =
  let pth = (UNDISCH_ALL o prove)
   (`i = i' ==> pc + n = pc' ==>
     bytes_loaded s (word pc) l ==> decode_len l (n,i) l' ==>
     x86_decode s (word pc) (n,i') /\ bytes_loaded s (word pc') l'`,
    REPEAT (DISCH_THEN (SUBST1_TAC o SYM)) THEN
    MATCH_ACCEPT_TAC X86_DECODE_CONS)
  and pth_pc = (UNDISCH o ARITH_RULE) `n + m:num = p ==> (pc + n) + m = pc + p`
  and ei,ei' = `i:instruction`,`i':instruction`
  and pl,el,el' = `(+):num->num->num`,`l:byte list`,`l':byte list`
  and en,em,ep,epc,epc' = `n:num`,`m:num`,`p:num`,`pc:num`,`pc':num`
  and len_tm = `LENGTH:byte list->num` in
  let offset_of pc = match pc with
    | Comb(Comb(Const("+",_),_),a) -> dest_small_numeral a
    | _ -> 0 in
  let rec go hi th =
    let l = rand (concl th) in
    let th1 = DECODE_LEN_THM l in
    let (n,i),l' = (dest_pair o rand F_F I) (dest_comb (concl th1)) in
    let th2 = REWRITE_CONV X86_INSTRUCTION_ALIASES i in
    let i' = rhs (concl th2) in
    let pc = rand (lhand (concl th)) in
    let th3,pcofs = match pc with
    | Comb(Comb(Const("+",_),pc),a) ->
      let th = NUM_ADD_CONV (mk_comb (mk_comb (pl, a), n)) in
      PROVE_HYP th (INST [pc,epc; a,en; n,em; rhs (concl th),ep] pth_pc),a
    | _ -> REFL (mk_comb (mk_comb (pl, pc), n)),`0` in
    let pc' = rhs (concl th3) in
    let th' = (PROVE_HYP th2 o PROVE_HYP th3 o PROVE_HYP th o PROVE_HYP th1)
      (INST [i,ei; i',ei'; pc,epc; n,en; pc',epc'; l,el; l',el'] pth) in
    let dth,bth = CONJ_PAIR th' in
    if offset_of pc' >= hi then [dth,pcofs]
    else (dth,pcofs)::(go hi bth) in
  fun mc_def ranges ->
    let lenth = TRANS (AP_TERM len_tm mc_def)
                      (LENGTH_CONV (mk_comb(len_tm,rhs(concl mc_def)))) in
    let dth = AP_TERM `bytes_loaded s (word pc)` mc_def in
    let th0 = EQ_MP dth (ASSUME (lhs (concl dth))) in
    let decodes = itlist (fun (lo,hi) acc ->
      go hi (BYTES_LOADED_OFFSET_RULE lo th0) @ acc) ranges [] in
    let arr = Array.make (dest_small_numeral (rhs (concl lenth))) None in
    List.iter (fun (th,pcofs) ->
        arr.(dest_small_numeral pcofs) <-
          Some ((GENL [`s:x86state`; `pc:num`] o DISCH_ALL) th))
      decodes;
    lenth,arr;;

(* ------------------------------------------------------------------------- *)
(* Data in an image: x86_image_data mc name off len defines name as the len  *)
(* bytes of the image mc at off and gives                                    *)
(*                                                                           *)
(* |- !s pc. bytes_loaded s (word pc) mc ==> bytes_loaded s (word(pc + off)) *)
(*           name                                                            *)
(* ------------------------------------------------------------------------- *)

let x86_image_data mc name off len =
  let l = dest_list(rand(concl mc)) in
  let data = mk_list(fst(chop_list len (snd(chop_list off l))),`:byte`) in
  let def = new_definition(mk_eq(mk_var(name,`:byte list`),data)) in
  def,BYTES_LOADED_SUBPROGRAM_RULE mc def off;;

(* A RIP-relative address as the simulation gives it, in normal form *)

let WORD_VAL_ADD_64 = prove
 (`!x n. word(val(word x:int64) + n):int64 = word(x + n)`,
  REWRITE_TAC[WORD_ADD; WORD_VAL]);;

(* ------------------------------------------------------------------------- *)
(* The driver, as NATIVE2_RUN_TAC for AArch64: from state k, run the tactic  *)
(* in derive for the offset of RIP in that state if there is one (to add     *)
(* facts), then the one in calls (to take a call as one step to the next     *)
(* state) or otherwise one step of the code, until RIP is not pc + n.        *)
(* A call is taken at the entry of the callee, after the step of the call    *)
(* instruction, which has pushed the return address.                         *)
(* ------------------------------------------------------------------------- *)

let state_of k = mk_var("s"^string_of_int k,`:x86state`);;

let find_asm p (asl,w) = snd(find (fun (_,th) -> p (concl th)) asl);;

let asm_with_lhs lhs gl =
  find_asm (fun c -> try lhand c = lhs with Failure _ -> false) gl;;

let get_pc_offset k (asl,w as gl) =
  try let th = asm_with_lhs (mk_comb(`read RIP`,state_of k)) gl in
      let t = rand(rand(concl th)) in
      if t = `pc:num` then 0 else
      if is_comb t && is_comb(rator t) && name_of(rator(rator t)) = "+" &&
         rand(rator t) = `pc:num`
      then dest_small_numeral(rand t) else -1
  with Failure _ -> -1;;

let find_read_fact comp k gl =
  rand(concl(asm_with_lhs
    (mk_comb(mk_comb(`read:(x86state,int64)component->x86state->int64`,
                     comp),state_of k)) gl));;

(* Each step adds the components it writes to the frame assumption
   (MAYCHANGE ...) s0 sk, which every later step processes again, so over a
   long run it would grow to thousands of terms. NATIVE2_FRAME_TAC replaces
   it by the frame of the postcondition of the goal, which subsumes it as it
   does at the end, and the drivers call it every 50 steps. It leaves a
   frame with variables that the goal's has not (such as the abbreviated
   frame base of the x86 API proofs), as the subsumption then needs more
   than MONOTONE_MAYCHANGE_TAC. *)

let NATIVE2_FRAME_TAC (asl,w as gl) =
  let sv = rand w in
  let isframe c =
    is_comb c && rand c = sv && maychange_term c &&
    is_comb(rator c) && type_of(rand(rator c)) = type_of sv in
  match (try let bv,body = dest_abs(rand(rator w)) in
             let fr = vsubst [sv,bv] (find maychange_term (conjuncts body)) in
             Some(fr,find (isframe o concl) (map snd asl))
         with Failure _ -> None) with
    Some(fr,old) when concl old <> fr &&
                      subset (frees(concl old)) (frees fr) ->
      UNDISCH_THEN (concl old) (fun th ->
        SUBGOAL_THEN fr ASSUME_TAC THENL
         [POP_ASSUM_LIST(K ALL_TAC) THEN ASSUME_TAC th THEN
          MONOTONE_MAYCHANGE_TAC;
          ALL_TAC]) gl
  | _ -> ALL_TAC gl;;

let rec NATIVE2_RUN_TAC exec derive calls k gl =
  let off = get_pc_offset k gl in
  if off < 0 then ALL_TAC gl else
  let dtac = try (assoc off derive) k with Failure _ -> ALL_TAC in
  let ctac = try (assoc off calls) k
             with Failure _ -> X86_STEPS_TAC exec [k+1] in
  ((if k > 0 && k mod 50 = 0 then NATIVE2_FRAME_TAC else ALL_TAC) THEN
   dtac THEN ctac THEN NATIVE2_RUN_TAC exec derive calls (k+1)) gl;;

(* ------------------------------------------------------------------------- *)
(* A call at state k (RIP at the callee's entry) by the subroutine theorem   *)
(* th for the code submc at offset in the image mc, with the arguments args  *)
(* (terms in s) followed by the callee's pc, stack pointer and return        *)
(* address, which come from the state.                                       *)
(* ------------------------------------------------------------------------- *)

let NATIVE2_CALL_TAC mc exec (offset,submc,th) args k =
  X86_SUBROUTINE_SIM_TAC (mc,exec,offset,submc,th)
   (args @ [mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral offset);
            `read RSP s`; `read (memory :> bytes64(read RSP s)) s`]) (k+1);;

(* ------------------------------------------------------------------------- *)
(* A ghost function for a buffer that a callee has written: the n 16-bit     *)
(* values at address a in state k as a new function with the given name,     *)
(* the facts in the assumptions about them rewritten in its terms, and the   *)
(* bounded form !i. i < n ==> read ... = name i, which the simulation keeps  *)
(* after stores elsewhere (it does not keep the unbounded one).              *)
(* ------------------------------------------------------------------------- *)

let NATIVE2_GHOST_TAC name a n k =
  let f = mk_var(name,`:num->int16`) in
  let inst = vsubst [state_of k,`s:x86state`; a,`a:int64`; f,`f:num->int16`;
                     mk_small_numeral n,`n:num`] in
  let rd = inst
    `\i. read (memory :> bytes16 (word_add a (word (2 * i)))) s`
  and uth = inst
    `!i. read (memory :> bytes16 (word_add a (word (2 * i)))) s = f i`
  and bth = inst
    `!i. i < n ==> read (memory :> bytes16 (word_add a (word (2 * i)))) s =
                   f i` in
  let keep th = let c = concl th in (is_eq c && rand c = f) || c = bth in
  RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV let_CONV)) THEN
  ABBREV_TAC (mk_eq(f,rd)) THEN
  SUBGOAL_THEN bth ASSUME_TAC THENL
   [EXPAND_TAC name THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN uth
   (fun th -> RULE_ASSUM_TAC(fun a -> if keep a then a
                                      else REWRITE_RULE[th] a))
  THENL [EXPAND_TAC name THEN REWRITE_TAC[]; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Safety. The SAFE theorems of the callees must keep their frames (what     *)
(* they may change), for the simulation of the caller to go on after the     *)
(* calls, and be in the subroutine form, with the return. Those from         *)
(* mk_safety_spec without ~keep_maychanges are not, so x86_framed_safe makes *)
(* them from the CORRECT theorems of a leaf function without a stack frame:  *)
(* the core theorem by PROVE_SAFETY_SPEC_TAC, the NOIBT one by               *)
(* X86_PROMOTE_RETURN_NOSTACK_TAC and then the IBT one by ADD_IBT_RULE.      *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

(*** The statement of the NOIBT subroutine form, from the core SAFE theorem
 *** (for f_events and the regions) and the NOIBT CORRECT theorem (for the
 *** hypotheses, the code and the frame), with the stack pointer and return
 *** address added to the arguments of f_events and the slot of the return
 *** address to the regions. All its variables are quantified, also those
 *** left free in the CORRECT theorem (as stackpointer and returnaddress
 *** in those of mlkem_frombytes, mlkem_tobytes and mlkem_unpack).
 ***)

let x86_noibt_safe_tm core_safe noibt_correct =
  let _,body = dest_exists(concl core_safe) in
  let _,cimp = strip_forall body in
  let s,cpb = dest_abs(el 2 (snd(strip_comb(rand cimp)))) in
  let e2,exb = dest_exists(find is_exists (conjuncts cpb)) in
  let c1,c23 = dest_conj exb in
  let c2,c3 = dest_conj c23 in
  let fargs = snd(strip_comb(rand c2)) in
  let mia,margs = strip_comb c3 in
  let rd = el 1 margs and wr = el 2 margs in
  let nvs,nimp = strip_forall(concl noibt_correct) in
  let nhyp,nens = dest_imp nimp in
  let ensc,nargs = strip_comb nens in
  let sem = el 0 nargs and npre = el 1 nargs and npost = el 2 nargs
  and nframe = el 3 nargs in
  let s',npb = dest_abs npre and s'',nqb = dest_abs npost in
  let is_read_of p c =
    is_eq c && (let l = lhand c in is_comb l && p (rator l)) in
  let keep c =
    (let h = fst(strip_comb c) in
     is_const h && mem (name_of h) ["bytes_loaded"; "C_ARGUMENTS"]) ||
    is_read_of (fun r -> r = `read RIP` || r = `read RSP` ||
                         can (term_match [] `read (memory :> bytes64 spv)`) r)
      c in
  let isreg = is_read_of (fun r -> r = `read RIP` || r = `read RSP`) in
  let ev = `e:(uarch_event)list` in
  let fargs' = fargs @ [`stackpointer:int64`; `returnaddress:int64`] in
  let fv = mk_var("f_events",
    itlist (fun a t -> mk_fun_ty (type_of a) t) fargs' `:(uarch_event)list`) in
  let addsp l = mk_list(dest_list l @ [`stackpointer:int64,8`],`:int64#num`) in
  let pre' = mk_abs(s',list_mk_conj(filter keep (conjuncts npb) @
                [mk_eq(mk_comb(`read events`,s'),ev)]))
  and post' = mk_abs(s'',list_mk_conj(filter isreg (conjuncts nqb) @
                [mk_exists(e2,list_mk_conj
                  [vsubst [s'',s] c1; mk_eq(e2,list_mk_comb(fv,fargs'));
                   list_mk_comb(mia,[e2; addsp rd; addsp wr])])])) in
  let body' = mk_imp(nhyp,list_mk_comb(ensc,[sem;pre';post';nframe])) in
  let qvs = ev :: filter (fun v -> free_in v body') nvs in
  let extra = subtract (frees body') (fv::qvs) in
  let first = filter (fun v -> mem v extra)
                [`stackpointer:int64`; `returnaddress:int64`] in
  mk_exists(fv,list_mk_forall(qvs @ first @ subtract extra first,body'));;

(*** The core, NOIBT and IBT SAFE theorems of the function with the name in
 *** subroutine_signatures, from its core and NOIBT CORRECT theorems
 ***)

let x86_framed_safe name core_correct core_exec noibt_correct tmc =
  let spec,pubs = mk_safety_spec ~keep_maychanges:true
                   (assoc name subroutine_signatures) core_correct core_exec in
  let core = prove(spec,
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    PROVE_SAFETY_SPEC_TAC ~public_vars:pubs core_exec) in
  let noibt = prove(x86_noibt_safe_tm core noibt_correct,
    X86_PROMOTE_RETURN_NOSTACK_TAC tmc core THEN
    DISCHARGE_SAFETY_PROPERTY_TAC) in
  core,noibt,ADD_IBT_RULE noibt;;

(* ------------------------------------------------------------------------- *)
(* A call at state k by the SAFE theorem with the label in the assumptions   *)
(* (put there by ASSUME_CALLEE_SAFETY_TAILED_TAC, and put back after), with  *)
(* the arguments as for NATIVE2_CALL_TAC; the events of the caller so far    *)
(* are a function of vars.                                                   *)
(* ------------------------------------------------------------------------- *)

let NATIVE2_SAFE_CALL_TAC mc exec vars label (offset,submc) args k =
  REMOVE_THEN label (fun th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true (mc,exec,offset,submc,th)
     (`e:(uarch_event)list` :: args @
      [mk_binop `(+):num->num->num` `pc:num` (mk_small_numeral offset);
       `read RSP s`; `read (memory :> bytes64(read RSP s)) s`]) (k+1)
    THENL [EXISTS_E2_TAC (ref vars); LABEL_TAC label th]);;
