(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Calls of an external allocator through the PLT of a shared object, and    *)
(* calls of contracts with hypotheses about the heap, with bstep.            *)
(*                                                                           *)
(* The contracts of arm/proofs/heap.ml are about the functions at f_new and  *)
(* f_delete. A shared object reaches them through its PLT: a call            *)
(* bl <operator new@plt> runs the stub                                       *)
(*                                                                           *)
(*     adrp x16, <page of the GOT slot>                                      *)
(*     ldr  x17, [x16, #<offset>]                                            *)
(*     add  x16, x16, #<offset>                                              *)
(*     br   x17                                                              *)
(*                                                                           *)
(* whose ldr reads the GOT slot of the import, which the loader set to       *)
(* imp "_Znwm" (operator new(size_t)), imp "_ZdlPv" (operator               *)
(* delete(void* )), imp "_Znam" or imp "_ZdaPv" (the array forms); the slot  *)
(* fact comes from ELF_RELOCATED_DATA_TAC (common/elf_image.ml). A client    *)
(* theorem of such an object therefore has the hypothesis                    *)
(*                                                                           *)
(*   heap_model heap_ok heap_fp heap_room stk (imp "_Znwm") (imp "_ZdlPv")   *)
(*                                                                           *)
(* (and a second one with "_Znam" and "_ZdaPv" for the array forms), and     *)
(* its writes, the image and the slots must be outside heap_fp H.            *)
(*                                                                           *)
(* With the goal at the stub (after the block that ended with the bl or the  *)
(* b of a tail call):                                                        *)
(*                                                                           *)
(*  - ARM_BSTEP_PLT_HEAP_NEW_TAC execth model_th "p" "s<n>" steps the stub   *)
(*    and goes through the contract of new (ARM_HEAP_NEW_TAC), naming the    *)
(*    block p;                                                               *)
(*  - ARM_BSTEP_PLT_HEAP_DELETE_TAC execth model_th "s<n>" and               *)
(*    ARM_BSTEP_PLT_HEAP_DELETE_NULL_TAC execth model_th "s<n>" do the same  *)
(*    for delete of a live block and of the null pointer; the first also     *)
(*    adds DISJOINT (memrange(p,n)) (heap_fp H) for the blocks (p,n) of H    *)
(*    with assumptions MEM (p,n) H (HEAP_BLOCK_DISJOINT_TAC), which the     *)
(*    frame of a client with the clauses of delete's frame needs.           *)
(*                                                                           *)
(* execth must decode the stub (layout_range "plt_operator_new", ...). The   *)
(* side conditions are those of ARM_HEAP_NEW_TAC (arm/proofs/heap.ml).       *)
(*                                                                           *)
(* For calls of other contracts (in-image callees, or the libc contracts),   *)
(* ARM_BSTEP_CONTRACT_TAC execth th ilist "s<n>" is ARM_BSTEP_PLT_CALL_TAC   *)
(* (arm/proofs/libc.ml) made to work with callees whose theorems have        *)
(* hypotheses about the heap, with the facts that the calls of new give:     *)
(*                                                                           *)
(*  - th, instantiated with ilist (terms in s, or free variables), is first  *)
(*    rewritten with the assumptions val x = t (x not a variable, such as    *)
(*    val (word (2 * n)) = 2 * n) that the proof states for the arguments;  *)
(*  - each conjunct of its hypothesis is proved as an assumption (up to the *)
(*    reduction of numerals), the alignment of an address at a numeral      *)
(*    offset from an aligned one, a SUBSET or DISJOINT fact of sets of      *)
(*    addresses (footprint_subset_rule, footprint_disjoint_rule of           *)
(*    common/footprint.ml), a nonoverlapping fact (NONOVERLAPPING_TAC, or    *)
(*    the DISJOINT form by the footprint rules), or an inequality of numbers *)
(*    that follows from those among the assumptions (such as                 *)
(*    pc + libsnappy_size <= 2 EXP 64 from the bound of the whole library);  *)
(*  - the byte regions of its frame are weakened to the regions of the       *)
(*    clauses of the goal's frame that contain them (arm_frame_weaken): the  *)
(*    stack of a callee to the caller's clause for the stack of its callees, *)
(*    so that the facts about the caller's own frame cross the call, and    *)
(*    (with ~subs, or ARM_BSTEP_CONTRACT_SUB_TAC subs) to the regions given  *)
(*    by theorems memrange(a,k) SUBSET memrange(b,l).                        *)
(*                                                                           *)
(* ARM_BSTEP_CONTRACT_SPECL_TAC execth th ilist "s<n>" is the same with the  *)
(* addresses of the instance normalized as the step tactics have them (for   *)
(* callees whose objects are at offsets from the caller's stack pointer);    *)
(* LABELLED_TAC names a step of a proof in its failures.                     *)
(*                                                                           *)
(* HEAP_BLOCK_DISJOINT_TAC and HEAP_BLOCK_NONZERO_TAC add the facts about    *)
(* live blocks that heap_props gives; MEMACCESS_INBOUNDS_TO_INSET_TAC turns  *)
(* the events of a libc contract into the set form of MEMACCESS_INSET_TAC;   *)
(* FOOTPRINT_SUBSET_TAC proves a SUBSET goal by footprint_subset_rule.       *)
(*                                                                           *)
(* ENSURES_DROP_EVENTS_TAC proves a correctness statement from the theorem   *)
(* of the same function with memory safety, which has the events in the     *)
(* pre- and postcondition (as the contracts of the heap do).                 *)
(* ========================================================================= *)

needs "arm/proofs/libc.ml";;
needs "arm/proofs/heap.ml";;

(* ------------------------------------------------------------------------- *)
(* The stub and the contracts of the heap.                                   *)
(* ------------------------------------------------------------------------- *)

let ARM_BSTEP_PLT_HEAP_NEW_TAC execth model_th pname sname =
  ARM_BSTEP_PLT_STUB_TAC execth THEN
  ARM_HEAP_NEW_TAC execth model_th pname sname;;

(* For each assumption MEM (p,n) H, with H the live blocks of the heap_ok    *)
(* fact of the current state: DISJOINT (memrange(p,n)) (heap_fp H), from     *)
(* heap_props (HEAP_BLOCK_DISJOINT). A frame with the clauses of the         *)
(* contract of delete, MAYCHANGE [memory :> footprint (heap_fp H)] ,,        *)
(* MAYCHANGE [memory :> bytes(p,n)], needs it to absorb the frame of a call. *)

let HEAP_BLOCK_DISJOINT_TAC model_th : tactic =
  fun (asl,w) ->
    let s = rand w in
    let ok = hd(snd(strip_comb(concl model_th))) in
    let h,okth = heap_ok_fact ok asl s in
    let props = MATCH_MP HEAP_MODEL_PROPS model_th in
    let mems = filter (fun (_,th) -> match concl th with
        Comb(Comb(Const("MEM",_),Comb(Comb(Const(",",_),_),_)),hh) ->
          compare hh h = 0
      | _ -> false) asl in
    let new_th (_,mth) =
      MATCH_MP HEAP_BLOCK_DISJOINT (CONJ props (CONJ okth mth)) in
    MAP_EVERY (ASSUME_TAC o new_th) mems (asl,w);;

(* For each assumption MEM (p,n) H as above: ~(p = word 0) and              *)
(* ~(val p = 0), the forms in which a test of p against 0 (cbz) is decided,  *)
(* from heap_props (HEAP_BLOCKS_MEM).                                        *)

let HEAP_BLOCK_NONZERO_TAC model_th : tactic =
  fun (asl,w) ->
    let s = rand w in
    let ok = hd(snd(strip_comb(concl model_th))) in
    let h,okth = heap_ok_fact ok asl s in
    let bth = MATCH_MP HEAP_PROPS_BLOCKS
                (CONJ (MATCH_MP HEAP_MODEL_PROPS model_th) okth) in
    let mems = filter (fun (_,th) -> match concl th with
        Comb(Comb(Const("MEM",_),Comb(Comb(Const(",",_),_),_)),hh) ->
          compare hh h = 0
      | _ -> false) asl in
    let new_ths (_,mth) =
      let nz = CONJUNCT1(MATCH_MP HEAP_BLOCKS_MEM (CONJ bth mth)) in
      [nz; REWRITE_RULE[GSYM VAL_EQ_0] nz] in
    MAP_EVERY ASSUME_TAC (flat(map new_ths mems)) (asl,w);;

let ARM_BSTEP_PLT_HEAP_DELETE_TAC execth model_th sname =
  ARM_BSTEP_PLT_STUB_TAC execth THEN
  HEAP_BLOCK_DISJOINT_TAC model_th THEN
  ARM_HEAP_DELETE_TAC execth model_th sname;;

let ARM_BSTEP_PLT_HEAP_DELETE_NULL_TAC execth model_th sname =
  ARM_BSTEP_PLT_STUB_TAC execth THEN
  ARM_HEAP_DELETE_NULL_TAC execth model_th sname;;

(* ------------------------------------------------------------------------- *)
(* Calls of contracts whose hypotheses are facts about the heap.             *)
(* ------------------------------------------------------------------------- *)

let ARM_CONTRACT_HYP_TAC : tactic =
  fun (asl,w) ->
    set_component_assumptions (map snd asl);
    let by_rule (asl,w) =
      match w with
        Comb(Comb(Const("SUBSET",_),s),t) ->
          ACCEPT_TAC (footprint_subset_rule s t) (asl,w)
      | Comb(Comb(Const("DISJOINT",_),s),t) ->
          ACCEPT_TAC (footprint_disjoint_rule s t) (asl,w)
      | _ -> failwith "ARM_CONTRACT_HYP_TAC" in
    let by_memrange =
      REWRITE_TAC[NONOVERLAPPING_MEMRANGE] THEN by_rule in
    let by_aligned =
      (ALIGNED_WORD_TAC THEN NO_TAC) ORELSE
      (MATCH_MP_TAC(CONJUNCT1 ALIGNED_WORD_SUB_EQ |> SPEC_ALL |> UNDISCH |>
                    EQ_IMP_RULE |> snd |> DISCH_ALL |>
                    REWRITE_RULE[IMP_IMP] |> GEN_ALL) THEN
       CONJ_TAC THENL
        [FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[aligned; VAL_WORD; DIMINDEX_64] THEN
         CONV_TAC(NUM_REDUCE_CONV THENC DEPTH_CONV DIVIDES_CONV) THEN
         REWRITE_TAC[]] THEN NO_TAC) in
    let by_arith (asl,w) =
      let ok t = (is_binary "<=" t || is_binary "<" t) &&
                 type_of(lhand t) = `:num` in
      if not(ok w) then failwith "by_arith" else
      let ths = filter (fun th -> ok(concl th)) (map snd asl) in
      (MAP_EVERY MP_TAC ths THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC)
      (asl,w) in
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           (match w with
              Comb(Comb(Const("aligned",_),_),_) -> by_aligned
            | _ -> NO_TAC);
           CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN
           (FIRST_ASSUM ACCEPT_TAC ORELSE NO_TAC);
           by_rule;
           CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
           NONOVERLAPPING_TAC;
           by_memrange;
           by_arith] (asl,w);;

(* The byte regions of the frame of eth (an ensures theorem) within a        *)
(* region of a clause MAYCHANGE [memory :> bytes(b,l)] of the frame of the   *)
(* goal w, by memrange_subset_rule (the same base, numeral offsets), are     *)
(* weakened to that region, so that the frame of the call is absorbed into   *)
(* the goal's (bstep absorbs a region only into a clause of the same region  *)
(* or a footprint). A caller with a clause for the stack of its callees and  *)
(* one for its own frame thus keeps the facts about its own frame.           *)

let arm_frame_weaken w eth =
  let targets =
    try filter (fun c -> match c with
        Comb(Comb(Const(":>",_),Const("memory",_)),
             Comb(Const("bytes",_),Comb(Comb(Const(",",_),_),_))) -> true
      | _ -> false) (maychange_components (heap_goal_frame w))
    with Failure _ -> [] in
  if targets = [] then eth else
  let rec go fr =
    match fr with
      Comb(Comb(Const(",,",_) as op,a),b) ->
        let a',tha = go a and b',thb = go b in
        mk_comb(mk_comb(op,a'),b'),MATCH_MP SUBSUMED_SEQ (CONJ tha thb)
    | Comb(Const("MAYCHANGE",_),
           Comb(Comb(Const("CONS",_),
                     (Comb(Comb(Const(":>",_),Const("memory",_)),
                           Comb(Const("bytes",_),
                                Comb(Comb(Const(",",_),a),k))) as c)),
                Const("NIL",_)))
        when not(mem c targets) ->
        (try
           let sub = tryfind (fun t ->
               match t with
                 Comb(_,Comb(_,Comb(Comb(_,b),l))) ->
                   PART_MATCH lhand
                     (MATCH_MP MAYCHANGE_BYTES_SUBSUMED
                        (memrange_subset_rule (a,k) (b,l))) fr
               | _ -> failwith "") targets in
           rand(concl sub),sub
         with Failure _ -> fr,ISPEC fr SUBSUMED_REFL)
    | _ -> fr,ISPEC fr SUBSUMED_REFL in
  let fr = rand(concl eth) in
  let fr',fth = go fr in
  if compare fr fr' = 0 then eth else
  MATCH_MP ENSURES_FRAME_SUBSUMED (CONJ fth eth);;

(* ~subs: theorems memrange(a,k) SUBSET memrange(b,l) that weaken byte      *)
(* regions of the callee's frame to regions of the caller's (for regions     *)
(* whose lengths are not numerals, such as the output of a tag inside the   *)
(* output buffer, which arm_frame_weaken does not relate).                   *)

let arm_frame_weaken_subs (subs:thm list) eth =
  if subs = [] then eth else
  let rec go fr =
    match fr with
      Comb(Comb(Const(",,",_) as op,a),b) ->
        let a',tha = go a and b',thb = go b in
        mk_comb(mk_comb(op,a'),b'),MATCH_MP SUBSUMED_SEQ (CONJ tha thb)
    | Comb(Const("MAYCHANGE",_),
           Comb(Comb(Const("CONS",_),
                     Comb(Comb(Const(":>",_),Const("memory",_)),
                          Comb(Const("bytes",_),
                               Comb(Comb(Const(",",_),a),k)))),
                Const("NIL",_))) ->
        (try
           let r = mk_comb(`memrange:int64#num->int64->bool`,mk_pair(a,k)) in
           let sub = find (fun th -> lhand(concl th) = r) subs in
           let th = PART_MATCH lhand (MATCH_MP MAYCHANGE_BYTES_SUBSUMED sub) fr in
           rand(concl th),th
         with Failure _ -> fr,ISPEC fr SUBSUMED_REFL)
    | _ -> fr,ISPEC fr SUBSUMED_REFL in
  let fr = rand(concl eth) in
  let fr',fth = go fr in
  if compare fr fr' = 0 then eth else
  MATCH_MP ENSURES_FRAME_SUBSUMED (CONJ fth eth);;

let ARM_BSTEP_CONTRACT_TAC ?keep ?(subs:thm list = []) execth (th:thm)
                           (ilist:term list) sname =
  W(fun (asl,w) ->
    set_component_assumptions (map snd asl);
    let s' = rand w in
    let args = map (arm_bstep_eval asl s') ilist in
    let sth = SPECL args th in
    (* the values of words that the assumptions give, val (word t) = t     *)
    let vals = mapfilter (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),(Comb(Const("val",_),_) as l)),_)
          when not(shared_occurs s' (concl th)) && not(is_var(rand l)) -> th
      | _ -> fail()) asl in
    let sth = CONV_RULE(REWRITE_CONV[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
                    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
                    MODIFIABLE_SIMD_REGS; MODIFIABLE_GPRS;
                    MODIFIABLE_UPPER_SIMD_REGS; ALLPAIRS; ALL;
                    PAIRWISE] THENC
                    DEPTH_CONV VAL_WORD_NUMERAL_CONV THENC
                    (if vals = [] then ALL_CONV else
                     PURE_REWRITE_CONV vals)) sth in
    let call eth =
      ARM_BSTEP_CALL_TAC ?keep execth
        (arm_frame_weaken w (arm_frame_weaken_subs subs eth)) in
    if not(is_imp(concl sth)) then call sth sname
    else
    let hyp_tm = lhand(concl sth) in
    let hth =
      try TAC_PROOF((asl,hyp_tm),REPEAT CONJ_TAC THEN ARM_CONTRACT_HYP_TAC)
      with Failure _ ->
        let bad = find (fun c ->
            not(can (fun c -> TAC_PROOF((asl,c),ARM_CONTRACT_HYP_TAC)) c))
          (conjuncts hyp_tm) in
        failwith ("ARM_BSTEP_CONTRACT_TAC: cannot prove the hypothesis `" ^
                  string_of_term bad ^ "`") in
    call (MP sth hth) sname);;

let ARM_BSTEP_CONTRACT_SUB_TAC ?keep (subs:thm list) =
  ARM_BSTEP_CONTRACT_TAC ?keep ~subs;;

(* ARM_BSTEP_CONTRACT_SPECL_TAC ~rules execth th ilist "s<n>": the call of   *)
(* the contract th instantiated with ilist (terms in s, evaluated in the     *)
(* current state), with its addresses in the form of the facts of the step  *)
(* tactics, word_add base (word n) (NORMALIZE_RELATIVE_ADDRESS_CONV), as     *)
(* when the objects of the callee are at offsets from the caller's stack    *)
(* pointer, and then rewritten with ~rules (if any). The value of an        *)
(* argument `read events s` (the events so far) is kept out of the          *)
(* normalization. The instance goes through ARM_BSTEP_CONTRACT_TAC.          *)

let ARM_BSTEP_CONTRACT_SPECL_TAC ?(rules:thm list = []) execth (th:thm)
                                 (ilist:term list) sname =
  W(fun (asl,w) ->
    let args = map (arm_bstep_eval asl (rand w)) ilist in
    let ev_v = `ev_call:uarch_event list` in
    let evs = filter (fun (i,_) -> i = `read events s`) (zip ilist args) in
    let args = map2 (fun i a -> if i = `read events s` then ev_v else a)
                 ilist args in
    let inst_ev th = match evs with (_,a)::_ -> INST [a,ev_v] th | [] -> th in
    let th' = CONV_RULE(DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                (SPECL args th) in
    let th' = if rules = [] then th' else REWRITE_RULE rules th' in
    ARM_BSTEP_CONTRACT_TAC execth (inst_ev th') [] sname);;

(* LABELLED_TAC msg tac: tac, which on failure prints the goal and fails     *)
(* with msg in front of the message; with ~solved:true, it also fails (after *)
(* printing them) if goals remain.                                           *)

let LABELLED_TAC ?(solved=false) msg (tac:tactic) : tactic =
  fun g -> let (_,gls,_) as r =
             try tac g with Failure s ->
               (print_goal g; failwith (msg ^ ": " ^ s)) in
           if solved && gls <> [] then
             (List.iter print_goal gls; failwith (msg ^ ": unsolved"))
           else r;;

(* ------------------------------------------------------------------------- *)
(* Correctness from correctness with memory safety. The goal is              *)
(*                                                                           *)
(*   !x1 ... xn. A ==> ensures arm P Q C                                     *)
(*                                                                           *)
(* (possibly after an outer !y1 ... ym. B ==>, as with heap_model), and sth  *)
(* is the theorem with events of the same statement:                         *)
(*                                                                           *)
(*   !y1 ... ym. B ==> !e x1 ... xn. A ==> ensures arm (P /\ events = e)     *)
(*                                          (Q /\ ?e2. ...) C                *)
(*                                                                           *)
(* with the same variable names and the conjuncts of P and Q in the same    *)
(* order.                                                                    *)
(* ------------------------------------------------------------------------- *)

let ENSURES_DROP_EVENTS_TAC (sth:thm) : tactic =
  REPEAT STRIP_TAC THEN
  W(fun (asl,w) ->
    let prove_ant ant =
      TAC_PROOF((asl,ant),REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC) in
    let ctx = frees w @ freesl (map (concl o snd) asl) in
    let ev = ref None in
    let rec inst th =
      let c = concl th in
      if is_forall c then
        let v,_ = dest_forall c in
        if name_of v = "e" then
          let e = variant ctx v in (ev := Some e; inst (SPEC e th))
        else
          let v' = try find (fun u -> name_of u = name_of v &&
                                      type_of u = type_of v) ctx
                   with Failure _ -> v in
          inst (SPEC v' th)
      else if is_imp c then inst (MP th (prove_ant (lhand c)))
      else th in
    let th = inst sth in
    let e = match !ev with
        Some e -> e
      | None -> failwith "ENSURES_DROP_EVENTS_TAC: no events variable e" in
    let gth = GEN e th in
    REWRITE_TAC[ensures] THEN BETA_TAC THEN
    X_GEN_TAC `s:armstate` THEN DISCH_TAC THEN
    MP_TAC(SPEC `read events (s:armstate)` gth) THEN
    REWRITE_TAC[ensures] THEN BETA_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `s:armstate`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EVENTUALLY_MONO_IMP THEN BETA_TAC THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The events of a callee whose contract states them in the list form       *)
(* memaccess_inbounds e rr wr (the contracts of common/libc_contracts.ml)    *)
(* in the set form memaccess_inset e (memranges rr) (memranges wr) with the  *)
(* memranges unfolded, for MEMACCESS_INSET_TAC.                              *)
(* ------------------------------------------------------------------------- *)

let MEMACCESS_INBOUNDS_TO_INSET_TAC : tactic =
  RULE_ASSUM_TAC(fun th ->
    match concl th with
      Comb(Comb(Comb(Const("memaccess_inbounds",_),_),_),_) ->
        REWRITE_RULE[MEMRANGES_CLAUSES; UNION_EMPTY]
          (MATCH_MP MEMACCESS_INBOUNDS_INSET th)
    | _ -> th);;

(* ------------------------------------------------------------------------- *)
(* A goal s SUBSET t about footprints and regions, by footprint_subset_rule  *)
(* from the assumptions (as the facts heap_fp H' SUBSET heap_fp H UNION      *)
(* memrange(p,n) that the contracts of delete give, chained).                *)
(* ------------------------------------------------------------------------- *)

let FOOTPRINT_SUBSET_TAC : tactic =
  fun (asl,w) ->
    match w with
      Comb(Comb(Const("SUBSET",_),s),t) ->
        set_component_assumptions (map snd asl);
        ACCEPT_TAC (footprint_subset_rule s t) (asl,w)
    | _ -> failwith "FOOTPRINT_SUBSET_TAC";;
