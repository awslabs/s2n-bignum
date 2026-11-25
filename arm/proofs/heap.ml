(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Contracts of an external allocator on AArch64 (C++ operator new and       *)
(* delete, malloc and free) and tactics for calls of it with bstep.          *)
(*                                                                           *)
(* The model (see common/heap.ml for heap_ok, heap_fp, heap_room and         *)
(* heap_props) is the hypothesis                                             *)
(*                                                                           *)
(*   heap_model heap_ok heap_fp heap_room stk f_new f_delete                 *)
(*                                                                           *)
(* of a client theorem, universally quantified over the first four           *)
(* parameters: the client knows nothing of the allocator but what the model  *)
(* says. f_new and f_delete are the addresses of the two functions (read     *)
(* from the GOT by a caller through the PLT). stk bounds the stack that the  *)
(* functions use below the SP of the call. A pair new[]/delete[], or         *)
(* malloc/free, of the same allocator is a second heap_model with the same   *)
(* heap_ok, heap_fp and heap_room. Sized operator delete (X1 the size) meets *)
(* the contract of delete, which does not read X1.                          *)
(*                                                                           *)
(* new (heap_new_contract): from heap_ok H at the call with X0 = sz,          *)
(* heap_room H (val sz), and the stack below SP outside heap_fp H, it        *)
(* returns to X30 with X0 = p, p nonzero, 16-byte aligned, not wrapping,     *)
(* not the address of a live block, its bytes in heap_fp H, heap_ok of       *)
(* (p,val sz)::H and a footprint for it within heap_fp H. It may change the  *)
(* registers that the ABI allows and X18, X30, the stack below SP (stk       *)
(* bytes) and memory in heap_fp H, and it reads and writes only these.       *)
(*                                                                           *)
(* delete (heap_delete_contract): from heap_ok H with X0 = p, (p,n) a block  *)
(* of H, it returns with heap_ok of heap_remove p H and a footprint for it   *)
(* within heap_fp H UNION memrange(p,n); it may change the same as new and   *)
(* the freed block. With X0 = 0 it keeps heap_ok H.                          *)
(*                                                                           *)
(* All three include memory safety: the events of the call are APPEND e2 e   *)
(* with memaccess_inset e2 R R for R the memory the call may change. There   *)
(* is no claim that e2 is a function of public values.                       *)
(*                                                                           *)
(* The non-vacuity of the model, an allocator in AArch64 code that meets it  *)
(* with a nontrivial heap_room and an invariant that holds initially, is     *)
(* arm/heap/heap_slab.ml.                                                    *)
(* ========================================================================= *)

needs "arm/proofs/bstep.ml";;
needs "common/heap.ml";;

(* ------------------------------------------------------------------------- *)
(* The contracts.                                                            *)
(* ------------------------------------------------------------------------- *)

let heap_new_contract = new_definition
 `heap_new_contract (heap_ok:(int64#num)list->(int64->byte)->bool)
                    (heap_fp:(int64#num)list->int64->bool)
                    (heap_room:(int64#num)list->num->bool)
                    (stk:num) (f_new:int64) <=>
  !H sz sp returnaddress e.
     heap_room H (val sz) /\
     DISJOINT (memrange(word_sub sp (word stk),stk)) (heap_fp H)
     ==> ensures arm
          (\s. read PC s = f_new /\ read SP s = sp /\
               read X30 s = returnaddress /\ read X0 s = sz /\
               read events s = e /\
               heap_ok H (read (memory :> footprint (heap_fp H)) s))
          (\s. read PC s = returnaddress /\
               ?p. read X0 s = p /\
                   ~(p = word 0) /\ aligned 16 p /\
                   val p + val sz < 2 EXP 64 /\
                   ~MEM p (MAP FST H) /\
                   memrange(p,val sz) SUBSET heap_fp H /\
                   heap_fp (CONS (p,val sz) H) SUBSET heap_fp H /\
                   heap_ok (CONS (p,val sz) H)
                     (read (memory :> footprint
                                (heap_fp (CONS (p,val sz) H))) s) /\
                   ?e2. read events s = APPEND e2 e /\
                        memaccess_inset e2
                         (heap_fp H UNION memrange(word_sub sp (word stk),stk))
                         (heap_fp H UNION memrange(word_sub sp (word stk),stk)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
           MAYCHANGE [memory :> bytes(word_sub sp (word stk),stk)] ,,
           MAYCHANGE [memory :> footprint (heap_fp H)])`;;

let heap_delete_contract = new_definition
 `heap_delete_contract (heap_ok:(int64#num)list->(int64->byte)->bool)
                       (heap_fp:(int64#num)list->int64->bool)
                       (stk:num) (f_delete:int64) <=>
  (!H p n sp returnaddress e.
     MEM (p,n) H /\
     DISJOINT (memrange(word_sub sp (word stk),stk))
              (heap_fp H UNION memrange(p,n))
     ==> ensures arm
          (\s. read PC s = f_delete /\ read SP s = sp /\
               read X30 s = returnaddress /\ read X0 s = p /\
               read events s = e /\
               heap_ok H (read (memory :> footprint (heap_fp H)) s))
          (\s. read PC s = returnaddress /\
               heap_fp (heap_remove p H) SUBSET heap_fp H UNION memrange(p,n) /\
               heap_ok (heap_remove p H)
                 (read (memory :> footprint (heap_fp (heap_remove p H))) s) /\
               ?e2. read events s = APPEND e2 e /\
                    memaccess_inset e2
                     (heap_fp H UNION memrange(p,n) UNION
                      memrange(word_sub sp (word stk),stk))
                     (heap_fp H UNION memrange(p,n) UNION
                      memrange(word_sub sp (word stk),stk)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
           MAYCHANGE [memory :> bytes(word_sub sp (word stk),stk)] ,,
           MAYCHANGE [memory :> footprint (heap_fp H)] ,,
           MAYCHANGE [memory :> bytes(p,n)])) /\
  (!H sp returnaddress e.
     DISJOINT (memrange(word_sub sp (word stk),stk)) (heap_fp H)
     ==> ensures arm
          (\s. read PC s = f_delete /\ read SP s = sp /\
               read X30 s = returnaddress /\ read X0 s = word 0 /\
               read events s = e /\
               heap_ok H (read (memory :> footprint (heap_fp H)) s))
          (\s. read PC s = returnaddress /\
               heap_ok H (read (memory :> footprint (heap_fp H)) s) /\
               ?e2. read events s = APPEND e2 e /\
                    memaccess_inset e2
                     (heap_fp H UNION memrange(word_sub sp (word stk),stk))
                     (heap_fp H UNION memrange(word_sub sp (word stk),stk)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
           MAYCHANGE [memory :> bytes(word_sub sp (word stk),stk)] ,,
           MAYCHANGE [memory :> footprint (heap_fp H)]))`;;

let heap_model = new_definition
 `heap_model (heap_ok:(int64#num)list->(int64->byte)->bool)
             (heap_fp:(int64#num)list->int64->bool)
             (heap_room:(int64#num)list->num->bool)
             (stk:num) (f_new:int64) (f_delete:int64) <=>
    heap_props heap_ok heap_fp /\
    heap_new_contract heap_ok heap_fp heap_room stk f_new /\
    heap_delete_contract heap_ok heap_fp stk f_delete`;;

(* The parts of the model as theorems.                                       *)

let HEAP_MODEL_PROPS = prove
 (`!heap_ok heap_fp heap_room stk f_new f_delete.
        heap_model heap_ok heap_fp heap_room stk f_new f_delete
        ==> heap_props heap_ok heap_fp`,
  SIMP_TAC[heap_model]);;

let HEAP_MODEL_NEW = prove
 (`!heap_ok heap_fp heap_room stk f_new f_delete.
        heap_model heap_ok heap_fp heap_room stk f_new f_delete
        ==> heap_new_contract heap_ok heap_fp heap_room stk f_new`,
  SIMP_TAC[heap_model]);;

let HEAP_MODEL_DELETE = prove
 (`!heap_ok heap_fp heap_room stk f_new f_delete.
        heap_model heap_ok heap_fp heap_room stk f_new f_delete
        ==> heap_delete_contract heap_ok heap_fp stk f_delete`,
  SIMP_TAC[heap_model]);;

(* The stack that a call uses is within a numeral bound K >= stk below SP.   *)

let MEMRANGE_STACK_SUBSET = prove
 (`!(sp:int64) stk k.
        stk <= k
        ==> memrange(word_sub sp (word stk),stk) SUBSET
            memrange(word_sub sp (word k),k)`,
  REWRITE_TAC[MEMRANGE_BELOW_SUBSET]);;

let MAYCHANGE_BYTES_SUBSUMED = prove
 (`!(m:(S,N word->byte)component) a k b l.
        memrange(a,k) SUBSET memrange(b,l)
        ==> MAYCHANGE [m :> bytes(a,k)] subsumed MAYCHANGE [m :> bytes(b,l)]`,
  REWRITE_TAC[GSYM CONTAINED_MEMRANGE; contained; MAYCHANGE_SING] THEN
  SIMP_TAC[SUBSUMED_ASSIGNS_SUBCOMPONENTS; SUBSUMED_ASSIGNS_BYTES]);;

(* ------------------------------------------------------------------------- *)
(* Calls of new and delete with bstep.                                       *)
(*                                                                           *)
(* ARM_HEAP_NEW_TAC execth model_th "p" "s3", on a goal `eventually arm P    *)
(* s2` at the call (PC = f_new), with model_th the hypothesis                *)
(* |- heap_model heap_ok heap_fp heap_room stk f_new f_delete, goes through   *)
(* the contract of new by ARM_BSTEP_CALL_TAC to a state s3 and names the     *)
(* block p. It needs among the assumptions                                   *)
(*                                                                           *)
(*   read SP s2 = sp, read X30 s2 = ra, read X0 s2 = sz (read events s2 = e  *)
(*   if the goal is about events),                                           *)
(*   heap_ok H (read (memory :> footprint (heap_fp H)) s2),                  *)
(*   heap_room H n with n the value of val sz,                               *)
(*   stk <= K for a numeral K, and the region (word_sub sp (word K),K)       *)
(*   outside heap_fp H (by the facts of common/footprint.ml),                *)
(*                                                                           *)
(* and the frame of the goal needs a clause MAYCHANGE [memory :> bytes(b,l)] *)
(* that contains that region: the callee's use of the stack is weakened to   *)
(* it, so that the facts about the rest of the caller's stack are kept. The  *)
(* new goal has the postcondition of new with the block p, its size reduced  *)
(* to a numeral where it is one, ~MEM p (MAP FST H) as ~(p = q) for the      *)
(* blocks (q,m) in front of H, and DISJOINT (memrange(p,n)) (heap_fp         *)
(* ((p,n)::H)) from heap_props.                                              *)
(*                                                                           *)
(* ARM_HEAP_DELETE_TAC execth model_th "s5" is the same for delete with      *)
(* X0 = p, for a block (p,n) of H: H a list with (p,n) in it, or with the    *)
(* assumption MEM (p,n) H; heap_remove p H is simplified for a list with the *)
(* facts ~(q = p). ARM_HEAP_DELETE_NULL_TAC is delete with X0 = word 0.      *)
(* ------------------------------------------------------------------------- *)

let heap_read_value (asl:(string * thm) list) c s =
  let tm = list_mk_icomb "read" [c;s] in
  rhs(concl(snd(find (fun (_,th) ->
      is_eq(concl th) && compare (lhs(concl th)) tm = 0) asl)));;

(* The heap_ok fact at s: (H, |- heap_ok H (read (memory :> footprint       *)
(* (heap_fp H)) s)).                                                         *)

let heap_ok_fact ok (asl:(string * thm) list) s =
  let th = snd(find (fun (_,th) ->
      match concl th with
        Comb(Comb(f0,_),Comb(Comb(Const("read",_),_),s')) ->
          compare f0 ok = 0 && compare s' s = 0
      | _ -> false) asl) in
  rand(rator(concl th)),th;;

(* fr with the clause old replaced by new, and |- fr subsumed fr', from      *)
(* cth: |- old subsumed new.                                                 *)

let rec heap_frame_weaken fr old cth =
  match fr with
    Comb(Comb(Const(",,",_) as op,a),b) ->
      let a',tha = heap_frame_weaken a old cth
      and b',thb = heap_frame_weaken b old cth in
      mk_comb(mk_comb(op,a'),b'),MATCH_MP SUBSUMED_SEQ (CONJ tha thb)
  | _ -> if compare fr old = 0 then rand(concl cth),cth
         else fr,ISPEC fr SUBSUMED_REFL;;

(* The frame of the postcondition of the goal.                               *)

let heap_goal_frame w =
  let p = rand(rator w) in
  let bv,bod = dest_abs p in
  rator(rator(find (fun c -> maychange_term c && rand c = bv)
                   (conjuncts bod)));;

(* Rename the free variable v to v' everywhere in the goal: in the          *)
(* assumptions as theorems (their hypotheses too), so that what they were    *)
(* proved from stays.                                                        *)

let HEAP_RENAME_TAC v v' : tactic =
  fun (asl,w) ->
    let has th = shared_occurs v (concl th) || exists (shared_occurs v) (hyp th) in
    let f th = if has th then INST [v',v] th else th in
    null_meta,[map (fun (l,th) -> l,f th) asl,
               if shared_occurs v w then vsubst [v',v] w else w],
    (fun i ths -> match ths with
        [th] -> INST [v,v'] th
      | _ -> failwith "HEAP_RENAME_TAC");;

(* The callee's stack, from the contract instance eth with SP = sp, weakened *)
(* to a clause of the goal's frame, and |- DISJOINT (memrange(word_sub sp   *)
(* (word stk),stk)) t for the footprint t of the precondition.               *)

let heap_stack_weaken (asl:(string * thm) list) stk sp w =
  let kth = snd(find (fun (_,th) ->
      match concl th with
        Comb(Comb(Const("<=",_),x),k) -> compare x stk = 0 && is_numeral k
      | _ -> false) asl) in
  let k = rand(concl kth) in
  let cth0 = MATCH_MP (SPECL [sp;stk;k] MEMRANGE_STACK_SUBSET) kth in
  let region = (mk_icomb(mk_icomb(`word_sub:int64->int64->int64`,sp),
                         mk_comb(`word:num->int64`,k)),k) in
  let clauses = try maychange_components (heap_goal_frame w)
                with Failure _ -> [] in
  let target = tryfind (fun c ->
      match c with
        Comb(Comb(Const(":>",_),Const("memory",_)),
             Comb(Const("bytes",_),Comb(Comb(Const(",",_),b),l))) ->
          c,memrange_subset_rule region (b,l)
      | _ -> failwith "") clauses in
  cth0,region,target;;

let HEAP_CALL_TAC (which:string) execth model_th (pname:string)
                  (sname:string) : tactic =
  fun (asl,w) ->
    let fail msg = failwith ("ARM_HEAP_" ^ which ^ "_TAC: " ^ msg) in
    let s = match w with
        Comb(Comb(Comb(Const("eventually",_),_),_),s) when is_var s -> s
      | _ -> fail "the goal is not `eventually arm P s`" in
    let ok,fp,room,stk = match snd(strip_comb(concl model_th)) with
        [ok;fp;room;stk;_;_] -> ok,fp,room,stk
      | _ -> fail "not a heap_model theorem" in
    let static = filter (fun (_,th) -> not(shared_occurs s (concl th))) asl in
    set_component_assumptions (map snd static);
    let value c = try heap_read_value asl c s with Failure _ ->
      fail ("no fact `read " ^ string_of_term c ^ " " ^ fst(dest_var s) ^
            " = ...`") in
    let sp = value `SP` and ra = value `X30` and x0 = value `X0` in
    let ev = try heap_read_value asl `events` s
             with Failure _ -> list_mk_icomb "read" [`events`;s] in
    let h,okth = try heap_ok_fact ok asl s with Failure _ ->
      fail "no heap_ok fact for the state" in
    let props = MATCH_MP HEAP_MODEL_PROPS model_th in
    let cth0,region,(_,cth1) =
      try heap_stack_weaken asl stk sp w with Failure _ ->
        fail ("no assumption `" ^ string_of_term stk ^ " <= K` or no " ^
              "clause of the frame for the stack below SP") in
    let stack = lhand(concl cth0) in
    let rm r = mk_icomb(`memrange:int64#num->int64->bool`,mk_pair r) in
    let disj t =
      let dth = try footprint_disjoint_rule (rm region) t with Failure _ ->
        fail ("cannot show the stack below SP outside `" ^
              string_of_term t ^ "`") in
      MATCH_MP DISJOINT_SUBSETS
        (CONJ cth0 (CONJ (ISPEC t SUBSET_REFL) dth)) in
    let reduce = CONV_RULE(DEPTH_CONV(WORD_RED_CONV ORELSEC NUM_RED_CONV)) in
    let eth,post_tac =
      match which with
        "NEW" ->
          let cth = MATCH_MP HEAP_MODEL_NEW model_th in
          let ith = SPECL [h;x0;sp;ra;ev]
                      (REWRITE_RULE[heap_new_contract] cth) in
          let rth =
            let tm = lhand(lhand(concl ith)) in
            let find_asm t = snd(find (fun (_,th) -> compare (concl th) t = 0)
                                      asl) in
            try find_asm tm with Failure _ ->
            try let eq = DEPTH_CONV WORD_RED_CONV tm in
                EQ_MP (SYM eq) (find_asm (rand(concl eq)))
            with Failure _ ->
              fail ("no assumption `" ^ string_of_term tm ^ "`") in
          let fpH = mk_comb(fp,h) in
          MP ith (CONJ rth (disj fpH)),
          (fun p ->
             (* the size as a numeral, and the new block outside the new  *)
             (* footprint                                                 *)
             W(fun (asl,w) ->
               let mentions th = vfree_in p (concl th) &&
                                 not(shared_occurs s (concl th)) in
               let newok = snd(find (fun (_,th) ->
                 match concl th with
                   Comb(Comb(f0,_),_) -> compare f0 ok = 0 &&
                                        vfree_in p (concl th)
                 | _ -> false) asl) in
               let dth = MATCH_MP HEAP_NEW_BLOCK_DISJOINT (CONJ props newok) in
               RULE_ASSUM_TAC(fun th ->
                 if mentions th || (vfree_in p (concl th) &&
                                    compare (rator(rator(concl th))) ok = 0)
                 then reduce th else th) THEN
               ASSUME_TAC(reduce dth) THEN
               (* ~MEM p (MAP FST H) as ~(p = q) for the blocks of a list H *)
               RULE_ASSUM_TAC(fun th ->
                 match concl th with
                   Comb(Const("~",_),Comb(Comb(Const("MEM",_),q),_))
                     when compare q p = 0 ->
                     REWRITE_RULE[MAP; MEM; FST; DE_MORGAN_THM] th
                 | _ -> th)))
      | "DELETE" ->
          let cth = CONJUNCT1(REWRITE_RULE[heap_delete_contract]
                      (MATCH_MP HEAP_MODEL_DELETE model_th)) in
          let p = x0 in
          (* the block: from MEM (p,n) H or the list                         *)
          let memth =
            try snd(find (fun (_,th) -> match concl th with
                Comb(Comb(Const("MEM",_),Comb(Comb(Const(",",_),q),_)),hh) ->
                  compare q p = 0 && compare hh h = 0
              | _ -> false) asl)
            with Failure _ ->
              let rec blocks l = match l with
                  Comb(Comb(Const("CONS",_),b),t) -> b::blocks t
                | _ -> [] in
              let b = try find (fun b -> compare (fst(dest_pair b)) p = 0)
                               (blocks h)
                      with Failure _ -> fail "no block at X0 in H" in
              EQT_ELIM(REWRITE_CONV[MEM] (mk_icomb(mk_icomb(`MEM:A->A list->bool`,
                                           b),h))) in
          let n = rand(rand(rator(concl memth))) in
          let ith = SPECL [h;p;n;sp;ra;ev] cth in
          let t = mk_icomb(mk_icomb(`(UNION):(int64->bool)->(int64->bool)->int64->bool`,
                                    mk_comb(fp,h)),rm(p,n)) in
          MP ith (CONJ memth (disj t)),
          (fun _ -> W(fun (asl,_) ->
             (* heap_remove p H as a list, with the facts ~(q = p) about   *)
             (* the addresses of the blocks in front of p                   *)
             let neqs = filter (fun th -> match concl th with
                 Comb(Const("~",_),Comb(Comb(Const("=",_),x),_)) ->
                   type_of x = `:int64`
               | _ -> false)
               (flat(map (CONJUNCTS o snd) asl)) in
             let neqs = neqs @ map (CONV_RULE(RAND_CONV SYM_CONV)) neqs in
             RULE_ASSUM_TAC(fun th ->
               if not(shared_occurs s (concl th)) &&
                  can (find_term (fun t -> is_const t &&
                           fst(dest_const t) = "heap_remove")) (concl th)
               then REWRITE_RULE(HEAP_REMOVE_CONS :: heap_remove :: FST ::
                                 neqs) th
               else th)))
      | "DELETE_NULL" ->
          let cth = CONJUNCT2(REWRITE_RULE[heap_delete_contract]
                      (MATCH_MP HEAP_MODEL_DELETE model_th)) in
          let ith = SPECL [h;sp;ra;ev] cth in
          MP ith (disj (mk_comb(fp,h))),(fun _ -> ALL_TAC)
      | _ -> fail "which" in
    (* the frame: the callee's stack within the goal's clause               *)
    let old = mk_icomb(`MAYCHANGE:((armstate,num)component)list->armstate->armstate->bool`,
                       mk_flist[mk_icomb(mk_icomb(`(:>):(armstate,int64->byte)component->(int64->byte,num)component->(armstate,num)component`,
                         `memory`),mk_icomb(`bytes:int64#num->(int64->byte,num)component`,
                                            mk_pair(lhand(rand(stack)),rand(rand(stack)))))]) in
    let sub = MATCH_MP MAYCHANGE_BYTES_SUBSUMED
                (MATCH_MP SUBSET_TRANS (CONJ cth0 cth1)) in
    let sub = PART_MATCH lhand sub old in
    let fr = rand(concl eth) in
    let _,fth = heap_frame_weaken fr old sub in
    let eth' = MATCH_MP ENSURES_FRAME_SUBSUMED (CONJ fth eth) in
    let eth' = CONV_RULE (RAND_CONV (REWRITE_CONV
                 [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI])) eth' in
    (ARM_BSTEP_CALL_TAC execth eth' sname THEN
     (if which = "NEW" then
        W(fun (asl,w) ->
          let s' = rand w in
          let v = heap_read_value asl `X0` s' in
          let pv = mk_var(pname,type_of v) in
          (if is_var v && v <> pv then HEAP_RENAME_TAC v pv else ALL_TAC) THEN
          post_tac pv)
      else post_tac `T`)) (asl,w);;

let ARM_HEAP_NEW_TAC execth model_th pname sname =
  HEAP_CALL_TAC "NEW" execth model_th pname sname;;

let ARM_HEAP_DELETE_TAC execth model_th sname =
  HEAP_CALL_TAC "DELETE" execth model_th "" sname;;

let ARM_HEAP_DELETE_NULL_TAC execth model_th sname =
  HEAP_CALL_TAC "DELETE_NULL" execth model_th "" sname;;
