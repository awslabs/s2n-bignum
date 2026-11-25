(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tactics shared by the proofs of the validator chain of snappy             *)
(* (IsValidCompressedBuffer and its callees).                                *)
(*                                                                           *)
(* ENSURES_FRAME_SPLIT_TAC old new: on a goal ensures arm P Q C, replace the *)
(* clause old of the frame C by new, which it subsumes (e.g. a byte region  *)
(* of the stack by its parts). The frame of a callee is weakened to the     *)
(* clause of the caller's frame that contains its region (ARM_BSTEP_CONTRACT_TAC), *)
(* so a caller states its own frame and the stack of its callees as         *)
(* separate clauses to keep the facts about its frame across the call.      *)
(* ========================================================================= *)

needs "arm/proofs/heap_plt.ml";;
needs "arm/proofs/snappy/decompressor_objects.ml";;
needs "common/snappy/snappy_memory.ml";;
needs "arm/proofs/snappy/bstep_decide.ml";;

(* The parts nw, a sequence of byte clauses MAYCHANGE [memory :> bytes(a,k)] *)
(* within the clause old (the same base, numeral offsets:                   *)
(* memrange_subset_rule), are subsumed by it.                               *)

let frame_parts_subsumed (nw:term) (old:term) : thm =
  let idem = prove(mk_eq(list_mk_icomb ",," [old;old],old),
                   MAYCHANGE_IDEMPOT_TAC) in
  let bl = match old with
      Comb(Const("MAYCHANGE",_),
           Comb(Comb(Const("CONS",_),
                     Comb(Comb(Const(":>",_),_),
                          Comb(Const("bytes",_),r))),_)) -> dest_pair r
    | _ -> failwith "frame_parts_subsumed: not a byte clause" in
  let rec go t =
    match t with
      Comb(Comb(Const(",,",_),a),b) ->
        MATCH_MP SUBSUMED_FOR_SEQ (CONJ idem (CONJ (go a) (go b)))
    | Comb(Const("MAYCHANGE",_),
           Comb(Comb(Const("CONS",_),
                     Comb(Comb(Const(":>",_),_),
                          Comb(Const("bytes",_),r))),_)) ->
        PART_MATCH lhand
          (MATCH_MP MAYCHANGE_BYTES_SUBSUMED
             (memrange_subset_rule (dest_pair r) bl)) t
    | _ -> failwith "frame_parts_subsumed: not a byte clause" in
  go nw;;

(* c' (c with old replaced by nw) subsumed c.                               *)

let rec frame_replace_subsumed (nw:term) (old:term) (c:term) : thm =
  if c = old then frame_parts_subsumed nw old else
  match c with
    Comb(Comb(Const(",,",_),a),b) ->
      MATCH_MP SUBSUMED_SEQ
        (CONJ (frame_replace_subsumed nw old a)
              (frame_replace_subsumed nw old b))
  | _ -> ISPEC c SUBSUMED_REFL;;

let ENSURES_FRAME_SPLIT_TAC (old:term) (nw:term) : tactic =
  fun (asl,w) ->
    let c = rand w in
    let c' = subst [nw,old] c in
    if c' = c then failwith "ENSURES_FRAME_SPLIT_TAC: clause not in the frame"
    else
    let sth = frame_replace_subsumed nw old c in
    (MATCH_MP_TAC ENSURES_FRAME_SUBSUMED THEN EXISTS_TAC c' THEN
     CONJ_TAC THENL [ACCEPT_TAC sth; ALL_TAC]) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* VAL_RUN_TAC execth i leaf: bstep one instruction at a time from step      *)
(* number i (as ARM_BSTEP_RUN_GEN_TAC of decompressor_objects.ml) and apply  *)
(* leaf at the return. At a conditional PC, the condition is first decided   *)
(* by arithmetic (BSTEP_ARITH_DECIDE_TAC ~rws: the pointer and length        *)
(* compares), and the case is split (then ~kill) only if that fails. ~norm   *)
(* runs after each step; ~calls lists PC values with a tactic for the call   *)
(* at that PC (given the step number, it returns the tactic and the number  *)
(* of steps it uses).                                                        *)
(* ------------------------------------------------------------------------- *)

let VAL_DECIDE_PC_TAC (rws:thm list) : tactic =
  fun (asl,w as g) ->
    let r = bstep_pc_value g in
    let c,_ = dest_cond r in
    let th =
      try TAC_PROOF((asl,c),BSTEP_ARITH_DECIDE_TAC ~rws) with Failure _ ->
      TAC_PROOF((asl,mk_neg c),BSTEP_ARITH_DECIDE_TAC ~rws) in
    (FIRST_X_ASSUM(fun pth -> match concl pth with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),pc),_)),r')
          when pc = `PC` && r' = r -> ASSUME_TAC(REWRITE_RULE[th] pth)
      | _ -> NO_TAC) THEN
     ASSUME_TAC th) g;;

let rec VAL_RUN_TAC ?(rws=[]) ?(rewrites=[]) ?(kill=ALL_TAC) ?(norm=ALL_TAC)
                    ?(calls=[]) execth i (leaf:tactic) : tactic = fun g ->
  let r = try bstep_pc_value g with Failure _ -> `T` in
  let again = VAL_RUN_TAC ~rws ~rewrites ~kill ~norm ~calls execth in
  if r = `returnaddress:int64` then leaf g
  else if is_cond r then
    ((VAL_DECIDE_PC_TAC rws ORELSE (BSTEP_SPLIT_PC_TAC THEN TRY kill)) THEN
     again i leaf) g
  else
    let same k = k = r || can (fun () -> WORD_RULE(mk_eq(k,r))) () in
    match (try Some(snd(find (fun (k,_) -> same k) calls))
           with Failure _ -> None) with
      Some ctac -> let tac,used = ctac i in
                   (tac THEN norm THEN again (i+used) leaf) g
    | None -> (ARM_BSTEP_TAC ~rewrites execth (i--i) THEN norm THEN
               again (i+1) leaf) g;;

(* ------------------------------------------------------------------------- *)
(* The suffix of a byte list in memory.                                      *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTELIST_SUFFIX = prove
 (`!(a:int64) l h s.
     read (memory :> bytelist(a,LENGTH l)) s = l /\ h <= LENGTH l
     ==> read (memory :> bytelist(word_add a (word h),LENGTH l - h)) s =
         SUB_LIST(h,LENGTH l - h) l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[READ_BYTELIST_EQ_EL] THEN
  REWRITE_TAC[LENGTH_SUB_LIST; MIN] THEN REWRITE_TAC[LE_REFL] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SNAPPY_EL_SUB_LIST o rand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_add (word_add (a:int64) (word h)) (word i) =
                         word_add a (word(h + i))`] THEN
  MATCH_MP_TAC READ_MEMORY_BYTELIST_EL THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Signed values of 64-bit words as integers, where the arithmetic facts     *)
(* show that there is no overflow: the compares of compiled code on pointer *)
(* differences and counts (ival of word_add and word_sub of such values, of *)
(* word n, word_zx and word_sx of narrower words). IVAL_NW_CONV ths turns     *)
(* ival t into an integer expression (atoms stay ival a), proving the side  *)
(* conditions (no overflow) by INT_ARITH from the facts ths (numerical facts *)
(* are used as their integer forms). INT_DECIDE_TAC ths proves a goal of     *)
(* integers and numbers so converted.                                        *)
(* ------------------------------------------------------------------------- *)

let IVAL_WORD_NUM_NW = prove
 (`!n. n < 2 EXP 63 ==> ival(word n:int64) = &n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word n:int64) = n` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `word n:int64` IVAL_EQ_VAL) THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let IVAL_WORD_ADD_NW = prove
 (`!x y:int64. --(&2 pow 63) <= ival x + ival y /\ ival x + ival y < &2 pow 63
               ==> ival(word_add x y) = ival x + ival y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_add x y:int64 = iword(ival x + ival y)` SUBST1_TAC THENL
   [REWRITE_TAC[IWORD_INT_ADD; IWORD_IVAL]; ALL_TAC] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let IVAL_WORD_SUB_NW = prove
 (`!x y:int64. --(&2 pow 63) <= ival x - ival y /\ ival x - ival y < &2 pow 63
               ==> ival(word_sub x y) = ival x - ival y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `word_sub x y:int64 = iword(ival x - ival y)` SUBST1_TAC THENL
   [REWRITE_TAC[IWORD_INT_SUB; IWORD_IVAL]; ALL_TAC] THEN
  MATCH_MP_TAC IVAL_IWORD THEN REWRITE_TAC[DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let IVAL_WORD_ZX_NW = prove
 (`(!b:byte. ival(word_zx b:int64) = &(val b)) /\
   (!b:int16. ival(word_zx b:int64) = &(val b)) /\
   (!b:int32. ival(word_zx b:int64) = &(val b))`,
  REPEAT CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[word_zx] THEN
  MATCH_MP_TAC IVAL_WORD_NUM_NW THEN
  W(fun (_,w) -> MP_TAC(ISPEC (rand(lhand w)) VAL_BOUND)) THEN
  REWRITE_TAC[DIMINDEX_8; DIMINDEX_16; DIMINDEX_32] THEN ARITH_TAC);;

let IVAL_WORD_SX_16_64 = prove
 (`!b:int16. ival(word_sx b:int64) = ival b`,
  GEN_TAC THEN MATCH_MP_TAC IVAL_WORD_SX THEN
  REWRITE_TAC[DIMINDEX_16; DIMINDEX_64] THEN ARITH_TAC);;

let IVAL_IWORD_16 = prove
 (`!i. --(&32768) <= i /\ i < &32768 ==> ival(iword i:int16) = i`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IVAL_IWORD THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN ASM_REWRITE_TAC[]);;

let int_facts_of (ths:thm list) =
  let ok th = let c = concl th in
    type_of c = bool_ty &&
    not(exists (fun v -> type_of v = `:armstate`) (frees c)) &&
    (try let _ = find_term (fun t -> match t with
           Const("read",_) | Const("write",_) -> true | _ -> false) c in false
     with Failure _ -> true) in
  map (REWRITE_RULE[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_LE;
                    GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD;
                    GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_POW])
      (filter ok ths);;

let INT_FACTS_ARITH_TAC (ths:thm list) : tactic =
  MAP_EVERY MP_TAC (int_facts_of ths) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LT; GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_EQ;
              GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL;
              GSYM INT_OF_NUM_POW] THEN
  CONV_TAC(DEPTH_CONV INT_RED_CONV) THEN INT_ARITH_TAC;;

let rec IVAL_NW_CONV (ths:thm list) tm =
  let side t = TAC_PROOF(([],t),INT_FACTS_ARITH_TAC ths) in
  match tm with
    Comb(Const("ival",_),t) when type_of t = `:int64` ->
      (match t with
         Comb(Const("word",_),n) ->
           let th = ISPEC n IVAL_WORD_NUM_NW in
           MP th (TAC_PROOF(([],lhand(concl th)),
             MAP_EVERY MP_TAC (filter (fun th -> let c = concl th in
               type_of c = bool_ty && (try type_of(lhand c) = `:num`
                                       with Failure _ -> false)) ths) THEN
             CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC))
       | Comb(Comb(Const(("word_add"|"word_sub") as op,_),x),y) ->
           let thx = IVAL_NW_CONV ths (mk_icomb(`ival:int64->int`,x))
           and thy = IVAL_NW_CONV ths (mk_icomb(`ival:int64->int`,y)) in
           let lem = if op = "word_add" then IVAL_WORD_ADD_NW
                     else IVAL_WORD_SUB_NW in
           let th = ISPECL [x;y] lem in
           let ant = lhand(concl th) in
           let antc = REWRITE_CONV[thx; thy] ant in
           let ath = EQ_MP (SYM antc) (side (rhs(concl antc))) in
           TRANS (MP th ath) (REWRITE_CONV[thx; thy] (rhs(rand(concl th))))
       | Comb(Const("word_zx",_),b) ->
           tryfind (fun th -> PART_MATCH lhs th tm) (CONJUNCTS IVAL_WORD_ZX_NW)
       | Comb(Const("word_sx",_),b) when type_of b = `:int16` ->
           let th1 = ISPEC b IVAL_WORD_SX_16_64 in
           TRANS th1 (IVAL_NW_CONV ths (rhs(concl th1)))
       | _ -> REFL tm)
  | Comb(Const("ival",_),(Comb(Const("iword",_),i) as t))
      when type_of t = `:int16` ->
      let th = ISPEC i IVAL_IWORD_16 in
      MP th (side (lhand(concl th)))
  | _ -> failwith "IVAL_NW_CONV";;

let INT_DECIDE_TAC ?(rws:thm list = []) (ths:thm list) : tactic =
  REWRITE_TAC(VAL_WORD_SUB_EQ_0 :: rws) THEN
  CONV_TAC(TOP_DEPTH_CONV (VAL_NOWRAP_CONV ths)) THEN
  CONV_TAC(ONCE_DEPTH_CONV (IVAL_NW_CONV ths)) THEN
  INT_FACTS_ARITH_TAC ths;;

(* ------------------------------------------------------------------------- *)
(* Bytes and halfwords of an image at any offset, from the 64-bit words at   *)
(* multiples of 8 that a constant rule of utils/loaded_image.ml gives        *)
(* (construle d k, e.g. SNAPPY_IMAGE_CONST_RULE, is only for offsets that    *)
(* are multiples of 4): |- !s pc. aligned_bytes_loaded s (word pc) mc ==>    *)
(* read (memory :> bytes8 (word_add (word pc) (word d))) s = word b.         *)
(* ------------------------------------------------------------------------- *)

let image_byte8_rule (construle:int->int->thm) (d:int) : thm =
  let d0 = d - d mod 8 and i = d mod 8 in
  let th64 = construle d0 64 in
  let abl = lhand(snd(dest_forall(snd(dest_forall(concl th64))))) in
  let v = rand(rhs(rand(snd(dest_forall(snd(dest_forall(concl th64))))))) in
  let b = Num.int_of_num(Num.mod_num (Num.quo_num (dest_numeral v)
            (Num.power_num (Num.num_of_int 2) (Num.num_of_int (8 * i))))
            (Num.num_of_int 256)) in
  let tm = list_mk_forall([`s:armstate`; `pc:num`],
    mk_imp(abl,
     subst [mk_small_numeral d,`d:num`; mk_small_numeral b,`b:num`]
      `read (memory :> bytes8 (word_add (word pc) (word d))) s:byte = word b`)) in
  prove(tm,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`memory:(armstate,int64->byte)component`;
                   mk_comb(`word_add (word pc:int64)`,
                           mk_comb(`word:num->int64`,mk_small_numeral d0));
                   mk_small_numeral i; `s:armstate`]
            READ_BYTES8_OF_BYTES64) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[th64; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
    CONV_TAC WORD_REDUCE_CONV);;

let image_bytes16_rule (construle:int->int->thm) (d:int) : thm =
  let t0 = image_byte8_rule construle d
  and t1 = image_byte8_rule construle (d + 1) in
  let abl = lhand(snd(dest_forall(snd(dest_forall(concl t0))))) in
  let b0 = dest_small_numeral(rand(rhs(rand(snd(dest_forall(snd(dest_forall(concl t0)))))))) 
  and b1 = dest_small_numeral(rand(rhs(rand(snd(dest_forall(snd(dest_forall(concl t1)))))))) in
  let tm = list_mk_forall([`s:armstate`; `pc:num`],
    mk_imp(abl,
     subst [mk_small_numeral d,`d:num`; mk_small_numeral (256 * b1 + b0),`b:num`]
      `read (memory :> bytes16 (word_add (word pc) (word d))) s:int16 = word b`)) in
  prove(tm,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[el 4 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC(map (REWRITE_RULE[GSYM WORD_ADD]) [t0; t1]) THEN
    CONV_TAC WORD_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* VAL_PRE_FACTS_TAC th ilist: before ARM_BSTEP_CONTRACT_TAC with the same   *)
(* th and ilist, add the memory facts of the precondition whose address is  *)
(* not in the form of the facts of the state (e.g. word_add (word_add b      *)
(* (word 32)) (word 8) for the fact at word_add b (word 40)): each from the *)
(* fact of the same component at an address equal by WORD_RULE.             *)
(* ------------------------------------------------------------------------- *)

let VAL_PRE_FACTS_TAC (th:thm) (ilist:term list) : tactic =
  fun (asl,w) ->
    let s' = rand w in
    let args = map (arm_bstep_eval asl s') ilist in
    let sth = SPECL args th in
    let c = concl sth in
    let ens = if is_imp c then rand c else c in
    let pre = rand(rator(rator ens)) in
    let body = rhs(concl(BETA_CONV(mk_comb(pre,s')))) in
    let facts = mapfilter (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
             Comb(Comb(Const(":>",_),Const("memory",_)),
                  Comb(k,a))),s1)),_) when s1 = s' -> (k,a,th)
      | _ -> fail()) asl in
    let have t = exists (fun (_,th) -> concl th = t) asl in
    let addfact t =
      match t with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
             Comb(Comb(Const(":>",_),Const("memory",_)),Comb(k,a))),s1)),_)
          when s1 = s' && not(have t) ->
          (try
             let (_,a',fth) = find (fun (k',a',_) -> k' = k &&
                 can (fun () -> WORD_RULE(mk_eq(a',a))) ()) facts in
             let eq = WORD_RULE(mk_eq(a',a)) in
             let nth = CONV_RULE(LAND_CONV(RATOR_CONV(RAND_CONV
                         (RAND_CONV(RAND_CONV(K eq)))))) fth in
             if concl nth = t then [nth] else []
           with Failure _ -> [])
      | _ -> [] in
    let news = flat(map addfact (conjuncts body)) in
    MAP_EVERY ASSUME_TAC news (asl,w);;

(* ------------------------------------------------------------------------- *)
(* VAL_NORM_COND_TAC rws: in the facts read c s = v of the goal's state (not *)
(* events) whose value has conditionals (a csel, a min), decide the          *)
(* conditions that the arithmetic facts decide (INT_DECIDE_TAC ~rws) and     *)
(* rewrite the fact with the decision.                                       *)
(* ------------------------------------------------------------------------- *)

let VAL_NORM_COND_TAC ?(rws:thm list = []) : tactic =
  fun (asl,w) ->
    let s = try rand w with Failure _ -> failwith "VAL_NORM_COND_TAC" in
    let ariths = filter (fun (_,th) ->
        let c = concl th in
        type_of c = bool_ty &&
        not(exists (fun v -> type_of v = `:armstate`) (frees c))) asl in
    let ths = map snd ariths in
    let decide b =
      try Some(EQT_INTRO(TAC_PROOF((asl,b),INT_DECIDE_TAC ~rws ths)))
      with Failure _ ->
      try Some(EQF_INTRO(TAC_PROOF((asl,mk_neg b),INT_DECIDE_TAC ~rws ths)))
      with Failure _ -> None in
    let fix (_,th) =
      match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s1)),v)
          when s1 = s && c <> `events:(armstate,(uarch_event)list)component` &&
               can (find_term is_cond) v ->
          let conds = setify(map (fun t -> fst(dest_cond t))
                        (find_terms is_cond v)) in
          let ds = mapfilter (fun b -> match decide b with
                                         Some d -> d | None -> fail()) conds in
          if ds = [] then fail() else
          (concl th,CONV_RULE(RAND_CONV(REWRITE_CONV ds)) th)
      | _ -> fail() in
    let fixes = mapfilter fix asl in
    MAP_EVERY (fun (oc,nth) -> UNDISCH_THEN oc (K(ASSUME_TAC nth))) fixes
      (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Facts for the footprint rules (the hypotheses of contracts and the        *)
(* memory-safety goals): DISJOINT forms of the nonoverlapping assumptions.   *)
(* ------------------------------------------------------------------------- *)

let VAL_DISJOINT_FACTS_TAC : tactic =
  fun (asl,w) ->
    let ths = mapfilter (fun (_,th) -> match concl th with
        Comb(Comb(Const("nonoverlapping",_),_),_) ->
          EQ_MP (PART_MATCH lhs NONOVERLAPPING_MEMRANGE (concl th)) th
      | _ -> fail()) asl in
    MAP_EVERY ASSUME_TAC ths (asl,w);;

(* The k - h bytes from a + h are within the k bytes from a.                 *)

let MEMRANGE_SUFFIX_SUBSET = prove
 (`!(a:int64) h k. h <= k ==> memrange(word_add a (word h),k - h) SUBSET
                               memrange(a,k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEMRANGE_OFFSET_SUBSET THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Code with cut points: an entry to the end or to a cut point, and the cut  *)
(* points to the end (ENSURES_MEASURE_INDUCT gives the latter from the       *)
(* segments between them). A precondition that is a disjunction of cases.   *)
(* ------------------------------------------------------------------------- *)

let ENSURES_CUT_ENTRY = prove
 (`!(step:A->A->bool) P Q (R:num->A->bool) C.
        C ,, C = C /\
        ensures step P (\s. Q s \/ ?n. R n s) C /\
        (!n. ensures step (R n) Q C)
        ==> ensures step P Q C`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[FUN_EQ_THM; seq])
    (CONJUNCTS_THEN2 (LABEL_TAC "entry") (LABEL_TAC "cut"))) THEN
  DISCH_THEN(LABEL_TAC "idem") THEN
  SUBGOAL_THEN `!a b c. (C:A->A->bool) a b /\ C b c ==> C a c`
   (LABEL_TAC "trans") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "idem" (fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
    EXISTS_TAC `b:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ensures] THEN X_GEN_TAC `s:A` THEN DISCH_TAC THEN
  USE_THEN "entry" (MP_TAC o SPEC `s:A` o REWRITE_RULE[ensures]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[EVENTUALLY_IMP_EVENTUALLY]
   `(!s'. P s' ==> eventually (step:A->A->bool) Q s')
    ==> eventually step P s ==> eventually step Q s`) THEN
  X_GEN_TAC `s':A` THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC) THENL
   [ONCE_REWRITE_TAC[eventually_CASES] THEN DISJ1_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(X_CHOOSE_TAC `n:num`)] THEN
  USE_THEN "cut" (MP_TAC o SPEC `s':A` o REWRITE_RULE[ensures] o
                  SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  X_GEN_TAC `s'':A` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "trans" MATCH_MP_TAC THEN
  EXISTS_TAC `s':A` THEN ASM_REWRITE_TAC[]);;

let ENSURES_DISJ_PRE = prove
 (`!(step:A->A->bool) P1 P2 Q C.
        ensures step P1 Q C /\ ensures step P2 Q C
        ==> ensures step (\s. P1 s \/ P2 s) Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;
