(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proof of CompressFragment (compress_fragment_spec.ml): the machine     *)
(* states at the cut points of the code and their relation to the states of  *)
(* the model snappy_cf1_step (common/snappy/snappy_compress.ml), and the     *)
(* tactics of the proofs of the segments between the cut points.             *)
(*                                                                           *)
(* The cut points are the loop headers of the code that correspond to the    *)
(* phases of the model: loop1 (phase 1, the head of the main loop), loop3    *)
(* (phase 6, the unrolled search, one probe per visit), loop4 (phase 2, the  *)
(* search loop with skipping, after the check against ip_limit), loop6      *)
(* (phase 4, the head of the emit_match loop) and join4 (phase 5,            *)
(* emit_remainder). snappy_cf1_mach says that a state is at the cut point of *)
(* a model state; snappy_cf1_cut that it is at the cut point of the model    *)
(* state after some k steps, whose potential is n. Each segment goes from a  *)
(* cut point to the end or to a cut point of a later model state, so the     *)
(* potential decreases (ENSURES_MEASURE_INDUCT).                             *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_spec.ml";;
needs "arm/proofs/bstep.ml";;
needs "common/snappy/snappy_roundtrip.ml";;
needs "common/snappy/snappy_words.ml";;
needs "common/ensures_measure.ml";;
needs "arm/proofs/snappy/events.ml";;

let SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "CompressFragment"; layout_range "plt_memcpy"];;

(* ------------------------------------------------------------------------- *)
(* The machine state at the cut points.                                      *)
(* ------------------------------------------------------------------------- *)

let snappy_cf1_ctx = new_definition
 `snappy_cf1_ctx pc (src:int64) (inp:byte list) (table:int64)
                 (stackpointer:int64) (x29:int64) (ra:int64) rw
                 (ea:int64) el ev (s:armstate) <=>
   aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
   read SP s = word_sub stackpointer (word 32) /\
   read (memory :> bytes64 (word_sub stackpointer (word 32))) s = x29 /\
   read (memory :> bytes64 (word_add (word_sub stackpointer (word 32))
                                     (word 8))) s = ra /\
   read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s = rw /\
   read (memory :> bytes(ea,el)) s = ev /\
   read (memory :> bytes(src,LENGTH inp)) s = num_of_bytelist inp /\
   read X7 s = src /\ read X13 s = word_add src (word(LENGTH inp)) /\
   read X3 s = table`;;

(* Memory safety: the events since the call (whose events were e) are in   *)
(* the regions that the code may read (the input, the regions it writes,    *)
(* the library and memcpy's region) and write (the output, the table and    *)
(* the stack frame), as in the _SAFE statement of compress_fragment_spec.ml. *)

let snappy_cf1_ev = new_definition
 `snappy_cf1_ev pc (src:int64) (inp:byte list) (op:int64) (table:int64)
                (stackpointer:int64) (ea:int64) el (e:uarch_event list)
                (s:armstate) <=>
   ?e2. read events s = APPEND e2 e /\
        memaccess_inbounds e2
         [src,LENGTH inp; op,snappy_max_compressed_length (LENGTH inp) - 5;
          table,2 * snappy_table_size (LENGTH inp);
          word_sub stackpointer (word 32),32;
          word pc,libsnappy_rw + libsnappy_rw_size; ea,el]
         [op,snappy_max_compressed_length (LENGTH inp) - 5;
          table,2 * snappy_table_size (LENGTH inp);
          word_sub stackpointer (word 32),32]`;;

let snappy_cf1_mach = new_definition
 `snappy_cf1_mach pc (src:int64) (inp:byte list) (op:int64) (table:int64)
     (stackpointer:int64) (x19:int64) (x29:int64) (ra:int64) rw
     (ea:int64) el ev (e:uarch_event list) st s <=>
   snappy_cf1_ctx pc src inp table stackpointer x29 ra rw ea el ev s /\
   snappy_cf1_ev pc src inp op table stackpointer ea el e s /\
   (!j. j < snappy_table_size(LENGTH inp)
        ==> read (memory :> bytes16 (word_add table (word(2 * j)))) s =
            word((snappy_t1 st) j)) /\
   read (memory :> bytes(op,LENGTH (snappy_out st))) s = num_of_bytelist (snappy_out st) /\
   ((snappy_phase st) = 5 /\
    read PC s = word(pc + CompressFragment_join4) /\
    read X1 s = word_add src (word (snappy_ip st)) /\
    read X0 s = word_add op (word(LENGTH (snappy_out st))) /\
    read X19 s = x19 \/
    ~((snappy_phase st) = 5) /\
    read X12 s = word_add src (word(LENGTH inp - 15)) /\
    read X9 s = word(2 * (snappy_table_size(LENGTH inp) - 1)) /\
    ((snappy_phase st) = 1 /\
     read PC s = word(pc + CompressFragment_loop1) /\
     read X6 s = word_add src (word (snappy_ip st)) /\
     read X16 s = word(snappy_load32 inp ((snappy_ip st) + 1)) /\
     read X2 s = word_add op (word(LENGTH (snappy_out st))) /\
     read X19 s = x19 \/
     (snappy_phase st) = 6 /\
     read PC s = word(pc + CompressFragment_loop3) /\
     read X1 s = word_add src (word (snappy_ip st)) /\
     read X6 s = word_add src (word (snappy_ne st)) /\
     read X14 s = word (snappy_ip st) /\
     read X0 s = word (snappy_aux st) /\
     read X15 s = word(4 * ((snappy_aux st) DIV 4)) /\
     read X17 s = word(4 * ((snappy_aux st) DIV 4) + 4) /\
     read X19 s = word_add src (word((snappy_ne st) + 5)) /\
     read (memory :> bytes64 (word_add (word_sub stackpointer (word 32))
                                       (word 16))) s = x19 /\
     read X18 s = word 0x1e35a7bd /\
     read X16 s = word(snappy_load32 inp (snappy_ip st)) /\
     read X5 s = word(snappy_load64 inp ((snappy_ip st) + 4 * ((snappy_aux st) DIV 4)) DIV
                      2 EXP (8 * ((snappy_aux st) MOD 4))) /\
     read X2 s = word_add op (word(LENGTH (snappy_out st))) \/
     (snappy_phase st) = 2 /\
     read PC s = word(pc + CompressFragment_loop4) /\
     read X1 s = word_add src (word (snappy_ip st)) /\
     (snappy_ip st) + (snappy_skip st) DIV 32 <= LENGTH inp - 15 /\
     (snappy_skip st) + (snappy_ne st) = (snappy_ip st) + 31 /\
     read X10 s = word_add src (word((snappy_ip st) + (snappy_skip st) DIV 32)) /\
     read X14 s = word((snappy_skip st) + (snappy_skip st) DIV 32) /\
     read X11 s = word(snappy_load32 inp (snappy_ip st)) /\
     read X0 s = word_add table
                  (word(2 * snappy_hash1 (snappy_table_size(LENGTH inp))
                                         (snappy_load32 inp (snappy_ip st)))) /\
     read X6 s = word_add src (word (snappy_ne st)) /\
     read X2 s = word_add op (word(LENGTH (snappy_out st))) /\
     read X16 s = word 0x1e35a7bd /\
     read X19 s = x19 \/
     (snappy_phase st) = 4 /\
     read PC s = word(pc + CompressFragment_loop6) /\
     read X1 s = word_add src (word (snappy_ip st)) /\
     read X4 s = word_add src (word (snappy_cand st)) /\
     read X0 s = word_add op (word(LENGTH (snappy_out st))) /\
     read X10 s = word_add src (word(LENGTH inp - 16)) /\
     read X11 s = word 0x1e35a7bd /\
     read X19 s = x19))`;;

(* The cut points with measure n: the state after some k steps of the model,  *)
(* with the potential n.                                                     *)

let snappy_cf1_cut = new_definition
 `snappy_cf1_cut pc src inp op table stackpointer x19 x29 ra rw ea el ev e n s <=>
   ?k. snappy_cf1_inv inp
         (snappy_crun (snappy_cf1_step inp) k (snappy_cf1_init inp)) /\
       snappy_cf1_pot inp
         (snappy_crun (snappy_cf1_step inp) k (snappy_cf1_init inp)) = n /\
       ~(snappy_phase
          (snappy_crun (snappy_cf1_step inp) k (snappy_cf1_init inp)) = 0) /\
       snappy_cf1_mach pc src inp op table stackpointer x19 x29 ra rw ea el ev e
         (snappy_crun (snappy_cf1_step inp) k (snappy_cf1_init inp)) s`;;

(* The end: the return, with the result and the registers restored.          *)

let snappy_cf1_done = new_definition
 `snappy_cf1_done (src:int64) inp (op:int64) stackpointer (x19:int64)
                  (x29:int64) (ra:int64) s <=>
   read PC s = ra /\
   read X0 s = word_add op (word(LENGTH(snappy_compress_fragment 1 inp))) /\
   read (memory :> bytelist(op,LENGTH(snappy_compress_fragment 1 inp))) s =
   snappy_compress_fragment 1 inp /\
   read SP s = stackpointer /\ read X19 s = x19 /\ read X29 s = x29`;;

(* The end with the events (the _SAFE statement).                            *)

let snappy_cf1_done_safe = new_definition
 `snappy_cf1_done_safe pc (src:int64) inp (op:int64) table stackpointer
                       (x19:int64) (x29:int64) (ra:int64) ea el e s <=>
   snappy_cf1_done src inp op stackpointer x19 x29 ra s /\
   snappy_cf1_ev pc src inp op table stackpointer ea el e s`;;

let SNAPPY_CF1_RUN_DEC = prove
 (`!(inp:byte list) j st.
        snappy_cf1_inv inp st /\ 0 < j /\
        ~(snappy_phase(snappy_crun (snappy_cf1_step inp) j st) = 0)
        ==> snappy_cf1_inv inp (snappy_crun (snappy_cf1_step inp) j st) /\
            snappy_cf1_pot inp (snappy_crun (snappy_cf1_step inp) j st) <
            snappy_cf1_pot inp st`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LT_REFL; snappy_crun] THEN
  X_GEN_TAC `st:snappy_cstate` THEN STRIP_TAC THEN
  ASM_CASES_TAC `snappy_phase st = 0` THENL
   [UNDISCH_TAC `~(snappy_phase (snappy_crun (snappy_cf1_step inp) j
                                  (snappy_cf1_step inp st)) = 0)` THEN
    ASM_SIMP_TAC[SNAPPY_CF1_FIX; SNAPPY_CRUN_FIX];
    ALL_TAC] THEN
  MP_TAC(SPECL [`inp:byte list`; `st:snappy_cstate`] SNAPPY_CF1_STEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `j = 0` THENL
   [ASM_REWRITE_TAC[snappy_crun]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `snappy_cf1_step inp st`) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let SNAPPY_CF1_CUT_INTRO = prove
 (`!pc src inp op table stackpointer x19 x29 ra rw ea el ev e k st j st' s.
        snappy_crun (snappy_cf1_step inp) k (snappy_cf1_init inp) = st /\
        snappy_cf1_inv inp st /\
        snappy_crun (snappy_cf1_step inp) j st = st' /\ 0 < j /\
        ~(snappy_phase st' = 0) /\
        snappy_cf1_mach pc src inp op table stackpointer x19 x29 ra rw ea el ev
          e st' s
        ==> ?m. m < snappy_cf1_pot inp st /\
                snappy_cf1_cut pc src inp op table stackpointer x19 x29 ra rw
                  ea el ev e m s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`inp:byte list`; `j:num`; `st:snappy_cstate`]
    SNAPPY_CF1_RUN_DEC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `snappy_cf1_pot inp st'` THEN ASM_REWRITE_TAC[snappy_cf1_cut] THEN
  EXISTS_TAC `k + j:num` THEN
  ASM_REWRITE_TAC[SNAPPY_CRUN_ADD]);;

(* ------------------------------------------------------------------------- *)
(* Tactics.                                                                  *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_CF1_TABLE_SPLIT = prove
 (`!(R:num->A) (t:num->A) h ts.
        h < ts /\ (!j. j < ts ==> R j = t j)
        ==> R h = t h /\ (!j. j < ts /\ ~(j = h) ==> R j = t j)`,
  MESON_TAC[]);;

let SNAPPY_CF1_TABLE_JOIN = prove
 (`!(R:num->int16) t h v ts.
        R h = word v /\ (!j. j < ts /\ ~(j = h) ==> R j = word(t j))
        ==> !j. j < ts ==> R j = word(snappy_tupd t h v j)`,
  REWRITE_TAC[snappy_tupd] THEN MESON_TAC[]);;

let is_table_fact tm =
  try let j,b = dest_forall tm in
      let a,c = dest_imp b in
      is_binary "<" a && lhand a = j &&
      (match lhs c with
         Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("memory",_)),
           Comb(Const("bytes16",_),_))),_) -> true
       | _ -> false)
  with Failure _ -> false;;

(* Split the table fact at index h (a term); the side condition h < ts is   *)
(* proved by tac.                                                            *)
let SNAPPY_TABLE_SPLIT_TAC h tac : tactic = fun (asl,w) ->
  let th = snd(find (fun (_,th) -> is_table_fact(concl th)) asl) in
  let j,b = dest_forall(concl th) in
  let ts = rand(lhand b) in
  let r = lhs(rand b) and v = rand(rand b) in
  let rr = mk_abs(j,r) and tt = mk_abs(j,v) in
  let lth = CONV_RULE(DEPTH_CONV BETA_CONV) (ISPECL [rr;tt;h;ts] SNAPPY_CF1_TABLE_SPLIT) in
  let hlt = mk_binary "<" (h,ts) in
  (SUBGOAL_THEN hlt ASSUME_TAC THENL [tac; ALL_TAC] THEN
   UNDISCH_THEN (concl th) (fun th ->
     MP_TAC(MP lth (CONJ (ASSUME hlt) th))) THEN
   DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)) (asl,w);;

let is_input_fact tm =
  match tm with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("memory",_)),
      Comb(Const("bytes",_),_))),_)),Comb(Const("num_of_bytelist",_),Var("inp",_))) -> true
  | _ -> false;;

(* Arithmetic from the assumptions that are about numbers only (no state).  *)
let is_num_fact tm =
  let rec ok t = match t with
      Comb(Comb(Const(("<"|"<="|"="),ty),a),b) when
          (try type_of a = `:num` with Failure _ -> false) -> true
    | Comb(Const("~",_),a) -> ok a
    | Comb(Comb(Const("/\\",_),a),b) -> ok a && ok b
    | _ -> false in
  ok tm && not(can (find_term (fun t -> match t with Const("read",_) -> true | _ -> false)) tm);;

(* First with the facts that share atoms with the goal, in stages           *)
(* (events.ml): the decision procedure numbers the atoms by genvar, so its   *)
(* cost with all the facts depends on what the proof did before, and blew up *)
(* in some orders.                                                           *)
(* Then with all the facts if snappy_arith_full (as before; the segment of  *)
(* loop6 turns it off).                                                      *)
let snappy_arith_full = par_local_ref (fun () -> true);;

let SNAPPY_ARITH_TAC : tactic = fun (asl,w) ->
  try SNAPPY_EV_ARITH_TAC (asl,w) with Failure _ when !(snappy_arith_full ()) ->
  let ths = filter (fun (_,th) -> is_num_fact(concl th)) asl in
  (MAP_EVERY (MP_TAC o snd) ths THEN ARITH_TAC) ([],w);;

(* Facts for the loads from the input at the current state: for each        *)
(* (kind,p) with kind 32, 64 or 8, read (memory :> bytes<kind>               *)
(* (word_add src (word p))) s = word(snappy_load<kind> inp p) (EL p inp for  *)
(* bytes8), the side condition by SNAPPY_ARITH_TAC.                          *)
let SNAPPY_LOAD_TAC (loads:(int * term) list) : tactic = fun (asl,w) ->
  let th = snd(find (fun (_,th) -> is_input_fact(concl th)) asl) in
  let m_s = lhand(concl th) in
  let s = rand m_s in
  let srcv = lhand(rand(rand(lhand m_s))) in
  let one (k,p) =
    let lth = match k with 32 -> SNAPPY_READ_LOAD32 | 64 -> SNAPPY_READ_LOAD64
              | _ -> SNAPPY_READ_EL in
    let th1 = ISPECL [`memory:(armstate,int64->byte)component`; srcv;
                      `inp:byte list`; p; s] lth in
    let side = rand(lhand(concl th1)) in
    let sth = TAC_PROOF((asl,side), SNAPPY_ARITH_TAC) in
    MP th1 (CONJ th sth) in
  MAP_EVERY (ASSUME_TAC o one) loads (asl,w);;

(* ABBREV_TAC, also in the assumptions.                                      *)
let SNAPPY_ABBREV_TAC tm : tactic =
  let v,t = dest_eq tm in
  let eq = mk_eq(t,v) in
  ABBREV_TAC tm THEN
  RULE_ASSUM_TAC(fun th -> if concl th = eq then th
                           else PURE_REWRITE_RULE[ASSUME eq] th);;

(* Rewrite the PC fact only (a branch condition), with ths.                  *)
let ARM_PC_REWRITE_TAC (ths:thm list) : tactic =
  let is_pc th = match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),_)),_) -> true
    | _ -> false in
  RULE_ASSUM_TAC(fun th -> if is_pc th then REWRITE_RULE ths th else th);;

let is_pc_cond_fact th =
  match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),_)),r) ->
      (try let f,args = strip_comb r in fst(dest_const f) = "COND" && length args = 3
       with Failure _ -> false)
  | _ -> false;;

let ARM_PC_CASES_TAC (dec:tactic) : tactic = fun (asl,w) ->
  let th = snd(find (fun (_,th) -> is_pc_cond_fact th) asl) in
  let r = rand(concl th) in
  let c = rand(rator(rator r)) in
  let fix b =
    let cth = if b then EQT_INTRO(ASSUME c) else EQF_INTRO(ASSUME(mk_neg c)) in
    UNDISCH_THEN (concl th) (fun pth ->
       ASSUME_TAC(PURE_ONCE_REWRITE_RULE[COND_CLAUSES]
         (CONV_RULE(RAND_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV(K cth))))) pth))) in
  (ASM_CASES_TAC c THENL [fix true THEN TRY dec; fix false THEN TRY dec]) (asl,w);;

(* Rewrite only the facts read c s = v about the components cs.             *)
let SNAPPY_REWRITE_FACTS_TAC (cs:term list) (ths:thm list) : tactic =
  let is_c th = match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),_)),_) -> mem c cs
    | _ -> false in
  RULE_ASSUM_TAC(fun th -> if is_c th then REWRITE_RULE ths th else th);;

(* MOD/DIV elimination as a rule on a term, with the numeric facts asl.      *)
let SNAPPY_MOD_ELIM_CONV (ths:thm list) : conv =
  let is_md op t = is_binary op t && is_numeral(rand t) in
  let ariths = filter (fun th -> is_num_fact(concl th)) ths in
  let prove_lt tm =
    TAC_PROOF(([],tm), MAP_EVERY (MP_TAC) ariths THEN ARITH_TAC) in
  let rec go tm =
    let cands = setify(find_terms (fun t -> is_md "MOD" t || is_md "DIV" t) tm) in
    let cands = sort (fun a b -> snappy_term_size a < snappy_term_size b) cands in
    let rec first l = match l with
        [] -> REFL tm
      | t::r ->
          (try let lth = prove_lt (mk_binary "<" (lhand t,rand t)) in
               let eq = if is_md "MOD" t then MATCH_MP MOD_LT lth
                        else MATCH_MP DIV_LT lth in
               let th1 = GEN_REWRITE_CONV ONCE_DEPTH_CONV [eq] tm in
               TRANS th1 (go (rand(concl th1)))
           with Failure _ -> first r) in
    first cands in
  go;;

let SNAPPY_VAL_THMS = [VAL_WORD_ADD; VAL_WORD_ZX_GEN; VAL_WORD_USHR; VAL_WORD_SHL;
  VAL_WORD; DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64];;

(* Normalize a branch condition in the PC fact: values of words as numbers,   *)
(* with MOD and DIV eliminated by the arithmetic assumptions.                 *)
let SNAPPY_PC_NUM_TAC (extra:thm list) : tactic = fun (asl,w) ->
  let ths = map snd asl in
  let is_pc th = match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),_)),_) -> true
    | _ -> false in
  RULE_ASSUM_TAC(fun th -> if is_pc th then
      CONV_RULE(RAND_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV
        (REWRITE_CONV [VAL_EQ_0; WORD_SUB_EQ_0] THENC
         ONCE_DEPTH_CONV(fun t -> if is_eq t && is_type(type_of(lhs t)) &&
                           fst(dest_type(type_of(lhs t))) = "word"
                         then REWR_CONV(GSYM VAL_EQ) t else failwith "") THENC
         REWRITE_CONV (extra @ SNAPPY_VAL_THMS) THENC NUM_REDUCE_CONV THENC
         SNAPPY_MOD_ELIM_CONV ths THENC REWRITE_CONV[LT_ADD_LCANCEL; LE_ADD_LCANCEL]))))) th
    else th) (asl,w);;

(* Prove read c s = v' from the fact read c s = v by proving v = v'.         *)
let SNAPPY_FACT_TAC (tac:tactic) : tactic = fun (asl,w) ->
  let l = lhs w in
  let th = snd(find (fun (_,th) -> try lhs(concl th) = l with Failure _ -> false) asl) in
  (GEN_REWRITE_TAC LAND_CONV [th] THEN tac) (asl,w);;

(* Bounds of the loads in a term, as facts for the arithmetic.              *)
let snappy_load_bounds tm =
  let ls = setify(find_terms (fun t -> match t with
      Comb(Comb(Const(("snappy_load32"|"snappy_load64"),_),_),_) -> true
    | _ -> false) tm) in
  map (fun t -> match t with
      Comb(Comb(Const("snappy_load32",_),l),p) -> SPECL [l;p] SNAPPY_LOAD32_BOUND
    | Comb(Comb(_,l),p) -> SPECL [l;p] SNAPPY_LOAD64_BOUND
    | _ -> fail()) ls;;

let SNAPPY_WORD_NUM_TAC : tactic =
  REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC SNAPPY_VAL_THMS THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  (fun (asl,w) -> let bs = snappy_load_bounds w in
     (MAP_EVERY ASSUME_TAC bs THEN
      CONV_TAC (SNAPPY_MOD_ELIM_CONV (bs @ map snd asl))) (asl,w)) THEN
  TRY SNAPPY_ARITH_TAC;;

let SNAPPY_WORD_ZX_WORD_64_16 = prove
 (`!n. word_zx (word n:int64):int16 = word n`,
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_16; DIMINDEX_64] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN CONV_TAC NUM_REDUCE_CONV);;

(* The table fact after a store of word v at index h: from the fact for h   *)
(* and the general fact for the other indices.                               *)
let SNAPPY_TABLE_JOIN_TAC (h:term) (v:term) : tactic = fun (asl,w) ->
  let gen = snd(find (fun (_,th) ->
     try let j,b = dest_forall(concl th) in
         let a,_ = dest_imp b in
         is_conj a && is_neg(rand a) && rand(rand(rand a)) = h
     with Failure _ -> false) asl) in
  let j,b = dest_forall(concl gen) in
  let a,c = dest_imp b in
  let r = lhs c and tj = rand(rand c) in
  let ts = rand(lhand a) in
  let rr = mk_abs(j,r) and t = rator tj in
  let rh = rand(concl(BETA_CONV(mk_comb(rr,h)))) in
  let spec = snd(find (fun (_,th) -> try lhs(concl th) = rh with Failure _ -> false) asl) in
  let lth = CONV_RULE(DEPTH_CONV BETA_CONV) (ISPECL [rr;t;h;v;ts] SNAPPY_CF1_TABLE_JOIN) in
  let need = lhand(lhand(concl lth)) in
  let vth = TAC_PROOF((asl,mk_eq(rand(concl spec), rand need)),
              REWRITE_TAC[WORD_RULE `word_sub (word_add (a:int64) b) a = b`;
                          SNAPPY_WORD_ZX_WORD_64_16] THEN
              TRY SNAPPY_WORD_NUM_TAC) in
  ASSUME_TAC(MP lth (CONJ (TRANS spec vth) gen)) (asl,w);;

(* snappy_crun f k s for a numeral k, unfolded.                              *)
let rec SNAPPY_CRUN_CONV tm =
  match tm with
    Comb(Comb(Comb(Const("snappy_crun",_),_),k),_) when is_numeral k ->
      if dest_small_numeral k = 0 then REWR_CONV (CONJUNCT1 snappy_crun) tm
      else (RATOR_CONV(RAND_CONV num_CONV) THENC
            REWR_CONV (CONJUNCT2 snappy_crun) THENC SNAPPY_CRUN_CONV) tm
  | _ -> failwith "SNAPPY_CRUN_CONV";;

(* Decide the conditions of a step of the model from the assumptions: by an  *)
(* assumption, its negation, or arithmetic, after rewriting with eqs (the    *)
(* abbreviations).                                                           *)
let SNAPPY_DECIDE_CONV (asl:(string*thm) list) (eqs:thm list) : conv =
  let tac = FIRST_ASSUM ACCEPT_TAC ORELSE SNAPPY_ARITH_TAC in
  let dec c =
    try EQT_INTRO(TAC_PROOF((asl,c),tac)) with Failure _ ->
    try EQF_INTRO(TAC_PROOF((asl,mk_neg c),tac)) with Failure _ ->
    failwith "SNAPPY_DECIDE_CONV" in
  fun tm ->
    match tm with
      Comb(Comb(Comb(Const("COND",_),c),_),_) ->
        let cth = (REWRITE_CONV eqs THENC NUM_REDUCE_CONV) c in
        let c' = rand(concl cth) in
        let dth = if c' = `T` || c' = `F` then cth else TRANS cth (dec c') in
        (RATOR_CONV(RATOR_CONV(RAND_CONV(K dth))) THENC
         GEN_REWRITE_CONV I [COND_CLAUSES]) tm
    | _ -> failwith "SNAPPY_DECIDE_CONV";;

let SNAPPY_CF1_STEP_CONV (asl:(string*thm) list) (eqs:thm list) : conv =
  let step tm =
    match tm with
      Comb(Comb(Const("snappy_cf1_step",_),_),st) when
        (try fst(dest_const(fst(strip_comb st))) = "SnappyCState" with Failure _ -> false) ->
        (GEN_REWRITE_CONV I [snappy_cf1_step] THENC TOP_DEPTH_CONV let_CONV THENC
         TOP_DEPTH_CONV (SNAPPY_DECIDE_CONV asl eqs) THENC REWRITE_CONV eqs) tm
    | _ -> failwith "SNAPPY_CF1_STEP_CONV" in
  DEPTH_CONV step;;

(* The cut after j steps of the model, from the cut point at st (the         *)
(* assumption crun k init = st): turns the goal done \/ ?m. m < pot st /\    *)
(* cut m s into the goal mach st' s, st' the state after the j steps.        *)
let SNAPPY_CF1_CUT_TAC (j:int) : tactic =
  (DISJ2_TAC ORELSE ALL_TAC) THEN MATCH_MP_TAC SNAPPY_CF1_CUT_INTRO THEN
  W(fun (asl,w) ->
    let kth = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),Comb(Comb(Comb(Const("snappy_crun",_),_),_),
             Comb(Const("snappy_cf1_init",_),_))),_) -> true
      | _ -> false) asl) in
    let k = rand(rator(lhand(concl kth))) and st = rand(concl kth) in
    let f = rand(rator(rator(lhand(concl kth)))) in
    let ith = snd(find (fun (_,th) -> match concl th with
        Comb(Comb(Const("snappy_cf1_inv",_),_),st') -> st' = st
      | _ -> false) asl) in
    let eqs = mapfilter (fun (_,th) -> match concl th with
        Comb(Comb(Const("=",_),l),Var(_,_)) when
          not(is_var l) && not(is_numeral l) &&
          not(can (find_term (fun t -> match t with
                    Const("read",_) -> true | _ -> false)) l) -> th
      | _ -> fail()) asl in
    let run = list_mk_comb(`snappy_crun`,[f; mk_small_numeral j; st]) in
    let runth = (SNAPPY_CRUN_CONV THENC SNAPPY_CF1_STEP_CONV asl eqs) run in
    MAP_EVERY EXISTS_TAC [k; mk_small_numeral j; rand(concl runth)] THEN
    REPEAT CONJ_TAC THENL
     [ACCEPT_TAC kth; ACCEPT_TAC ith; ACCEPT_TAC runth; ARITH_TAC;
      REWRITE_TAC[snappy_phase] THEN ARITH_TAC; ALL_TAC]);;

(* The goal snappy_cf1_ev ... e s at the end of a path: the regions in the  *)
(* form of the assumptions (the output length as 27 + n + n DIV 6 and the    *)
(* abbreviations of the segment), then SNAPPY_EVENTS_TAC.                    *)
let SNAPPY_CF1_EV_TAC : tactic = fun (asl,w) ->
  if not(try fst(dest_const(fst(strip_comb w))) = "snappy_cf1_ev"
         with Failure _ -> false) then failwith "SNAPPY_CF1_EV_TAC" else
  let eqs = mapfilter (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),l),Var(_,_)) when
        not(is_var l) && not(is_numeral l) &&
        not(can (find_term (fun t -> match t with
                  Const("read",_) -> true | _ -> false)) l) -> th
    | _ -> fail()) asl in
  let mtm = `snappy_max_compressed_length (LENGTH(inp:byte list)) - 5 =
             27 + LENGTH inp + LENGTH inp DIV 6` in
  let mth = TAC_PROOF((asl,mtm),
    MP_TAC(SPEC `LENGTH(inp:byte list)` SNAPPY_MAX_COMPRESSED_LENGTH_32) THEN
    ANTS_TAC THENL [SNAPPY_EV_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ARITH_TAC) in
  (REWRITE_TAC[snappy_cf1_ev] THEN REWRITE_TAC[mth] THEN REWRITE_TAC eqs THEN
   SNAPPY_EVENTS_TAC) (asl,w);;

(* The goal mach st' s: its conjuncts from the facts, by word arithmetic on  *)
(* the values of the registers, and by arithmetic.                           *)
let SNAPPY_CF1_MACH_TAC : tactic = fun (asl,w) ->
  let eqs = mapfilter (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),l),Var(_,_)) when
        not(is_var l) && not(is_numeral l) &&
        not(can (find_term (fun t -> match t with
                  Const("read",_) -> true | _ -> false)) l) -> th
    | _ -> fail()) asl in
  (REWRITE_TAC[snappy_cf1_mach; snappy_cf1_ctx; snappy_phase; snappy_ip;
     snappy_ne; snappy_skip; snappy_cand; snappy_aux; snappy_t1; snappy_t2;
     snappy_out] THEN
   CONV_TAC(ONCE_DEPTH_CONV NUM_EQ_CONV) THEN REWRITE_TAC eqs THEN
   REPEAT CONJ_TAC THEN
   TRY(SNAPPY_CF1_EV_TAC THEN NO_TAC) THEN
   TRY(FIRST_ASSUM ACCEPT_TAC) THEN
   TRY(SNAPPY_FACT_TAC (TRY REFL_TAC THEN SNAPPY_WORD_NUM_TAC)) THEN
   TRY SNAPPY_ARITH_TAC) (asl,w);;

(* As SNAPPY_CF1_MACH_TAC, but a register fact is either proved or left as   *)
(* it is, and lengths of appended lists are computed first.                  *)
let SNAPPY_CF1_MACH2_TAC : tactic = fun (asl,w) ->
  let eqs = mapfilter (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),l),Var(_,_)) when
        not(is_var l) && not(is_numeral l) &&
        not(can (find_term (fun t -> match t with
                  Const("read",_) -> true | _ -> false)) l) -> th
    | _ -> fail()) asl in
  (REWRITE_TAC[snappy_cf1_mach; snappy_cf1_ctx; snappy_phase; snappy_ip;
     snappy_ne; snappy_skip; snappy_cand; snappy_aux; snappy_t1; snappy_t2;
     snappy_out] THEN
   CONV_TAC(ONCE_DEPTH_CONV NUM_EQ_CONV) THEN REWRITE_TAC eqs THEN
   REPEAT CONJ_TAC THEN
   TRY(SNAPPY_CF1_EV_TAC THEN NO_TAC) THEN
   TRY(FIRST_ASSUM ACCEPT_TAC) THEN
   TRY(SNAPPY_FACT_TAC (TRY REFL_TAC THEN
         REWRITE_TAC[LENGTH_APPEND; LENGTH; LENGTH_SUB_LIST;
                     LENGTH_BYTELIST_OF_NUM] THEN
         REWRITE_TAC eqs THEN SNAPPY_WORD_NUM_TAC THEN NO_TAC)) THEN
   TRY SNAPPY_ARITH_TAC) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* The statements of the segments.                                           *)
(* ------------------------------------------------------------------------- *)

let snappy_cf1_hyps_str =
 "aligned 4096 (word pc:int64) /\\
    pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\\
    elf_relocated_data (word(pc + libsnappy_rw)) rw
      (snappy_libsnappy_gcc12_O2_relocated pc imp) /\\
    aligned 16 stackpointer /\\
    LENGTH inp <= 65536 /\\
    val src + LENGTH inp + 65536 < 2 EXP 64 /\\
    val op + (snappy_max_compressed_length (LENGTH inp) - 5) < 2 EXP 64 /\\
    PAIRWISE nonoverlapping
     [op,(snappy_max_compressed_length (LENGTH inp) - 5);
      table,2 * snappy_table_size (LENGTH inp);
      word_sub stackpointer (word 32),32] /\\
    ALLPAIRS nonoverlapping
     [op,(snappy_max_compressed_length (LENGTH inp) - 5);
      table,2 * snappy_table_size (LENGTH inp);
      word_sub stackpointer (word 32),32]
     [src,LENGTH inp; word pc,libsnappy_rw + libsnappy_rw_size; ea,el]";;

let snappy_cf1_frame_str =
 "MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
  MAYCHANGE [memory :> bytes(op,(snappy_max_compressed_length (LENGTH inp) - 5));
             memory :> bytes(table,2 * snappy_table_size (LENGTH inp));
             memory :> bytes(word_sub stackpointer (word 32),32)] ,,
  MAYCHANGE [X19] ,, MAYCHANGE [X29] ,, MAYCHANGE [SP]";;

(* A segment from the cut point of a model state of phase ph to the end     *)
(* (done, for the segment of emit_remainder, with the extra hypothesis on    *)
(* memcpy) or to a later cut point. The segments that never end are stated   *)
(* for any predicate D of the end (qd = "(D:armstate->bool) ").              *)

let snappy_cf1_seg_stmt_gen qd extra dn ph =
  let st = "(SnappyCState " ^ string_of_int ph ^ " ip ne sk c x t1 t2 out)" in
  parse_term
   ("!" ^ qd ^ "pc src (inp:byte list) op table stackpointer x19 x29 ra rw ea el ev imp
             e k ip ne sk c x t1 t2 out.
     " ^ extra ^ snappy_cf1_hyps_str ^ " /\\
     snappy_crun (snappy_cf1_step inp) k (snappy_cf1_init inp) = " ^ st ^ " /\\
     snappy_cf1_inv inp " ^ st ^ "
     ==> ensures arm
          (\\s. snappy_cf1_mach pc src inp op table stackpointer x19 x29 ra rw ea el ev e
                 " ^ st ^ " s)
          (\\s. " ^ dn ^ " s \\/
               ?m. m < snappy_cf1_pot inp " ^ st ^ " /\\
                   snappy_cf1_cut pc src inp op table stackpointer x19 x29 ra rw ea el ev e m s)
          (" ^ snappy_cf1_frame_str ^ ")");;

let snappy_cf1_seg_stmt ph = snappy_cf1_seg_stmt_gen "(D:armstate->bool) " "" "D" ph;;

let snappy_cf1_done_str =
  "snappy_cf1_done src inp op stackpointer x19 x29 ra";;
let snappy_cf1_done_safe_str =
  "snappy_cf1_done_safe pc src inp op table stackpointer x19 x29 ra ea el e";;
let snappy_cf1_memcpy_str = "memcpy_contract (imp \"memcpy\") ea el ev /\\\n    ";;
let snappy_cf1_memcpy_safe_str =
  "memcpy_correct_safe_contract (imp \"memcpy\") ea el ev /\\\n    ";;

let SNAPPY_CF1_SEG2_STMT = snappy_cf1_seg_stmt 2;;
let SNAPPY_CF1_SEG1_STMT = snappy_cf1_seg_stmt 1;;
let SNAPPY_CF1_SEG4_STMT = snappy_cf1_seg_stmt 4;;
let SNAPPY_CF1_SEG5_STMT =
  snappy_cf1_seg_stmt_gen "" snappy_cf1_memcpy_str snappy_cf1_done_str 5;;
let SNAPPY_CF1_SEG5_SAFE_STMT =
  snappy_cf1_seg_stmt_gen "" snappy_cf1_memcpy_safe_str snappy_cf1_done_safe_str 5;;
let SNAPPY_CF1_SEG6_STMT = snappy_cf1_seg_stmt 6;;

(* The start of the proof of a segment: the hypotheses and the precondition  *)
(* as assumptions at the state s0, the facts of the invariant of the model   *)
(* state, the output region MaxCompressedLength - 5 as 27 + n + n DIV 6, and *)
(* the abbreviation ts                                                       *)
(* of the table size with its bounds.                                        *)

let SNAPPY_CF1_SEG_START_TAC =
  REWRITE_TAC[ALLPAIRS; ALL; PAIRWISE] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[snappy_cf1_mach; snappy_cf1_ctx; snappy_phase; snappy_ip;
    snappy_ne; snappy_skip; snappy_cand; snappy_aux; snappy_t1; snappy_t2;
    snappy_out] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_EQ_CONV) THEN REWRITE_TAC[] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e2:uarch_event list` STRIP_ASSUME_TAC o
    REWRITE_RULE[snappy_cf1_ev] o check (fun th ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "snappy_cf1_ev"
      with Failure _ -> false)) THEN
  FIRST_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "snappy_cf1_inv"
    with Failure _ -> false)) THEN
  REWRITE_TAC[snappy_cf1_inv] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN `snappy_max_compressed_length (LENGTH(inp:byte list)) - 5 =
                27 + LENGTH inp + LENGTH inp DIV 6`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
   [MP_TAC(SPEC `LENGTH(inp:byte list)` SNAPPY_MAX_COMPRESSED_LENGTH_32) THEN
    ANTS_TAC THENL [SNAPPY_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN ARITH_TAC;
    ALL_TAC] THEN
  SNAPPY_ABBREV_TAC `ts = snappy_table_size (LENGTH(inp:byte list))` THEN
  SUBGOAL_THEN `256 <= ts /\ ts <= 32768` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ts" THEN REWRITE_TAC[SNAPPY_TABLE_SIZE_BOUNDS]; ALL_TAC];;

(* The bound of a table entry, t j + 4 <= LENGTH inp and t j < 65536 from    *)
(* snappy_tbound t b, b + 4 <= LENGTH inp being provable by arithmetic.     *)

let SNAPPY_TBOUND_TAC (j:term) : tactic =
  FIRST_ASSUM(MP_TAC o SPEC j o REWRITE_RULE[snappy_tbound] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "snappy_tbound"
    with Failure _ -> false)) THEN
  SNAPPY_ARITH_TAC;;
