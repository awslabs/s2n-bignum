(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* snappy::internal::CompressFragmentDoubleHash (compression level 2), as    *)
(* compiled by gcc 12 -O2: how the states of the machine correspond to the   *)
(* states of the model snappy_cf2_step (common/snappy/snappy_compress.ml).   *)
(*                                                                           *)
(* The proof follows the model. At seven points of the code the machine     *)
(* state holds a state st of the model (snappy_cf2_at ... pt st s):          *)
(*                                                                           *)
(*   loop1  (+0x44)   phase 1, the head of the main loop                     *)
(*   loop2  (+0x68)   phase 2, a probe of the search whose bound is checked  *)
(*   join4  (+0x158)  phase 7, the head of the backtracking                  *)
(*   loop4  (+0x180)  phase 7, a step of the backtracking that may go on     *)
(*   join5  (+0x190)  phase 3, the table updates and the literal             *)
(*   loop5  (+0x1e0)  phase 4, the head of the copy loop                     *)
(*   join2  (+0xdc)   phase 5, emit_remainder                                *)
(*                                                                           *)
(* and each piece of code between them does at least one step of the model,  *)
(* or returns with the output of the model (SNAPPY_ENSURES_POT). In every    *)
(* state the uint16_t tables hold the model's tables (snappy_tval), the      *)
(* output holds the model's output, and the stack holds the saved registers. *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/snappy/gcc12_O2/libsnappy.ml";;
needs "arm/proofs/libc.ml";;
needs "common/snappy/snappy_compress_word.ml";;
needs "common/arith_facts.ml";;

let SNAPPY_CF2_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "CompressFragmentDoubleHash"; layout_range "plt_memcpy"];;

(* ------------------------------------------------------------------------- *)
(* The registers at the points of the code.                                  *)
(* ------------------------------------------------------------------------- *)

let snappy_cf2_regs = new_definition
 `snappy_cf2_regs (src:byte list) (inp:int64) (op:int64) (table2:int64)
                  (ts:num) (pt:num) (st:snappy_cstate) (s:armstate) <=>
   if pt = CompressFragmentDoubleHash_join2 then
     snappy_phase st = 5 /\
     read X0 s = word_add op (word(LENGTH(snappy_out st))) /\
     read X2 s = word_add op (word(LENGTH(snappy_out st))) /\
     read X1 s = word_add inp (word(snappy_ip st))
   else
     read X0 s = inp /\
     read X2 s = word_add op (word(LENGTH(snappy_out st))) /\
     read X9 s = word(2 * (ts - 1)) /\
     read X10 s = word_add inp (word(LENGTH src - 15)) /\
     read X11 s = word 58295818150454627 /\
     read X12 s = word 2654435761 /\
     (if pt = CompressFragmentDoubleHash_loop1 then
        snappy_phase st = 1 /\
        read X1 s = word_add inp (word(snappy_ip st))
      else if pt = CompressFragmentDoubleHash_loop2 then
        snappy_phase st = 2 /\
        snappy_ip st + snappy_skip st DIV 512 <= LENGTH src - 15 /\
        snappy_skip st <= 512 + snappy_ip st /\
        read X1 s = word_add inp (word(snappy_ne st)) /\
        read X8 s = word_add inp (word(snappy_ip st)) /\
        read X16 s = word(snappy_load64 src (snappy_ip st)) /\
        read X4 s = word_add table2
                     (word(2 * snappy_hash8 ts
                                (snappy_load64 src (snappy_ip st)))) /\
        read X17 s = word_add inp
                      (word(snappy_ip st + snappy_skip st DIV 512)) /\
        read X18 s = word(snappy_skip st + 1)
      else if pt = CompressFragmentDoubleHash_loop5 then
        snappy_phase st = 4 /\
        read X16 s = word_add inp (word(LENGTH src - 8)) /\
        read X8 s = word_add inp (word(snappy_ip st)) /\
        read X14 s = word_add inp (word(snappy_cand st)) /\
        read X4 s = word(snappy_aux st)
      else
        (if pt = CompressFragmentDoubleHash_join5 then snappy_phase st = 3
         else snappy_phase st = 7) /\
        (pt = CompressFragmentDoubleHash_loop4
         ==> snappy_ne st < snappy_ip st /\ 0 < snappy_cand st) /\
        snappy_ip st <= LENGTH src - 15 /\
        snappy_ne st + 17 <= LENGTH src /\
        read X16 s = word_add inp (word(LENGTH src - 8)) /\
        read X1 s = word_add inp (word(snappy_ne st)) /\
        read X8 s = word_add inp (word(snappy_ip st)) /\
        read X14 s = word_add inp (word(snappy_cand st)) /\
        read X4 s = word(snappy_aux st))`;;

(* The points.                                                               *)

let snappy_cf2_point = new_definition
 `snappy_cf2_point pt <=>
    pt = CompressFragmentDoubleHash_loop1 \/
    pt = CompressFragmentDoubleHash_loop2 \/
    pt = CompressFragmentDoubleHash_join4 \/
    pt = CompressFragmentDoubleHash_loop4 \/
    pt = CompressFragmentDoubleHash_join5 \/
    pt = CompressFragmentDoubleHash_loop5 \/
    pt = CompressFragmentDoubleHash_join2`;;

(* ------------------------------------------------------------------------- *)
(* Memory safety: the events since the start e are in the regions that the   *)
(* code may read (the input, the regions it writes, the library and memcpy's *)
(* region) and write (the output, the tables and the stack frame).           *)
(* ------------------------------------------------------------------------- *)

let snappy_cf2_events = new_definition
 `snappy_cf2_events (src:byte list) (inp:int64) (op:int64) (table:int64)
                    (table2:int64) (ts:num) (pc:num) (stackpointer:int64)
                    (ea:int64) (el:num) (e:(uarch_event)list) (s:armstate) <=>
   ?e2. read events s = APPEND e2 e /\
        memaccess_inbounds e2
         [inp,LENGTH src; op,(snappy_max_compressed_length (LENGTH src) - 5);
          table,2 * ts; table2,2 * ts; word_sub stackpointer (word 48),48;
          word pc,libsnappy_rw + libsnappy_rw_size; ea,el]
         [op,(snappy_max_compressed_length (LENGTH src) - 5);
          table,2 * ts; table2,2 * ts; word_sub stackpointer (word 48),48]`;;

(* ------------------------------------------------------------------------- *)
(* The machine state at a point, for a state st of the model. The stack      *)
(* frame of 48 bytes below stackpointer holds x29, x30, x19 and x20 of the   *)
(* caller (and x21 at sp + 32 while it is used, on the way to join4), x21    *)
(* holds the caller's value; the tables, the output, the input, the          *)
(* relocated data and memcpy's region are as they were.                       *)
(* ------------------------------------------------------------------------- *)

let snappy_cf2_at = new_definition
 `snappy_cf2_at (src:byte list) (inp:int64) (op:int64) (table:int64)
                (table2:int64) (ts:num) (pc:num) (stackpointer:int64)
                (returnaddress:int64) (x19:int64) (x20:int64) (x21:int64)
                (x29:int64) (rw:num) (ea:int64) (el:num) (ev:num)
                (e:(uarch_event)list) (pt:num) (st:snappy_cstate)
                (s:armstate) <=>
   aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
   read PC s = word(pc + pt) /\
   read SP s = word_sub stackpointer (word 48) /\
   read X29 s = word_sub stackpointer (word 48) /\
   read (memory :> bytes64 (word_sub stackpointer (word 48))) s = x29 /\
   read (memory :> bytes64
          (word_add (word_sub stackpointer (word 48)) (word 8))) s =
   returnaddress /\
   read (memory :> bytes64
          (word_add (word_sub stackpointer (word 48)) (word 16))) s = x19 /\
   read (memory :> bytes64
          (word_add (word_sub stackpointer (word 48)) (word 24))) s = x20 /\
   read X21 s = x21 /\
   read X3 s = table /\
   read X5 s = table2 /\
   read X13 s = word_add inp (word(LENGTH src)) /\
   read (memory :> bytes(inp,LENGTH src)) s = num_of_bytelist src /\
   read (memory :> bytes(table,2 * ts)) s = snappy_tval ts (snappy_t1 st) /\
   read (memory :> bytes(table2,2 * ts)) s = snappy_tval ts (snappy_t2 st) /\
   read (memory :> bytes(op,LENGTH(snappy_out st))) s =
   num_of_bytelist(snappy_out st) /\
   read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s = rw /\
   read (memory :> bytes(ea,el)) s = ev /\
   snappy_cf2_events src inp op table table2 ts pc stackpointer ea el e s /\
   snappy_cf2_regs src inp op table2 ts pt st s`;;

(* The end: the return with the output of the model and the registers that  *)
(* the caller expects to be preserved.                                       *)

let snappy_cf2_post = new_definition
 `snappy_cf2_post (src:byte list) (op:int64) (stackpointer:int64)
                  (returnaddress:int64) (x19:int64) (x20:int64) (x21:int64)
                  (x29:int64) (s:armstate) <=>
   read PC s = returnaddress /\
   read X0 s = word_add op (word(LENGTH(snappy_compress_fragment 2 src))) /\
   read (memory :> bytes(op,LENGTH(snappy_compress_fragment 2 src))) s =
   num_of_bytelist(snappy_compress_fragment 2 src) /\
   read SP s = stackpointer /\
   read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
   read X29 s = x29`;;

let snappy_cf2_post_safe = new_definition
 `snappy_cf2_post_safe (src:byte list) (inp:int64) (op:int64) (table:int64)
                       (table2:int64) (ts:num) (pc:num) (stackpointer:int64)
                       (returnaddress:int64) (x19:int64) (x20:int64)
                       (x21:int64) (x29:int64) (ea:int64) (el:num)
                       (e:(uarch_event)list) (s:armstate) <=>
   snappy_cf2_post src op stackpointer returnaddress x19 x20 x21 x29 s /\
   snappy_cf2_events src inp op table table2 ts pc stackpointer ea el e s`;;

(* ------------------------------------------------------------------------- *)
(* The hypotheses, the frame and the statements of the pieces of code, as    *)
(* text shared by the spec files.                                            *)
(* ------------------------------------------------------------------------- *)

let snappy_cf2_vars =
  "src inp op table table2 ts pc imp stackpointer returnaddress \
   x19 x20 x21 x29 rw ea el ev e";;

let snappy_cf2_hyps =
 "LENGTH (src:byte list) <= 65536 /\\
  ts = snappy_table_size (LENGTH src) DIV 2 /\\
  aligned 4096 (word pc:int64) /\\
  pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\\
  aligned 16 (stackpointer:int64) /\\
  elf_relocated_data (word(pc + libsnappy_rw)) rw
    (snappy_libsnappy_gcc12_O2_relocated pc imp) /\\
  val (inp:int64) + LENGTH src + 65536 < 2 EXP 64 /\\
  val (op:int64) + (snappy_max_compressed_length (LENGTH src) - 5) < 2 EXP 64 /\\
  ALLPAIRS nonoverlapping
   [op,(snappy_max_compressed_length (LENGTH src) - 5); table:int64,2 * ts;
    table2:int64,2 * ts; word_sub stackpointer (word 48),48]
   [inp,LENGTH src; word pc,libsnappy_rw + libsnappy_rw_size; ea,el] /\\
  nonoverlapping (op,(snappy_max_compressed_length (LENGTH src) - 5)) (table,2 * ts) /\\
  nonoverlapping (op,(snappy_max_compressed_length (LENGTH src) - 5)) (table2,2 * ts) /\\
  nonoverlapping (op,(snappy_max_compressed_length (LENGTH src) - 5))
                 (word_sub stackpointer (word 48),48) /\\
  nonoverlapping (table,2 * ts) (table2,2 * ts) /\\
  nonoverlapping (table,2 * ts) (word_sub stackpointer (word 48),48) /\\
  nonoverlapping (table2,2 * ts) (word_sub stackpointer (word 48),48)";;

let snappy_cf2_frame =
 "MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
  MAYCHANGE [X18; X19; X20; X21; X29; X30; SP] ,,
  MAYCHANGE [memory :> bytes(op,(snappy_max_compressed_length (LENGTH src) - 5));
             memory :> bytes(table,2 * ts); memory :> bytes(table2,2 * ts);
             memory :> bytes(word_sub stackpointer (word 48),48)]";;

let snappy_cf2_args =
  "src inp op table table2 ts pc stackpointer returnaddress \
   x19 x20 x21 x29 rw ea el ev e";;

(* The statement of the piece of code from the point pt (other than join2,  *)
(* the return): from a state that corresponds to a reachable state st of the *)
(* model, the code reaches a point that corresponds to a reachable state     *)
(* with a smaller potential.                                                 *)

let snappy_cf2_piece_stmt pt =
  parse_term
   ("!" ^ snappy_cf2_vars ^ " st. " ^ snappy_cf2_hyps ^ " /\\
     snappy_cf2_reach src st
     ==> ensures arm
          (\\s. snappy_cf2_at " ^ snappy_cf2_args ^ " " ^ pt ^ " st s)
          (\\s. ?pt' st'. snappy_cf2_reach src st' /\\
                         snappy_cf2_pot src st' < snappy_cf2_pot src st /\\
                         snappy_cf2_point pt' /\\
                         snappy_cf2_at " ^ snappy_cf2_args ^ " pt' st' s)
          (" ^ snappy_cf2_frame ^ ")");;

(* ------------------------------------------------------------------------- *)
(* Tactics shared by the proofs of the pieces.                               *)
(* ------------------------------------------------------------------------- *)

(* The start of a piece: the fields of the model state as variables ph, ip,  *)
(* ne, sk, c, x, t1, t2, out, the hypotheses and the invariant of the model  *)
(* (snappy_cf2_inv) as assumptions, and the precondition unfolded (only the  *)
(* precondition: the postcondition keeps snappy_cf2_at folded).              *)

let CF2_PIECE_START_TAC =
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT GEN_TAC THEN SPEC_TAC(`st:snappy_cstate`,`st:snappy_cstate`) THEN
  MATCH_MP_TAC snappy_cstate_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`ph:num`; `ip:num`; `ne:num`; `sk:num`; `c:num`;
                       `x:num`; `t1:num->num`; `t2:num->num`;
                       `out:byte list`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(fun th ->
    if (try fst(dest_const(fst(strip_comb(concl th)))) = "snappy_cf2_reach"
        with Failure _ -> false)
    then MP_TAC(MATCH_MP SNAPPY_CF2_REACH_INV
           (CONJ (ASSUME `LENGTH (src:byte list) <= 65536`) th))
    else failwith "") THEN
  DISCH_TAC THEN
  CONV_TAC(RATOR_CONV(RATOR_CONV(RAND_CONV(ABS_CONV(REWRITE_CONV
   [snappy_cf2_at; snappy_cf2_regs; snappy_cf2_events]))))) THEN
  REWRITE_TAC[snappy_phase; snappy_ip; snappy_ne; snappy_skip; snappy_cand;
              snappy_aux; snappy_t1; snappy_t2; snappy_out] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

(* The assumptions about numbers: those that do not mention the state.     *)

let cf2_arith_asl =
  let bad t = match t with
      Const(("read"|"aligned_bytes_loaded"|"ensures"|"eventually"|
             "memcpy_contract"|"elf_relocated_data"),_) -> true
    | _ -> false in
  fun asl -> filter (fun (_,th) -> not(can (find_term bad) (concl th))) asl;;

(* A goal of arithmetic by tac from the numerical assumptions: first from    *)
(* those that are relevant to it (relevant_arith_facts of                    *)
(* common/arith_facts.ml: the decision procedure splits the cases of every   *)
(* disequality and disjunction it is given, also of facts about other        *)
(* terms), then, if that fails, from all of them as before.                  *)

let cf2_arith_prove (asl,w) (tac:tactic) =
  let aasl = cf2_arith_asl asl in
  let rel = relevant_arith_facts (map snd aasl) w in
  try if length rel = length aasl then failwith "cf2_arith_prove" else
      TAC_PROOF((map (fun th -> ("",th)) rel,w),tac)
  with Failure _ -> TAC_PROOF((aasl,w),tac);;

(* Bounds of the model's numbers that are not linear facts.                 *)

let CF2_BOUND_RULES = map (CONV_RULE NUM_REDUCE_CONV)
  [SNAPPY_LOAD32_BOUND; SNAPPY_LOAD64_BOUND];;

(* Remove x MOD n from the goal (n a numeral) where x < n follows from the  *)
(* numerical assumptions, innermost first.                                   *)

let CF2_MOD_ELIM_TAC : tactic = fun (asl,w) ->
  let mods = setify (find_terms (fun t -> match t with
      Comb(Comb(Const("MOD",_),_),n) -> is_numeral n | _ -> false) w) in
  let bound x n =
    let lt = mk_binary "<" (x,n) in
    try EQT_ELIM(NUM_REDUCE_CONV lt) with Failure _ ->
    try TAC_PROOF(([],lt),SIMP_TAC CF2_BOUND_RULES) with Failure _ ->
    cf2_arith_prove (asl,lt)
      (MAP_EVERY (fun th -> ASSUME_TAC(ISPEC `src:byte list` th))
                 CF2_BOUND_RULES THEN ASM_ARITH_TAC) in
  let try_one t =
    let x,n = dest_binary "MOD" t in MATCH_MP MOD_LT (bound x n) in
  match mapfilter try_one mods with
    [] -> failwith "CF2_MOD_ELIM_TAC"
  | ths -> REWRITE_TAC ths (asl,w);;

let CF2_VAL_RULES =
  [VAL_WORD_ADD; VAL_WORD; VAL_WORD_ZX_GEN; VAL_WORD_USHR; VAL_WORD_SUB_CASES;
   DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64];;

(* Arithmetic from the numerical assumptions (cf2_arith_prove) and the       *)
(* bounds of the loads.                                                      *)

let CF2_ARITH_TAC : tactic = fun (asl,w) ->
  ACCEPT_TAC(cf2_arith_prove (asl,w)
    (MAP_EVERY (fun th -> ASSUME_TAC(ISPEC `src:byte list` th))
       CF2_BOUND_RULES THEN ASM_ARITH_TAC)) (asl,w);;

(* Prove w = w' for words, by the offsets from a common base or by their    *)
(* values (with the arithmetic on the numerical assumptions only: with all   *)
(* the facts about the state it can take very long).                         *)

let CF2_WORD_EQ_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  FIRST
   [REFL_TAC;
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    CF2_ARITH_TAC;
    REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC CF2_VAL_RULES THEN
    CONV_TAC NUM_REDUCE_CONV THEN REPEAT CF2_MOD_ELIM_TAC THEN
    CF2_ARITH_TAC];;

(* Substitute the phase and unfold the invariant of the model.              *)

let CF2_INV_TAC =
  FIRST_X_ASSUM(fun th -> match concl th with
      Comb(Comb(Const("=",_),(Var("ph",_) as v)),n) when is_numeral n ->
        SUBST_ALL_TAC th
    | _ -> failwith "") THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "snappy_cf2_inv"
    with Failure _ -> false)) THEN
  REWRITE_TAC[snappy_cf2_inv] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN STRIP_TAC;;

(* The table size is a power of 2, between 128 and 16384.                   *)

let CF2_TS_TAC =
  FIRST_ASSUM(fun th -> match concl th with
      Comb(Comb(Const("=",_),Var("ts",_)),_) ->
        STRIP_ASSUME_TAC(REWRITE_RULE[SYM th]
          (SPEC `LENGTH(src:byte list)` SNAPPY_POW2_TABLE_SIZE))
    | _ -> failwith "CF2_TS_TAC");;

(* A fact read (memory :> bytes64 (word_add inp (word p))) s = word(load64), *)
(* or bytes32, bytes8, for the current state, from the input region; the    *)
(* bound p + 8 <= LENGTH src from the numerical assumptions.                 *)

let CF2_INPUT_TAC =
  let pat = `read (memory :> bytes(a,LENGTH(l:byte list))) (s:armstate) =
             num_of_bytelist l` in
  fun lemma p (asl,w) ->
    let s = rand w in
    let th = snd(find (fun (_,th) ->
        can (term_match [] pat) (concl th) && rand(lhand(concl th)) = s &&
        rand(rand(concl th)) = `src:byte list`) asl) in
    let a = lhand(rand(rand(lhand(lhand(concl th))))) in
    let l = rand(rand(concl th)) in
    let ith = ISPECL [`memory:(armstate,int64->byte)component`; a; l; p; s]
                     lemma in
    (MP_TAC ith THEN ANTS_TAC THENL
      [CONJ_TAC THENL [ACCEPT_TAC th;
                       W(fun (asl,w) -> ACCEPT_TAC(cf2_arith_prove
                          (asl,w) ASM_ARITH_TAC))];
       DISCH_TAC]) (asl,w);;

(* At a branch on data, the PC fact is read PC s = if b then .. else ..:     *)
(* prove b <=> cond (by the values of the words, with the numerical          *)
(* assumptions) and split on cond.                                           *)

let CF2_COND_EQ_TAC extra =
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0] THEN
  REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC CF2_VAL_RULES THEN
  REWRITE_TAC extra THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CF2_MOD_ELIM_TAC THEN
  REWRITE_TAC extra THEN
  W(fun (asl,w) -> ACCEPT_TAC(cf2_arith_prove (asl,w)
                     (MAP_EVERY (fun th -> ASSUME_TAC(ISPEC `src:byte list` th))
                        CF2_BOUND_RULES THEN ASM_ARITH_TAC)) ORELSE
                   (REWRITE_TAC[] THEN NO_TAC) ORELSE
                   ASM_MESON_TAC[]);;

let CF2_BRANCH_TAC ?(extra=[]) (cond:term) : tactic = fun (asl,w) ->
  let s = rand w in
  let is_pc th = match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),s')),r)
        -> s' = s && is_cond r
    | _ -> false in
  let pcth = snd(find (is_pc o snd) asl) in
  let b,_ = dest_cond(rhs(concl pcth)) in
  let eqth = TAC_PROOF((asl,mk_iff(b,cond)),CF2_COND_EQ_TAC extra) in
  (ASM_CASES_TAC cond THEN
   FIRST_X_ASSUM(fun cth ->
     FIRST_X_ASSUM(fun th -> if concl th = concl pcth then
        ASSUME_TAC(REWRITE_RULE[eqth; cth] th) else failwith "") THEN
     ASSUME_TAC cth)) (asl,w);;

(* A step of the model between explicit states, snappy_cf2_step src X = Y:  *)
(* unfold it and decide its conditions by the assumptions (in the form that  *)
(* the model has them, or arithmetic ones).                                  *)

let CF2_MODEL_STEP_TAC =
  SNAPPY_CF2_UNFOLD_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[SNAPPY_CSTATE_INJ] THEN
         CONV_TAC NUM_REDUCE_CONV THEN
         TRY(CF2_ARITH_TAC ORELSE (REWRITE_TAC[] THEN NO_TAC))) THEN
  ASM_REWRITE_TAC[SNAPPY_CSTATE_INJ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN TRY CF2_ARITH_TAC;;

(* snappy_cf2_reach src Y from the assumption snappy_cf2_reach src X0 by    *)
(* the steps X0 -> m1 -> ... -> mk -> Y (mids = [m1; ...; mk]).              *)

let CF2_REACH_TAC (mids:term list) : tactic = fun (asl,w) ->
  let r0 = snd(find (fun (_,th) ->
      try fst(dest_const(fst(strip_comb(concl th)))) = "snappy_cf2_reach"
      with Failure _ -> false) asl) in
  let x0 = rand(concl r0) in
  let rec tac prevs = match prevs with
      [] -> ACCEPT_TAC r0
    | p::rest ->
        MATCH_MP_TAC SNAPPY_CF2_REACH_STEP_EQ THEN EXISTS_TAC p THEN
        CONJ_TAC THENL [tac rest; CF2_MODEL_STEP_TAC] in
  tac (rev (x0 :: mids)) (asl,w);;

(* The new point: DISJ2 and the witnesses, then reachability, the smaller   *)
(* potential, the point, and the state at it, whose conjuncts that are not   *)
(* assumptions as they are are left as goals (with the step of the model     *)
(* done).                                                                    *)

let CF2_TARGET_TAC (pt:term) (st:term) (mids:term list) =
  MAP_EVERY EXISTS_TAC [pt; st] THEN
  REPEAT CONJ_TAC THENL
   [CF2_REACH_TAC mids;
    REWRITE_TAC[snappy_cf2_pot] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CF2_ARITH_TAC;
    REWRITE_TAC[snappy_cf2_point] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[snappy_cf2_at; snappy_cf2_regs; snappy_phase; snappy_ip;
                snappy_ne; snappy_skip; snappy_cand; snappy_aux; snappy_t1;
                snappy_t2; snappy_out] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(REWRITE_TAC[snappy_cf2_events] THEN MEMSAFE_EVENTS_TAC THEN NO_TAC) THEN
    TRY(SIMP_TAC[SNAPPY_HASH8_WORD; SNAPPY_HASH4_WORD; SNAPPY_LOAD64_BOUND;
                 SNAPPY_POW2_TABLE_SIZE] THEN NO_TAC) THEN
    TRY(CF2_WORD_EQ_TAC THEN NO_TAC) THEN
    TRY CF2_ARITH_TAC];;

(* After ENSURES_INIT_TAC: the events since the start chosen as e2, the     *)
(* phase substituted, the invariant of the model unfolded, the facts about   *)
(* the table size.                                                           *)

let CF2_INIT_TAC =
  ENSURES_INIT_TAC "s0" THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e2:(uarch_event)list` STRIP_ASSUME_TAC o
    check (fun th -> is_exists(concl th) &&
                     fst(dest_var(fst(dest_exists(concl th)))) = "e2")) THEN
  CF2_INV_TAC THEN CF2_TS_TAC;;

(* Split the table fact read (memory :> bytes(a,2 * ts)) s = snappy_tval ts t *)
(* at the entry e (SNAPPY_TABLE_SPLIT), with e < ts and the 16-bit bound of  *)
(* the entries from the assumptions (also for an updated table t, which the  *)
(* match of SNAPPY_TBOUND_16 gives as \j. t j).                             *)

let CF2_TABLE_SPLIT_TAC (a:term) (e:term) : tactic = fun (asl,w) ->
  let s = rand w in
  let th = snd(find (fun (_,th) -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),
        Comb(Comb(Const(":>",_),Const("memory",_)),
             Comb(Const("bytes",_),Comb(Comb(Const(",",_),a'),_)))),s')),
           Comb(Comb(Const("snappy_tval",_),_),_)) -> a' = a && s' = s
    | _ -> false) asl) in
  let t = rand(rhs(concl th)) and k = lhand(rhs(concl th)) in
  let ith = ISPECL [`memory:(armstate,int64->byte)component`; a; k; t; e; s]
                   SNAPPY_TABLE_SPLIT in
  (MP_TAC ith THEN ANTS_TAC THENL
    [REPEAT CONJ_TAC THENL
      [ACCEPT_TAC th;
       ASM_SIMP_TAC[SNAPPY_HASH4_LT; SNAPPY_HASH8_LT; ARITH_RULE
         `128 <= ts ==> ~(ts = 0)`] THEN CF2_ARITH_TAC;
       MATCH_MP_TAC SNAPPY_TBOUND_16 THEN REWRITE_TAC[ETA_AX] THEN
       FIRST_ASSUM(fun bth -> match concl bth with
           Comb(Comb(Const("snappy_tbound",_),t'),b) when t' = t ->
             EXISTS_TAC b THEN CONJ_TAC THENL [ACCEPT_TAC bth; CF2_ARITH_TAC]
         | _ -> failwith "")];
     STRIP_TAC]) (asl,w);;

(* Put a table together again (SNAPPY_TABLE_JOIN): the goal                 *)
(* read (memory :> bytes(a,2 * ts)) s = snappy_tval ts (snappy_tupd t e v).  *)

let CF2_TABLE_JOIN_TAC =
  MATCH_MP_TAC SNAPPY_TABLE_JOIN THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[SNAPPY_HASH4_LT; SNAPPY_HASH8_LT; ARITH_RULE
      `128 <= ts ==> ~(ts = 0)`] THEN CF2_ARITH_TAC;
    CF2_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    ASM_REWRITE_TAC[] THEN CF2_WORD_EQ_TAC;
    FIRST_ASSUM ACCEPT_TAC];;
