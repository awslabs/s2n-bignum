(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proof of InternalCompress (internal_compress_spec.ml). The code is    *)
(* run by bstep, through the in-image methods of ByteArraySource and         *)
(* UncheckedByteArraySink (reached through their vtables in the relocated    *)
(* data), memcpy through the PLT for the header, and the contracts of        *)
(* WorkingMemory::GetHashTable, MaxCompressedLength, CompressFragment and    *)
(* CompressFragmentDoubleHash. The loop over the fragments has one cut point *)
(* (loop1, snappy_ic_inv after k fragments) and the measure LENGTH inp -     *)
(* 65536 * k: SNAPPY_IC_ENTRY goes from the call to the end (empty input)   *)
(* or to loop1 with k = 0 (after the varint header, one case per length of  *)
(* the varint), SNAPPY_IC_ITER from loop1 to the end or to loop1 with k + 1,*)
(* and SNAPPY_IC_ENSURES_LOOP puts them together.                           *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/internal_compress_spec.ml";;
needs "arm/proofs/bstep.ml";;
needs "common/snappy/snappy_roundtrip.ml";;
needs "common/snappy/snappy_words.ml";;
needs "common/snappy/snappy_blocks.ml";;
needs "common/ensures_measure.ml";;
needs "arm/proofs/snappy/events_inset.ml";;

(* The output region has at least 32 bytes, for the events of the varint.    *)
snappy_ev_bounds () :=
  (fun tm -> map (fun t -> SPEC (rand t) SNAPPY_MAX_COMPRESSED_LENGTH_GE_32)
     (setify(find_terms (fun t -> match t with
        Comb(Const("snappy_max_compressed_length",_),_) -> true
      | _ -> false) tm))) :: !(snappy_ev_bounds ());;

let SNAPPY_IC_EXEC = ARM_MK_EXEC_RANGES_RULE snappy_libsnappy_gcc12_O2_mc
   [layout_range "InternalCompress"; layout_range "ByteArraySource_Available";
    layout_range "ByteArraySource_Peek"; layout_range "ByteArraySource_Skip";
    layout_range "UncheckedByteArraySink_GetAppendBuffer";
    layout_range "UncheckedByteArraySink_Append"; layout_range "plt_memcpy"];;

let SNAPPY_IC_VT_REWRITES =
  map (fun (b,k) ->
    let tm = subst [mk_small_numeral b,`b:num`; mk_small_numeral k,`k:num`;
                    mk_small_numeral (b+k),`bk:num`]
      `word_add (word (pc + b)) (word k):int64 = word_add (word pc) (word bk)` in
    prove(tm, REWRITE_TAC[GSYM WORD_ADD; GSYM ADD_ASSOC] THEN
              CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN REFL_TAC))
  [layout "vtable_ByteArraySource",16; layout "vtable_ByteArraySource",24;
   layout "vtable_ByteArraySource",32; layout "vtable_UncheckedByteArraySink",16;
   layout "vtable_UncheckedByteArraySink",24];;

let SNAPPY_IC_SP_REWRITES = [WORD_RULE `word_sub (word_sub stackpointer (word 160)) (word 32):int64 =
                                 word_add (word_sub stackpointer (word 208)) (word 16)`];;

(* ------------------------------------------------------------------------- *)
(* Tactics.                                                                  *)
(* ------------------------------------------------------------------------- *)

let rec snappy_ic_term_size tm =
  match tm with
    Comb(a,b) -> snappy_ic_term_size a + snappy_ic_term_size b
  | Abs(_,b) -> 1 + snappy_ic_term_size b
  | _ -> 1;;

(* The assumptions that are about numbers only (no state).                   *)
let snappy_ic_is_num_fact tm =
  let rec ok t = match t with
      Comb(Comb(Const(("<"|"<="|"="),_),a),_) when
          (try type_of a = `:num` with Failure _ -> false) -> true
    | Comb(Const("~",_),a) -> ok a
    | Comb(Comb(Const("/\\",_),a),b) -> ok a && ok b
    | Comb(Comb(Const("\\/",_),a),b) -> ok a && ok b
    | _ -> false in
  ok tm && not(can (find_term (fun t ->
    match t with Const("read",_) -> true | _ -> false)) tm);;

let snappy_ic_has_cond tm = can (find_term is_cond) tm;;

let SNAPPY_IC_ARITH_TAC : tactic = fun (asl,w) ->
  let ths = filter (fun (_,th) -> snappy_ic_is_num_fact(concl th)) asl in
  let ths0 = filter (fun (_,th) -> not(snappy_ic_has_cond(concl th))) ths in
  ((MAP_EVERY (MP_TAC o snd) ths0 THEN ARITH_TAC) ORELSE
   (MAP_EVERY (MP_TAC o snd) ths THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC))
  ([],w);;

let SNAPPY_IC_INT_SUB_EQ = prove
 (`!a b c. (&a - &b = &c:int) <=> a = b + c`,
  REWRITE_TAC[INT_EQ_SUB_LADD; INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC);;

(* Eliminate x MOD n and x DIV n (n a numeral) with x < n by arithmetic.    *)
let SNAPPY_IC_MOD_ELIM_CONV (ths:thm list) : conv =
  let is_md op t = is_binary op t && is_numeral(rand t) in
  let ariths = filter (fun th -> snappy_ic_is_num_fact(concl th) &&
                                 not(can (find_term is_cond) (concl th))) ths in
  let prove_lt tm =
    TAC_PROOF(([],tm), MAP_EVERY MP_TAC ariths THEN ARITH_TAC) in
  let rec go tm =
    let cands = setify(find_terms (fun t -> is_md "MOD" t || is_md "DIV" t) tm) in
    let cands = sort (fun a b -> snappy_ic_term_size a < snappy_ic_term_size b) cands in
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

let SNAPPY_IC_VAL_THMS = [SNAPPY_IC_INT_SUB_EQ; VAL_EQ_0; WORD_SUB_EQ_0; GSYM VAL_EQ; VAL_WORD_ADD; VAL_WORD_SUB_CASES; VAL_WORD_ZX_GEN;
  VAL_WORD_USHR; VAL_WORD_SHL; VAL_WORD; DIMINDEX_8; DIMINDEX_16;
  DIMINDEX_32; DIMINDEX_64];;

let SNAPPY_IC_CF_LEMMA = prove
 (`!(x:N word) n. n < 2 EXP dimindex(:N)
       ==> ((&(val x) - &n = &(val(word_sub x (word n))):int) <=> n <= val x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUB_CASES] THEN
  ASM_SIMP_TAC[VAL_WORD_EQ] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB];
    MATCH_MP_TAC(INT_ARITH `(&a:int) < &b ==> ~(&a - &b = &c:int)`) THEN
    REWRITE_TAC[INT_OF_NUM_LT] THEN ASM_ARITH_TAC]);;

let SNAPPY_IC_CF_CONV tm =
  match tm with
    Comb(Comb(Const("=",_),Comb(Comb(Const("int_sub",_),Comb(_,Comb(Const("val",_),x))),
         Comb(_,n))),Comb(_,Comb(Const("val",_),_))) when is_numeral n ->
      let th = ISPECL [x; n] SNAPPY_IC_CF_LEMMA in
      let side = lhand(concl th) in
      let sth = EQT_ELIM((REWRITE_CONV[DIMINDEX_8; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64] THENC NUM_REDUCE_CONV) side) in
      MP th sth
  | _ -> failwith "SNAPPY_IC_CF_CONV";;

(* A term as numbers: the values of words, with MOD and DIV eliminated.      *)
let SNAPPY_IC_NUM_CONV (ths:thm list) (extra:thm list) : conv =
  TRY_CONV(ONCE_DEPTH_CONV SNAPPY_IC_CF_CONV) THENC
  REWRITE_CONV (extra @ SNAPPY_IC_VAL_THMS) THENC NUM_REDUCE_CONV THENC
  SNAPPY_IC_MOD_ELIM_CONV ths THENC
  REWRITE_CONV[LT_ADD_LCANCEL; LE_ADD_LCANCEL; EQ_ADD_LCANCEL];;

let snappy_ic_is_pc_fact th = match concl th with
    Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Const("PC",_)),_)),_) -> true
  | _ -> false;;

let snappy_ic_is_pc_cond_fact th =
  snappy_ic_is_pc_fact th &&
  (try let f,args = strip_comb(rand(concl th)) in
       fst(dest_const f) = "COND" && length args = 3
   with Failure _ -> false);;

(* The branch condition c of the PC fact: decided by tac (proving c or ~c   *)
(* after SNAPPY_IC_NUM_CONV, with COND_CASES and SNAPPY_IC_ARITH_TAC if tac is not        *)
(* given), or split into the two cases.                                     *)
let SNAPPY_IC_PC_COND_TAC (extra:thm list) : tactic = fun (asl,w) ->
  let ths = map snd asl in
  let th = find snappy_ic_is_pc_cond_fact ths in
  let c = rand(rator(rator(rand(concl th)))) in
  let cth = SNAPPY_IC_NUM_CONV ths extra c in
  let c' = rand(concl cth) in
  let decide b =
    let g = if b then c' else mk_neg c' in
    try Some(TAC_PROOF((asl,g),
      REPEAT COND_CASES_TAC THEN CONV_TAC(SNAPPY_IC_NUM_CONV ths extra) THEN
      REPEAT COND_CASES_TAC THEN SNAPPY_IC_ARITH_TAC))
    with Failure _ -> None in
  let fix bth =
    UNDISCH_THEN (concl th) (fun pth ->
      ASSUME_TAC(PURE_ONCE_REWRITE_RULE[COND_CLAUSES]
        (CONV_RULE(RAND_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV(K bth))))) pth))) in
  match decide true with
    Some t -> fix (EQT_INTRO(EQ_MP (SYM cth) t)) (asl,w)
  | None -> match decide false with
      Some t -> fix (EQF_INTRO(EQ_MP (AP_TERM `(~)` (SYM cth)) t)) (asl,w)
    | None -> failwith ("SNAPPY_IC_PC_COND_TAC: undecided " ^ string_of_term c');;

let SNAPPY_IC_PC_CASES_TAC (extra:thm list) : tactic = fun (asl,w) ->
  let ths = map snd asl in
  let th = find snappy_ic_is_pc_cond_fact ths in
  let c = rand(rator(rator(rand(concl th)))) in
  let cth = SNAPPY_IC_NUM_CONV ths extra c in
  let c' = rand(concl cth) in
  let fix b =
    let bth = if b then EQT_INTRO(EQ_MP (SYM cth) (ASSUME c'))
              else EQF_INTRO(EQ_MP (AP_TERM `(~)` (SYM cth)) (ASSUME(mk_neg c'))) in
    UNDISCH_THEN (concl th) (fun pth ->
      ASSUME_TAC(PURE_ONCE_REWRITE_RULE[COND_CLAUSES]
        (CONV_RULE(RAND_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV(K bth))))) pth))) in
  (ASM_CASES_TAC c' THENL [fix true; fix false]) (asl,w);;

(* Prove v = v' for the fact read c s = v when the goal is read c s = v'.   *)
let SNAPPY_IC_FACT_TAC (tac:tactic) : tactic = fun (asl,w) ->
  let l = lhs w in
  let th = snd(find (fun (_,th) -> try lhs(concl th) = l with Failure _ -> false) asl) in
  (GEN_REWRITE_TAC LAND_CONV [th] THEN tac) (asl,w);;

(* Rewrite only the facts read c s = v about the components cs.             *)
let SNAPPY_IC_REWRITE_FACTS_TAC (cs:term list) (ths:thm list) : tactic =
  let is_c th = match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),_)),_) -> mem c cs
    | _ -> false in
  RULE_ASSUM_TAC(fun th -> if is_c th then REWRITE_RULE ths th else th);;

(* Replace the fact read c s = v (s the current state) by read c s = v',     *)
(* proving v = v' by tac.                                                   *)
let SNAPPY_IC_FACT_UPDATE_TAC (c:term) (v':term) (tac:tactic) : tactic = fun (asl,w) ->
  let st = rand w in
  let is_c th = match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c'),s)),_) ->
        c' = c && s = st
    | _ -> false in
  let th = snd(find (fun (_,th) -> is_c th) asl) in
  let v = rand(concl th) in
  let eq = TAC_PROOF((asl,mk_eq(v,v')),tac) in
  (UNDISCH_THEN (concl th) (fun th -> ASSUME_TAC(TRANS th eq))) (asl,w);;

(* The usual proof of v = v' for words that are numbers.                    *)
let SNAPPY_IC_WORD_EQ_TAC : tactic = fun (asl,w) ->
  let ths = map snd asl in
  (REWRITE_TAC[GSYM VAL_EQ] THEN CONV_TAC(SNAPPY_IC_NUM_CONV ths []) THEN
   REPEAT COND_CASES_TAC THEN
   CONV_TAC(SNAPPY_IC_NUM_CONV ths []) THEN TRY SNAPPY_IC_ARITH_TAC) (asl,w);;

let SNAPPY_IC_HYPS_TAC =
  REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(W(fun (asl,w) -> if is_comb w && fst(strip_comb w) = `aligned:num->int64->bool` then
       ACCEPT_TAC(EQT_ELIM(ALIGNED_WORD_CONV (map snd asl) w)) else NO_TAC)) THEN
  TRY(W(fun (asl,w) -> if is_binary "<" w || is_binary "<=" w then
       (REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
        CONV_TAC(SNAPPY_IC_MOD_ELIM_CONV (map snd asl)) THEN SNAPPY_IC_ARITH_TAC) else NO_TAC)) THEN
  NONOVERLAPPING_TAC;;


(* ------------------------------------------------------------------------- *)
(* The state at the head of the loop over the fragments (loop1), after k     *)
(* fragments: the output so far is the varint of the length and the blocks  *)
(* of the first 65536 * k bytes.                                             *)
(* ------------------------------------------------------------------------- *)

let snappy_ic_len = new_definition
 `snappy_ic_len level (inp:byte list) k =
    LENGTH(snappy_varint_encode(LENGTH inp)) +
    LENGTH(snappy_compress_blocks level (SUB_LIST(0,65536 * k) inp))`;;

let snappy_ic_out = new_definition
 `snappy_ic_out level (inp:byte list) k =
    APPEND (snappy_varint_encode(LENGTH inp))
           (snappy_compress_blocks level (SUB_LIST(0,65536 * k) inp))`;;

let snappy_ic_frame = new_definition
 `snappy_ic_frame pc (stackpointer:int64) (x19:int64) x20 x21 x22 x23 x24 x25
                  x26 x27 x28 x29 (ra:int64) rw ea el ev (s:armstate) <=>
   aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
   read SP s = word_sub stackpointer (word 160) /\
   read (memory :> bytes64 (word_sub stackpointer (word 160))) s = x29 /\
   read (memory :> bytes64 (word_add (word_sub stackpointer (word 160))
                                     (word 8))) s = ra /\
   read (memory :> bytes64 (word_add (word_sub stackpointer (word 160))
                                     (word 16))) s = x19 /\
   read (memory :> bytes64 (word_add (word_sub stackpointer (word 160))
                                     (word 24))) s = x20 /\
   read (memory :> bytes64 (word_add (word_sub stackpointer (word 160))
                                     (word 32))) s = x21 /\
   read (memory :> bytes64 (word_add (word_sub stackpointer (word 160))
                                     (word 40))) s = x22 /\
   read (memory :> bytes64 (word_add (word_sub stackpointer (word 160))
                                     (word 48))) s = x23 /\
   read (memory :> bytes64 (word_add (word_sub stackpointer (word 160))
                                     (word 56))) s = x24 /\
   read (memory :> bytes64 (word_add (word_sub stackpointer (word 160))
                                     (word 64))) s = x25 /\
   read (memory :> bytes64 (word_add (word_sub stackpointer (word 160))
                                     (word 72))) s = x26 /\
   read (memory :> bytes64 (word_add (word_sub stackpointer (word 160))
                                     (word 80))) s = x27 /\
   read (memory :> bytes64 (word_add (word_sub stackpointer (word 160))
                                     (word 88))) s = x28 /\
   read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s = rw /\
   read (memory :> bytes(ea,el)) s = ev`;;

let snappy_ic_inv = new_definition
 `snappy_ic_inv pc level (inp:byte list) (src:int64) (out:int64) (so:int64)
                (sk:int64) (wm:int64) (mem:int64) rw ea el ev stackpointer
                x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 ra k s <=>
   snappy_ic_frame pc stackpointer x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
                   x29 ra rw ea el ev s /\
   read PC s = word(pc + InternalCompress_loop1) /\
   read X19 s = so /\ read X22 s = sk /\ read X24 s = wm /\
   read X26 s = word level /\
   read X21 s = word(LENGTH inp - 65536 * k) /\
   read X25 s = word(snappy_ic_len level inp k) /\
   read (memory :> bytes64 (word_add (word_sub stackpointer (word 160))
                                     (word 104))) s =
     word_add (word_sub stackpointer (word 160)) (word 152) /\
   read (memory :> bytes64 (word_add (word_sub stackpointer (word 160))
                                     (word 112))) s =
     word_add (word_sub stackpointer (word 160)) (word 140) /\
   read (memory :> bytes64 so) s = word(pc + vtable_ByteArraySource) /\
   read (memory :> bytes64 (word_add so (word 8))) s =
     word_add src (word(65536 * k)) /\
   read (memory :> bytes64 (word_add so (word 16))) s =
     word(LENGTH inp - 65536 * k) /\
   read (memory :> bytes64 sk) s = word(pc + vtable_UncheckedByteArraySink) /\
   read (memory :> bytes64 (word_add sk (word 8))) s =
     word_add out (word(snappy_ic_len level inp k)) /\
   read (memory :> bytes64 (word_add wm (word 24))) s = mem /\
   read (memory :> bytes(src,LENGTH inp)) s = num_of_bytelist inp /\
   read (memory :> bytes(out,snappy_ic_len level inp k)) s =
     num_of_bytelist(snappy_ic_out level inp k)`;;

let snappy_ic_post = new_definition
 `snappy_ic_post level (inp:byte list) (out:int64) (sk:int64)
     (stackpointer:int64) (x19:int64) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
     (ra:int64) s <=>
   read PC s = ra /\
   read X0 s = word(LENGTH(snappy_compress level inp)) /\
   read (memory :> bytelist(out,LENGTH(snappy_compress level inp))) s =
     snappy_compress level inp /\
   read (memory :> bytes64 (word_add sk (word 8))) s =
     word_add out (word(LENGTH(snappy_compress level inp))) /\
   read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
   read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
   read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
   read X28 s = x28 /\ read X29 s = x29 /\ read SP s = stackpointer`;;


(* Memory safety (the _SAFE statement): the events since the call are in the *)
(* regions that the code may read and write. The cut point and the end with  *)
(* the events.                                                               *)

let snappy_ic_ev = new_definition
 `snappy_ic_ev pc (inp:byte list) (src:int64) (out:int64) (so:int64)
               (sk:int64) (wm:int64) (mem:int64) nw (ea:int64) el
               (stackpointer:int64) (e:uarch_event list) (s:armstate) <=>
   ?e2. read events s = APPEND e2 e /\
        memaccess_inset e2
         (memrange(src,LENGTH inp) UNION memrange(wm,48) UNION
          memrange(out,snappy_max_compressed_length (LENGTH inp)) UNION
          memrange(mem,snappy_working_memory_size nw) UNION
          memrange(so,24) UNION memrange(sk,16) UNION
          memrange(word_sub stackpointer (word 160),160) UNION
          memrange(word_sub stackpointer (word 208),48) UNION
          memrange(word pc,libsnappy_rw + libsnappy_rw_size) UNION
          memrange(ea,el))
         (memrange(out,snappy_max_compressed_length (LENGTH inp)) UNION
          memrange(mem,snappy_working_memory_size nw) UNION
          memrange(so,24) UNION memrange(sk,16) UNION
          memrange(word_sub stackpointer (word 160),160) UNION
          memrange(word_sub stackpointer (word 208),48))`;;

let snappy_ic_inv_safe = new_definition
 `snappy_ic_inv_safe pc level (inp:byte list) (src:int64) (out:int64) (so:int64)
                (sk:int64) (wm:int64) (mem:int64) nw rw ea el ev stackpointer
                x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 ra
                (e:uarch_event list) k s <=>
   snappy_ic_inv pc level inp src out so sk wm mem rw ea el ev stackpointer
                 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 ra k s /\
   snappy_ic_ev pc inp src out so sk wm mem nw ea el stackpointer e s`;;

let snappy_ic_post_safe = new_definition
 `snappy_ic_post_safe pc level (inp:byte list) (src:int64) (out:int64)
     (so:int64) (sk:int64) (wm:int64) (mem:int64) nw (ea:int64) el
     (stackpointer:int64) (x19:int64) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
     (ra:int64) (e:uarch_event list) s <=>
   snappy_ic_post level inp out sk stackpointer x19 x20 x21 x22 x23 x24 x25
                  x26 x27 x28 x29 ra s /\
   snappy_ic_ev pc inp src out so sk wm mem nw ea el stackpointer e s`;;

let snappy_ic_hyps_str =
 "aligned 4096 (word pc:int64) /\\
    pc + libsnappy_rw + libsnappy_rw_size <= 2 EXP 64 /\\
    memcpy_contract (imp \"memcpy\") ea el ev /\\
    memset_correct_safe_contract (imp \"memset\") ea el ev /\\
    elf_relocated_data (word(pc + libsnappy_rw)) rw
      (snappy_libsnappy_gcc12_O2_relocated pc imp) /\\
    aligned 16 stackpointer /\\
    (level = 1 \\/ level = 2) /\\
    LENGTH inp < 2 EXP 32 /\\
    snappy_fragment_size (LENGTH inp) <= snappy_fragment_size nw /\\
    val src + LENGTH inp + 65536 < 2 EXP 64 /\\
    val out + snappy_max_compressed_length (LENGTH inp) < 2 EXP 64 /\\
    PAIRWISE nonoverlapping
     [out,snappy_max_compressed_length (LENGTH inp); mem,snappy_working_memory_size nw;
      so,24; sk,16; word_sub stackpointer (word 160),160;
      word_sub stackpointer (word 208),48] /\\
    ALLPAIRS nonoverlapping
     [out,snappy_max_compressed_length (LENGTH inp); mem,snappy_working_memory_size nw;
      so,24; sk,16; word_sub stackpointer (word 160),160;
      word_sub stackpointer (word 208),48]
     [src,LENGTH inp; wm,48; word pc,libsnappy_rw + libsnappy_rw_size;
      ea,el]";;

let snappy_ic_hyps_safe_str =
  let old = "memcpy_contract (imp \"memcpy\")" and h = snappy_ic_hyps_str in
  let n = String.length old in
  let rec find i = if String.sub h i n = old then i else find (i + 1) in
  let i = find 0 in
  String.sub h 0 i ^ "memcpy_correct_safe_contract (imp \"memcpy\")" ^
  String.sub h (i + n) (String.length h - i - n);;

let snappy_ic_frame_str =
 "MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18; X30] ,,
  MAYCHANGE [memory :> bytes(out,snappy_max_compressed_length
                                   (LENGTH inp));
             memory :> bytes(mem,snappy_working_memory_size nw);
             memory :> bytes(so,24); memory :> bytes(sk,16);
             memory :> bytes(word_sub stackpointer (word 160),160);
             memory :> bytes(word_sub stackpointer (word 208),48)] ,,
  MAYCHANGE [X19] ,, MAYCHANGE [X20] ,, MAYCHANGE [X21] ,,
  MAYCHANGE [X22] ,, MAYCHANGE [X23] ,, MAYCHANGE [X24] ,,
  MAYCHANGE [X25] ,, MAYCHANGE [X26] ,, MAYCHANGE [X27] ,,
  MAYCHANGE [X28] ,, MAYCHANGE [X29] ,, MAYCHANGE [SP]";;

let snappy_ic_vars_str =
  "pc level (inp:byte list) src out so sk wm mem nw imp ea el ev rw stackpointer
   x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 ra";;

let snappy_ic_invargs_str =
  "pc level inp src out so sk wm mem rw ea el ev stackpointer
   x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 ra";;

let snappy_ic_postargs_str =
  "level inp out sk stackpointer x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 ra";;

let snappy_ic_invargs_safe_str =
  "pc level inp src out so sk wm mem nw rw ea el ev stackpointer
   x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 ra e";;

let snappy_ic_postargs_safe_str =
  "pc level inp src out so sk wm mem nw ea el stackpointer
   x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 ra e";;

let SNAPPY_IC_ITER_SAFE_STMT = parse_term
 ("!" ^ snappy_ic_vars_str ^ " (e:uarch_event list) k.
    " ^ snappy_ic_hyps_safe_str ^ " /\\ 65536 * k < LENGTH inp
    ==> ensures arm
         (\\s. snappy_ic_inv_safe " ^ snappy_ic_invargs_safe_str ^ " k s)
         (\\s. snappy_ic_post_safe " ^ snappy_ic_postargs_safe_str ^ " s \\/
              ?m. m < LENGTH inp - 65536 * k /\\
                  ?k'. 65536 * k' < LENGTH inp /\\ m = LENGTH inp - 65536 * k' /\\
                       snappy_ic_inv_safe " ^ snappy_ic_invargs_safe_str ^ " k' s)
         (" ^ snappy_ic_frame_str ^ ")");;

let SNAPPY_IC_ITER_STMT = parse_term
 ("!" ^ snappy_ic_vars_str ^ " k.
    " ^ snappy_ic_hyps_str ^ " /\\ 65536 * k < LENGTH inp
    ==> ensures arm
         (\\s. snappy_ic_inv " ^ snappy_ic_invargs_str ^ " k s)
         (\\s. snappy_ic_post " ^ snappy_ic_postargs_str ^ " s \\/
              ?m. m < LENGTH inp - 65536 * k /\\
                  ?k'. 65536 * k' < LENGTH inp /\\ m = LENGTH inp - 65536 * k' /\\
                       snappy_ic_inv " ^ snappy_ic_invargs_str ^ " k' s)
         (" ^ snappy_ic_frame_str ^ ")");;

let snappy_ic_pre = new_definition
 `snappy_ic_pre pc level (inp:byte list) (src:int64) (out:int64) (so:int64)
     (sk:int64) (wm:int64) (mem:int64) nw owns rw (ea:int64) el ev
     (stackpointer:int64) (x19:int64) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
     (ra:int64) s <=>
   aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc /\
   read PC s = word(pc + InternalCompress) /\
   read SP s = stackpointer /\ read X30 s = ra /\
   read X0 s = so /\ read X1 s = sk /\ read X2 s = word level /\ read X3 s = wm /\
   read (memory :> bytes64 so) s = word(pc + vtable_ByteArraySource) /\
   read (memory :> bytes64 (word_add so (word 8))) s = src /\
   read (memory :> bytes64 (word_add so (word 16))) s = word(LENGTH inp) /\
   read (memory :> bytes64 sk) s = word(pc + vtable_UncheckedByteArraySink) /\
   read (memory :> bytes64 (word_add sk (word 8))) s = out /\
   snappy_working_memory wm mem nw owns s /\
   read (memory :> bytes(word(pc + libsnappy_rw),libsnappy_rw_size)) s = rw /\
   read (memory :> bytes(ea,el)) s = ev /\
   read (memory :> bytelist(src,LENGTH inp)) s = inp /\
   read X19 s = x19 /\ read X20 s = x20 /\ read X21 s = x21 /\
   read X22 s = x22 /\ read X23 s = x23 /\ read X24 s = x24 /\
   read X25 s = x25 /\ read X26 s = x26 /\ read X27 s = x27 /\
   read X28 s = x28 /\ read X29 s = x29`;;

let SNAPPY_IC_ENTRY_STMT = parse_term
 ("!" ^ snappy_ic_vars_str ^ " owns.
    " ^ snappy_ic_hyps_str ^ "
    ==> ensures arm
         (\\s. snappy_ic_pre pc level inp src out so sk wm mem nw owns rw ea el ev
                 stackpointer x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 ra s)
         (\\s. snappy_ic_post " ^ snappy_ic_postargs_str ^ " s \\/
              ?m. ?k'. 65536 * k' < LENGTH inp /\\ m = LENGTH inp - 65536 * k' /\\
                       snappy_ic_inv " ^ snappy_ic_invargs_str ^ " k' s)
         (" ^ snappy_ic_frame_str ^ ")");;

let SNAPPY_IC_ENTRY_SAFE_STMT = parse_term
 ("!" ^ snappy_ic_vars_str ^ " owns (e:uarch_event list).
    " ^ snappy_ic_hyps_safe_str ^ "
    ==> ensures arm
         (\\s. snappy_ic_pre pc level inp src out so sk wm mem nw owns rw ea el ev
                 stackpointer x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 ra s /\\
              read events s = e)
         (\\s. snappy_ic_post_safe " ^ snappy_ic_postargs_safe_str ^ " s \\/
              ?m. ?k'. 65536 * k' < LENGTH inp /\\ m = LENGTH inp - 65536 * k' /\\
                       snappy_ic_inv_safe " ^ snappy_ic_invargs_safe_str ^ " k' s)
         (" ^ snappy_ic_frame_str ^ ")");;

(* The _SAFE proofs run the same tactics as the _CORRECT ones: a call takes  *)
(* the _SAFE contract of the callee when the hypotheses have memcpy's        *)
(* correct_safe contract, and the events of the cut points and of the end    *)
(* are proved at the end of each path (SNAPPY_IC_EV_FINAL_TAC, nothing for   *)
(* the _CORRECT goals).                                                      *)

let snappy_ic_is_safe (asl,w) =
  exists (fun (_,th) ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "memcpy_correct_safe_contract"
    with Failure _ -> false) asl;;

let SNAPPY_IC_MP_SPEC_TAC (cth:thm) (sth:thm) (args:term list) : tactic =
  fun (asl,w) ->
    if snappy_ic_is_safe (asl,w)
    then MP_TAC(SPECL (snappy_current_events (asl,w) :: args) sth) (asl,w)
    else MP_TAC(SPECL args cth) (asl,w);;

let SNAPPY_IC_EV_FINAL_TAC : tactic =
  GEN_REWRITE_TAC TOP_DEPTH_CONV
    [snappy_ic_post_safe; snappy_ic_inv_safe; snappy_ic_ev] THEN
  SNAPPY_INSET_FIRST_TAC;;

let SNAPPY_IC_NUM_OF_BYTELIST_APPEND = prove
 (`!(l1:byte list) l2.
        num_of_bytelist(APPEND l1 l2) =
        num_of_bytelist l1 + 2 EXP (8 * LENGTH l1) * num_of_bytelist l2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; num_of_bytelist; LENGTH; MULT_CLAUSES; EXP; ADD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `8 * SUC n = 8 + 8 * n`; EXP_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let SNAPPY_IC_READ_BYTES_APPEND = prove
 (`!a (l1:byte list) l2 L (s:armstate).
        read (memory :> bytes(a,L)) s = num_of_bytelist l1 /\ LENGTH l1 = L /\
        read (memory :> bytelist(word_add a (word L),LENGTH l2)) s = l2
        ==> read (memory :> bytes(a,L + LENGTH l2)) s =
            num_of_bytelist(APPEND l1 l2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
  ASM_REWRITE_TAC[SNAPPY_IC_NUM_OF_BYTELIST_APPEND]);;

let SNAPPY_IC_OUT_LEN = prove
 (`!level (inp:byte list) k.
        LENGTH(snappy_ic_out level inp k) = snappy_ic_len level inp k`,
  REWRITE_TAC[snappy_ic_out; snappy_ic_len; LENGTH_APPEND]);;

(* Prove a conjunct read c s = v of a cut point or of the end from the facts. *)
let SNAPPY_IC_CONJ_TAC (eqs:thm list) : tactic =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         FIRST_ASSUM(fun th -> ACCEPT_TAC(REWRITE_RULE[READ_BYTELIST_EQ_BYTES] th));
         SNAPPY_IC_FACT_TAC (REWRITE_TAC eqs THEN NO_TAC);
         REWRITE_TAC eqs THEN FIRST_ASSUM ACCEPT_TAC;
         SNAPPY_IC_FACT_TAC (SIMP_TAC(eqs @ [SNAPPY_VARINT_ENCODE_1; LENGTH; ARITH]) THEN NO_TAC);
         SNAPPY_IC_FACT_TAC (REWRITE_TAC(WORD_ADD :: eqs) THEN CONV_TAC WORD_RULE);
         SNAPPY_IC_FACT_TAC (AP_TERM_TAC THEN SNAPPY_IC_ARITH_TAC);
         SNAPPY_IC_FACT_TAC (REWRITE_TAC(eqs @ [ARITH_RULE `65536 * (k + 1) = 65536 * k + 65536`; WORD_ADD]) THEN CONV_TAC WORD_RULE);
         REWRITE_TAC eqs THEN MATCH_MP_TAC SNAPPY_IC_READ_BYTES_APPEND THEN
         REWRITE_TAC[SNAPPY_IC_OUT_LEN] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];;

let SNAPPY_IC_COMPRESS_LAST = prove
 (`!level (inp:byte list) k.
        65536 * k < LENGTH inp /\ LENGTH inp < 2 EXP 32 /\
        LENGTH inp - 65536 * k <= 65536
        ==> APPEND (snappy_ic_out level inp k)
             (snappy_compress_fragment level
               (SUB_LIST(65536 * k,MIN 65536 (LENGTH inp - 65536 * k)) inp)) =
            snappy_compress level inp`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[snappy_ic_out; snappy_compress; GSYM NOT_LT; GSYM APPEND_ASSOC] THEN
  AP_TERM_TAC THEN
  MP_TAC(SPECL [`level:num`; `k:num`; `inp:byte list`] SNAPPY_BLOCKS_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `65536 * k + MIN 65536 (LENGTH(inp:byte list) - 65536 * k) = LENGTH inp`
  SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[SNAPPY_BLOCKS_ALL]]);;

let SNAPPY_IC_OUT_NEXT = prove
 (`!level (inp:byte list) k.
        65536 * k < LENGTH inp /\ 65536 < LENGTH inp - 65536 * k
        ==> APPEND (snappy_ic_out level inp k)
             (snappy_compress_fragment level
               (SUB_LIST(65536 * k,MIN 65536 (LENGTH inp - 65536 * k)) inp)) =
            snappy_ic_out level inp (k + 1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[snappy_ic_out; GSYM APPEND_ASSOC] THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`level:num`; `k:num`; `inp:byte list`] SNAPPY_BLOCKS_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let SNAPPY_IC_READ_BYTES_ZERO_SPLIT = prove
 (`!a x y (s:armstate).
        read (memory :> bytes(a,x + y)) s = 0
        ==> read (memory :> bytes(a,x)) s = 0 /\
            read (memory :> bytes(word_add a (word x),y)) s = 0`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; ADD_EQ_0; MULT_EQ_0;
              EXP_EQ_0; ARITH_EQ]);;

let SNAPPY_IC_TABLE_SIZE_HALF = prove
 (`!n. 2 * (snappy_table_size n DIV 2) + 2 * (snappy_table_size n DIV 2) =
       2 * snappy_table_size n`,
  GEN_TAC THEN MP_TAC(SPEC `n:num` SNAPPY_TABLE_SIZE_CASES) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN CONV_TAC NUM_REDUCE_CONV);;

let SNAPPY_IC_TABLE_SIZE_ISHR = prove
 (`!n. word_zx (word_ishr (word (snappy_table_size n):int32) 1):int64 =
       word (snappy_table_size n DIV 2) /\
       word_shl (word_sx (word_ishr (word (snappy_table_size n):int32) 1):int64) 1 =
       word (2 * (snappy_table_size n DIV 2))`,
  GEN_TAC THEN MP_TAC(SPEC `n:num` SNAPPY_TABLE_SIZE_CASES) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN CONV_TAC NUM_REDUCE_CONV);;

let SNAPPY_IC_ENSURES_LOOP = prove
 (`!(step:A->A->bool) P Q C (R:num->A->bool).
        C ,, C = C /\
        ensures step P (\s. Q s \/ ?m. R m s) C /\
        (!n. ensures step (R n) (\s. Q s \/ ?m. m < n /\ R m s) C)
        ==> ensures step P Q C`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`step:A->A->bool`; `R:num->A->bool`; `Q:A->bool`; `C:A->A->bool`]
    ENSURES_MEASURE_INDUCT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `C ,, C = (C:A->A->bool)` THEN
  REWRITE_TAC[FUN_EQ_THM; seq] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!a b c. (C:A->A->bool) a b /\ C b c ==> C a c` ASSUME_TAC
  THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ensures] THEN DISCH_TAC THEN X_GEN_TAC `s:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:A`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[EVENTUALLY_IMP_EVENTUALLY]
   `(!s'. P s' ==> eventually (step:A->A->bool) Q s')
    ==> eventually step P s ==> eventually step Q s`) THEN
  X_GEN_TAC `s':A` THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC) THENL
   [ONCE_REWRITE_TAC[eventually_CASES] THEN DISJ1_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(X_CHOOSE_TAC `m:num`)] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o check (fun th ->
    try fst(dest_const(fst(strip_comb(snd(dest_forall(concl th)))))) = "ensures"
    with Failure _ -> false)) THEN
  REWRITE_TAC[ensures] THEN DISCH_THEN(MP_TAC o SPEC `s':A`) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_MONO) THEN
  X_GEN_TAC `s'':A` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let SNAPPY_IC_MASK_THMS =
  let mk k = CONV_RULE NUM_REDUCE_CONV (ISPECL [`x:int32`; mk_small_numeral k] VAL_WORD_AND_MASK_WORD) in
  let mk' k = CONV_RULE NUM_REDUCE_CONV (ONCE_REWRITE_RULE[WORD_AND_SYM] (ISPECL [`x:int32`; mk_small_numeral k] VAL_WORD_AND_MASK_WORD)) in
  map mk [7;8] @ map mk' [7;8];;
let SNAPPY_IC_BYTES1 = prove
 (`!a (s:armstate) v. read (memory :> bytes8 a) s = v ==> read (memory :> bytes(a,1)) s = val v`,
  SIMP_TAC[READ_MEMORY_BYTES_BYTES8]);;
let SNAPPY_IC_BYTE_OR128 = prove
 (`!y:int32. val(word_zx(word_or y (word 128)):byte) = val y MOD 128 + 128 /\
             val(word_zx(word_or y (word 4294967168)):byte) = val y MOD 128 + 128`,
  GEN_TAC THEN
  REWRITE_TAC[BITBLAST_RULE `word_zx(word_or (y:int32) (word 128)):byte = word_or (word_and (word_zx y) (word 127)) (word 128)`;
              BITBLAST_RULE `word_zx(word_or (y:int32) (word 4294967168)):byte = word_or (word_and (word_zx y) (word 127)) (word 128)`] THEN
  SIMP_TAC[VAL_WORD_OR_DISJOINT; BITBLAST_RULE `word_and (word_and (word_zx (y:int32)) (word 127)) (word 128):byte = word 0`] THEN
  REWRITE_TAC[CONV_RULE NUM_REDUCE_CONV (ISPECL [`word_zx (y:int32):byte`; `7`] VAL_WORD_AND_MASK_WORD)] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `256 = 128 * 2`; MOD_MOD]);;

let SNAPPY_IC_NE_OF_NONOVERLAP = prove
 (`!a b:int64. nonoverlapping (a,1) (b,1) ==> ~(a = b)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; NONOVERLAPPING_MODULO_REFL; ARITH_EQ]);;

let SNAPPY_IC_VAL32_BYTES = prove
 (`!v. v < 2 EXP 32
       ==> v = v MOD 256 + 256 * ((v DIV 256) MOD 256) +
               65536 * ((v DIV 65536) MOD 256) + 16777216 * (v DIV 16777216)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`v:num`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`v DIV 256`; `256`] DIVISION) THEN
  MP_TAC(SPECL [`v DIV 65536`; `256`] DIVISION) THEN
  REWRITE_TAC[DIV_DIV] THEN CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC);;

let SNAPPY_IC_W4 =
  `word_insert
   (word_insert
    (word_insert
     (word_insert (word 0:int32) (0,8)
     (word_ushr (word_or (word_and (y:int32) (word 255)) (word 128)) 0):int32)
     (8,8)
    (word_or (word_subword y (7,8)) (word 128):int32):int32)
    (16,8)
   (word_or (word_subword y (14,8)) (word 128):int32):int32)
   (24,8)
   (z:int32):int32`;;

let SNAPPY_IC_W4_BYTES =
  let w = SNAPPY_IC_W4 in
  let mk k rhs = BITBLAST_RULE(mk_eq(subst [w,`w:int32`; mk_small_numeral k,`k:num`]
                   `word_zx (word_ushr (w:int32) k):byte`, rhs)) in
  [mk 0 `word_zx (word_or (y:int32) (word 128)):byte`;
   mk 8 `word_zx (word_or (word_subword (y:int32) (7,8):int32) (word 128)):byte`;
   mk 16 `word_zx (word_or (word_subword (y:int32) (14,8):int32) (word 128)):byte`;
   mk 24 `word_zx (z:int32):byte`];;

let SNAPPY_IC_VAL32_SPLIT = prove
 (`!w:int32. val w = val(word_zx (word_ushr w 0):byte) +
                     256 * val(word_zx (word_ushr w 8):byte) +
                     65536 * val(word_zx (word_ushr w 16):byte) +
                     16777216 * val(word_zx (word_ushr w 24):byte)`,
  GEN_TAC THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD_USHR; DIMINDEX_8; DIMINDEX_32] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `w:int32` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_32] THEN
  ABBREV_TAC `v = val(w:int32)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(v DIV 16777216) MOD 256 = v DIV 16777216` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    UNDISCH_TAC `v < 2 EXP 32` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DIV_1] THEN MATCH_MP_TAC SNAPPY_IC_VAL32_BYTES THEN
  FIRST_ASSUM ACCEPT_TAC);;

let SNAPPY_IC_VAL_W4 =
  REWRITE_RULE SNAPPY_IC_W4_BYTES (ISPEC SNAPPY_IC_W4 SNAPPY_IC_VAL32_SPLIT);;

let SNAPPY_IC_MOD_256_128 = prove
 (`!n. n MOD 256 MOD 128 = n MOD 128`,
  REWRITE_TAC[ARITH_RULE `256 = 128 * 2`; MOD_MOD]);;

(* Decide the conditionals in the goal whose conditions are about numbers.   *)
let SNAPPY_IC_DECIDE_CONDS_TAC : tactic =
  let rec go (asl,w) =
    match find_terms (fun t -> is_cond t && snappy_ic_is_num_fact (rand(rator(rator t))) ||
                               (is_cond t && (let c = rand(rator(rator t)) in is_binary "<" c || is_binary "<=" c))) w with
      [] -> ALL_TAC (asl,w)
    | t::_ ->
       let c = rand(rator(rator t)) in
       let th = try EQT_INTRO(TAC_PROOF((asl,c),SNAPPY_IC_ARITH_TAC))
                with Failure _ -> EQF_INTRO(TAC_PROOF((asl,mk_neg c),SNAPPY_IC_ARITH_TAC)) in
       (REWRITE_TAC[th] THEN go) (asl,w) in
  go;;

let SNAPPY_IC_BYTES_SPLIT_CONV =
  let pth = prove
   (`!a k (s:armstate). read (memory :> bytes(a,k + 1)) s =
        val(read (memory :> bytes8 a) s) +
        2 EXP 8 * read (memory :> bytes(word_add a (word 1),k)) s`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[GSYM READ_MEMORY_BYTES_BYTES8; ARITH_RULE `k + 1 = 1 + k`] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
    CONV_TAC NUM_REDUCE_CONV) in
  let rec conv tm =
    match tm with
      Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("memory",_)),
           Comb(Const("bytes",_),Comb(Comb(Const(",",_),a),k)))),s)
        when is_numeral k && dest_small_numeral k >= 1 ->
        let n = dest_small_numeral k in
        if n = 1 then REWR_CONV READ_MEMORY_BYTES_BYTES8 tm else
        let th = SPECL [a; mk_small_numeral(n-1); s] pth in
        let th = CONV_RULE(LAND_CONV(DEPTH_CONV NUM_ADD_CONV)) th in
        let th2 = CONV_RULE(RAND_CONV(RAND_CONV(RAND_CONV conv))) th in
        th2
    | _ -> failwith "SNAPPY_IC_BYTES_SPLIT_CONV" in
  conv;;

let SNAPPY_IC_BYTES4 = prove
 (`!a (s:armstate). read (memory :> bytes(a,4)) s = val(read (memory :> bytes32 a) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SNAPPY_READ_BYTES32; VAL_WORD; DIMINDEX_32] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPECL [`a:int64`; `4`; `read memory (s:armstate)`] READ_BYTES_BOUND) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let SNAPPY_IC_ADDR_NORM = [GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];;

(* The goal read (memory :> bytes(a,L)) s = num_of_bytelist(varint n).       *)
let SNAPPY_IC_VARINT_BYTES_TAC : tactic = fun (asl,w) ->
  let s = rand(lhs w) in
  let b8 = filter (fun th -> match concl th with
      Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),Comb(Comb(Const(":>",_),Const("memory",_)),
           Comb(Const(("bytes8"|"bytes32"),_),_))),s')),_) -> s' = s
    | _ -> false) (map snd asl) in
  (MP_TAC(SPEC `LENGTH(inp:byte list)` SNAPPY_VARINT_ENCODE_CASES) THEN
   ANTS_TAC THENL [SNAPPY_IC_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
   SNAPPY_IC_DECIDE_CONDS_TAC THEN
   REWRITE_TAC[num_of_bytelist; MULT_CLAUSES; ADD_CLAUSES] THEN
   REWRITE_TAC[SNAPPY_IC_BYTES4] THEN
   TRY(CONV_TAC(LAND_CONV SNAPPY_IC_BYTES_SPLIT_CONV)) THEN
   REWRITE_TAC SNAPPY_IC_ADDR_NORM THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
   REWRITE_TAC b8 THEN REWRITE_TAC[SNAPPY_IC_VAL_W4] THEN
   CONV_TAC(SNAPPY_IC_NUM_CONV (map snd asl) (SNAPPY_IC_BYTE_OR128 :: VAL_WORD_SUBWORD :: SNAPPY_IC_MASK_THMS)) THEN
   REWRITE_TAC[SNAPPY_IC_MOD_256_128] THEN
   TRY SNAPPY_IC_ARITH_TAC) (asl,w);;

let SNAPPY_IC_VARINT_LEN_TAC l =
  SUBGOAL_THEN (mk_eq(`LENGTH(snappy_varint_encode(LENGTH(inp:byte list)))`, mk_small_numeral l)) ASSUME_TAC THENL
   [MP_TAC(SPEC `LENGTH(inp:byte list)` SNAPPY_VARINT_ENCODE_CASES) THEN
    ANTS_TAC THENL [SNAPPY_IC_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SNAPPY_IC_ARITH_TAC; ALL_TAC];;
let SNAPPY_IC_LOOP0_TAC n0 n1 l =
  ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC (n0--n1) THEN
  SNAPPY_IC_VARINT_LEN_TAC l THEN
  SUBGOAL_THEN `word_zx(word_zx(word level:int64):int32):int64 = word level` ASSUME_TAC THENL
   [SNAPPY_IC_WORD_EQ_TAC; ALL_TAC] THEN
  BSTEP_FINAL_TAC THEN SNAPPY_IC_EV_FINAL_TAC THEN
  DISJ2_TAC THEN EXISTS_TAC `LENGTH(inp:byte list)` THEN
  EXISTS_TAC `0` THEN
  REWRITE_TAC[MULT_CLAUSES; SUB_0] THEN CONJ_TAC THENL [SNAPPY_IC_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[snappy_ic_inv; snappy_ic_frame; snappy_ic_len; snappy_ic_out;
              MULT_CLAUSES; SUB_LIST_CLAUSES; SNAPPY_BLOCKS_NIL; LENGTH; ADD_CLAUSES;
              APPEND_NIL; SUB_0; WORD_ADD_0] THEN
  REPEAT CONJ_TAC THEN
  TRY(SNAPPY_IC_CONJ_TAC [ASSUME (mk_eq(`LENGTH(snappy_varint_encode(LENGTH(inp:byte list)))`, mk_small_numeral l));
               ASSUME `word_zx(word_zx(word level:int64):int32):int64 = word level`]);;

(* The memcpy of the header writes bytes(out,L) for the length L of the      *)
(* varint; the frame of the call is weakened to the clause of the output     *)
(* region, so that bstep absorbs it into the goal's frame.                   *)

let SNAPPY_IC_MAYCHANGE_BYTES_SUBSUMED = prove
 (`!(m:(S,N word->byte)component) a k b l.
        memrange(a,k) SUBSET memrange(b,l)
        ==> MAYCHANGE [m :> bytes(a,k)] subsumed MAYCHANGE [m :> bytes(b,l)]`,
  REWRITE_TAC[GSYM CONTAINED_MEMRANGE; contained; MAYCHANGE_SING] THEN
  SIMP_TAC[SUBSUMED_ASSIGNS_SUBCOMPONENTS; SUBSUMED_ASSIGNS_BYTES]);;

let snappy_ic_frame_weaken asl ((a:term),(l:term)) eth =
  let rec go fr =
    match fr with
      Comb(Comb(Const(",,",_) as op,x),y) ->
        let x',tx = go x and y',ty = go y in
        mk_comb(mk_comb(op,x'),y'),MATCH_MP SUBSUMED_SEQ (CONJ tx ty)
    | Comb(Const("MAYCHANGE",_),
           Comb(Comb(Const("CONS",_),
                     Comb(Comb(Const(":>",_),Const("memory",_)),
                          Comb(Const("bytes",_),Comb(Comb(Const(",",_),a'),k)))),
                Const("NIL",_)))
        when compare a' a = 0 && compare k l <> 0 ->
        let le = TAC_PROOF((asl,mk_binary "<=" (k,l)), SNAPPY_IC_ARITH_TAC) in
        let sub = MP (ISPECL [a;k;l] MEMRANGE_PREFIX_SUBSET) le in
        let th = MP (ISPECL [`memory:(armstate,int64->byte)component`;a;k;a;l]
                       SNAPPY_IC_MAYCHANGE_BYTES_SUBSUMED) sub in
        rand(concl th),th
    | _ -> fr,ISPEC fr SUBSUMED_REFL in
  let fr = rand(concl eth) in
  let fr',fth = go fr in
  if compare fr fr' = 0 then eth else
  MATCH_MP ENSURES_FRAME_SUBSUMED (CONJ fth eth);;

let SNAPPY_IC_MEMCPY_TAC (th:thm) sname =
  let safe = fst(dest_const(fst(strip_comb(concl th)))) =
             "memcpy_correct_safe_contract" in
  ARM_BSTEP_PLT_STUB_TAC SNAPPY_IC_EXEC THEN
  ARM_CONTRACT_INSTANCE_TAC
   (REWRITE_RULE[memcpy_contract; memcpy_correct_safe_contract] th)
   ((if safe then [`read events s`] else []) @
    [`read X0 s`; `read X1 s`; `read X2 s`;
    `num_of_bytelist(snappy_varint_encode(LENGTH(inp:byte list)))`; `read X30 s`])
   (fun cth -> W(fun (asl,w) ->
      ARM_BSTEP_CALL_TAC SNAPPY_IC_EXEC
        (snappy_ic_frame_weaken asl
           (`out:int64`,`snappy_max_compressed_length (LENGTH(inp:byte list))`) cth)
        sname));;

let SNAPPY_IC_NE_TAC =
  MP_TAC(SPEC `LENGTH(inp:byte list)` SNAPPY_MAX_COMPRESSED_LENGTH_GE_32) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(out = word_add (word_sub stackpointer (word 160)) (word 144):int64)` ASSUME_TAC THENL
   [MATCH_MP_TAC SNAPPY_IC_NE_OF_NONOVERLAP THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_neg(concl th) && is_eq(rand(concl th)) && lhs(rand(concl th)) = `out:int64`
     then SNAPPY_IC_REWRITE_FACTS_TAC [`PC`] [VAL_EQ_0; WORD_SUB_EQ_0; th] else NO_TAC);;

(* From join5 (PC there, state s<b>) with the L bytes of the varint stored *)
(* at sp + 144: Append, memcpy of the header, then join2 and loop1.        *)
let SNAPPY_IC_HEADER_TAC b l =
  let sn k = "s" ^ string_of_int k in
  let bm = b + 15 in
  ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC ((b+1)--bm) THEN
  SNAPPY_IC_NE_TAC THEN
  ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC ((bm+1)--(bm+1)) THEN
  SUBGOAL_THEN (subst [mk_small_numeral l,`l:num`; mk_var(sn (bm+1),`:armstate`),`s:armstate`]
    `read (memory :> bytes(word_add (word_sub stackpointer (word 160)) (word 144),l)) s =
     num_of_bytelist(snappy_varint_encode(LENGTH(inp:byte list)))`) ASSUME_TAC THENL
   [SNAPPY_IC_VARINT_BYTES_TAC; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if (try mem (fst(dest_const(fst(strip_comb(concl th))))) ["memcpy_contract"; "memcpy_correct_safe_contract"] with Failure _ -> false) then
   SNAPPY_IC_MEMCPY_TAC th (sn (bm+6))
   else NO_TAC) THEN
  ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC ((bm+7)--(bm+13)) THEN
  SNAPPY_IC_FACT_UPDATE_TAC `SP` `word_sub stackpointer (word 160):int64` (CONV_TAC WORD_RULE) THEN
  SNAPPY_IC_LOOP0_TAC (bm+14) (bm+18) l;;

let SNAPPY_IC_COMPRESS_NIL = prove
 (`!level. snappy_compress level [] = [word 0]`,
  REWRITE_TAC[snappy_compress; LENGTH; SNAPPY_BLOCKS_NIL; APPEND_NIL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[SNAPPY_VARINT_ENCODE_1; ARITH]);;


let SNAPPY_IC_ITER_TAC =
((REWRITE_TAC[ALLPAIRS; ALL; PAIRWISE] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RAND_CONV o ABS_CONV o TOP_DEPTH_CONV)
    [snappy_ic_inv_safe; snappy_ic_ev; snappy_ic_inv; snappy_ic_frame] THEN
  ENSURES_INIT_TAC "s0" THEN SNAPPY_EV_CHOOSE_TAC THEN
  ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
    ~select:(elf_slots_at [layout "got_memcpy";
       layout "vtable_ByteArraySource" + 16; layout "vtable_ByteArraySource" + 24;
       layout "vtable_ByteArraySource" + 32;
       layout "vtable_UncheckedByteArraySink" + 16;
       layout "vtable_UncheckedByteArraySink" + 24])) THEN
(ABBREV_TAC `m = MIN 65536 (LENGTH(inp:byte list) - 65536 * k)` THEN
  SUBGOAL_THEN `0 < LENGTH(inp:byte list) - 65536 * k /\ LENGTH inp - 65536 * k < 2 EXP 32 /\
    m <= 65536 /\ m <= LENGTH inp - 65536 * k /\ 0 < m /\ 65536 * k + m <= LENGTH inp` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN SNAPPY_IC_ARITH_TAC; ALL_TAC]) THEN
(SUBGOAL_THEN `snappy_ic_len level (inp:byte list) k + (snappy_max_compressed_length m - 5) <=
                snappy_max_compressed_length (LENGTH inp)` ASSUME_TAC THENL
   [REWRITE_TAC[snappy_ic_len; GSYM ADD_ASSOC] THEN
    REWRITE_TAC[SYM(ASSUME `MIN 65536 (LENGTH(inp:byte list) - 65536 * k) = m`)] THEN
    MATCH_MP_TAC SNAPPY_BLOCKS_REGION5 THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; SNAPPY_IC_ARITH_TAC;
      MATCH_MP_TAC LENGTH_SNAPPY_VARINT_ENCODE THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC SNAPPY_BLOCKS_PREFIX_LENGTH THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SNAPPY_IC_ARITH_TAC]];
    ALL_TAC]) THEN
(ARM_BSTEP_TAC ~rewrites:SNAPPY_IC_VT_REWRITES SNAPPY_IC_EXEC (1--16)) THEN
(SNAPPY_IC_FACT_UPDATE_TAC `X20` `word m:int64` (REWRITE_TAC[SYM(ASSUME `MIN 65536 (LENGTH(inp:byte list) - 65536 * k) = m`)] THEN SNAPPY_IC_WORD_EQ_TAC)) THEN
(SNAPPY_IC_FACT_UPDATE_TAC `X28` `word m:int64` (REWRITE_TAC[SYM(ASSUME `MIN 65536 (LENGTH(inp:byte list) - 65536 * k) = m`)] THEN SNAPPY_IC_WORD_EQ_TAC)) THEN
(SNAPPY_IC_PC_COND_TAC [ASSUME `MIN 65536 (LENGTH(inp:byte list) - 65536 * k) = m`]) THEN
(ARM_BSTEP_TAC ~rewrites:SNAPPY_IC_VT_REWRITES SNAPPY_IC_EXEC (17--21)) THEN
(SUBGOAL_THEN `2 * snappy_table_size m <= snappy_working_memory_size nw /\
                val(word m:int64) MOD 2 EXP 32 = m` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[snappy_working_memory_size] THEN
      MATCH_MP_TAC(ARITH_RULE `a <= b ==> 2 * a <= 2 * b + c + d`) THEN
      MATCH_MP_TAC SNAPPY_TABLE_SIZE_MONO THEN
      UNDISCH_TAC `snappy_fragment_size (LENGTH(inp:byte list)) <= snappy_fragment_size nw` THEN
      REWRITE_TAC[snappy_fragment_size; SYM(ASSUME `MIN 65536 (LENGTH(inp:byte list) - 65536 * k) = m`)] THEN ARITH_TAC;
      REWRITE_TAC[VAL_WORD; DIMINDEX_64; SYM(ASSUME `MIN 65536 (LENGTH(inp:byte list) - 65536 * k) = m`)] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      SIMP_TAC[MOD_LT; ARITH_RULE `MIN 65536 x < 18446744073709551616 /\ MIN 65536 x < 4294967296`]];
    ALL_TAC]) THEN
(SNAPPY_IC_MP_SPEC_TAC SNAPPY_WORKING_MEMORY_GET_HASH_TABLE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   SNAPPY_WORKING_MEMORY_GET_HASH_TABLE_GCC12_O2_IMAGE_SUBROUTINE_SAFE [`wm:int64`; `word m:int64`; `word_add (word_sub stackpointer (word 160)) (word 140):int64`;
   `mem:int64`; `pc:num`; `rw:num`; `word_sub stackpointer (word 160):int64`; `word (pc + 17432):int64`;
   `so:int64`; `word m:int64`; `word(LENGTH(inp:byte list) - 65536 * k):int64`; `read X29 s21`;
   `ea:int64`; `el:num`; `ev:num`] THEN
  REWRITE_TAC[ASSUME `val(word m:int64) MOD 2 EXP 32 = m`;
    WORD_RULE `word_sub (word_sub sp (word 160)) (word 48):int64 = word_sub sp (word 208)`;
    C_ARGUMENTS; C_RETURN; ALLPAIRS; ALL]) THEN
(ANTS_TAC THENL [SNAPPY_IC_HYPS_TAC; ALL_TAC]) THEN
(DISCH_THEN(fun th -> ARM_BSTEP_CALL_TAC SNAPPY_IC_EXEC th "s22")) THEN
(ARM_BSTEP_TAC ~rewrites:SNAPPY_IC_VT_REWRITES SNAPPY_IC_EXEC (22--24)) THEN
(SNAPPY_IC_MP_SPEC_TAC SNAPPY_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
    SNAPPY_MAX_COMPRESSED_LENGTH_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    [`word m:int64`; `pc:num`; `word (pc + InternalCompress_after_MaxCompressedLength):int64`] THEN
  ANTS_TAC THENL [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; CONV_TAC NUM_REDUCE_CONV THEN SNAPPY_IC_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN] THEN
  DISCH_THEN(fun th -> ARM_BSTEP_CALL_TAC SNAPPY_IC_EXEC th "s25")) THEN
(ARM_BSTEP_TAC ~rewrites:SNAPPY_IC_VT_REWRITES SNAPPY_IC_EXEC (26--36))) THEN
  (ASM_CASES_TAC `level = 1` THENL [ALL_TAC; SUBGOAL_THEN `level = 2` ASSUME_TAC THENL [SNAPPY_IC_ARITH_TAC; ALL_TAC]] THEN
  SNAPPY_IC_PC_COND_TAC []) THENL
   [((ARM_BSTEP_TAC ~rewrites:SNAPPY_IC_VT_REWRITES SNAPPY_IC_EXEC (37--43)) THEN
(SUBGOAL_THEN `snappy_table_size m < 2 EXP 32` ASSUME_TAC THENL
   [MP_TAC(SPEC `m:num` SNAPPY_TABLE_SIZE_BOUNDS) THEN ARITH_TAC; ALL_TAC] THEN
  SNAPPY_IC_FACT_UPDATE_TAC `X4` `word(snappy_table_size m):int64` SNAPPY_IC_WORD_EQ_TAC) THEN
(SUBGOAL_THEN `LENGTH(SUB_LIST(65536 * k,m) (inp:byte list)) = m` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN SNAPPY_IC_ARITH_TAC; ALL_TAC]) THEN
(SUBGOAL_THEN `read (memory :> bytelist(word_add src (word(65536 * k)),m)) s43 =
                SUB_LIST(65536 * k,m) (inp:byte list)` ASSUME_TAC THENL
   [REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SNAPPY_READ_BYTES_SUB THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SNAPPY_IC_ARITH_TAC];
    ALL_TAC]) THEN
(SNAPPY_IC_MP_SPEC_TAC SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   SNAPPY_COMPRESS_FRAGMENT_GCC12_O2_IMAGE_SUBROUTINE_SAFE
   [`word_add src (word(65536 * k)):int64`; `SUB_LIST(65536 * k,m) (inp:byte list)`;
   `word_add out (word(snappy_ic_len level (inp:byte list) k)):int64`; `mem:int64`; `pc:num`;
   `imp:string->int64`; `ea:int64`; `el:num`; `ev:num`; `rw:num`;
   `word_sub stackpointer (word 160):int64`;
   `word (pc + InternalCompress_after_CompressFragment):int64`] THEN
  REWRITE_TAC[ASSUME `LENGTH(SUB_LIST(65536 * k,m) (inp:byte list)) = m`;
    WORD_RULE `word_sub (word_sub sp (word 160)) (word 32):int64 =
               word_add (word_sub sp (word 208)) (word 16)`;
    C_ARGUMENTS; C_RETURN; ALLPAIRS; ALL; PAIRWISE]) THEN
(ANTS_TAC THENL [SNAPPY_IC_HYPS_TAC; DISCH_THEN(fun th -> ARM_BSTEP_CALL_TAC SNAPPY_IC_EXEC th "s44")]) THEN
(SUBGOAL_THEN `LENGTH(snappy_compress_fragment 1 (SUB_LIST(65536 * k,m) (inp:byte list))) <=
                snappy_max_compressed_length m - 5` ASSUME_TAC THENL
   [MP_TAC(SPECL [`1`; `SUB_LIST(65536 * k,m) (inp:byte list)`] SNAPPY_FRAGMENT_LENGTH5) THEN
    REWRITE_TAC[ASSUME `LENGTH(SUB_LIST(65536 * k,m) (inp:byte list)) = m`] THEN
    DISCH_THEN MATCH_MP_TAC THEN SNAPPY_IC_ARITH_TAC;
    ALL_TAC]) THEN
(ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC (45--77)) THEN
(ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC (78--79)) THEN
(SUBGOAL_THEN `word_sub (word(LENGTH(inp:byte list) - 65536 * k)) (word m):int64 = word(LENGTH inp - 65536 * k - m)` ASSUME_TAC THENL
   [SNAPPY_IC_WORD_EQ_TAC; ALL_TAC]) THEN
(FIRST_ASSUM(fun th -> if is_eq(concl th) && (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_sub" with Failure _ -> false) then
     SNAPPY_IC_REWRITE_FACTS_TAC [`PC`; `X21`; `memory :> bytes64 (word_add so (word 16))`] [th] else NO_TAC)) THEN
(SNAPPY_IC_FACT_UPDATE_TAC `SP` `word_sub stackpointer (word 160):int64` (CONV_TAC WORD_RULE))) THEN
    (SNAPPY_IC_PC_CASES_TAC []) THENL
     [(ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC (80--87) THEN
  ABBREV_TAC `fr = snappy_compress_fragment 1 (SUB_LIST(65536 * k,m) (inp:byte list))` THEN
  SUBGOAL_THEN `APPEND (snappy_ic_out level inp k) fr = snappy_compress level (inp:byte list)` ASSUME_TAC THENL
   [EXPAND_TAC "fr" THEN
    REWRITE_TAC[SYM(ASSUME `MIN 65536 (LENGTH(inp:byte list) - 65536 * k) = m`)] THEN
    REWRITE_TAC[ASSUME `level = 1`] THEN MATCH_MP_TAC SNAPPY_IC_COMPRESS_LAST THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN SNAPPY_IC_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(snappy_compress level (inp:byte list)) = snappy_ic_len level inp k + LENGTH(fr:byte list)` ASSUME_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `APPEND (snappy_ic_out level inp k) fr = snappy_compress level (inp:byte list)`);
                LENGTH_APPEND; SNAPPY_IC_OUT_LEN]; ALL_TAC] THEN
  BSTEP_FINAL_TAC THEN SNAPPY_IC_EV_FINAL_TAC THEN DISJ1_TAC THEN REWRITE_TAC[snappy_ic_post] THEN
  REWRITE_TAC[ASSUME `LENGTH(snappy_compress level (inp:byte list)) = snappy_ic_len level inp k + LENGTH(fr:byte list)`] THEN
  REWRITE_TAC[READ_BYTELIST_EQ_BYTES; LENGTH_APPEND; SNAPPY_IC_OUT_LEN;
     SYM(ASSUME `APPEND (snappy_ic_out level inp k) fr = snappy_compress level (inp:byte list)`)] THEN
  REPEAT CONJ_TAC THEN SNAPPY_IC_CONJ_TAC []);
      (SUBGOAL_THEN `m = 65536` ASSUME_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `MIN 65536 (LENGTH(inp:byte list) - 65536 * k) = m`)] THEN SNAPPY_IC_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `fr = snappy_compress_fragment 1 (SUB_LIST(65536 * k,m) (inp:byte list))` THEN
  SUBGOAL_THEN `APPEND (snappy_ic_out level inp k) fr = snappy_ic_out level (inp:byte list) (k + 1)` ASSUME_TAC THENL
   [EXPAND_TAC "fr" THEN
    REWRITE_TAC[SYM(ASSUME `MIN 65536 (LENGTH(inp:byte list) - 65536 * k) = m`)] THEN
    REWRITE_TAC[ASSUME `level = 1`] THEN MATCH_MP_TAC SNAPPY_IC_OUT_NEXT THEN
    CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN SNAPPY_IC_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `snappy_ic_len level (inp:byte list) (k + 1) = snappy_ic_len level inp k + LENGTH(fr:byte list)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SNAPPY_IC_OUT_LEN; SYM(ASSUME `APPEND (snappy_ic_out level inp k) fr = snappy_ic_out level (inp:byte list) (k + 1)`);
                LENGTH_APPEND]; ALL_TAC] THEN
  BSTEP_FINAL_TAC THEN SNAPPY_IC_EV_FINAL_TAC THEN
  DISJ2_TAC THEN EXISTS_TAC `LENGTH(inp:byte list) - 65536 * (k + 1)` THEN
  CONJ_TAC THENL [SNAPPY_IC_ARITH_TAC; EXISTS_TAC `k + 1`] THEN
  CONJ_TAC THENL [SNAPPY_IC_ARITH_TAC; REWRITE_TAC[]] THEN
  REWRITE_TAC[snappy_ic_inv; snappy_ic_frame] THEN
  REPEAT CONJ_TAC THEN
  SNAPPY_IC_CONJ_TAC [ASSUME `snappy_ic_len level (inp:byte list) (k + 1) = snappy_ic_len level inp k + LENGTH(fr:byte list)`;
               SYM(ASSUME `APPEND (snappy_ic_out level inp k) fr = snappy_ic_out level (inp:byte list) (k + 1)`);
               ASSUME `m = 65536`])];
    ((ARM_BSTEP_TAC ~rewrites:SNAPPY_IC_VT_REWRITES SNAPPY_IC_EXEC (37--39)) THEN
(ARM_BSTEP_TAC ~rewrites:SNAPPY_IC_VT_REWRITES SNAPPY_IC_EXEC (40--49)) THEN
(SNAPPY_IC_REWRITE_FACTS_TAC [`X4`; `X5`; `X6`] [SNAPPY_IC_TABLE_SIZE_ISHR]) THEN
(MP_TAC(SPECL [`mem:int64`; `2 * (snappy_table_size m DIV 2)`; `2 * (snappy_table_size m DIV 2)`; `s49:armstate`] SNAPPY_IC_READ_BYTES_ZERO_SPLIT) THEN
  REWRITE_TAC[SNAPPY_IC_TABLE_SIZE_HALF] THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `2 * (snappy_table_size m DIV 2) + 2 * (snappy_table_size m DIV 2) <= snappy_working_memory_size nw` ASSUME_TAC THENL
   [REWRITE_TAC[SNAPPY_IC_TABLE_SIZE_HALF] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `snappy_table_size m DIV 2 < 2 EXP 32` ASSUME_TAC THENL
   [MP_TAC(SPEC `m:num` SNAPPY_TABLE_SIZE_BOUNDS) THEN ARITH_TAC; ALL_TAC]) THEN
(SUBGOAL_THEN `LENGTH(SUB_LIST(65536 * k,m) (inp:byte list)) = m` ASSUME_TAC THENL
   [REWRITE_TAC[LENGTH_SUB_LIST] THEN SNAPPY_IC_ARITH_TAC; ALL_TAC]) THEN
(SUBGOAL_THEN `read (memory :> bytelist(word_add src (word(65536 * k)),m)) s49 =
                SUB_LIST(65536 * k,m) (inp:byte list)` ASSUME_TAC THENL
   [REWRITE_TAC[READ_BYTELIST_EQ_BYTES] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SNAPPY_READ_BYTES_SUB THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SNAPPY_IC_ARITH_TAC];
    ALL_TAC]) THEN
(SNAPPY_IC_MP_SPEC_TAC SNAPPY_COMPRESS_FRAGMENT_DOUBLE_HASH_GCC12_O2_IMAGE_SUBROUTINE_CORRECT
   SNAPPY_COMPRESS_FRAGMENT_DOUBLE_HASH_GCC12_O2_IMAGE_SUBROUTINE_SAFE
   [`word_add src (word(65536 * k)):int64`; `SUB_LIST(65536 * k,m) (inp:byte list)`;
   `word_add out (word(snappy_ic_len level (inp:byte list) k)):int64`; `mem:int64`;
   `word_add mem (word (2 * (snappy_table_size m DIV 2))):int64`; `pc:num`;
   `imp:string->int64`; `ea:int64`; `el:num`; `ev:num`; `rw:num`;
   `word_sub stackpointer (word 160):int64`;
   `word (pc + InternalCompress_after_CompressFragmentDoubleHash):int64`] THEN
  REWRITE_TAC[ASSUME `LENGTH(SUB_LIST(65536 * k,m) (inp:byte list)) = m`;
    WORD_RULE `word_sub (word_sub sp (word 160)) (word 48):int64 = word_sub sp (word 208)`;
    C_ARGUMENTS; C_RETURN; ALLPAIRS; ALL; PAIRWISE]) THEN
(ANTS_TAC THENL [SNAPPY_IC_HYPS_TAC; DISCH_THEN(fun th -> ARM_BSTEP_CALL_TAC SNAPPY_IC_EXEC th "s50")]) THEN
(SUBGOAL_THEN `LENGTH(snappy_compress_fragment 2 (SUB_LIST(65536 * k,m) (inp:byte list))) <=
                snappy_max_compressed_length m - 5` ASSUME_TAC THENL
   [MP_TAC(SPECL [`2`; `SUB_LIST(65536 * k,m) (inp:byte list)`] SNAPPY_FRAGMENT_LENGTH5) THEN
    REWRITE_TAC[ASSUME `LENGTH(SUB_LIST(65536 * k,m) (inp:byte list)) = m`] THEN
    DISCH_THEN MATCH_MP_TAC THEN SNAPPY_IC_ARITH_TAC;
    ALL_TAC]) THEN
(ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC (51--83)) THEN
(ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC (84--85)) THEN
(SUBGOAL_THEN `word_sub (word(LENGTH(inp:byte list) - 65536 * k)) (word m):int64 = word(LENGTH inp - 65536 * k - m)` ASSUME_TAC THENL
   [SNAPPY_IC_WORD_EQ_TAC; ALL_TAC]) THEN
(FIRST_ASSUM(fun th -> if is_eq(concl th) && (try fst(dest_const(fst(strip_comb(lhs(concl th))))) = "word_sub" with Failure _ -> false) then
     SNAPPY_IC_REWRITE_FACTS_TAC [`PC`; `X21`; `memory :> bytes64 (word_add so (word 16))`] [th] else NO_TAC)) THEN
(SNAPPY_IC_FACT_UPDATE_TAC `SP` `word_sub stackpointer (word 160):int64` (CONV_TAC WORD_RULE))) THEN
    (SNAPPY_IC_PC_CASES_TAC []) THENL
     [(ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC (86--93) THEN
  ABBREV_TAC `fr = snappy_compress_fragment 2 (SUB_LIST(65536 * k,m) (inp:byte list))` THEN
  SUBGOAL_THEN `APPEND (snappy_ic_out level inp k) fr = snappy_compress level (inp:byte list)` ASSUME_TAC THENL
   [EXPAND_TAC "fr" THEN
    REWRITE_TAC[SYM(ASSUME `MIN 65536 (LENGTH(inp:byte list) - 65536 * k) = m`)] THEN
    REWRITE_TAC[ASSUME `level = 2`] THEN MATCH_MP_TAC SNAPPY_IC_COMPRESS_LAST THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN SNAPPY_IC_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `LENGTH(snappy_compress level (inp:byte list)) = snappy_ic_len level inp k + LENGTH(fr:byte list)` ASSUME_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `APPEND (snappy_ic_out level inp k) fr = snappy_compress level (inp:byte list)`);
                LENGTH_APPEND; SNAPPY_IC_OUT_LEN]; ALL_TAC] THEN
  BSTEP_FINAL_TAC THEN SNAPPY_IC_EV_FINAL_TAC THEN DISJ1_TAC THEN REWRITE_TAC[snappy_ic_post] THEN
  REWRITE_TAC[ASSUME `LENGTH(snappy_compress level (inp:byte list)) = snappy_ic_len level inp k + LENGTH(fr:byte list)`] THEN
  REWRITE_TAC[READ_BYTELIST_EQ_BYTES; LENGTH_APPEND; SNAPPY_IC_OUT_LEN;
     SYM(ASSUME `APPEND (snappy_ic_out level inp k) fr = snappy_compress level (inp:byte list)`)] THEN
  REPEAT CONJ_TAC THEN SNAPPY_IC_CONJ_TAC []);
      (SUBGOAL_THEN `m = 65536` ASSUME_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `MIN 65536 (LENGTH(inp:byte list) - 65536 * k) = m`)] THEN SNAPPY_IC_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `fr = snappy_compress_fragment 2 (SUB_LIST(65536 * k,m) (inp:byte list))` THEN
  SUBGOAL_THEN `APPEND (snappy_ic_out level inp k) fr = snappy_ic_out level (inp:byte list) (k + 1)` ASSUME_TAC THENL
   [EXPAND_TAC "fr" THEN
    REWRITE_TAC[SYM(ASSUME `MIN 65536 (LENGTH(inp:byte list) - 65536 * k) = m`)] THEN
    REWRITE_TAC[ASSUME `level = 2`] THEN MATCH_MP_TAC SNAPPY_IC_OUT_NEXT THEN
    CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN SNAPPY_IC_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `snappy_ic_len level (inp:byte list) (k + 1) = snappy_ic_len level inp k + LENGTH(fr:byte list)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SNAPPY_IC_OUT_LEN; SYM(ASSUME `APPEND (snappy_ic_out level inp k) fr = snappy_ic_out level (inp:byte list) (k + 1)`);
                LENGTH_APPEND]; ALL_TAC] THEN
  BSTEP_FINAL_TAC THEN SNAPPY_IC_EV_FINAL_TAC THEN
  DISJ2_TAC THEN EXISTS_TAC `LENGTH(inp:byte list) - 65536 * (k + 1)` THEN
  CONJ_TAC THENL [SNAPPY_IC_ARITH_TAC; EXISTS_TAC `k + 1`] THEN
  CONJ_TAC THENL [SNAPPY_IC_ARITH_TAC; REWRITE_TAC[]] THEN
  REWRITE_TAC[snappy_ic_inv; snappy_ic_frame] THEN
  REPEAT CONJ_TAC THEN
  SNAPPY_IC_CONJ_TAC [ASSUME `snappy_ic_len level (inp:byte list) (k + 1) = snappy_ic_len level inp k + LENGTH(fr:byte list)`;
               SYM(ASSUME `APPEND (snappy_ic_out level inp k) fr = snappy_ic_out level (inp:byte list) (k + 1)`);
               ASSUME `m = 65536`])]];;

let SNAPPY_IC_ITER = prove
 (SNAPPY_IC_ITER_STMT,
  SNAPPY_IC_ITER_TAC);;

let SNAPPY_IC_ITER_SAFE = prove
 (SNAPPY_IC_ITER_SAFE_STMT,
  SNAPPY_IC_ITER_TAC);;

let SNAPPY_IC_ENTRY_TAC =
(REWRITE_TAC[ALLPAIRS; ALL; PAIRWISE] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RAND_CONV o ABS_CONV o TOP_DEPTH_CONV)
    [snappy_ic_pre; snappy_working_memory] THEN
  ENSURES_INIT_TAC "s0" THEN
  ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
    ~select:(elf_slots_at [layout "got_memcpy";
       layout "vtable_ByteArraySource" + 16; layout "vtable_ByteArraySource" + 24;
       layout "vtable_ByteArraySource" + 32;
       layout "vtable_UncheckedByteArraySink" + 16;
       layout "vtable_UncheckedByteArraySink" + 24]) THEN
  SUBGOAL_THEN `LENGTH(snappy_varint_encode(LENGTH(inp:byte list))) <= 5 /\
                LENGTH(snappy_varint_encode(LENGTH inp)) <= snappy_max_compressed_length (LENGTH inp)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `LENGTH(inp:byte list)` LENGTH_SNAPPY_VARINT_ENCODE) THEN
    MP_TAC(SPEC `LENGTH(inp:byte list)` SNAPPY_MAX_COMPRESSED_LENGTH_GE_32) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC]) THEN
  (ARM_BSTEP_TAC ~rewrites:SNAPPY_IC_VT_REWRITES SNAPPY_IC_EXEC (1--20) THEN SNAPPY_IC_PC_COND_TAC [] THEN
  ARM_BSTEP_TAC ~rewrites:SNAPPY_IC_VT_REWRITES SNAPPY_IC_EXEC (21--23)) THEN
  (SNAPPY_IC_PC_CASES_TAC []) THENL
  [(ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC (24--30) THEN SNAPPY_IC_PC_CASES_TAC []) THENL
   [(ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC (31--34) THEN SNAPPY_IC_HEADER_TAC 34 2);
    (ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC (31--35) THEN SNAPPY_IC_PC_CASES_TAC []) THENL
     [(ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC (36--40) THEN SNAPPY_IC_PC_CASES_TAC []) THENL [(ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC (41--49) THEN SNAPPY_IC_HEADER_TAC 49 5); (ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC (41--48) THEN SNAPPY_IC_HEADER_TAC 48 4)];
      (ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC (36--39) THEN SNAPPY_IC_HEADER_TAC 39 3)]];
   (ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC (24--40) THEN SNAPPY_IC_NE_TAC THEN
  ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC (41--41)) THEN (SUBGOAL_THEN `read (memory :> bytes(word_add (word_sub stackpointer (word 160)) (word 144),1)) s41 =
     num_of_bytelist(snappy_varint_encode(LENGTH(inp:byte list)))` ASSUME_TAC THENL
   [SNAPPY_IC_VARINT_BYTES_TAC; ALL_TAC]) THEN (FIRST_ASSUM(fun th -> if (try mem (fst(dest_const(fst(strip_comb(concl th))))) ["memcpy_contract"; "memcpy_correct_safe_contract"] with Failure _ -> false) then
   SNAPPY_IC_MEMCPY_TAC th "s46"
   else NO_TAC)) THEN (ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC (47--53)) THEN
  (SNAPPY_IC_FACT_UPDATE_TAC `SP` `word_sub stackpointer (word 160):int64` (CONV_TAC WORD_RULE) THEN
  SNAPPY_IC_PC_CASES_TAC []) THENL
   [(ARM_BSTEP_TAC ~rewrites:(SNAPPY_IC_VT_REWRITES @ SNAPPY_IC_SP_REWRITES) SNAPPY_IC_EXEC (54--60) THEN
  SUBGOAL_THEN `inp:byte list = []` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN SNAPPY_IC_ARITH_TAC; ALL_TAC] THEN
  BSTEP_FINAL_TAC THEN SNAPPY_IC_EV_FINAL_TAC THEN DISJ1_TAC THEN REWRITE_TAC[snappy_ic_post]) THEN (REWRITE_TAC[SNAPPY_IC_COMPRESS_NIL; LENGTH; READ_BYTELIST_EQ_BYTES] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THEN SNAPPY_IC_CONJ_TAC []);
    (SNAPPY_IC_LOOP0_TAC 54 59 1)]];;

let SNAPPY_IC_ENTRY = prove
 (SNAPPY_IC_ENTRY_STMT,
  SNAPPY_IC_ENTRY_TAC);;

let SNAPPY_IC_ENTRY_SAFE = prove
 (SNAPPY_IC_ENTRY_SAFE_STMT,
  SNAPPY_IC_ENTRY_TAC);;

let SNAPPY_IC_MAIN_STMT = parse_term
 ("!" ^ snappy_ic_vars_str ^ " owns.
    " ^ snappy_ic_hyps_str ^ "
    ==> ensures arm
         (\\s. snappy_ic_pre pc level inp src out so sk wm mem nw owns rw ea el ev
                 stackpointer x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 ra s)
         (\\s. snappy_ic_post " ^ snappy_ic_postargs_str ^ " s)
         (" ^ snappy_ic_frame_str ^ ")");;

let SNAPPY_IC_ENSURES_EXISTS = prove
 (`!(step:A->A->bool) (P:B->A->bool) Q C.
        (!k. ensures step (P k) Q C) ==> ensures step (\s. ?k. P k s) Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

let SNAPPY_IC_MAIN = prove
 (SNAPPY_IC_MAIN_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC SNAPPY_IC_ENSURES_LOOP THEN
  EXISTS_TAC (parse_term ("\\m s. ?k'. 65536 * k' < LENGTH(inp:byte list) /\\
      m = LENGTH inp - 65536 * k' /\\ snappy_ic_inv " ^ snappy_ic_invargs_str ^ " k' s")) THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    MP_TAC(SPEC_ALL SNAPPY_IC_ENTRY) THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC SNAPPY_IC_ENSURES_EXISTS THEN X_GEN_TAC `k:num` THEN
    ASM_CASES_TAC `65536 * k < LENGTH(inp:byte list)` THEN
    ASM_REWRITE_TAC[ENSURES_TRIVIAL] THEN
    ASM_CASES_TAC `n = LENGTH(inp:byte list) - 65536 * k` THEN
    ASM_REWRITE_TAC[ENSURES_TRIVIAL] THEN
    MP_TAC(SPEC_ALL SNAPPY_IC_ITER) THEN ASM_REWRITE_TAC[]]);;

let SNAPPY_INTERNAL_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (SNAPPY_INTERNAL_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  MAP_EVERY X_GEN_TAC [`level:num`; `inp:byte list`; `src:int64`; `out:int64`;
    `so:int64`; `sk:int64`; `wm:int64`; `mem:int64`; `nw:num`; `owns:bool`;
    `pc:num`; `imp:string->int64`; `ea:int64`; `el:num`; `ev:num`; `rw:num`;
    `stackpointer:int64`; `returnaddress:int64`] THEN
  DISCH_TAC THEN
  MAP_EVERY (fun (n,c) -> ENSURES_PRESERVED_TAC n c)
   [("x19_init",`X19`); ("x20_init",`X20`); ("x21_init",`X21`);
    ("x22_init",`X22`); ("x23_init",`X23`); ("x24_init",`X24`);
    ("x25_init",`X25`); ("x26_init",`X26`); ("x27_init",`X27`);
    ("x28_init",`X28`); ("x29_init",`X29`)] THEN
  MATCH_MP_TAC(ISPECL [`SP`; `stackpointer:int64`]
    ENSURES_MAYCHANGE_EXISTING_PRESERVED) THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV; ENSURES_PRESERVED_KEEP_TAC;
    SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`pc:num`; `level:num`; `inp:byte list`; `src:int64`; `out:int64`;
    `so:int64`; `sk:int64`; `wm:int64`; `mem:int64`; `nw:num`;
    `imp:string->int64`; `ea:int64`; `el:num`; `ev:num`; `rw:num`;
    `stackpointer:int64`; `x19_init:int64`; `x20_init:int64`; `x21_init:int64`;
    `x22_init:int64`; `x23_init:int64`; `x24_init:int64`; `x25_init:int64`;
    `x26_init:int64`; `x27_init:int64`; `x28_init:int64`; `x29_init:int64`;
    `returnaddress:int64`; `owns:bool`] SNAPPY_IC_MAIN) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; GSYM SEQ_ASSOC] THEN
  DISCH_TAC THEN MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC (parse_term "\\s. snappy_ic_pre pc level inp src out so sk wm mem nw owns rw ea el ev
                 stackpointer x19_init x20_init x21_init x22_init x23_init x24_init x25_init
                 x26_init x27_init x28_init x29_init returnaddress s") THEN
  CONJ_TAC THENL
   [REWRITE_TAC[snappy_ic_pre] THEN SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (parse_term "\\s. snappy_ic_post level inp out sk stackpointer x19_init x20_init
                 x21_init x22_init x23_init x24_init x25_init x26_init x27_init x28_init
                 x29_init returnaddress s") THEN
  ASM_REWRITE_TAC[snappy_ic_post] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Memory safety.                                                            *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_IC_MAIN_SAFE_STMT = parse_term
 ("!" ^ snappy_ic_vars_str ^ " owns (e:uarch_event list).
    " ^ snappy_ic_hyps_safe_str ^ "
    ==> ensures arm
         (\\s. snappy_ic_pre pc level inp src out so sk wm mem nw owns rw ea el ev
                 stackpointer x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 ra s /\\
              read events s = e)
         (\\s. snappy_ic_post_safe " ^ snappy_ic_postargs_safe_str ^ " s)
         (" ^ snappy_ic_frame_str ^ ")");;

let SNAPPY_IC_MAIN_SAFE = prove
 (SNAPPY_IC_MAIN_SAFE_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC SNAPPY_IC_ENSURES_LOOP THEN
  EXISTS_TAC (parse_term ("\\m s. ?k'. 65536 * k' < LENGTH(inp:byte list) /\\
      m = LENGTH inp - 65536 * k' /\\ snappy_ic_inv_safe " ^ snappy_ic_invargs_safe_str ^ " k' s")) THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN MAYCHANGE_IDEMPOT_TAC;
    MP_TAC(SPEC_ALL SNAPPY_IC_ENTRY_SAFE) THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC SNAPPY_IC_ENSURES_EXISTS THEN X_GEN_TAC `k:num` THEN
    ASM_CASES_TAC `65536 * k < LENGTH(inp:byte list)` THEN
    ASM_REWRITE_TAC[ENSURES_TRIVIAL] THEN
    ASM_CASES_TAC `n = LENGTH(inp:byte list) - 65536 * k` THEN
    ASM_REWRITE_TAC[ENSURES_TRIVIAL] THEN
    MP_TAC(SPEC_ALL SNAPPY_IC_ITER_SAFE) THEN ASM_REWRITE_TAC[]]);;

let SNAPPY_INTERNAL_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_INTERNAL_COMPRESS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  MAP_EVERY X_GEN_TAC [`e:uarch_event list`; `level:num`; `inp:byte list`;
    `src:int64`; `out:int64`;
    `so:int64`; `sk:int64`; `wm:int64`; `mem:int64`; `nw:num`; `owns:bool`;
    `pc:num`; `imp:string->int64`; `ea:int64`; `el:num`; `ev:num`; `rw:num`;
    `stackpointer:int64`; `returnaddress:int64`] THEN
  DISCH_TAC THEN
  MAP_EVERY (fun (n,c) -> ENSURES_PRESERVED_TAC n c)
   [("x19_init",`X19`); ("x20_init",`X20`); ("x21_init",`X21`);
    ("x22_init",`X22`); ("x23_init",`X23`); ("x24_init",`X24`);
    ("x25_init",`X25`); ("x26_init",`X26`); ("x27_init",`X27`);
    ("x28_init",`X28`); ("x29_init",`X29`)] THEN
  MATCH_MP_TAC(ISPECL [`SP`; `stackpointer:int64`]
    ENSURES_MAYCHANGE_EXISTING_PRESERVED) THEN
  REPEAT CONJ_TAC THENL
   [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV; ENSURES_PRESERVED_KEEP_TAC;
    SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`pc:num`; `level:num`; `inp:byte list`; `src:int64`; `out:int64`;
    `so:int64`; `sk:int64`; `wm:int64`; `mem:int64`; `nw:num`;
    `imp:string->int64`; `ea:int64`; `el:num`; `ev:num`; `rw:num`;
    `stackpointer:int64`; `x19_init:int64`; `x20_init:int64`; `x21_init:int64`;
    `x22_init:int64`; `x23_init:int64`; `x24_init:int64`; `x25_init:int64`;
    `x26_init:int64`; `x27_init:int64`; `x28_init:int64`; `x29_init:int64`;
    `returnaddress:int64`; `owns:bool`; `e:uarch_event list`] SNAPPY_IC_MAIN_SAFE) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; GSYM SEQ_ASSOC] THEN
  DISCH_TAC THEN MATCH_MP_TAC ENSURES_PRECONDITION_THM THEN
  EXISTS_TAC (parse_term "\\s. snappy_ic_pre pc level inp src out so sk wm mem nw owns rw ea el ev
                 stackpointer x19_init x20_init x21_init x22_init x23_init x24_init x25_init
                 x26_init x27_init x28_init x29_init returnaddress s /\\ read events s = e") THEN
  CONJ_TAC THENL
   [REWRITE_TAC[snappy_ic_pre] THEN SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC ENSURES_POSTCONDITION_THM THEN
  EXISTS_TAC (parse_term "\\s. snappy_ic_post_safe pc level inp src out so sk wm mem nw ea el
                 stackpointer x19_init x20_init
                 x21_init x22_init x23_init x24_init x25_init x26_init x27_init x28_init
                 x29_init returnaddress e s") THEN
  ASM_REWRITE_TAC[snappy_ic_post_safe; snappy_ic_post; snappy_ic_ev] THEN SIMP_TAC[]);;
