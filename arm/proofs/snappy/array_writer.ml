(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics for the proofs of the array writer path of snappy's    *)
(* decompressor (RawUncompress, DecompressAllTags<SnappyArrayWriter>,        *)
(* snappy_uncompress), independent of the build:                             *)
(*                                                                           *)
(*  - SNAPPY_VARINT_BYTES: the header with the rest of the stream, byte by   *)
(*    byte, as ReadUncompressedLength reads it;                              *)
(*  - byte lists and nonoverlapping regions after a prefix;                  *)
(*  - BSTEP_GHOST_READS_TAC: the reads of the current state inside facts     *)
(*    that bstep does not carry (an implication, an equivalence, a           *)
(*    universal) named by variables, so that the facts no longer mention    *)
(*    the state and the reads are plain facts that bstep carries.            *)
(*  - BSTEP_DROP_NUM_DISEQS_TAC and bstep_keep_not_bytes8_at: fewer facts    *)
(*    for the arithmetic of the calls through contracts.                     *)
(* ========================================================================= *)

needs "arm/proofs/snappy/relative.ml";;
needs "arm/proofs/heap_plt.ml";;
needs "arm/proofs/snappy/decompressor_objects.ml";;
needs "common/snappy/snappy_memory.ml";;
needs "arm/proofs/snappy/bstep_decide.ml";;

(* ------------------------------------------------------------------------- *)
(* The header and the rest of the stream, byte by byte.                      *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_VARINT_BYTES = prove
 (`!l:byte list.
     snappy_varint l =
     if LENGTH l = 0 then NONE
     else if val(EL 0 l) < 128
     then SOME(val(EL 0 l),SUB_LIST(1,LENGTH l - 1) l)
     else if LENGTH l = 1 then NONE
     else if val(EL 1 l) < 128
     then SOME(val(EL 0 l) - 128 + 128 * val(EL 1 l),
               SUB_LIST(2,LENGTH l - 2) l)
     else if LENGTH l = 2 then NONE
     else if val(EL 2 l) < 128
     then SOME(val(EL 0 l) - 128 + 128 * (val(EL 1 l) - 128 +
               128 * val(EL 2 l)),SUB_LIST(3,LENGTH l - 3) l)
     else if LENGTH l = 3 then NONE
     else if val(EL 3 l) < 128
     then SOME(val(EL 0 l) - 128 + 128 * (val(EL 1 l) - 128 +
               128 * (val(EL 2 l) - 128 + 128 * val(EL 3 l))),
               SUB_LIST(4,LENGTH l - 4) l)
     else if LENGTH l = 4 then NONE
     else if val(EL 4 l) < 16
     then SOME(val(EL 0 l) - 128 + 128 * (val(EL 1 l) - 128 +
               128 * (val(EL 2 l) - 128 + 128 * (val(EL 3 l) - 128 +
               128 * val(EL 4 l)))),SUB_LIST(5,LENGTH l - 5) l)
     else NONE`,
  let cases v h t =
    DISJ_CASES_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN h (X_CHOOSE_THEN t SUBST1_TAC))
      (ISPEC v list_CASES) in
  GEN_TAC THEN cases `l:byte list` `b0:byte` `t0:byte list` THENL
   [ALL_TAC; cases `t0:byte list` `b1:byte` `t1:byte list`] THENL
   [ALL_TAC; ALL_TAC; cases `t1:byte list` `b2:byte` `t2:byte list`] THENL
   [ALL_TAC; ALL_TAC; ALL_TAC; cases `t2:byte list` `b3:byte` `t3:byte list`]
  THENL
   [ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC;
    cases `t3:byte list` `b4:byte` `t4:byte list`] THEN
  REWRITE_TAC[snappy_varint;
              ARITH_RULE `5 = SUC 4 /\ 4 = SUC 3 /\ 3 = SUC 2`; TWO; ONE] THEN
  REWRITE_TAC[snappy_varint_from; LENGTH; EL; HD; TL; SUC_INJ; NOT_SUC;
              SUB_LIST_CLAUSES; SUB_LIST_LENGTH; SUB_0;
              ARITH_RULE `SUC m - SUC n = m - n`] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[snappy_bind; option_DISTINCT; option_INJ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN TRY(FIRST_ASSUM CONTR_TAC));;

(* The test of the fifth byte of the header: (c & 0x7f) & 0xf0 == 0 (the     *)
(* mask of LeftShiftOverflows for the shift 28), with bit 7 clear.          *)

let SNAPPY_HEADER_BYTE5_MASK = prove
 (`!b:byte.
     (val(word_and (word_and (word_zx b:int32) (word 127)) (word 240)) = 0 /\
      val b < 128 ==> val b < 16) /\
     (~(val(word_and (word_and (word_zx b:int32) (word 127)) (word 240)) = 0)
      ==> ~(val b < 16))`,
  GEN_TAC THEN REWRITE_TAC[VAL_EQ_0; VAL_BYTE_LT_16; VAL_BYTE_LT_128] THEN
  BITBLAST_TAC);;

(* ------------------------------------------------------------------------- *)
(* Byte lists and regions after a prefix of h bytes.                         *)
(* ------------------------------------------------------------------------- *)

let READ_BYTELIST_SUFFIX = prove
 (`!(m:(S,N word->byte)component) a (l:byte list) h s.
        read (m :> bytelist(a,LENGTH l)) s = l /\ h <= LENGTH l
        ==> read (m :> bytelist(word_add a (word h),LENGTH l - h)) s =
            SUB_LIST(h,LENGTH l - h) l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[READ_BYTELIST_EQ_EL] THEN
  REWRITE_TAC[SNAPPY_LENGTH_SUB_LIST_SUFFIX] THEN STRIP_TAC THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SNAPPY_EL_SUB_LIST o rand o snd) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[WORD_RULE `word_add (word_add a (word h)) (word i):N word =
                         word_add a (word(h + i))`] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let NONOVERLAPPING_SUFFIX = prove
 (`!(a:int64) n h b k.
        nonoverlapping (a,n) (b,k) /\ h <= n
        ==> nonoverlapping (word_add a (word h),n - h) (b,k)`,
  REWRITE_TAC[NONOVERLAPPING_MEMRANGE] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `h:num`; `n - h:num`; `n:num`]
    MEMRANGE_OFFSET_SUBSET) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]]);;

let NONOVERLAPPING_PREFIX = prove
 (`!(a:int64) n k b l.
        nonoverlapping (a,n) (b,l) /\ k <= n ==> nonoverlapping (a,k) (b,l)`,
  REWRITE_TAC[NONOVERLAPPING_MEMRANGE] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `k:num`; `n:num`] MEMRANGE_PREFIX_SUBSET) THEN
  ASM SET_TAC[]);;

let NONOVERLAPPING_PREFIX_RIGHT = prove
 (`!(a:int64) n k b l.
        nonoverlapping (b,l) (a,n) /\ k <= n ==> nonoverlapping (b,l) (a,k)`,
  REWRITE_TAC[NONOVERLAPPING_MEMRANGE] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `k:num`; `n:num`] MEMRANGE_PREFIX_SUBSET) THEN
  ASM SET_TAC[]);;

let NONOVERLAPPING_SUFFIX_PREFIX = prove
 (`!(a:int64) n h b k j.
        nonoverlapping (a,n) (b,k) /\ h <= n /\ j <= k
        ==> nonoverlapping (word_add a (word h),n - h) (b,j)`,
  REWRITE_TAC[NONOVERLAPPING_MEMRANGE] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:int64`; `h:num`; `n - h:num`; `n:num`]
    MEMRANGE_OFFSET_SUBSET) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`b:int64`; `j:num`; `k:num`] MEMRANGE_PREFIX_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM SET_TAC[]);;

(* A frame with a footprint of a region as the frame with the region.        *)

let SUBSUMED_ASSIGNS_FOOTPRINT_MEMRANGE = prove
 (`!(a:N word) k.
        k <= 2 EXP dimindex(:N)
        ==> ASSIGNS (footprint (memrange(a,k))) subsumed ASSIGNS (bytes(a,k))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[subsumed; ASSIGNS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:N word->byte`; `m':N word->byte`] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:N word->byte` (SUBST1_TAC o SYM)) THEN
  ABBREV_TAC `(m1:N word->byte) =
              write (footprint (memrange(a:N word,k))) (f:N word->byte) m` THEN
  EXISTS_TAC `read (bytes(a:N word,k)) m1` THEN
  MP_TAC(ISPECL [`a:N word`; `k:num`] EXTENSIONALLY_VALID_COMPONENT_BYTES) THEN
  REWRITE_TAC[EXTENSIONALLY_VALID_COMPONENT] THEN
  DISCH_THEN(MP_TAC o SPEC `m1:N word->byte` o CONJUNCT1 o CONJUNCT2) THEN
  DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:N word` THEN
  MP_TAC(ISPECL [`a:N word`; `x:N word`; `k:num`;
                 `read (bytes(a:N word,k)) m1`; `m:N word->byte`]
    READ_ELEMENT_WRITE_BYTES) THEN
  MP_TAC(ISPECL [`a:N word`; `x:N word`; `k:num`;
                 `read (bytes(a:N word,k)) m1`; `m1:N word->byte`]
    READ_ELEMENT_WRITE_BYTES) THEN
  ASM_REWRITE_TAC[READ_ELEMENT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_THEN `write (footprint (memrange(a:N word,k))) (f:N word->byte) m = m1`
    (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[WRITE_FOOTPRINT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_MEMRANGE]) THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_neg(concl th) && is_binary "<" (dest_neg(concl th)))) THEN
  REWRITE_TAC[WORD_RULE `word_sub (word_add a (word i)) a:N word = word i`;
              VAL_WORD] THEN
  SUBGOAL_THEN `i MOD 2 EXP dimindex(:N) = i` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let MAYCHANGE_FOOTPRINT_MEMRANGE_SUBSUMED = prove
 (`!(m:(S,N word->byte)component) a k.
        k <= 2 EXP dimindex(:N)
        ==> MAYCHANGE [m :> footprint (memrange(a,k))] subsumed
            MAYCHANGE [m :> bytes(a,k)]`,
  REWRITE_TAC[MAYCHANGE_SING] THEN
  SIMP_TAC[SUBSUMED_ASSIGNS_SUBCOMPONENTS;
           SUBSUMED_ASSIGNS_FOOTPRINT_MEMRANGE]);;

(* word_add (word_add x (word a)) (word b) = word_add x (word (a + b)) for   *)
(* numerals a, b: the form of addresses in bstep's facts.                    *)

let WORD_ADD_ADD_NUM_CONV tm =
  match tm with
    Comb(Comb(Const("word_add",_),
              Comb(Comb(Const("word_add",_),x),Comb(Const("word",_),a))),
         Comb(Const("word",_),b))
      when is_numeral a && is_numeral b ->
      let c = mk_numeral(dest_numeral a +/ dest_numeral b) in
      let r = mk_comb(mk_comb(rator(rator tm),x),
                      mk_comb(rator(rand tm),c)) in
      WORD_RULE(mk_eq(tm,r))
  | _ -> failwith "WORD_ADD_ADD_NUM_CONV";;

(* ------------------------------------------------------------------------- *)
(* Preconditions that are disjunctions or existentials (cut points).         *)
(* ------------------------------------------------------------------------- *)

let ENSURES_DISJ_PRECONDITION = prove
 (`!(step:A->A->bool) P1 P2 Q C.
        ensures step P1 Q C /\ ensures step P2 Q C
        ==> ensures step (\s. P1 s \/ P2 s) Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

let ENSURES_EXISTS_PRECONDITION = prove
 (`!(step:A->A->bool) (P:B->A->bool) Q C.
        (!x. ensures step (P x) Q C)
        ==> ensures step (\s. ?x. P x s) Q C`,
  REWRITE_TAC[ensures] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Reads of the current state (the state of the goal eventually ... s) in    *)
(* assumptions that are not of the form read c s = v are replaced by new     *)
(* variables (named after prefix), with the facts read c s = v added.        *)
(* ------------------------------------------------------------------------- *)

let BSTEP_GHOST_READS_TAC (prefix:string) : tactic =
  fun (asl,w) ->
    let s = rand w in
    let is_read_fact tm =
      match tm with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),_),s1)),_) -> s1 = s
      | _ -> false in
    let reads = setify(itlist (fun (_,th) acc ->
      let c = concl th in
      if is_read_fact c || not(vfree_in s c) then acc else
      let fv = frees c in
      find_terms (fun t -> match t with
          Comb(Comb(Const("read",_),_),s1) ->
            s1 = s && subset (frees t) fv
        | _ -> false) c @ acc) asl []) in
    let ghost r (asl,w) =
      let v = genvar (type_of r) in
      let v' = mk_var(prefix ^ string_of_int(length asl),type_of r) in
      let eth = prove(mk_exists(v,mk_eq(r,v)),EXISTS_TAC r THEN REFL_TAC) in
      (X_CHOOSE_THEN v' (fun th ->
         RULE_ASSUM_TAC(fun a -> if is_read_fact(concl a) then a
                                 else PURE_REWRITE_RULE[th] a) THEN
         ASSUME_TAC th) eth) (asl,w) in
    MAP_EVERY ghost reads (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Before a call through a contract: the facts that cross the call are moved *)
(* by proofs that their components are orthogonal to each clause of the      *)
(* callee's frame, by integer arithmetic on all the numeric assumptions      *)
(* (NONOVERLAPPING_RULE of common/components.ml), which case-splits on each  *)
(* disequality. BSTEP_DROP_NUM_DISEQS_TAC drops the numeric disequalities    *)
(* that do not mention the current state (such as ~(LENGTH l = k) of a case  *)
(* split), and bstep_keep_not_bytes8_at a, as the ~keep of the contract      *)
(* tactics, does not carry the bytes read at a + k (such as the header bytes  *)
(* of the stream) across the call. In RawUncompress with a Source the calls  *)
(* of DecompressAllTags took up to 475 s each with them, and 2 s without.    *)
(* ------------------------------------------------------------------------- *)

let BSTEP_DROP_NUM_DISEQS_TAC : tactic =
  W(fun (asl,w) ->
    let s = rand w in
    DISCARD_ASSUMPTIONS_TAC (fun th -> let c = concl th in
      is_neg c && is_eq(dest_neg c) && type_of(lhand(dest_neg c)) = `:num` &&
      not(vfree_in s c)));;

let bstep_keep_not_bytes8_at (base:term) (c:term) =
  match c with
    Comb(Comb(Const(":>",_),Const("memory",_)),Comb(Const("bytes8",_),a)) ->
      not(a = base ||
          (is_binary "word_add" a && lhand a = base))
  | _ -> true;;

(* ------------------------------------------------------------------------- *)
(* The kill tactic for ARM_BSTEP_RUN_GEN_TAC: close the case of a branch     *)
(* (the last assumption) that its reduction (a test of a word_and with 0, a  *)
(* bitval of T or F) or the arithmetic facts contradict.                     *)
(* ------------------------------------------------------------------------- *)

let BSTEP_KILL_TAC : tactic =
  fun (asl,w) ->
    match asl with
      [] -> ALL_TAC (asl,w)
    | (_,cth)::rest ->
        let red = try CONV_RULE(REWRITE_CONV[WORD_AND_0; VAL_WORD_0;
                                             BITVAL_CLAUSES; WORD_ZX_0;
                                             option_DISTINCT; NOT_CLAUSES] THENC
                                WORD_REDUCE_CONV THENC
                                NUM_REDUCE_CONV) cth
                  with Failure _ -> cth in
        if concl red = `F` then CONTR_TAC red (asl,w) else
        try
          let c = concl cth in
          let nc = if is_neg c then dest_neg c else mk_neg c in
          let th = TAC_PROOF((rest,nc),BSTEP_ARITH_DECIDE_TAC ~rws:[]) in
          (if is_neg c then CONTR_TAC(MP (NOT_ELIM cth) th)
           else CONTR_TAC(MP (NOT_ELIM th) cth)) (asl,w)
        with Failure _ -> ALL_TAC (asl,w);;

(* ENSURES_DROP_EVENTS_TAC (arm/proofs/heap_plt.ml) for postconditions that *)
(* its final MESON_TAC does not prove in time (many conjuncts, universals): *)
(* each conjunct of the correctness postcondition is a conjunct of that of  *)
(* the safety theorem.                                                       *)

let ENSURES_DROP_EVENTS_CONJ_TAC (sth:thm) : tactic =
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
      | None -> failwith "ENSURES_DROP_EVENTS_CONJ_TAC: no events variable e" in
    let gth = GEN e th in
    REWRITE_TAC[ensures] THEN BETA_TAC THEN
    X_GEN_TAC `s:armstate` THEN DISCH_TAC THEN
    MP_TAC(SPEC `read events (s:armstate)` gth) THEN
    REWRITE_TAC[ensures] THEN BETA_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `s:armstate`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EVENTUALLY_MONO_IMP THEN BETA_TAC THEN
    GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
    FIRST_ASSUM ACCEPT_TAC);;
