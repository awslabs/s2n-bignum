(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* InternalUncompress<SnappyDecompressionValidator> (0x5260): correctness    *)
(* and memory safety (internal_uncompress_validator_spec.ml), relative to   *)
(* the contract of DecompressAllTags<SnappyDecompressionValidator>.          *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/internal_uncompress_validator_spec.ml";;
needs "arm/proofs/snappy/validator_tactics.ml";;
needs "arm/proofs/snappy/array_writer.ml";;

(*** One case per input length L = 0, 1, 2, 3, 4 and L >= 5; the branches  ***)
(*** on the header bytes are split (Peek, Skip and Available are stepped    ***)
(*** through the vtable). At the call of DecompressAllTags the path gives h, ***)
(*** the number of header bytes (ptr_ = inp + h), the header m              ***)
(*** (SNAPPY_VARINT_BYTES and the byte tests) and its 32-bit value in w20,  ***)
(*** stored as expected_; the contract is instantiated with the rest of the ***)
(*** stream after h bytes. Only the non-overlap facts that the contract    ***)
(*** needs beyond those of the spec are added (the rest of the stream with  ***)
(*** the objects, by NONOVERLAPPING_SUBSETS). After the call the cases of   ***)
(*** eof_ are split; the result is then the compare of expected_ and        ***)
(*** produced_, which the contract relates to the decode of the tags.       ***)
(*** As the proof of RawUncompress with a Source and a char pointer, whose ***)
(*** tactics for the header are repeated with the offsets of this code.  ***)

(* ------------------------------------------------------------------------- *)
(* A byte of the image, from the 16-byte word that contains it.              *)
(* ------------------------------------------------------------------------- *)

let IU_IMAGE_BYTE_RULE =
  let imagel = dest_list(rhs(concl snappy_libsnappy_gcc12_O2_mc)) in
  fun k ->
    let b = (k / 16) * 16 and i = k mod 16 in
    let th128 = SNAPPY_IMAGE_CONST_RULE b 128 in
    let v = el k imagel in
    let tm = subst [mk_small_numeral k,`k:num`; v,`v:byte`]
     `!s pc. aligned_bytes_loaded s (word pc) snappy_libsnappy_gcc12_O2_mc
             ==> read (memory :> bytes8 (word_add (word pc) (word k))) s = v` in
    let eq = WORD_RULE (subst [mk_small_numeral k,`k:num`;
                               mk_small_numeral b,`b:num`;
                               mk_small_numeral i,`i:num`]
       `word_add (word pc) (word k):int64 =
        word_add (word_add (word pc) (word b)) (word i)`) in
    prove(tm, REPEAT STRIP_TAC THEN SUBST1_TAC eq THEN
      SIMP_TAC[READ_BYTES8_OF_BYTES128; ARITH] THEN ASM_SIMP_TAC[th128] THEN
      CONV_TAC WORD_REDUCE_CONV);;

(* The table LeftShiftOverflows_masks at rodata_pattern_generation_masks +   *)
(* 0x200 = 0x7dc0: entries 0 for the shifts 0, 7, 14, 21 and 0xf0 for 28.    *)

let IU_MASK_FACTS =
  let addr k = WORD_RULE (subst [mk_small_numeral k,`k:num`;
                                 mk_small_numeral (0x7dc0 + k),`j:num`]
    `word_add (word k) (word_add (word pc) (word 32192)):int64 =
     word_add (word pc) (word j)`) in
  flat (map (fun k ->
    let th = IU_IMAGE_BYTE_RULE (0x7dc0 + k) in
    if k = 0 then [th] else [th; REWRITE_RULE[GSYM(addr k)] th])
   [0;7;14;21;28]);;

let IU_MASK_SUBSETS =
  map (fun k ->
    let addr = WORD_RULE (subst [mk_small_numeral k,`k:num`;
                                 mk_small_numeral (0x7dc0 + k),`j:num`]
      `word_add (word k) (word_add (word pc) (word 32192)):int64 =
       word_add (word pc) (word j)`) in
    prove(subst [mk_small_numeral k,`k:num`]
      `memrange(word_add (word k) (word_add (word pc) (word 32192)):int64,1)
       SUBSET memrange(word pc,libsnappy_size)`,
      SUBST1_TAC addr THEN MATCH_MP_TAC MEMRANGE_OFFSET_SUBSET THEN
      CONV_TAC NUM_REDUCE_CONV)) [7;14;21;28];;

(* Before the ldrb w0, [x19, x21] (0x52e0): the bytes of the masks in the   *)
(* current state, also with the address in the form of the code.            *)

let IU_MASK_NORM_TAC : tactic =
  W(fun (asl,w) ->
    let s = rand w in
    try
      let pcth = snd(find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s1)),_) ->
            c = `PC` && s1 = s
        | _ -> false) asl) in
      if rand(concl pcth) <> `word(pc + 21216):int64` then ALL_TAC else
      let a = snd(find (fun (_,th) -> match concl th with
          Comb(Comb(Comb(Const("aligned_bytes_loaded",_),s1),_),_) -> s1 = s
        | _ -> false) asl) in
      MAP_EVERY (fun th -> ASSUME_TAC(MATCH_MP th a)) IU_MASK_FACTS
    with Failure _ -> ALL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic.                                                               *)
(* ------------------------------------------------------------------------- *)

let IU_QLT = prove
 (`!(a:int64) n h. val a + n < 2 EXP 64 /\ h <= n
                   ==> val(word_add a (word h)) + (n - h) < 2 EXP 64`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `h MOD 2 EXP 64 = h` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(val(a:int64) + h) MOD 2 EXP 64 = val a + h` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let IU_WORD_SUB_SUB = prove
 (`!x:int64 a b. word_sub (word_sub x (word a)) (word b) = word_sub x (word(a + b))`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let IU_WORD_SUB_NUM = prove
 (`!n h. h <= n ==> word_sub (word n) (word h):int64 = word(n - h)`,
  SIMP_TAC[WORD_SUB]);;

let IU_WORD_ZX_32 = prove
 (`!m. m < 2 EXP 32 ==> word_zx(word m:int32):int64 = word m`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `m < 2 EXP 32 ==> m < 2 EXP 64`]);;

(* The decompressor at sp - 48 does not reach the top of the memory.         *)

let IU_VAL_D = prove
 (`!sp:int64. 464 <= val sp
              ==> val(word_add (word_sub sp (word 144)) (word 96)) + 48 <=
                  2 EXP 64`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[WORD_RULE `word_add (word_sub sp (word 144)) (word 96):int64 =
                         word_sub sp (word 48)`] THEN
  MP_TAC(ISPEC `sp:int64` VAL_BOUND) THEN REWRITE_TAC[DIMINDEX_64] THEN
  DISCH_TAC THEN REWRITE_TAC[VAL_WORD_SUB_CASES; VAL_WORD; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* Non-overlap of subregions.                                                *)

let NONOVERLAPPING_SUBSETS = prove
 (`!(a:int64) n b k a' n' b' k'.
        nonoverlapping (a',n') (b',k') /\
        memrange(a,n) SUBSET memrange(a',n') /\
        memrange(b,k) SUBSET memrange(b',k')
        ==> nonoverlapping (a,n) (b,k)`,
  REWRITE_TAC[NONOVERLAPPING_MEMRANGE] THEN SET_TAC[]);;

(* For each conjunct nonoverlapping (a,n) (b,k) of hyp: a proof from a fact  *)
(* nonoverlapping (a',n') (b',k') of ths (in either order) with (a,n) and    *)
(* (b,k) inside by memrange_subset_rule or a SUBSET fact of subs.            *)

let iu_nonoverlap_facts (subs:thm list) (ths:thm list) (hyp:term) =
  let rm (a,k) = mk_comb(`memrange:int64#num->int64->bool`,mk_pair(a,k)) in
  let sub r r' =
    try memrange_subset_rule r r' with Failure _ ->
    find (fun th -> concl th = mk_binary "SUBSET" (rm r,rm r')) subs in
  let one c =
    match c with
      Comb(Comb(Const("nonoverlapping",_),p),q) ->
        let r1 = dest_pair p and r2 = dest_pair q in
        tryfind (fun th ->
          match concl th with
            Comb(Comb(Const("nonoverlapping",_),p'),q') ->
              let r1' = dest_pair p' and r2' = dest_pair q' in
              (try MATCH_MP NONOVERLAPPING_SUBSETS
                     (CONJ th (CONJ (sub r1 r1') (sub r2 r2')))
               with Failure _ ->
                 let th' = ONCE_REWRITE_RULE[NONOVERLAPPING_SYM] th in
                 MATCH_MP NONOVERLAPPING_SUBSETS
                   (CONJ th' (CONJ (sub r1 r2') (sub r2 r1'))))
          | _ -> fail()) ths
    | _ -> fail() in
  mapfilter one (conjuncts hyp);;

(* ------------------------------------------------------------------------- *)
(* The branches on the header bytes.                                         *)
(* ------------------------------------------------------------------------- *)

let IU_BYTE_RULES = [BIT7_WORD_ZX_BYTE];;

let IU_BYTE5_TAC : tactic =
  fun (asl,w) ->
    let facts = map snd asl in
    let pat = `val(word_and (word_and (word_zx (b:byte):int32) (word 127))
                            (word 240)) = 0` in
    let add = mapfilter (fun th ->
      let c = concl th in
      try
        let i = term_match [] pat c in
        let b = instantiate i `b:byte` in
        let lt = mk_comb(mk_comb(`(<):num->num->bool`,
                   mk_comb(`val:byte->num`,b)),`128`) in
        let lth = find (fun t -> concl t = lt) facts in
        MP (CONJUNCT1 (ISPEC b SNAPPY_HEADER_BYTE5_MASK)) (CONJ th lth)
      with Failure _ ->
      try
        let i = term_match [] (mk_neg pat) c in
        let b = instantiate i `b:byte` in
        MP (CONJUNCT2 (ISPEC b SNAPPY_HEADER_BYTE5_MASK)) th
      with Failure _ ->
        let i = term_match [] `~(val(b:byte) < 128)` c in
        let b = instantiate i `b:byte` in
        MP (ARITH_RULE(mk_imp(c,mk_neg(mk_comb(mk_comb(`(<):num->num->bool`,
              mk_comb(`val:byte->num`,b)),`16`))))) th) facts in
    MAP_EVERY ASSUME_TAC add (asl,w);;

let IU_KILL_TAC : tactic =
  fun (asl,w) ->
    match asl with
      [] -> ALL_TAC (asl,w)
    | (_,cth0)::rest ->
        let masks = flat (map (fun (_,a) ->
            mapfilter (fun th -> MATCH_MP th a) IU_MASK_FACTS) asl) in
        let cth = try CONV_RULE(REWRITE_CONV masks THENC
                                DEPTH_CONV WORD_RED_CONV) cth0
                  with Failure _ -> cth0 in
        let red = CONV_RULE(REWRITE_CONV[WORD_AND_0; VAL_WORD_0; BITVAL_CLAUSES;
                                         WORD_ZX_0] THENC
                            DEPTH_CONV WORD_RED_CONV THENC
                            NUM_REDUCE_CONV) cth in
        if concl red = `F` then CONTR_TAC red (asl,w) else
        try
          let c = concl cth in
          let nc = if is_neg c then dest_neg c else mk_neg c in
          let rest' = filter (fun (_,th) -> let c = concl th in
                        not(is_neg c && is_eq(dest_neg c))) rest in
          let th = TAC_PROOF((rest',nc),BSTEP_ARITH_DECIDE_TAC ~rws:[]) in
          (if is_neg c then CONTR_TAC(MP (NOT_ELIM cth) th)
           else CONTR_TAC(MP (NOT_ELIM th) cth)) (asl,w)
        with Failure _ ->
          (if concl cth = concl cth0 then ALL_TAC
           else POP_ASSUM(K ALL_TAC) THEN ASSUME_TAC cth) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* The call of DecompressAllTags<Validator> after a header of h bytes.       *)
(* ------------------------------------------------------------------------- *)

let IU_DAT = SNAPPY_DECOMPRESSOR_DECOMPRESS_ALL_TAGS_VALIDATOR_GCC12_O2_IMAGE_SUBROUTINE_SAFE;;

let iu_find_fact ?(vars=[]) pat asl =
  let lcs = subtract (frees pat) vars in
  snd(find (fun (_,th) -> can (term_match lcs pat) (concl th)) asl);;

let IU_EOF_CASES_TAC : tactic =
  W(fun (asl,w) ->
    let th = iu_find_fact ~vars:[`a:int64`; `s:armstate`; `b:bool`]
      `read (memory :> bytes8 a) s = word(bitval b)` asl in
    let v = rand(rand(rand(concl th))) in
    ASM_CASES_TAC v THEN
    POP_ASSUM(fun c -> RULE_ASSUM_TAC(REWRITE_RULE[c; BITVAL_CLAUSES]) THEN
                       ASSUME_TAC c));;

let iu_verbose = ref false;;

let IU_DAT_CALL_TAC exec =
  fun i ->
   ((RULE_ASSUM_TAC(REWRITE_RULE IU_BYTE_RULES) THEN IU_BYTE5_TAC) THEN
    W(fun (asl,w) ->
      let s = rand w in
      let facts = map (fun th -> if is_eq(concl th) then EQT_INTRO th else th)
                   (filter (fun th -> let c = concl th in
                            not(vfree_in s c) && not(is_forall c) &&
                            not(is_imp c) &&
                            not(can (find_term is_abs) c))
                         (map snd asl)) in
      let vth = REWRITE_CONV (SNAPPY_VARINT_BYTES :: facts)
                  `snappy_varint (l:byte list)` in
      let mexpr = lhand(rand(rand(concl vth))) in
      (* the 32-bit header value in w20, stored as expected_ *)
      let lth = iu_find_fact ~vars:[`x:int32`] (vsubst [s,`s:armstate`]
        `read (memory :> bytes64 v) s = word_zx (x:int32)`) asl in
      let w32 = rand(rand(concl lth)) in
      let wgoal = mk_eq(w32,mk_comb(`word:num->int32`,mexpr)) in
      let wth = TAC_PROOF((asl,wgoal), REWRITE_TAC[word_jshl; VAL_WORD; DIMINDEX_32] THEN
                    CONV_TAC NUM_REDUCE_CONV THEN SNAPPY_HEADER_WORD_TAC) in
      let mlt = CONJUNCT1(MATCH_MP SNAPPY_VARINT_SOME vth) in
      ASSUME_TAC vth THEN ASSUME_TAC wth THEN ASSUME_TAC mlt THEN
      ABBREV_TAC (mk_eq(`m:num`,mexpr))) THEN
    W(fun (asl,w) ->
      let s = rand w in
      let ev t = arm_bstep_eval asl s t in
      let pth = iu_find_fact ~vars:[`h:num`] (vsubst [s,`s:armstate`]
        `read (memory :> bytes64 (word_add src (word 8))) s =
         word_add inp (word h)`) asl in
      let h = rand(rand(rand(concl pth))) in
      let wth = snd(find (fun (_,th) -> is_eq(concl th) &&
                            rand(concl th) = `word m:int32`) asl) in
      let mlt = snd(find (fun (_,th) -> concl th = `m < 2 EXP 32`) asl) in
      let vth = iu_find_fact ~vars:[`r:byte list`]
        `snappy_varint (l:byte list) = SOME(m,r)` asl in
      let rest = rand(rand(rand(concl vth))) in
      let cf = snd(find (fun (_,th) -> let c = concl th in
                 c = `5 <= LENGTH(l:byte list)` ||
                 (is_eq c && lhand c = `LENGTH(l:byte list)` &&
                  is_numeral(rand c))) asl) in
      let hle = MP (ARITH_RULE(mk_imp(concl cf,
                      mk_binary "<=" (h,`LENGTH(l:byte list)`)))) cf in
      let wzx = MP (SPEC `m:num` IU_WORD_ZX_32) mlt in
      let left_th = iu_find_fact ~vars:[`x:int64`] (vsubst [s,`s:armstate`]
        `read (memory :> bytes64 (word_add src (word 16))) s = x`) asl in
      let lv = rand(concl left_th) in
      let lvth =
        let th1 = (REWRITE_CONV[IU_WORD_SUB_SUB] THENC NUM_REDUCE_CONV) lv in
        let th2 = MP (SPECL [`LENGTH(l:byte list)`; h] IU_WORD_SUB_NUM) hle in
        TRANS th1 th2 in
      let bl = iu_find_fact (vsubst [s,`s:armstate`]
        `read (memory :> bytelist(inp,LENGTH(l:byte list))) s = l`) asl in
      let blth = MATCH_MP READ_BYTELIST_SUFFIX (CONJ bl hle) in
      let qn = subst [h,`h:num`] `word_add (inp:int64) (word h)` in
      let novs = mapfilter (fun (_,th) -> match concl th with
          Comb(Comb(Const("nonoverlapping",_),p1),_)
            when p1 = `inp:int64,LENGTH(l:byte list)` ->
            MATCH_MP NONOVERLAPPING_SUFFIX (CONJ th hle)
        | _ -> fail()) asl in
      let qlt = MP (SPECL [`inp:int64`; `LENGTH(l:byte list)`; h] IU_QLT)
                  (CONJ (ASSUME `val(inp:int64) + LENGTH(l:byte list) < 2 EXP 64`) hle) in
      let rlt = MP (ARITH_RULE(mk_imp(`LENGTH(l:byte list) < 2 EXP 58`,
                     subst [h,`h:num`] `LENGTH(l:byte list) - h < 2 EXP 58`)))
                   (ASSUME `LENGTH(l:byte list) < 2 EXP 58`) in
      let dth0 = MP (SPEC `sp:int64` IU_VAL_D) (ASSUME `464 <= val(sp:int64)`) in
      let hk = MP (ARITH_RULE(mk_imp(concl hle,
                 subst [h,`h:num`] `h + LENGTH(l:byte list) - h <= LENGTH l`))) hle in
      let insub = ISPEC `inp:int64` (MATCH_MP MEMRANGE_OFFSET_SUBSET hk) in
      let args = [ev `read events s`; ev `read X0 s`; `src:int64`; ev `read X1 s`;
                  qn; rest; `m:num`; `word 0:int64`; `pc:num`; `rw:num`;
                  ev `read SP s`; ev `read X30 s`;
                  ev `read X19 s`; ev `read X20 s`; ev `read X21 s`; ev `read X22 s`;
                  ev `read X23 s`; ev `read X24 s`; ev `read X25 s`; ev `read X26 s`;
                  ev `read X29 s`; `ea:int64`; `el:num`; `ev:num`] in
      let args = map (fun t -> rhs(concl(REWRITE_CONV[wth; wzx; lvth] t))) args in
      let dth = CONV_RULE (REWRITE_CONV[SNAPPY_LENGTH_SUB_LIST_SUFFIX; ALLPAIRS;
                                        ALL; PAIRWISE] THENC
                           DEPTH_CONV WORD_ADD_ADD_NUM_CONV)
                  (SPECL args IU_DAT) in
      let novths = map snd (filter (fun (_,th) -> match concl th with
          Comb(Comb(Const("nonoverlapping",_),_),_) -> true | _ -> false) asl) in
      let extra = iu_nonoverlap_facts [insub] (novs @ novths) (lhand(concl dth)) in
      (if !iu_verbose then
         (Printf.printf "IU CALL h = %s, %d nonoverlap facts\n%!"
            (string_of_term h) (length extra)));
      RULE_ASSUM_TAC(REWRITE_RULE[wth; wzx; lvth]) THEN
      MAP_EVERY ASSUME_TAC ([blth; qlt; rlt; dth0; insub] @ extra) THEN
      (* see BSTEP_DROP_NUM_DISEQS_TAC *)
      BSTEP_DROP_NUM_DISEQS_TAC THEN
      (ARM_BSTEP_CONTRACT_TAC ~keep:(bstep_keep_not_bytes8_at `inp:int64`)
         exec dth [] ("s" ^ string_of_int i)) THEN
      IU_EOF_CASES_TAC)), 1;;

(* ------------------------------------------------------------------------- *)
(* The leaves.                                                               *)
(* ------------------------------------------------------------------------- *)

let iu_leaf_debug = ref false;;

let IU_SP_RULE =
  WORD_RULE `word_add (word_sub sp (word 144)) (word 144):int64 = sp`;;

let IU_EVENTS_TAC : tactic =
  TRY(W(fun (asl,w) ->
    let evth = snd(find (fun (_,th) -> is_eq(concl th) &&
      lhand(concl th) = lhand(lhand(snd(dest_exists w)))) asl) in
    REWRITE_TAC[evth])) THEN
  MEMACCESS_INSET_TAC;;

let IU_FAIL_LEAF : tactic =
  BSTEP_FINAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE (IU_SP_RULE :: IU_BYTE_RULES)) THEN IU_BYTE5_TAC THEN
  SUBGOAL_THEN `snappy_varint (l:byte list) = NONE` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SNAPPY_VARINT_BYTES] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[snappy_decode; snappy_bind; option_DISTINCT;
                  BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  (if !iu_leaf_debug then ALL_TAC else
   REPEAT CONJ_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
   IU_EVENTS_TAC);;

let IU_SUCCESS_LEAF : tactic =
  BSTEP_FINAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IU_SP_RULE]) THEN
  REWRITE_TAC[snappy_decode] THEN
  W(fun (asl,w) ->
    let vth = iu_find_fact ~vars:[`r:byte list`]
      `snappy_varint (l:byte list) = SOME(m,r)` asl in
    REWRITE_TAC[vth; snappy_bind]) THEN
  (if !iu_leaf_debug then ALL_TAC else
   REPEAT CONJ_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
   TRY(IU_EVENTS_TAC THEN NO_TAC) THEN
   W(fun (asl,w) ->
     let x0 = snd(find (fun (_,th) -> is_eq(concl th) &&
                lhand(concl th) = lhand w) asl) in
     let iffs = mapfilter (fun (_,th) -> match concl th with
         Comb(Comb(Const("=",_),(Comb(Comb(Const("=",_),_),_))),_)
           when type_of(lhand(concl th)) = bool_ty ->
           CONV_RULE(LAND_CONV SYM_CONV) th
       | _ -> fail()) asl in
     REWRITE_TAC([x0; VAL_EQ_0; WORD_SUB_EQ_0] @ iffs) THEN
     TRY(COND_CASES_TAC) THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
     CONV_TAC WORD_REDUCE_CONV));;

let IU_LEAF : tactic =
  W(fun (asl,w) ->
    if exists (fun (_,th) -> can (term_match []
                 `snappy_varint (l:byte list) = SOME x`) (concl th)) asl
    then IU_SUCCESS_LEAF
    else IU_FAIL_LEAF);;

let IU_EXEC = SNAPPY_INTERNAL_UNCOMPRESS_VALIDATOR_GCC12_O2_EXEC;;

let IU_CASE_TAC lk =
  let big = (lk = None) in
  let len = match lk with Some k -> k | None -> 5 in
  let num k = mk_small_numeral k in
  (* the facts ~(LENGTH l = k), each once (duplicates make the arithmetic  *)
  (* of the side conditions split twice as many cases)                       *)
  let neq k = W(fun (asl,w) ->
    let t = subst [num k,`k:num`] `~(LENGTH(l:byte list) = k)` in
    if exists (fun (_,th) -> concl th = t) asl then ALL_TAC
    else SUBGOAL_THEN t ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) in
  (if big then MAP_EVERY neq (0--4)
   else MAP_EVERY (fun k -> if k = len then ALL_TAC else neq k) (0--5)) THEN
  (if big then
     ASSUME_TAC(MP (ISPECL [`inp:int64`; `5`; `LENGTH(l:byte list)`]
                      MEMRANGE_PREFIX_SUBSET)
                   (ASSUME `5 <= LENGTH(l:byte list)`))
   else if len = 0 then ALL_TAC
   else ASSUME_TAC(MP (ISPECL [`inp:int64`; num len; `LENGTH(l:byte list)`]
                         MEMRANGE_PREFIX_SUBSET)
                      (MP (ARITH_RULE(mk_imp(subst [num len,`k:num`]
                             `LENGTH(l:byte list) = k`,
                             subst [num len,`k:num`] `k <= LENGTH(l:byte list)`)))
                          (ASSUME (subst [num len,`k:num`] `LENGTH(l:byte list) = k`))))) THEN
  MAP_EVERY ASSUME_TAC IU_MASK_SUBSETS THEN
  ENSURES_INIT_TAC "s0" THEN
  ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
           ~select:(elf_slots_at [0x1fc90; 0x1fc98; 0x1fca0]) THEN
  MAP_EVERY (fun th -> FIRST_ASSUM(fun a ->
      try ASSUME_TAC (MATCH_MP th a) with Failure _ -> NO_TAC)) IU_MASK_FACTS THEN
  MAP_EVERY (fun k -> FIRST_ASSUM(fun th ->
      if can (term_match [] `read (memory :> bytelist(a,LENGTH l)) s = l`) (concl th)
      then MP_TAC(MATCH_MP READ_MEMORY_BYTELIST_EL
             (CONJ th (let hyp = if big then `5 <= LENGTH(l:byte list)`
                         else subst [num len,`k:num`] `LENGTH(l:byte list) = k` in
                       MP (ARITH_RULE(mk_imp(hyp,subst [num k,`k:num`]
                             `k < LENGTH(l:byte list)`))) (ASSUME hyp))))
      else NO_TAC) THEN
      REWRITE_TAC[WORD_ADD_0] THEN DISCH_TAC)
     (if len = 0 then [] else 0--(len-1)) THEN
  ARM_BSTEP_RUN_GEN_TAC ~kill:IU_KILL_TAC ~norm:IU_MASK_NORM_TAC
    ~calls:[`word(pc + 27184):int64`, IU_DAT_CALL_TAC IU_EXEC] IU_EXEC 1 IU_LEAF;;

(* The setup of the goal: the frame clauses of the decompressor in the form  *)
(* of the stores (from the SP of the frame).                                 *)

let IU_SETUP_TAC : tactic =
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; ALL; PAIRWISE] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ENSURES_FRAME_SPLIT_TAC
   `MAYCHANGE [memory :> bytes(word_sub sp (word 48),41)]`
   `MAYCHANGE [memory :> bytes(word_add (word_sub sp (word 144)) (word 96),41)]` THEN
  ENSURES_FRAME_SPLIT_TAC
   `MAYCHANGE [memory :> bytes(word_sub sp (word 7),5)]`
   `MAYCHANGE [memory :> bytes(word_add (word_sub sp (word 144)) (word 137),5)]` THEN
  SUBGOAL_THEN `val(word(LENGTH(l:byte list)):int64) = LENGTH l` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC];;

let SNAPPY_INTERNAL_UNCOMPRESS_VALIDATOR_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_INTERNAL_UNCOMPRESS_VALIDATOR_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  IU_SETUP_TAC THEN
  ASM_CASES_TAC `LENGTH(l:byte list) = 0` THENL [IU_CASE_TAC (Some 0); ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(l:byte list) = 1` THENL [IU_CASE_TAC (Some 1); ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(l:byte list) = 2` THENL [IU_CASE_TAC (Some 2); ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(l:byte list) = 3` THENL [IU_CASE_TAC (Some 3); ALL_TAC] THEN
  ASM_CASES_TAC `LENGTH(l:byte list) = 4` THENL [IU_CASE_TAC (Some 4); ALL_TAC] THEN
  SUBGOAL_THEN `5 <= LENGTH(l:byte list)` ASSUME_TAC THENL
   [W(fun (asl,w) -> MAP_EVERY (MP_TAC o snd) (filter (fun (_,th) ->
       can (term_match [] `~(LENGTH(l:byte list) = k)`) (concl th)) asl)) THEN
    ARITH_TAC;
    IU_CASE_TAC None]);;
