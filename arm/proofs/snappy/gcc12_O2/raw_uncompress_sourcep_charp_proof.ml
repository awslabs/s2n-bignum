(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/snappy/gcc12_O2/raw_uncompress_sourcep_charp_spec.ml";;
needs "arm/proofs/snappy/array_writer.ml";;

(*** One case per input length L = 0, 1, 2, 3, 4 and L >= 5; the branches  ***)
(*** on the header bytes are split by ARM_BSTEP_RUN_GEN_TAC (Peek and Skip  ***)
(*** are stepped through the vtable). At the call of DecompressAllTags the  ***)
(*** path gives h, the number of header bytes (ptr_ = inp + h), the header  ***)
(*** m (SNAPPY_VARINT_BYTES and the byte tests) and the 32-bit value in w20 ***)
(*** (bit-blasting); the contract is instantiated with the rest of the      ***)
(*** stream after h bytes and weakened from (out, m) to (out, outlen). After ***)
(*** the call the reads in its postcondition are named (BSTEP_GHOST_READS)  ***)
(*** and the cases of eof_ split, so that the facts cross the rest.         ***)

(* ------------------------------------------------------------------------- *)
(* A byte of the image, from the 16-byte word that contains it.              *)
(* ------------------------------------------------------------------------- *)

let SNAPPY_IMAGE_BYTE_RULE =
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

let RU_MASK_FACTS =
  let addr k = WORD_RULE (subst [mk_small_numeral k,`k:num`;
                                 mk_small_numeral (0x7dc0 + k),`j:num`]
    `word_add (word k) (word_add (word pc) (word 32192)):int64 =
     word_add (word pc) (word j)`) in
  flat (map (fun k ->
    let th = SNAPPY_IMAGE_BYTE_RULE (0x7dc0 + k) in
    if k = 0 then [th] else [th; REWRITE_RULE[GSYM(addr k)] th])
   [0;7;14;21;28]);;

(* op_limit_min_slop_ as the code computes it from the header value.         *)

let RU_QLT = prove
 (`!(a:int64) n h. val a + n < 2 EXP 64 /\ h <= n
                   ==> val(word_add a (word h)) + (n - h) < 2 EXP 64`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `h MOD 2 EXP 64 = h` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(val(a:int64) + h) MOD 2 EXP 64 = val a + h` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let RU_WORD_SUB_SUB = prove
 (`!x:int64 a b. word_sub (word_sub x (word a)) (word b) = word_sub x (word(a + b))`,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let RU_WORD_SUB_NUM = prove
 (`!n h. h <= n ==> word_sub (word n) (word h):int64 = word(n - h)`,
  SIMP_TAC[WORD_SUB]);;

let RU_WORD_ZX_32 = prove
 (`!m. m < 2 EXP 32 ==> word_zx(word m:int32):int64 = word m`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `m < 2 EXP 32 ==> m < 2 EXP 64`]);;

let RU_MIN_SLOP = prove
 (`!m. m < 2 EXP 32
       ==> word_zx (if ~(&(val (word m:int32)) - &63:int =
                         &(val(word_sub (word m:int32) (word 63))) /\
                         ~(val(word_sub (word m:int32) (word 63)) = 0))
                    then word m else word 63:int32):int64 = word(MIN m 63)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word m:int32`; `63`] WORD_CMP_HI_INT) THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `val(word m:int32) = m` SUBST1_TAC THENL
   [ASM_SIMP_TAC[VAL_WORD; DIMINDEX_32; MOD_LT]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `MIN m 63 = m` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[RU_WORD_ZX_32]];
    SUBGOAL_THEN `MIN m 63 = 63` SUBST1_TAC THENL
     [ASM_ARITH_TAC; CONV_TAC WORD_REDUCE_CONV]]);;

(* ------------------------------------------------------------------------- *)
(* Rules for the branches on the header bytes, as bstep leaves them.         *)
(* ------------------------------------------------------------------------- *)

let RU_BYTE_RULES = [BIT7_WORD_ZX_BYTE];;

(* From the tests of a byte, the facts val b < 16 or ~(val b < 16).          *)

let RU_BYTE5_TAC : tactic =
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

(* Close a case of a branch that the facts contradict: by reduction of its   *)
(* condition (e.g. a test of a word_and with 0), or by arithmetic.           *)

(* The bytes of the masks as the code addresses them, inside the image.     *)

let RU_MASK_SUBSETS =
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

(* Before the ldrb w0, [x19, x22] (0x50b8): the bytes of                    *)
(* LeftShiftOverflows_masks in the current state, also with the address in *)
(* the form of the code (bstep does not carry facts with such addresses     *)
(* across the steps).                                                       *)

let RU_MASK_NORM_TAC : tactic =
  W(fun (asl,w) ->
    let s = rand w in
    try
      let pcth = snd(find (fun (_,th) -> match concl th with
          Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),s1)),_) ->
            c = `PC` && s1 = s
        | _ -> false) asl) in
      if rand(concl pcth) <> `word(pc + 20664):int64` then ALL_TAC else
      let a = snd(find (fun (_,th) -> match concl th with
          Comb(Comb(Comb(Const("aligned_bytes_loaded",_),s1),_),_) -> s1 = s
        | _ -> false) asl) in
      MAP_EVERY (fun th -> ASSUME_TAC(MATCH_MP th a)) RU_MASK_FACTS
    with Failure _ -> ALL_TAC);;

let RU_KILL_TAC : tactic =
  fun (asl,w) ->
    match asl with
      [] -> ALL_TAC (asl,w)
    | (_,cth0)::rest ->
        let masks = flat (map (fun (_,a) ->
            mapfilter (fun th -> MATCH_MP th a) RU_MASK_FACTS) asl) in
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
          (* without the disequalities, which make ARITH_TAC split cases *)
          let rest' = filter (fun (_,th) -> let c = concl th in
                        not(is_neg c && is_eq(dest_neg c))) rest in
          let th = TAC_PROOF((rest',nc),BSTEP_ARITH_DECIDE_TAC ~rws:[]) in
          (if is_neg c then CONTR_TAC(MP (NOT_ELIM cth) th)
           else CONTR_TAC(MP (NOT_ELIM th) cth)) (asl,w)
        with Failure _ ->
          (if concl cth = concl cth0 then ALL_TAC
           else POP_ASSUM(K ALL_TAC) THEN ASSUME_TAC cth) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* The call of DecompressAllTags, after the header: h header bytes read,     *)
(* the header value m in w20.                                                *)
(* ------------------------------------------------------------------------- *)

let RU_DAT = SNAPPY_DECOMPRESSOR_DECOMPRESS_ALL_TAGS_SNAPPY_ARRAY_WRITER_GCC12_O2_IMAGE_SUBROUTINE_SAFE;;

let ru_find_fact ?(vars=[]) pat asl =
  let lcs = subtract (frees pat) vars in
  snd(find (fun (_,th) -> can (term_match lcs pat) (concl th)) asl);;

(* After the call: the cases of eof_ (the bool ok of the postcondition).    *)

let RU_EOF_CASES_TAC : tactic =
  W(fun (asl,w) ->
    let th = ru_find_fact ~vars:[`a:int64`; `s:armstate`; `b:bool`] `read (memory :> bytes8 a) s = word(bitval b)` asl in
    let v = rand(rand(rand(concl th))) in
    ASM_CASES_TAC v THEN
    POP_ASSUM(fun c -> RULE_ASSUM_TAC(REWRITE_RULE[c; BITVAL_CLAUSES]) THEN
                       ASSUME_TAC c));;

let RU_DAT_CALL_TAC exec =
  fun i ->
   ((RULE_ASSUM_TAC(REWRITE_RULE RU_BYTE_RULES) THEN RU_BYTE5_TAC) THEN
    W(fun (asl,w) ->
      let s = rand w in
      let ev t = arm_bstep_eval asl s t in
      (* the header bytes read: ptr_ of the source is inp + h *)
      let pth = ru_find_fact ~vars:[`h:num`] (vsubst [s,`s:armstate`]
        `read (memory :> bytes64 (word_add src (word 8))) s =
         word_add inp (word h)`) asl in
      let h = rand(rand(rand(concl pth))) in
      let facts = map (fun th -> if is_eq(concl th) then EQT_INTRO th else th)
                   (filter (fun th -> let c = concl th in
                            not(vfree_in s c) && not(is_forall c) &&
                            not(is_imp c) &&
                            not(can (find_term is_abs) c))
                         (map snd asl)) in
      let vth = REWRITE_CONV (SNAPPY_VARINT_BYTES :: facts)
                  `snappy_varint (l:byte list)` in
      let mexpr = lhand(rand(rand(concl vth))) in
      (* the 32-bit header value in w20, from op_limit_ *)
      let lth = ru_find_fact ~vars:[`x:int32`] (vsubst [s,`s:armstate`]
        `read (memory :> bytes64 (word_add (word_sub sp (word 176))
                                           (word 112))) s =
         word_add out (word_zx (x:int32))`) asl in
      let w32 = rand(rand(rand(concl lth))) in
      let wgoal = mk_eq(w32,mk_comb(`word:num->int32`,mexpr)) in
      let wth = TAC_PROOF((asl,wgoal), REWRITE_TAC[word_jshl; VAL_WORD; DIMINDEX_32] THEN
                    CONV_TAC NUM_REDUCE_CONV THEN SNAPPY_HEADER_WORD_TAC) in
      let mlt = CONJUNCT1(MATCH_MP SNAPPY_VARINT_SOME vth) in
      ASSUME_TAC vth THEN ASSUME_TAC wth THEN ASSUME_TAC mlt THEN
      ABBREV_TAC (mk_eq(`m:num`,mexpr))) THEN
    W(fun (asl,w) ->
      let s = rand w in
      let ev t = arm_bstep_eval asl s t in
      let pth = ru_find_fact ~vars:[`h:num`] (vsubst [s,`s:armstate`]
        `read (memory :> bytes64 (word_add src (word 8))) s =
         word_add inp (word h)`) asl in
      let h = rand(rand(rand(concl pth))) in
      let wth = snd(find (fun (_,th) -> is_eq(concl th) && rand(concl th) = `word m:int32`) asl) in
      let mlt = snd(find (fun (_,th) -> concl th = `m < 2 EXP 32`) asl) in
      let vth = ru_find_fact ~vars:[`r:byte list`] `snappy_varint (l:byte list) = SOME(m,r)` asl in
      let rest = rand(rand(rand(concl vth))) in
      let cf = snd(find (fun (_,th) -> let c = concl th in
                 c = `5 <= LENGTH(l:byte list)` ||
                 (is_eq c && lhand c = `LENGTH(l:byte list)` &&
                  is_numeral(rand c))) asl) in
      let hle = MP (ARITH_RULE(mk_imp(concl cf,
                      mk_binary "<=" (h,`LENGTH(l:byte list)`)))) cf in
      let mle = MP (SPEC `m:num` (ru_find_fact `!m. snappy_header l = SOME m ==> m <= outlen` asl))
                   (REWRITE_RULE[GSYM SNAPPY_HEADER] (EXISTS (mk_exists(`r:byte list`,
                      subst [`r:byte list`,rest] (concl vth)),rest) vth)) in
      let wzx = MP (SPEC `m:num` RU_WORD_ZX_32) mlt
      and slop = MP (SPEC `m:num` RU_MIN_SLOP) mlt in
      let left_th = ru_find_fact ~vars:[`x:int64`] (vsubst [s,`s:armstate`]
        `read (memory :> bytes64 (word_add src (word 16))) s = x`) asl in
      let lv = rand(concl left_th) in
      let lvth =
        let th1 = (REWRITE_CONV[RU_WORD_SUB_SUB] THENC NUM_REDUCE_CONV) lv in
        let th2 = MP (SPECL [`LENGTH(l:byte list)`; h] RU_WORD_SUB_NUM) hle in
        TRANS th1 th2 in
      let bl = ru_find_fact (vsubst [s,`s:armstate`]
        `read (memory :> bytelist(inp,LENGTH(l:byte list))) s = l`) asl in
      let blth = MATCH_MP READ_BYTELIST_SUFFIX (CONJ bl hle) in
      let qn = subst [h,`h:num`] `word_add (inp:int64) (word h)` in
      let ln = subst [h,`h:num`] `LENGTH(l:byte list) - h` in
      let novs = mapfilter (fun (_,th) -> match concl th with
          Comb(Comb(Const("nonoverlapping",_),p1),_)
            when p1 = `inp:int64,LENGTH(l:byte list)` ->
            MATCH_MP NONOVERLAPPING_SUFFIX (CONJ th hle)
        | _ -> fail()) asl in
      let nov_out =
        let th = ru_find_fact `nonoverlapping (inp:int64,LENGTH(l:byte list)) (out,outlen)` asl in
        MATCH_MP NONOVERLAPPING_SUFFIX_PREFIX (CONJ th (CONJ hle mle)) in
      let outnovs = mapfilter (fun (_,th) -> match concl th with
          Comb(Comb(Const("nonoverlapping",_),p1),_)
            when p1 = `out:int64,outlen:num` ->
            MATCH_MP NONOVERLAPPING_PREFIX (CONJ th mle)
        | _ -> fail()) asl in
      let srcout = MATCH_MP NONOVERLAPPING_PREFIX_RIGHT
        (CONJ (ru_find_fact `nonoverlapping (src:int64,24) (out,outlen)` asl) mle) in
      let outlt = ARITH_RULE(mk_imp(mk_conj(`val(out:int64) + outlen + 64 < 2 EXP 64`,concl mle),
                    `val(out:int64) + m < 2 EXP 64`)) in
      let outlt = MP outlt (CONJ (ASSUME `val(out:int64) + outlen + 64 < 2 EXP 64`) mle) in
      let qlt = MP (SPECL [`inp:int64`; `LENGTH(l:byte list)`; h] RU_QLT)
                  (CONJ (ASSUME `val(inp:int64) + LENGTH(l:byte list) < 2 EXP 64`) hle) in
      let sub = ISPEC `out:int64` (MATCH_MP MEMRANGE_PREFIX_SUBSET mle) in
      let hk = MP (ARITH_RULE(mk_imp(concl hle,
                 subst [h,`h:num`] `h + LENGTH(l:byte list) - h <= LENGTH l`))) hle in
      let insub = ISPEC `inp:int64` (MATCH_MP MEMRANGE_OFFSET_SUBSET hk) in
      let args = [ev `read events s`; ev `read X0 s`; ev `read X1 s`; `src:int64`;
                  qn; rest; `word 0:int64`; `out:int64`; `m:num`; `pc:num`; `rw:num`;
                  ev `read SP s`; ev `read X30 s`;
                  ev `read X19 s`; ev `read X20 s`; ev `read X21 s`; ev `read X22 s`;
                  ev `read X23 s`; ev `read X24 s`; ev `read X25 s`; ev `read X26 s`;
                  ev `read X27 s`; ev `read X28 s`; ev `read X29 s`;
                  `ea:int64`; `el:num`; `ev:num`] in
      let args = map (fun t -> rhs(concl(REWRITE_CONV[wth; wzx; slop; lvth] t))) args in
      let dth = CONV_RULE (REWRITE_CONV[SNAPPY_LENGTH_SUB_LIST_SUFFIX] THENC
                           DEPTH_CONV WORD_ADD_ADD_NUM_CONV)
                  (SPECL args RU_DAT) in
      RULE_ASSUM_TAC(REWRITE_RULE[wth; wzx; slop; lvth]) THEN
      MAP_EVERY ASSUME_TAC ([blth; nov_out; srcout; outlt; qlt; sub; insub; mle;
                             ISPEC `inp:int64` (MATCH_MP MEMRANGE_PREFIX_SUBSET hle)] @ novs @ outnovs) THEN
      (* see BSTEP_DROP_NUM_DISEQS_TAC *)
      BSTEP_DROP_NUM_DISEQS_TAC THEN
      (ARM_BSTEP_CONTRACT_SUB_TAC ~keep:(bstep_keep_not_bytes8_at `inp:int64`)
         [sub] exec dth []
         ("s" ^ string_of_int i)) THEN
      BSTEP_GHOST_READS_TAC "ru" THEN
      RU_EOF_CASES_TAC)), 1;;

let RU_FAIL_LEAF : tactic =
  BSTEP_FINAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE RU_BYTE_RULES) THEN RU_BYTE5_TAC THEN
  SUBGOAL_THEN `snappy_varint (l:byte list) = NONE` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SNAPPY_VARINT_BYTES] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[snappy_decode; snappy_bind; option_DISTINCT;
                  BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[WORD_RULE `word_add (word_sub sp (word 176)) (word 176):int64 = sp`] THEN
  MEMACCESS_INSET_TAC;;


let RU_SUCCESS_LEAF : tactic =
  BSTEP_FINAL_TAC THEN
  REWRITE_TAC[snappy_decode] THEN
  W(fun (asl,w) ->
    let vth = ru_find_fact ~vars:[`r:byte list`] `snappy_varint (l:byte list) = SOME(m,r)` asl in
    REWRITE_TAC[vth; snappy_bind]) THEN
  TRY(W(fun (asl,w) ->
    let iff = ru_find_fact ~vars:[`p:bool`; `r:byte list`; `ob:byte list`] `(p:bool) <=> ~(snappy_decode_tags m r ob = NONE)` asl in
    REWRITE_TAC[GSYM iff])) THEN
  REWRITE_TAC[VAL_EQ_0; WORD_SUB_EQ_0; BITVAL_CLAUSES] THEN
  CONV_TAC WORD_REDUCE_CONV THEN
  REWRITE_TAC[WORD_RULE `word_add (word_sub sp (word 176)) (word 176):int64 = sp`] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC WORD_REDUCE_CONV THEN NO_TAC) THEN
  TRY(ASM_REWRITE_TAC[] THEN CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN CONV_TAC WORD_REDUCE_CONV THEN
      NO_TAC) THEN
  TRY(W(fun (asl,w) ->
        let x0 = snd(find (fun (_,th) -> is_eq(concl th) &&
                   lhand(concl th) = lhand w) asl) in
        REWRITE_TAC[x0; VAL_EQ_0; WORD_SUB_EQ_0] THEN
        COND_CASES_TAC THEN POP_ASSUM(fun c -> REWRITE_TAC[c; BITVAL_CLAUSES]) THEN
        CONV_TAC WORD_REDUCE_CONV) THEN NO_TAC) THEN
  TRY(X_GEN_TAC `x:byte list` THEN DISCH_TAC THEN
      W(fun (asl,w) ->
        let dth = ru_find_fact ~vars:[`r:byte list`] `snappy_decode_tags m r [] = SOME (x:byte list)` asl in
        let lth = CONJUNCT1(MATCH_MP SNAPPY_DECODE_TAGS_SOME dth) in
        let uth = ru_find_fact ~vars:[`r:byte list`; `v:byte list`] `!x:byte list. snappy_decode_tags m r [] = SOME x ==> (v:byte list) = x` asl in
        REWRITE_TAC[lth] THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC uth THEN ACCEPT_TAC dth) THEN NO_TAC) THEN
  W(fun (asl,w) ->
    let s = rand(lhand(lhand(snd(dest_exists w)))) in
    let evth = snd(find (fun (_,th) -> is_eq(concl th) &&
      lhand(concl th) = mk_comb(`read events:armstate->(uarch_event)list`,s)) asl) in
    REWRITE_TAC[evth]) THEN
  MEMACCESS_INSET_TAC;;

let RU_LEAF : tactic =
  W(fun (asl,w) ->
    if exists (fun (_,th) -> can (term_match [] `snappy_varint (l:byte list) = SOME x`) (concl th)) asl
    then RU_SUCCESS_LEAF
    else RU_FAIL_LEAF);;

let exec = SNAPPY_RAW_UNCOMPRESS_SOURCEP_CHARP_GCC12_O2_EXEC;;

let RU_CASE_TAC lk =
  let big = (lk = None) in
  let len = match lk with Some k -> k | None -> 5 in
  let num k = mk_small_numeral k in
  (if big then MAP_EVERY (fun k -> SUBGOAL_THEN (subst [num k,`k:num`] `~(LENGTH(l:byte list) = k)`) ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) (0--4)
   else MAP_EVERY (fun k -> if k = len then ALL_TAC else SUBGOAL_THEN (subst [num k,`k:num`] `~(LENGTH(l:byte list) = k)`) ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) (0--5)) THEN
  (if big then
     ASSUME_TAC(MP (ISPECL [`inp:int64`; `5`; `LENGTH(l:byte list)`]
                      MEMRANGE_PREFIX_SUBSET)
                   (ASSUME `5 <= LENGTH(l:byte list)`))
   else ALL_TAC) THEN
  MAP_EVERY ASSUME_TAC RU_MASK_SUBSETS THEN
  ENSURES_INIT_TAC "s0" THEN
  ELF_RELOCATED_DATA_TAC ~defs:[snappy_libsnappy_gcc12_O2_relocated]
           ~select:(elf_slots_at [0x1fc90; 0x1fc98; 0x1fca0]) THEN
  MAP_EVERY (fun th -> FIRST_ASSUM(fun a -> try ASSUME_TAC (MATCH_MP th a) with Failure _ -> NO_TAC)) RU_MASK_FACTS THEN
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
  ARM_BSTEP_RUN_GEN_TAC ~kill:RU_KILL_TAC ~norm:RU_MASK_NORM_TAC
    ~calls:[`word(pc + 25504):int64`, RU_DAT_CALL_TAC exec] exec 1 RU_LEAF;;

let SNAPPY_RAW_UNCOMPRESS_SOURCEP_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (SNAPPY_RAW_UNCOMPRESS_SOURCEP_CHARP_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              ALLPAIRS; ALL] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* the decompressor at sp - 48 is 8-aligned (DecompressAllTags needs it) *)
  ASSUME_TAC(MATCH_MP (MATCH_MP ALIGNED_WORD_WEAKEN
    (EQT_ELIM(DIVIDES_CONV `8 divides 16`))) (ASSUME `aligned 16 (sp:int64)`)) THEN
  SUBGOAL_THEN `val(word(LENGTH(l:byte list)):int64) = LENGTH l` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_EQ_EQ; DIMINDEX_64] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  (* the cases of L, each with only its own fact about L (RU_CASE_TAC adds  *)
  (* the disequalities that the code's branches need)                      *)
  MP_TAC(ARITH_RULE `LENGTH(l:byte list) = 0 \/ LENGTH l = 1 \/ LENGTH l = 2 \/
                     LENGTH l = 3 \/ LENGTH l = 4 \/ 5 <= LENGTH l`) THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC)) THENL
   [RU_CASE_TAC (Some 0); RU_CASE_TAC (Some 1); RU_CASE_TAC (Some 2);
    RU_CASE_TAC (Some 3); RU_CASE_TAC (Some 4); DISCH_TAC THEN RU_CASE_TAC None]);;
