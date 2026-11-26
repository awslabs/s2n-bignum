(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tactics and lemmas shared by the proofs of verify_internal (44, 65, 87):  *)
(* the normalization of the addresses of the frame from its lowest address  *)
(* rsp0 - 1654 for the memory-safety checks, the discharge of the events of *)
(* a segment, the precondition of a region lemma or callee, the chunks of   *)
(* mu and of tr, and the template of the whole function. See                *)
(* verify_internal_44_proof.ml for their use.                               *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_verify.ml";;

let VM_ARGS =
  "sig m mlen pre prelen pk ext sigb pkb M PRE' mf mc pc rsp0";;

let VM_LAMBDA =
  "\\(sig:int64) (m:int64) (mlen:num) (pre:int64) (prelen:num) (pk:int64) " ^
  "(ext:int32) (sigb:num->byte) (pkb:num->byte) (M:num) (PRE':num) " ^
  "(mf:int64) (mc:int64) (pc:num) (rsp0:int64).";;

(* The memory-safety checks compare regions at offsets of rsp0, below it for
   the stacks of the callees: they are stated from the lowest address of the
   frame, rsp0 - 1654, as the containment arithmetic needs offsets that do
   not wrap around. Used as memaccess_inbounds_normalize_tac in this proof,
   with the generalization of the bytes in byte-indexed addresses. *)
let VM_RSP0_NORM_TAC =
  W(fun (asl,w) ->
    if not (free_in `rsp0:int64` w) then ALL_TAC else
    let fb = mk_var("fb_vm",`:int64`) in
    REWRITE_TAC[WORD_RULE `word_sub (word_sub (x:int64) (word a)) (word b) =
                           word_sub x (word (a + b))`] THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    ABBREV_TAC (mk_eq(fb, `word_sub rsp0 (word 1654):int64`)) THEN
    SUBGOAL_THEN (mk_eq(`rsp0:int64`,
                        mk_comb(mk_comb(`word_add:int64->int64->int64`,fb),
                                `word 1654:int64`))) SUBST1_TAC THENL
     [EXPAND_TAC "fb_vm" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    CONV_TAC(REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))));;

let VM_NORM_TAC = VM_RSP0_NORM_TAC THEN VAL_BYTE_GEN_TAC;;

(* The same for the whole goal and the assumptions, once the events are
   matched (the template no longer has rsp0 as an argument then). *)
let VM_GLOBAL_NORM_TAC =
  let sub = WORD_RULE `word_sub (word_sub (x:int64) (word a)) (word b) =
                       word_sub x (word (a + b))` in
  let norm = REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) in
  RULE_ASSUM_TAC(CONV_RULE(REWRITE_CONV[sub] THENC DEPTH_CONV NUM_ADD_CONV)) THEN
  REWRITE_TAC[sub] THEN CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
  ABBREV_TAC `fb_vm = word_sub rsp0 (word 1654):int64` THEN
  SUBGOAL_THEN `rsp0 = word_add fb_vm (word 1654):int64` SUBST_ALL_TAC THENL
   [EXPAND_TAC "fb_vm" THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
  RULE_ASSUM_TAC(CONV_RULE norm) THEN CONV_TAC norm;;

(* the frame, with the same normalization *)
let VM_MAYCHANGE_TAC =
  W(fun (asl,w) -> if maychange_term w then ALL_TAC else NO_TAC) THEN
  VM_GLOBAL_NORM_TAC THEN
  FIRST_X_ASSUM(fun th -> if maychange_term (concl th) && not(is_forall(concl th))
                          then MP_TAC th else NO_TAC) THEN
  VAL_BYTE_GEN_TAC THEN DISCH_TAC THEN MONOTONE_MAYCHANGE_TAC;;

(* SEG_DISCHARGE_TAC (inline_verify.ml) with that normalization *)
let VM_DISCHARGE_TAC =
  let beta_all =
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) in
  let select_tac =
    W(fun (asl,w) ->
      let conds = map (fun t -> rand(rator(rator t))) (find_terms is_cond w) in
      let ths = mapfilter (fun (_,th) ->
        let c = concl th in
        if mem c conds then EQT_INTRO th
        else if is_neg c && mem (rand c) conds then EQF_INTRO th
        else failwith "") asl in
      REWRITE_TAC ths) in
  let is_vdef th = let c = concl th in
    is_eq c && is_var(lhs c) && type_of(lhs c) = `:(uarch_event)list` in
  let is_meminb v th = let c = concl th in
    (match strip_comb c with
       Const("memaccess_inbounds",_),(e::_) -> e = v
     | _ -> false) in
  let split_tac =
    W(fun (asl,w) ->
      let defs = filter is_vdef (map snd asl) in
      MAP_EVERY (fun dth ->
        let v = lhs(concl dth) in
        MAP_EVERY (fun (_,mth) ->
          if is_meminb v mth then
            STRIP_ASSUME_TAC(REWRITE_RULE[MEMACCESS_INBOUNDS_APPEND] (REWRITE_RULE[dth] mth))
          else ALL_TAC) asl) defs) in
  REWRITE_TAC[ENUMERATEL_ADD1] THEN beta_all THEN select_tac THEN
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    if is_conj w then
      CONJ_TAC THENL
       [(REWRITE_TAC[APPEND_ASSOC] THEN NO_TAC) ORELSE FULL_UNIFY_F_EVENTS_TAC;
        ALL_TAC]
    else ALL_TAC) THEN
  beta_all THEN
  REWRITE_TAC[NOT_LT] THEN RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  VM_GLOBAL_NORM_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
  REWRITE_TAC[GSYM APPEND_ASSOC] THEN
  split_tac THEN
  REWRITE_TAC[MEMACCESS_INBOUNDS_APPEND] THEN REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   BYTE_IDX_DISCHARGE_TAC DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

(* The events of a segment, l = APPEND (f_ev ...) old with old in l after
   concrete events and callee events: l as APPEND x old (x is l with old
   replaced by []), and the unification of f_ev ... with x. *)
let VM_TAIL_UNIFY_TAC (asl,w) =
  let l,r = dest_eq w in
  let old = rand r in
  if not (is_var old) || not (free_in old l) then failwith "VM_TAIL_UNIFY_TAC" else
  let x0 = subst [mk_mconst("NIL",type_of old),old] l in
  let x = rhs(concl(PURE_REWRITE_CONV[APPEND_NIL; CONJUNCT1 APPEND] x0)) in
  let th = prove(mk_eq(l,mk_comb(mk_comb(rator(rator r),x),old)),
                 REWRITE_TAC[APPEND; GSYM APPEND_ASSOC; APPEND_NIL]) in
  (GEN_REWRITE_TAC LAND_CONV [th] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   UNIFY_F_EVENTS_TAC) (asl,w);;

(* VERIF_EVENTS_TAC olds with that normalization *)
let VM_EVENTS_TAC olds =
  let beta_all =
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE(TOP_DEPTH_CONV BETA_CONV)) in
  let select_tac =
    W(fun (asl,w) ->
      let conds = map (fun t -> rand(rator(rator t)))
                      (find_terms is_cond w) in
      let ths = mapfilter (fun (_,th) ->
        let c = concl th in
        if mem c conds then EQT_INTRO th
        else if is_neg c && mem (rand c) conds then EQF_INTRO th
        else failwith "") asl in
      REWRITE_TAC ths) in
  REWRITE_TAC[ENUMERATEL_ADD1] THEN beta_all THEN select_tac THEN
  VERIF_META_EXISTS_TAC THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  CONJ_TAC THENL
   [W(fun (asl,w) ->
      REWRITE_TAC(mapfilter (fun (_,th) ->
        if VERIF_IS_E2_EQ th then th else fail()) asl)) THEN
    ((REWRITE_TAC[APPEND_ASSOC] THEN NO_TAC) ORELSE FULL_UNIFY_F_EVENTS_TAC ORELSE
     VM_TAIL_UNIFY_TAC);
    ALL_TAC] THEN
  beta_all THEN VERIF_OLD_EVENTS_TAC THEN VM_GLOBAL_NORM_TAC THEN
  VERIF_EMPTY_REGIONS_TAC THEN
  CONV_TAC(VERIF_SPLIT_CONV olds) THEN REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   BYTE_IDX_DISCHARGE_TAC DISCHARGE_MEMACCESS_INBOUNDS_TAC);;

let VM_MC = mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc;;

let VM_ALLOWED =
  [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`; `pk:int64`;
   `ext:int32`; `sigb:num->byte`; `pkb:num->byte`; `M:num`; `PRE':num`;
   `mf:int64`; `mc:int64`; `pc:num`; `rsp0:int64`];;

(* The events so far as APPEND e_tail e, when they have too many chains of
   CONS and APPEND for FULL_EXISTS_E2_TAC: e_tail is the events with e
   replaced by []. *)
let VM_EVENTS_PRE_TAC (asl,w) =
  let l,r = dest_eq w in
  let et = lhand r and ev = rand r in
  let x = subst [mk_mconst("NIL",type_of ev),ev] l in
  let th = prove(mk_eq(l,mk_comb(mk_comb(rator(rator r),x),ev)),
                 REWRITE_TAC[APPEND; GSYM APPEND_ASSOC; APPEND_NIL]) in
  UNIFY_ACCEPT_TAC [et] th (asl,w);;

(* The precondition of a region lemma or callee, after the parts that
   X86_SUBROUTINE_SIM_TAC proves: facts whose addresses or values need
   normalization, then the events. *)
let VM_ZX_JOIN = WORD_BLAST `word_zx (word_join (x:int128) (y:int128):int256):int128 = y`;;

let VM_PRE_TAC allowed =
  REPEAT CONJ_TAC THEN
  TRY(REWRITE_TAC[WORD_RULE `word_add (word_sub (x:int64) (word 8)) (word 8) = x`;
                  WORD_RULE `word_add (word_sub (x:int64) (word 8)) (word 16) =
                             word_add x (word 8)`] THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC(REPEATC(CHANGED_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))) THEN
      ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(FIRST_ASSUM(fun eq -> GEN_REWRITE_TAC LAND_CONV [eq]) THEN
      CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(FIRST_ASSUM(fun eq -> GEN_REWRITE_TAC LAND_CONV [eq]) THEN
      CONV_TAC WORD_REDUCE_CONV THEN NO_TAC) THEN
  TRY(FIRST_ASSUM(fun eq -> GEN_REWRITE_TAC LAND_CONV [eq]) THEN
      REPEAT AP_TERM_TAC THEN ARITH_TAC) THEN
  TRY(REPEAT AP_TERM_TAC THEN ARITH_TAC THEN NO_TAC) THEN
  TRY(REWRITE_TAC[XMM2; XMM3; XMM4; XMM5; XMM6; READ_COMPONENT_COMPOSE;
                  READ_ZEROTOP_128] THEN
      ASM_REWRITE_TAC[VM_ZX_JOIN] THEN CONV_TAC WORD_REDUCE_CONV THEN NO_TAC) THEN
  (FULL_EXISTS_E2_TAC (ref allowed) ORELSE VM_EVENTS_PRE_TAC);;

let VM_ASSUME_TAC th name = ASSUME_CALLEE_SAFETY_TAILED_TAC th name;;

(* the 4 chunks of the 64 bytes of mu at m, when ext is nonzero *)
let VM_M_CHUNKS_TAC =
  SUBGOAL_THEN `64 <= mlen` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[GSYM VAL_EQ_0] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun i ->
    MP_TAC(SPECL [`m:int64`; `mlen:num`; `M:num`; mk_small_numeral i;
                  `s0:x86state`] VERIF_BYTES128_OF_BYTES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[WORD_ADD_0; EXP; DIV_1] o
               CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV))) [0;1;2;3];;

let VM_MU_OF_CHUNKS_TAC a s =
  MP_TAC(SPECL [a; `M:num`; `4`; s] VERIF_BYTES_OF_BYTES128) THEN
  ANTS_TAC THENL
   [CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[WORD_ADD_0; DIV_1; GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN ASM_REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN DISCH_TAC];;

(* aligned 16 (word_add rsp0 (word k)) for the SSE stores at rsp0 + k *)
let VM_ALIGNED_TAC ks =
  SUBGOAL_THEN `aligned 16 (rsp0:int64)` ASSUME_TAC THENL
   [MATCH_MP_TAC(MP (ISPECL [`16`;`32`;`rsp0:int64`] ALIGNED_WORD_WEAKEN)
                    (EQT_ELIM(DIVIDES_CONV `16 divides 32`))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY (fun k ->
    SUBGOAL_THEN (subst [mk_small_numeral k,`k:num`]
                    `aligned 16 (word_add rsp0 (word k):int64)`) ASSUME_TAC THENL
     [MATCH_MP_TAC ALIGNED_WORD_ADD THEN ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN
      REWRITE_TAC[];
      ALL_TAC]) ks;;

(* the branch on ext, with the case as val ext = 0 or its negation (an
   equation ext = word 0 would be used to rewrite the arguments of the
   events) *)
let VM_EXT_PC_TAC =
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if c = `val(ext:int32) = 0` || c = `~(val(ext:int32) = 0)` then th else fail()) asl in
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read RIP s = (if b then x else y):int64`) (concl th)
      then REWRITE_RULE(ths @ [WORD_AND_REFL])
            (REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0] th) else th) THEN
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read RIP s = (if b then x else y):int64`) (concl th)
      then REWRITE_RULE(ths @ [GSYM VAL_EQ_0]) th else th));;

(* The 64 bytes of tr from the Keccak state after the absorption of pk *)

let VM_BYTES_OF_SUBWORDS = prove
 (`!(X:1600 word) n.
     8 * n <= 1600
     ==> num_of_bytelist(list_of_seq (\j. word_subword X (8 * j,8):byte) n) =
         val X MOD 2 EXP (8 * n)`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[list_of_seq; num_of_bytelist; MULT_CLAUSES; EXP; MOD_1] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  ASM_REWRITE_TAC[NUM_OF_BYTELIST_APPEND; LENGTH_LIST_OF_SEQ; num_of_bytelist;
                  MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[VAL_WORD_SUBWORD; DIMINDEX_8] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `8 + 8 * n = 8 * n + 8`; EXP_ADD] THEN
  MP_TAC(SPECL [`val(X:1600 word)`; `2 EXP (8 * n)`; `2 EXP 8`] MOD_MULT_MOD) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `256 * x = x * 256`] THEN ARITH_TAC);;

let VM_SHAKE_BYTES = prove
 (`!n P. num_of_bytelist(list_of_seq (mld_shake256_byte n P) 64) =
         val(keccak_f1600 (mld_shake256_state n P)) MOD 2 EXP 512`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`keccak_f1600 (mld_shake256_state n P)`; `64`] VM_BYTES_OF_SUBWORDS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[mld_shake256_byte; mld_keccak_squeeze_byte] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `(136 + j) DIV 136 = 1 /\ (136 + j) MOD 136 = j` (fun th -> REWRITE_TAC[th]) THENL
   [ONCE_REWRITE_TAC[ADD_SYM] THEN
    SUBGOAL_THEN `j + 136 = j + 1 * 136` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[DIV_MULT_ADD; MOD_MULT_ADD; ARITH_EQ; DIV_LT; MOD_LT;
                 ARITH_RULE `j < 64 ==> j < 136`] THEN ARITH_TAC;
    REWRITE_TAC[num_CONV `1`; keccak_squeeze]]);;

let VM_TR_CHUNK = prove
 (`!n P k. k < 4
           ==> word_subword (keccak_f1600 (mld_shake256_state n P)) (128 * k,128):int128 =
               word((num_of_bytelist(list_of_seq (mld_shake256_byte n P) 64) DIV
                     2 EXP (128 * k)) MOD 2 EXP 128)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VM_SHAKE_BYTES; word_subword; DIMINDEX_128] THEN
  AP_TERM_TAC THEN REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
  SUBGOAL_THEN `MIN 512 (128 * k + 128) = 128 * k + 128` (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let VM_RHO = `num_of_bytelist (list_of_seq (pkb:num->byte) 32)`;;

let VM_T1 = `mld_polyt1_unpack (\j. (pkb:num->byte) (32 + 320 * i + j))`;;
let VM_SHL = mk_comb(`mld_poly_shiftl`,VM_T1);;
let VM_NTT1 = mk_comb(`mld_poly_ntt`,VM_SHL);;

let VM_ALLOWED_LOOP = `front:(uarch_event)list`::`i:num`::VM_ALLOWED;;

(* VERIF_SLICE_TAC with the arithmetic of LOCAL_ARITH_TAC *)
let VM_SLICE_TAC tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[GSYM ADD_ASSOC] THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN LOCAL_ARITH_TAC);
    ALL_TAC];;

let VM_HRET = prove
 (`!omega k (b:num->byte) i.
     mld_unpack_hints_ret omega k b i = word 0 <=> mld_unpack_hints_ok omega k b i`,
  REWRITE_TAC[mld_unpack_hints_ret] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

(* The two 64-bit halves of a 128-bit fact about memory at a in state st *)
let VM_SPLIT128_TAC a st =
  let pat = subst [a,`a:int64`; st,`s:x86state`]
                  `read (memory :> bytes128 a) s = x` in
  FIRST_ASSUM(fun th ->
    if can (term_match (frees a @ [st]) pat) (concl th)
    then STRIP_ASSUME_TAC(CONV_RULE(READ_MEMORY_SPLIT_CONV 1 THENC
                                    DEPTH_CONV WORD_RED_CONV) th)
    else NO_TAC);;

let VI44_TOP_TEMPLATE =
  `\(sig:int64) (m:int64) (mlen:num) (pre:int64) (prelen:num) (pk:int64)
    (ext:int32) (sigb:num->byte) (pkb:num->byte) (M:num) (PRE':num)
    (mf:int64) (mc:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
    f_ev_all sig m mlen pre prelen pk ext sigb pkb M PRE' mf mc pc stackpointer
             returnaddress :(uarch_event)list`;;

let VI44_RSP0 = `word_add bot (word 1654):int64`;;

let VI44_TOP_ALLOWED =
  [`sig:int64`; `m:int64`; `mlen:num`; `pre:int64`; `prelen:num`; `pk:int64`;
   `ext:int32`; `sigb:num->byte`; `pkb:num->byte`; `M:num`; `PRE':num`;
   `mf:int64`; `mc:int64`; `pc:num`; `stackpointer:int64`;
   `returnaddress:int64`; `bot:int64`];;

let VI44_ALIGNED32_LEMMA = prove
 (`!x y:int64. aligned 32 y ==> aligned 32 (word_add x y) ==> aligned 32 x`,
  MESON_TAC[ALIGNED_WORD_ADD_EQ]);;
