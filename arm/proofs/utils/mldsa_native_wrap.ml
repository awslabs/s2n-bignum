(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the FULL proofs of the external API functions of sign.c in      *)
(* mldsa-native (keypair, signature, signature_extmu, verify, verify_extmu   *)
(* and the pre-hash functions), which call the internal functions, the       *)
(* domain separation prefix, mldsa_shake256 and the C library: the buffers   *)
(* that gcc aligns to 32 bytes in their stack frames, the arguments that are *)
(* NULL with length 0, the GOT entries in the preconditions of the callees,  *)
(* the postcondition of the prefix, whether signing succeeds as a function   *)
(* of what it declassifies, and the CORRECT and SAFE theorems from FULL      *)
(* theorems whose postconditions have an existential (the random bytes).     *)
(* ========================================================================= *)

needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "common/mldsa_native_sign.ml";;

(* ------------------------------------------------------------------------- *)
(* The FULL theorem of a callee as an assumption, as                         *)
(* ASSUME_CALLEE_SAFETY_TAILED_TAC does it: e split as APPEND e_tail e and   *)
(* e_tail quantified last. That proves the reordering of the quantifiers by  *)
(* MESON, which takes too long with the 18 variables of the signing          *)
(* functions; here it is by SPECL and GENL.                                  *)
(* ------------------------------------------------------------------------- *)

let MLD_WRAP_ASSUME_CALLEE_TAC =
  let append_lemma = MESON[SAFETY_APPEND_EXISTS]
    `(forall (e:((A)address_uarch_event)list). P e) <=>
      (forall e_tail e. P (APPEND e_tail e))` in
  fun th name ->
    let th' = ONCE_REWRITE_RULE[append_lemma] th in
    let f,body = dest_exists(concl th') in
    let args = fst(strip_forall body) in
    let gth = GENL (tl args @ [hd args]) (SPECL args (ASSUME body)) in
    let eth = EXISTS (mk_exists(f,concl gth),f) gth in
    ASSUME_CALLEE_SAFETY_TAC (CHOOSE (f,th') eth) name;;

(* ------------------------------------------------------------------------- *)
(* The start of a proof with a stack frame of its own, after                 *)
(* WORD_FORALL_OFFSET_TAC n: the alignment of the new stackpointer, the GOT  *)
(* entries gots (layout names) that the code reads itself in the form for    *)
(* the simulation, the canary, and the registers SP, X30 and X19 ... that    *)
(* the frame saves.                                                          *)
(* ------------------------------------------------------------------------- *)

let MLD_WRAP_FRAME_TAC n gots regs =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC (subst [mk_small_numeral n,`n:num`]
      `aligned 16 (word_add stackpointer (word n):int64)`) THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC(map (fun g -> SPECL [`pc:num`; g] WORD_ADD) gots) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  MAP_EVERY (fun r ->
    ENSURES_PRESERVED_TAC ("x"^string_of_int r^"_init")
     (parse_term("X"^string_of_int r))) regs;;

(* ------------------------------------------------------------------------- *)
(* A buffer in a stack frame aligned to 32 bytes, as gcc computes it from    *)
(* the stack pointer sp, a multiple of 16: (sp + n) AND NOT 31. For a        *)
(* numeral n, MLD_WRAP_BUFFER_RULE n proves that it is sp + k1 if sp is a    *)
(* multiple of 32 and sp + k2 if not. MLD_WRAP_SYMBUF_TAC kv rewrites that   *)
(* address of stackpointer in the assumptions to stackpointer + kv, with kv  *)
(* the abbreviation of (if aligned 32 stackpointer then k1 else k2), between *)
(* k1 and k2, so that the two cases are simulated together; the assumptions  *)
(* must include aligned 16 stackpointer. MLD_WRAP_NORM_TAC puts the          *)
(* addresses of registers relative to it as the callees' preconditions have  *)
(* them, stackpointer + (kv + n). At the end, MLD_WRAP_SYMBUF_END_TAC kv     *)
(* splits the two cases and replaces kv by k1 or k2, for the events and      *)
(* their memory regions (it does nothing if kv is not such an abbreviation). *)
(* ------------------------------------------------------------------------- *)

let MLD_WRAP_ALIGNED_16_32 = prove
 (`(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`,
  CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`x:int64`; `4`] (CONJUNCT1 WORD_AND_MASK_WORD));
    MP_TAC(ISPECL [`x:int64`; `5`] (CONJUNCT1 WORD_AND_MASK_WORD))] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 16 < 16`; ARITH_RULE `x MOD 32 < 32`;
           ARITH_RULE `x < 16 ==> x < 2 EXP 64`;
           ARITH_RULE `x < 32 ==> x < 2 EXP 64`]);;

let MLD_WRAP_BUFFER_RULE n =
  let nv = dest_small_numeral n in
  let k1 = 32 * (nv / 32) and k2 = 32 * ((nv + 16) / 32) - 16 in
  let tm = subst [n,`n:num`; mk_small_numeral k1,`k1:num`;
                  mk_small_numeral k2,`k2:num`]
   `!sp:int64. aligned 16 sp
               ==> word_and (word_add sp (word n))
                            (word 18446744073709551584) =
                   word_add sp (word(if aligned 32 sp then k1 else k2))` in
  prove(tm,
    REWRITE_TAC[MLD_WRAP_ALIGNED_16_32] THEN GEN_TAC THEN
    COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
    W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let MLD_WRAP_SYMBUF_TAC kv =
  let pat = `word_and (word_add (stackpointer:int64) (word n))
                      (word 18446744073709551584)`
  and a16 = `aligned 16 (stackpointer:int64)`
  and le = `(<=):num->num->bool` in
  W(fun (asl,w) ->
    let ths = map snd asl in
    let t = find_term (can (term_match [`stackpointer:int64`] pat))
             (end_itlist (curry mk_conj) (map concl ths)) in
    let n = rand(rand(lhand t)) in
    let ath = find (fun th -> concl th = a16) ths in
    let th = MP (SPEC `stackpointer:int64` (MLD_WRAP_BUFFER_RULE n)) ath in
    let cond = rand(rand(rhs(concl th))) in
    let k1 = rand(rator cond) and k2 = rand cond in
    let lo,hi = if dest_small_numeral k1 <= dest_small_numeral k2
                then k1,k2 else k2,k1 in
    ABBREV_TAC(mk_eq(kv,cond)) THEN
    (fun g -> SUBST_ALL_TAC
       (REWRITE_RULE[snd(find (fun (_,a) -> concl a = mk_eq(cond,kv))
                              (fst g))] th) g) THEN
    SUBGOAL_THEN (mk_conj(mk_binop le lo kv,mk_binop le kv hi))
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC (name_of kv) THEN COND_CASES_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
      ALL_TAC]);;

let MLD_WRAP_NORM_TAC =
  let pat = `read (r:(armstate,int64)component) s =
             word_add (word_add stackpointer x) y` in
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [`stackpointer:int64`] pat) (concl th)
    then CONV_RULE(RAND_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th else th);;

let MLD_WRAP_SYMBUF_END_TAC kv =
  let a32 = `aligned 32 (stackpointer:int64)` in
  let isdef th = is_eq(concl th) && rhs(concl th) = kv &&
                 is_cond(lhs(concl th)) in
  W(fun (asl,w) ->
    if not(exists (isdef o snd) asl) then ALL_TAC else
    ASM_CASES_TAC a32 THEN
    FIRST_X_ASSUM(fun th ->
      if isdef th
      then W(fun (asl,_) ->
        let cth =
          try EQT_INTRO(snd(find (fun (_,a) -> concl a = a32) asl))
          with Failure _ ->
            EQF_INTRO(snd(find (fun (_,a) -> concl a = mk_neg a32) asl)) in
        SUBST_ALL_TAC(SYM(REWRITE_RULE[cth] th)))
      else NO_TAC) THEN
    CONV_TAC(DEPTH_CONV NUM_ADD_CONV) THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NUM_ADD_CONV)) THEN
    ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Arguments that are NULL with length 0, which the callees list among the   *)
(* regions of their hypotheses and of memaccess_inbounds. MLD_WRAP_NULL_TAC  *)
(* regs adds that each region (a,n) of regs does not overlap (word 0,0), for *)
(* NONOVERLAPPING_TAC in the hypotheses of the callee, and that the 0 bytes  *)
(* at word 0 are 0, for its precondition. Regions of length 0 contain no     *)
(* access, so MLD_WRAP_EMPTY_REGIONS_TAC removes those that are literally of *)
(* length 0 from the readable regions of the memaccess_inbounds assumptions, *)
(* so that the others are the regions of the caller.                         *)
(* ------------------------------------------------------------------------- *)

let MLD_WRAP_NONOVERLAPPING_EMPTY = prove
 (`!(a:int64) n (b:int64). nonoverlapping (a,n) (b,0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_TRIVIAL THEN REWRITE_TAC[]);;

let MLD_WRAP_NULL_TAC regs =
  MAP_EVERY (fun (a,n) ->
    ASSUME_TAC(ISPECL [a; n; `word 0:int64`] MLD_WRAP_NONOVERLAPPING_EMPTY))
   regs THEN
  ASSUME_TAC(GEN `s:armstate`
   (ISPECL [`word 0:int64`; `s:armstate`; `memory`]
      READ_MEMORY_BYTES_TRIVIAL));;

let MLD_WRAP_MEMACCESS_EMPTY = prove
 (`!(e:uarch_event list) rr rr' wr.
        (!r. MEM r rr ==> SND r = 0 \/ MEM r rr') /\ ~(rr' = [])
        ==> memaccess_inbounds e rr wr ==> memaccess_inbounds e rr' wr`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC MEMACCESS_INBOUNDS_CONTAINED THEN
  REWRITE_TAC[GSYM ALL_MEM; GSYM EX_MEM; FORALL_PAIR_THM; EXISTS_PAIR_THM] THEN
  CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`a:int64`; `n:num`] THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `a:int64,n:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `~(rr':(int64#num)list = [])` THEN
      SPEC_TAC(`rr':(int64#num)list`,`l:(int64#num)list`) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; NOT_CONS_NIL] THEN
      MAP_EVERY EXISTS_TAC [`FST(h:int64#num)`; `SND(h:int64#num)`] THEN
      ASM_REWRITE_TAC[contained; CONTAINED_MODULO_TRIVIAL];
      MAP_EVERY EXISTS_TAC [`a:int64`; `n:num`] THEN
      ASM_REWRITE_TAC[contained; CONTAINED_MODULO_REFL; LE_REFL]];
    MAP_EVERY EXISTS_TAC [`a:int64`; `n:num`] THEN
    ASM_REWRITE_TAC[contained; CONTAINED_MODULO_REFL; LE_REFL]]);;

let MLD_WRAP_EMPTY_REGIONS_RULE th =
  try let c,args = strip_comb(concl th) in
      if not(is_const c && name_of c = "memaccess_inbounds") then th else
      let e,rr,wr = match args with [e;rr;wr] -> e,rr,wr | _ -> fail() in
      let els = dest_list rr in
      let els' = filter (fun r -> not(is_pair r && rand r = `0`)) els in
      if length els' = length els || els' = [] then th else
      let rr' = mk_list(els',type_of(hd els)) in
      let lth = ISPECL [e; rr; rr'; wr] MLD_WRAP_MEMACCESS_EMPTY in
      let sth = prove(lhand(concl lth),
        REWRITE_TAC[MEM; NOT_CONS_NIL] THEN REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC[]) in
      MP (MP lth sth) th
  with Failure _ -> th;;

let MLD_WRAP_EMPTY_REGIONS_TAC = RULE_ASSUM_TAC MLD_WRAP_EMPTY_REGIONS_RULE;;

(* ------------------------------------------------------------------------- *)
(* The bytes that randombytes writes into a buffer, whose address is in the  *)
(* register reg in state s: MLD_WRAP_RANDOM_TAC v reg n s abbreviates the n  *)
(* bytes at that address as v and adds v < 2 EXP (8 * n).                    *)
(* ------------------------------------------------------------------------- *)

let MLD_WRAP_READ_BYTES_BOUND = prove
 (`!a n (s:armstate) x.
        read (memory :> bytes(a,n)) s = x ==> x < 2 EXP (8 * n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]);;

let MLD_WRAP_RANDOM_TAC v reg n s =
  W(fun (asl,w) ->
    let a = rhs(concl(snd(find (fun (_,th) ->
              is_eq(concl th) && lhs(concl th) = list_mk_icomb "read" [reg; s])
             asl))) in
    let t = subst [a,`a:int64`; n,`n:num`; s,`s:armstate`]
              `read (memory :> bytes(a,n)) s` in
    ABBREV_TAC(mk_eq(v,t)) THEN
    FIRST_ASSUM(ASSUME_TAC o CONV_RULE(RAND_CONV(RAND_CONV NUM_MULT_CONV)) o
                MATCH_MP MLD_WRAP_READ_BYTES_BOUND o
                check (fun th -> concl th = mk_eq(t,v))));;

(* ------------------------------------------------------------------------- *)
(* Case facts. MLD_WRAP_CASE_THMS cs gives, for each term c of cs that is an *)
(* assumption, or whose negation is, c = T or c = F. MLD_WRAP_LET_TAC cs ths *)
(* simplifies the postcondition of the prefix (a let term) with those and    *)
(* ths, without rewriting the case facts themselves; MLD_WRAP_USE_CASE_TAC c *)
(* ths rewrites the assumptions in which c occurs with the case fact for c   *)
(* and ths; MLD_WRAP_TERMINATES_TAC proves the condition of the termination  *)
(* hypothesis from the case facts and adds its conclusions; MLD_WRAP_MP_TAC  *)
(* c uses the assumption c on an assumption c ==> p.                         *)
(* ------------------------------------------------------------------------- *)

let MLD_WRAP_CASE_THMS cs (asl,w) =
  mapfilter (fun c ->
    try EQT_INTRO(snd(find (fun (_,a) -> concl a = c) asl))
    with Failure _ ->
      EQF_INTRO(snd(find (fun (_,a) -> concl a = mk_neg c) asl))) cs;;

let MLD_WRAP_LET_TAC cs ths =
  FIRST_X_ASSUM(fun th ->
    if is_let(concl th) then
      W(fun g ->
        STRIP_ASSUME_TAC
         (REWRITE_RULE(MLD_WRAP_CASE_THMS cs g @ ths)
           (CONV_RULE(TOP_DEPTH_CONV let_CONV) th)))
    else NO_TAC);;

let MLD_WRAP_PREFIX_THMS =
  [VAL_WORD_ZX_GEN; VAL_WORD_0; MOD_0; mld_domain_separation_prefix_length;
   ADD_EQ_0; ARITH_EQ; CONJUNCT1 bytelist_of_num];;

let MLD_WRAP_USE_CASE_TAC c ths =
  W(fun (asl,w) ->
    let cths = MLD_WRAP_CASE_THMS [c] (asl,w) in
    RULE_ASSUM_TAC(fun th ->
      let t = concl th in
      if t = c || t = mk_neg c || not(free_in c t) then th
      else REWRITE_RULE(cths @ ths) th));;

let MLD_WRAP_TERMINATES_TAC =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_imp c && can (find_term (fun t ->
         is_const t && name_of t = "mld_matrix_terminates")) (rand c)
    then SUBGOAL_THEN (lhand c) (STRIP_ASSUME_TAC o MP th) THENL
          [ASM_REWRITE_TAC[] THEN NO_TAC; ALL_TAC]
    else NO_TAC);;

let MLD_WRAP_MP_TAC c =
  FIRST_X_ASSUM(fun th ->
    if is_imp(concl th) && lhand(concl th) = c
    then W(fun (asl,w) ->
      STRIP_ASSUME_TAC(MP th (snd(find (fun (_,a) -> concl a = c) asl))))
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The prefix in the buffer has length at most 332                           *)
(* (MLD_WRAP_PREFIX_LENGTH_LE), and ctxlen + 77 for the 64-byte SHAKE256     *)
(* pre-hash (MLD_WRAP_PREFIX_LENGTH_SHAKE256), of which                      *)
(* MLD_WRAP_SHAKE256_TERMINATES_TAC gives the termination hypothesis of the  *)
(* pre-hash function from that on ctxlen <= 255, and                         *)
(* MLD_WRAP_SHAKE256_RESULT_TAC proves the result and the signature given in *)
(* those terms. The bounds on the regions of a length involving val are not  *)
(* seen by SIMPLE_ARITH_TAC: MLD_WRAP_DRIVER_TAC tm bth proves the           *)
(* nonoverlapping fact tm about a region whose length has the bound bth, for *)
(* NONOVERLAPPING_TAC in the hypotheses of a callee, and MLD_WRAP_WIDEN_TAC  *)
(* cths replaces each readable region r of the memaccess_inbounds            *)
(* assumptions by r' for each theorem contained r r' of cths.                *)
(* ------------------------------------------------------------------------- *)

let MLD_WRAP_PREFIX_LENGTH_LE = prove
 (`!h ctxlen phlen. mld_domain_separation_prefix_length h ctxlen phlen <= 332`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix_length; mld_prehash_valid;
              mld_prehash_length] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN SIMPLE_ARITH_TAC);;

let MLD_WRAP_PREFIX_LENGTH_SHAKE256 = prove
 (`!ctxlen. mld_domain_separation_prefix_length 12 ctxlen 64 =
            if 255 < ctxlen then 0 else ctxlen + 77`,
  GEN_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix_length; mld_prehash_valid;
              mld_prehash_length] THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THEN ARITH_TAC);;

let MLD_WRAP_SHAKE256_TERMINATES_TAC =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_imp c && lhand c = `ctxlen <= 255` then
      SUBGOAL_THEN
       (mk_imp(`~(12 = 0) /\
                ~(mld_domain_separation_prefix_length 12 ctxlen 64 = 0)`,
               rand c)) ASSUME_TAC THENL
       [REWRITE_TAC[MLD_WRAP_PREFIX_LENGTH_SHAKE256] THEN COND_CASES_TAC THEN
        REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN MATCH_MP_TAC th THEN
        SIMPLE_ARITH_TAC;
        ALL_TAC]
    else NO_TAC);;

let MLD_WRAP_SHAKE256_RESULT_TAC =
  REWRITE_TAC[MLD_WRAP_PREFIX_LENGTH_SHAKE256] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MLD_WRAP_PREFIX_LENGTH_SHAKE256]) THEN
  ASM_CASES_TAC `255 < ctxlen` THEN
  MLD_WRAP_USE_CASE_TAC `255 < ctxlen` [ADD_EQ_0; ARITH_EQ] THEN
  ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ];;

let MLD_WRAP_CONTAINED_REFL = prove
 (`!(a:int64) n. contained (a,n) (a,n)`,
  REWRITE_TAC[contained; CONTAINED_MODULO_REFL; LE_REFL]);;

let MLD_WRAP_DRIVER_TAC tm bth =
  let len = lhand(concl bth) in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [MP_TAC bth THEN SPEC_TAC(len,`l:num`) THEN GEN_TAC THEN DISCH_TAC THEN
    NONOVERLAPPING_TAC;
    ALL_TAC];;

let MLD_WRAP_WIDEN_TAC cths =
  RULE_ASSUM_TAC(fun th ->
    try let c,args = strip_comb(concl th) in
        if not(is_const c && name_of c = "memaccess_inbounds") then th else
        let e,rr,wr = match args with [e;rr;wr] -> e,rr,wr | _ -> fail() in
        let els = dest_list rr in
        let sub r =
          try rand(concl(find (fun t -> lhand(concl t) = r) cths))
          with Failure _ -> r in
        let els' = map sub els in
        if els' = els then th else
        let rr' = mk_list(els',type_of(hd els)) in
        let lth = ISPECL [e; rr; rr'; wr; wr] MEMACCESS_INBOUNDS_CONTAINED in
        let sth = prove(lhand(concl lth),
          REWRITE_TAC[ALL; EX] THEN
          REWRITE_TAC(MLD_WRAP_CONTAINED_REFL :: map EQT_INTRO cths)) in
        MP (MP lth sth) th
    with Failure _ -> th);;

(* ------------------------------------------------------------------------- *)
(* The GOT entries. The wrappers read those of the stack guard and of the C  *)
(* library functions they call through the PLT, which the simulation needs   *)
(* as read (memory :> bytes64(word_add (word pc) (word n))) s = x, while the *)
(* preconditions of the callees have word(pc + n); MLD_WRAP_GOT_TAC adds the *)
(* second form of each such assumption.                                      *)
(* ------------------------------------------------------------------------- *)

let MLD_WRAP_GOT_TAC =
  let pat = `read (memory :> bytes64 (word_add (word pc) (word n))) s =
             x:int64` in
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      if can (term_match [] pat) (concl th) then
        let th' = REWRITE_RULE[GSYM WORD_ADD] th in
        if exists (fun (_,a) -> concl a = concl th') asl then fail()
        else th'
      else fail()) asl in
    MAP_EVERY ASSUME_TAC ths);;

(* ------------------------------------------------------------------------- *)
(* The end of a path: the return value, a conditional of a callee extended   *)
(* by word_zx (MLD_WRAP_RET_TAC), and the events, after the split of the     *)
(* cases of the buffer at stackpointer + kb if there is one and the removal  *)
(* of the regions of length 0 (MLD_WRAP_DISCHARGE_TAC).                      *)
(* ------------------------------------------------------------------------- *)

let MLD_WRAP_RET_TAC =
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ]) THEN
  CONV_TAC WORD_REDUCE_CONV;;

let MLD_WRAP_DISCHARGE_TAC =
  MLD_WRAP_SYMBUF_END_TAC `kb:num` THEN
  MLD_WRAP_EMPTY_REGIONS_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLD_WRAP_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(MLD_WRAP_RET_TAC THEN NO_TAC) THEN MLD_WRAP_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Signing succeeds (mld_sign_ok) if and only if one of the attempts that it *)
(* declassifies (mld_sign_declass, zero beyond the last) passes all its      *)
(* checks: the events of the callers that zero the signature on failure are  *)
(* functions of the declassified values. The signature of a failed signing   *)
(* is zero (MLD_WRAP_SIGN_SIG_FAIL).                                         *)
(* ------------------------------------------------------------------------- *)

let MLD_WRAP_SIGN_OK_DECLASS = prove
 (`!k l unpack p ctlen tau g1 bndz bndw bndh w1enc w1p dlo mkhint omega
    maxatt sk mu rnd.
     mld_sign_ok k l unpack p ctlen tau g1 bndz bndw bndh w1enc w1p dlo
      mkhint omega maxatt sk mu rnd <=>
     ?n. FST(SND(mld_sign_declass k l unpack p ctlen tau g1 bndz bndw bndh
                  w1enc w1p dlo mkhint omega maxatt sk mu rnd n)) =
         l + 2 * k + 1`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!kappa. FST(SND(mld_sign_attempt_declass k l ctlen tau g1 bndz bndw bndh
                     w1enc w1p dlo mkhint omega
                     (mld_polyvec_matrix_expand l (mld_sk_rho sk))
                     (mld_polyvec_map mld_poly_ntt (mld_sk_s1 unpack p sk))
                     (mld_polyvec_map mld_poly_ntt (mld_sk_s2 l unpack p sk))
                     (mld_polyvec_map mld_poly_ntt (mld_sk_t0 k l p sk))
                     mu (mld_sign_rhoprime (\j. sk(32 + j)) rnd mu) kappa)) =
            mld_sign_attempt_rej k l ctlen tau g1 bndz bndw bndh
                     w1enc w1p dlo mkhint omega
                     (mld_polyvec_matrix_expand l (mld_sk_rho sk))
                     (mld_polyvec_map mld_poly_ntt (mld_sk_s1 unpack p sk))
                     (mld_polyvec_map mld_poly_ntt (mld_sk_s2 l unpack p sk))
                     (mld_polyvec_map mld_poly_ntt (mld_sk_t0 k l p sk))
                     mu (mld_sign_rhoprime (\j. sk(32 + j)) rnd mu) kappa`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC[mld_sign_attempt_declass; mld_sign_attempt_rej] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mld_sign_declass; mld_sign_nattempts] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [UNDISCH_TAC
     `mld_sign_ok k l unpack p ctlen tau g1 bndz bndw bndh w1enc w1p dlo
       mkhint omega maxatt sk mu rnd` THEN
    REWRITE_TAC[mld_sign_ok] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o ONCE_REWRITE_RULE[MINIMAL]) THEN
    EXISTS_TAC
     `minimal n. n < maxatt /\
                 mld_sign_rejn k l unpack p ctlen tau g1 bndz bndw bndh w1enc
                  w1p dlo mkhint omega sk mu rnd n = l + 2 * k + 1` THEN
    ASM_REWRITE_TAC[ARITH_RULE `n < n + 1`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[mld_sign_rejn]) THEN
    REWRITE_TAC[mld_sign_rejn] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `n:num` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [UNDISCH_TAC
       `~mld_sign_ok k l unpack p ctlen tau g1 bndz bndw bndh w1enc w1p dlo
         mkhint omega maxatt sk mu rnd` THEN
      REWRITE_TAC[mld_sign_ok; NOT_EXISTS_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[mld_sign_rejn];
      ARITH_TAC]]);;

let MLD_WRAP_SIGN_SIG_FAIL = prove
 (`(!sk mu rnd t. ~mld_sign_ok_44 sk mu rnd
                  ==> mld_sign_sig_44 sk mu rnd t = word 0) /\
   (!sk mu rnd t. ~mld_sign_ok_65 sk mu rnd
                  ==> mld_sign_sig_65 sk mu rnd t = word 0) /\
   (!sk mu rnd t. ~mld_sign_ok_87 sk mu rnd
                  ==> mld_sign_sig_87 sk mu rnd t = word 0)`,
  REWRITE_TAC[mld_sign_sig_44; mld_sign_ok_44; mld_sign_sig_65;
              mld_sign_ok_65; mld_sign_sig_87; mld_sign_ok_87;
              mld_sign_sig] THEN
  SIMP_TAC[]);;

let MLD_WRAP_SIGN_OK_DECLASS_44 = prove
 (`!sk mu rnd.
        mld_sign_ok_44 sk mu rnd <=>
        ?n. FST(SND(mld_sign_declass_44 sk mu rnd n)) = 13`,
  REWRITE_TAC[mld_sign_ok_44; mld_sign_declass_44;
              MLD_WRAP_SIGN_OK_DECLASS] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MLD_WRAP_SIGN_OK_DECLASS_65 = prove
 (`!sk mu rnd.
        mld_sign_ok_65 sk mu rnd <=>
        ?n. FST(SND(mld_sign_declass_65 sk mu rnd n)) = 18`,
  REWRITE_TAC[mld_sign_ok_65; mld_sign_declass_65;
              MLD_WRAP_SIGN_OK_DECLASS] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MLD_WRAP_SIGN_OK_DECLASS_87 = prove
 (`!sk mu rnd.
        mld_sign_ok_87 sk mu rnd <=>
        ?n. FST(SND(mld_sign_declass_87 sk mu rnd n)) = 24`,
  REWRITE_TAC[mld_sign_ok_87; mld_sign_declass_87;
              MLD_WRAP_SIGN_OK_DECLASS] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The CORRECT and SAFE theorems from a FULL theorem fullth whose hypothesis *)
(* is the conjunction of the contracts of the C library functions. Their     *)
(* postconditions follow from that of fullth by first-order logic, for the   *)
(* existentials over the random bytes, and the distinctness of the results   *)
(* (0, -3, -4, -6 and -9 as 32-bit integers).                                *)
(* ------------------------------------------------------------------------- *)

let MLD_WRAP_RET_DISTINCT =
  let vs = map (fun n -> mk_comb(`word:num->int64`,mk_small_numeral n))
            [0; 4294967287; 4294967290; 4294967292; 4294967293] in
  let tms = flat(map (fun a -> mapfilter (fun b ->
              if a = b then fail() else mk_neg(mk_eq(a,b))) vs) vs) in
  prove(list_mk_conj tms,CONV_TAC WORD_REDUCE_CONV);;

let MLD_WRAP_SIGN_RET = prove
 (`!b. ((if b then word 0 else word 4294967292):int64 = word 4294967293 <=>
        F) /\
       ((if b then word 0 else word 4294967292):int64 = word 0 <=> b)`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[] THEN
  CONV_TAC WORD_REDUCE_CONV);;

let MLD_WRAP_CORRECT_TAC fullth =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC (MP (SPEC_ALL fullth) th)) THEN
  MESON_TAC[MLD_WRAP_RET_DISTINCT];;

let MLD_WRAP_SAFE_TAC fullth =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC (MP (SPEC_ALL fullth) th)) THEN
  MESON_TAC[MLD_WRAP_RET_DISTINCT];;
