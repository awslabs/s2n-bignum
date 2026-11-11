(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the FULL proofs of the external API functions of sign.c in      *)
(* mldsa-native's x86-64 code and of the functions that they call, as in     *)
(* arm/proofs/utils/mldsa_native_wrap.ml for AArch64: the random bytes that  *)
(* randombytes writes, the distinct results of the functions, the CORRECT    *)
(* and SAFE theorems from FULL theorems whose postconditions have an         *)
(* existential (the random bytes), the constants of the image that the code  *)
(* reads RIP-relative without an alignment check, the callees of the signing *)
(* functions as assumptions, the case facts of their branches, the length of *)
(* the domain separation prefix and when signing succeeds.                   *)
(* ========================================================================= *)

needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "x86/proofs/utils/mldsa_native_top.ml";;
needs "x86/proofs/utils/mldsa_native_scalar.ml";;

(* ------------------------------------------------------------------------- *)
(* The bytes that randombytes writes into a buffer at a in state s:          *)
(* API_RANDOM_TAC v a n s abbreviates the n bytes at a as v and adds         *)
(* v < 2 EXP (8 * n).                                                        *)
(* ------------------------------------------------------------------------- *)

let API_READ_BYTES_BOUND = prove
 (`!a n (s:x86state) x.
        read (memory :> bytes(a,n)) s = x ==> x < 2 EXP (8 * n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]);;

let API_RANDOM_TAC v a n s =
  let t = subst [a,`a:int64`; mk_small_numeral n,`n:num`; s,`s:x86state`]
            `read (memory :> bytes(a,n)) s` in
  ABBREV_TAC(mk_eq(v,t)) THEN
  FIRST_ASSUM(ASSUME_TAC o CONV_RULE(RAND_CONV(RAND_CONV NUM_MULT_CONV)) o
              MATCH_MP API_READ_BYTES_BOUND o
              check (fun th -> concl th = mk_eq(t,v)));;

(* ------------------------------------------------------------------------- *)
(* The results 0 and -3 (MLD_ERR_RNG_FAIL) are distinct, and the CORRECT and *)
(* SAFE theorems follow from the FULL theorem as usual, with the existential *)
(* of the postcondition.                                                     *)
(* ------------------------------------------------------------------------- *)

let API_RET_DISTINCT = prove
 (`~(word 0:int64 = word 4294967293) /\ ~(word 4294967293:int64 = word 0)`,
  CONV_TAC WORD_REDUCE_CONV);;

let API_CORRECT_TAC fullth =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC (MP (SPEC_ALL fullth) th)) THEN
  MESON_TAC[API_RET_DISTINCT];;

let API_SAFE_TAC fullth =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC (MP (SPEC_ALL fullth) th)) THEN
  MESON_TAC[API_RET_DISTINCT];;

(* ------------------------------------------------------------------------- *)
(* A constant of the image read RIP-relative by an instruction without an    *)
(* alignment check (e.g. MOVZX): IMAGE_RIPREL_CONST_TAC th r, before the     *)
(* simulation of the instruction that ends at pc + r and loads the constant  *)
(* of th (from IMAGE_CONST_RULE_FOR of utils/mldsa_native_scalar.ml, at      *)
(* pc + d), adds the value of the constant at the address in the form of the *)
(* simulation, word(val(word(pc + r)) + (d - r)), as IMAGE_RIPREL_TAC does   *)
(* without the alignment of the address, which a constant at an address that *)
(* is not a multiple of 16 does not have.                                    *)
(* ------------------------------------------------------------------------- *)

let IMAGE_RIPREL_CONST_TAC =
  let word_tm = `word:num->int64`
  and val_tm = `val:int64->num`
  and plus_tm = `(+):num->num->num` in
  fun th r ->
    FIRST_ASSUM(fun bth ->
      let cth = MATCH_MP th bth in
      let l = lhs(concl cth) in
      let wad = rand(rand(rand(rator l))) in
      let p,dt = dest_binop plus_tm (rand wad) in
      let d = dest_small_numeral dt in
      let rt = mk_small_numeral r and kt = mk_small_numeral(d - r) in
      let addr = mk_comb(word_tm,
        mk_binop plus_tm
         (mk_comb(val_tm,mk_comb(word_tm,mk_binop plus_tm p rt))) kt) in
      let eqth = CONV_RULE(RAND_CONV(RAND_CONV NUM_REDUCE_CONV))
        (REWRITE_CONV[RIPREL_ADDR_LEMMA; GSYM ADD_ASSOC] addr) in
      ASSUME_TAC(REWRITE_RULE[SYM eqth] cth));;

(* ------------------------------------------------------------------------- *)
(* The signing functions of sign.c, as in                                    *)
(* arm/proofs/utils/mldsa_native_wrap.ml: the FULL theorem of a callee as an *)
(* assumption with e_tail last, quickly for the many variables of            *)
(* mldsa{44,65,87}_signature_internal (API_ASSUME_CALLEE_TAC); the arguments *)
(* that are NULL with length 0 (API_NULL_TAC regs adds that each region of   *)
(* regs does not overlap (word 0,0), and that the 0 bytes at word 0 are 0)   *)
(* and the removal of the regions of length 0 from the readable regions of   *)
(* the memaccess_inbounds assumptions (API_EMPTY_REGIONS_TAC); and the       *)
(* results of signing, 0 or -4 (API_SIGN_RET), distinct from -3 and -9       *)
(* (API_SIGN_DISTINCT), for the CORRECT and SAFE theorems                    *)
(* (API_SIGN_CORRECT_TAC and API_SIGN_SAFE_TAC).                             *)
(* ------------------------------------------------------------------------- *)

let API_ASSUME_CALLEE_TAC =
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

let API_NONOVERLAPPING_EMPTY = prove
 (`!(a:int64) n (b:int64). nonoverlapping (a,n) (b,0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_TRIVIAL THEN REWRITE_TAC[]);;

let API_NULL_TAC regs =
  MAP_EVERY (fun (a,n) ->
    ASSUME_TAC(ISPECL [a; n; `word 0:int64`] API_NONOVERLAPPING_EMPTY))
   regs THEN
  ASSUME_TAC(GEN `s:x86state`
   (ISPECL [`word 0:int64`; `s:x86state`; `memory`]
      READ_MEMORY_BYTES_TRIVIAL));;

let API_MEMACCESS_EMPTY = prove
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

let API_EMPTY_REGIONS_RULE th =
  try let c,args = strip_comb(concl th) in
      if not(is_const c && name_of c = "memaccess_inbounds") then th else
      let e,rr,wr = match args with [e;rr;wr] -> e,rr,wr | _ -> fail() in
      let els = dest_list rr in
      let els' = filter (fun r -> not(is_pair r && rand r = `0`)) els in
      if length els' = length els || els' = [] then th else
      let rr' = mk_list(els',type_of(hd els)) in
      let lth = ISPECL [e; rr; rr'; wr] API_MEMACCESS_EMPTY in
      let sth = prove(lhand(concl lth),
        REWRITE_TAC[MEM; NOT_CONS_NIL] THEN REPEAT STRIP_TAC THEN
        ASM_REWRITE_TAC[]) in
      MP (MP lth sth) th
  with Failure _ -> th;;

let API_EMPTY_REGIONS_TAC = RULE_ASSUM_TAC API_EMPTY_REGIONS_RULE;;

let API_SIGN_RET = prove
 (`!b. ((if b then word 0 else word 4294967292):int64 = word 4294967293 <=>
        F) /\
       ((if b then word 0 else word 4294967292):int64 = word 0 <=> b)`,
  GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[] THEN
  CONV_TAC WORD_REDUCE_CONV);;

let API_SIGN_DISTINCT =
  let vs = map (fun n -> mk_comb(`word:num->int64`,mk_small_numeral n))
            [0; 4294967287; 4294967292; 4294967293] in
  let tms = flat(map (fun a -> mapfilter (fun b ->
              if a = b then fail() else mk_neg(mk_eq(a,b))) vs) vs) in
  prove(list_mk_conj tms,CONV_TAC WORD_REDUCE_CONV);;

let API_SIGN_CORRECT_TAC fullth =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC (MP (SPEC_ALL fullth) th)) THEN
  MESON_TAC[API_SIGN_DISTINCT];;

let API_SIGN_SAFE_TAC fullth =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC (MP (SPEC_ALL fullth) th)) THEN
  MESON_TAC[API_SIGN_DISTINCT];;

(* ------------------------------------------------------------------------- *)
(* Case facts, as in arm/proofs/utils/mldsa_native_wrap.ml. API_CASE_THMS cs *)
(* gives, for each term c of cs that is an assumption, or whose negation is, *)
(* c = T or c = F. API_LET_TAC cs ths simplifies the postcondition of the    *)
(* prefix (a let term) with those and ths (API_PREFIX_THMS for a pure        *)
(* ML-DSA prefix, with hashalg 0 and no pre-hash), without rewriting the     *)
(* case facts themselves; API_USE_CASE_TAC c ths rewrites the assumptions in *)
(* which c occurs with the case fact for c and ths; API_MP_TAC c uses the    *)
(* assumption c on an assumption c ==> p.                                    *)
(* ------------------------------------------------------------------------- *)

let API_CASE_THMS cs (asl,w) =
  mapfilter (fun c ->
    try EQT_INTRO(snd(find (fun (_,a) -> concl a = c) asl))
    with Failure _ ->
      EQF_INTRO(snd(find (fun (_,a) -> concl a = mk_neg c) asl))) cs;;

let API_LET_TAC cs ths =
  FIRST_X_ASSUM(fun th ->
    if is_let(concl th) then
      W(fun g ->
        STRIP_ASSUME_TAC
         (REWRITE_RULE(API_CASE_THMS cs g @ ths)
           (CONV_RULE(TOP_DEPTH_CONV let_CONV) th)))
    else NO_TAC);;

let API_PREFIX_THMS =
  [VAL_WORD_ZX_GEN; VAL_WORD_0; MOD_0; mld_domain_separation_prefix_length;
   ADD_EQ_0; ARITH_EQ; CONJUNCT1 bytelist_of_num];;

let API_USE_CASE_TAC c ths =
  W(fun (asl,w) ->
    let cths = API_CASE_THMS [c] (asl,w) in
    RULE_ASSUM_TAC(fun th ->
      let t = concl th in
      if t = c || t = mk_neg c || not(free_in c t) then th
      else REWRITE_RULE(cths @ ths) th));;

let API_MP_TAC c =
  FIRST_X_ASSUM(fun th ->
    if is_imp(concl th) && lhand(concl th) = c
    then W(fun (asl,w) ->
      STRIP_ASSUME_TAC(MP th (snd(find (fun (_,a) -> concl a = c) asl))))
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The prefix in the buffer has length at most 332 (API_PREFIX_LENGTH_LE),   *)
(* and ctxlen + 77 for the 64-byte SHAKE256 pre-hash                         *)
(* (API_PREFIX_LENGTH_SHAKE256), of which API_SHAKE256_TERMINATES_TAC gives  *)
(* the termination hypothesis of the pre-hash function from that on ctxlen   *)
(* <= 255, and API_SHAKE256_RESULT_TAC proves the result and the signature   *)
(* given in those terms. The bounds on the regions of a length that is not a *)
(* numeral are not seen by NONOVERLAPPING_TAC: API_DRIVER_TAC tm bth proves  *)
(* the nonoverlapping fact tm about a region whose length has the bound bth, *)
(* for the hypotheses of a callee, and API_WIDEN_TAC cths replaces each      *)
(* readable region r of the memaccess_inbounds assumptions by r' for each    *)
(* theorem contained r r' of cths.                                           *)
(* ------------------------------------------------------------------------- *)

let API_PREFIX_LENGTH_LE = prove
 (`!h ctxlen phlen. mld_domain_separation_prefix_length h ctxlen phlen <= 332`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix_length; mld_prehash_valid;
              mld_prehash_length] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN SIMPLE_ARITH_TAC);;

let API_PREFIX_LENGTH_SHAKE256 = prove
 (`!ctxlen. mld_domain_separation_prefix_length 12 ctxlen 64 =
            if 255 < ctxlen then 0 else ctxlen + 77`,
  GEN_TAC THEN
  REWRITE_TAC[mld_domain_separation_prefix_length; mld_prehash_valid;
              mld_prehash_length] THEN
  CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THEN ARITH_TAC);;

let API_SHAKE256_TERMINATES_TAC =
  FIRST_ASSUM(fun th ->
    let c = concl th in
    if is_imp c && lhand c = `ctxlen <= 255` then
      SUBGOAL_THEN
       (mk_imp(`~(12 = 0) /\
                ~(mld_domain_separation_prefix_length 12 ctxlen 64 = 0)`,
               rand c)) ASSUME_TAC THENL
       [REWRITE_TAC[API_PREFIX_LENGTH_SHAKE256] THEN COND_CASES_TAC THEN
        REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN MATCH_MP_TAC th THEN
        SIMPLE_ARITH_TAC;
        ALL_TAC]
    else NO_TAC);;

let API_SHAKE256_RESULT_TAC =
  REWRITE_TAC[API_PREFIX_LENGTH_SHAKE256] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[API_PREFIX_LENGTH_SHAKE256]) THEN
  ASM_CASES_TAC `255 < ctxlen` THEN
  API_USE_CASE_TAC `255 < ctxlen` [ADD_EQ_0; ARITH_EQ] THEN
  ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ];;

let API_CONTAINED_REFL = prove
 (`!(a:int64) n. contained (a,n) (a,n)`,
  REWRITE_TAC[contained; CONTAINED_MODULO_REFL; LE_REFL]);;

let API_DRIVER_TAC tm bth =
  let len = lhand(concl bth) in
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [MP_TAC bth THEN SPEC_TAC(len,`l:num`) THEN GEN_TAC THEN DISCH_TAC THEN
    NONOVERLAPPING_TAC;
    ALL_TAC];;

let API_WIDEN_TAC cths =
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
          REWRITE_TAC(API_CONTAINED_REFL :: map EQT_INTRO cths)) in
        MP (MP lth sth) th
    with Failure _ -> th);;

(* ------------------------------------------------------------------------- *)
(* Signing succeeds (mld_sign_ok) if and only if one of the attempts that it *)
(* declassifies (mld_sign_declass, zero beyond the last) passes all its      *)
(* checks, as in arm/proofs/utils/mldsa_native_wrap.ml: the events of the    *)
(* callers that zero the signature on failure are functions of the           *)
(* declassified values. The signature of a failed signing is zero            *)
(* (API_SIGN_SIG_FAIL).                                                      *)
(* ------------------------------------------------------------------------- *)

let API_SIGN_OK_DECLASS = prove
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

let API_SIGN_SIG_FAIL = prove
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

let API_SIGN_OK_DECLASS_44 = prove
 (`!sk mu rnd.
        mld_sign_ok_44 sk mu rnd <=>
        ?n. FST(SND(mld_sign_declass_44 sk mu rnd n)) = 13`,
  REWRITE_TAC[mld_sign_ok_44; mld_sign_declass_44; API_SIGN_OK_DECLASS] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let API_SIGN_OK_DECLASS_65 = prove
 (`!sk mu rnd.
        mld_sign_ok_65 sk mu rnd <=>
        ?n. FST(SND(mld_sign_declass_65 sk mu rnd n)) = 18`,
  REWRITE_TAC[mld_sign_ok_65; mld_sign_declass_65; API_SIGN_OK_DECLASS] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let API_SIGN_OK_DECLASS_87 = prove
 (`!sk mu rnd.
        mld_sign_ok_87 sk mu rnd <=>
        ?n. FST(SND(mld_sign_declass_87 sk mu rnd n)) = 24`,
  REWRITE_TAC[mld_sign_ok_87; mld_sign_declass_87; API_SIGN_OK_DECLASS] THEN
  CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The branches on the result of a test of a 32-bit value x (e.g. hashalg)   *)
(* against 0, whose RIP the simulation leaves as a conditional: API_PC_TAC   *)
(* cs rewrites it with the case facts for the terms of cs (word_zx x = word  *)
(* 0, or its negation, as assumptions). API_TERMINATES_TAC proves the        *)
(* condition of the termination hypothesis from the case facts and adds its  *)
(* conclusions, and API_RET_TAC proves a result given by a conditional.      *)
(* ------------------------------------------------------------------------- *)

let API_PC_TAC cs =
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let c = concl th in
      if mem c cs || (is_neg c && mem (rand c) cs) then th else fail()) asl in
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read RIP s = (if b then x else y):int64`)
             (concl th)
      then REWRITE_RULE(WORD_ZX_ZX_32_64_32::VAL_EQ_0::ths) th else th));;

let API_TERMINATES_TAC =
  FIRST_X_ASSUM(fun th ->
    let c = concl th in
    if is_imp c && can (find_term (fun t ->
         is_const t && name_of t = "mld_matrix_terminates")) (rand c)
    then SUBGOAL_THEN (lhand c) (STRIP_ASSUME_TAC o MP th) THENL
          [ASM_REWRITE_TAC[] THEN NO_TAC; ALL_TAC]
    else NO_TAC);;

let API_RET_TAC =
  TRY(COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ]) THEN
  CONV_TAC WORD_REDUCE_CONV;;
