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

(* The part that depends on AArch64; the rest is in                          *)
(* common/fips204/properties/mldsa_native_wrap.ml.                           *)

needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_prefix.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/fips204/properties/mldsa_native_wrap.ml";;

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

let MLD_WRAP_NORM_TAC =
  let pat = `read (r:(armstate,int64)component) s =
             word_add (word_add stackpointer x) y` in
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [`stackpointer:int64`] pat) (concl th)
    then CONV_RULE(RAND_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) th else th);;

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

let MLD_WRAP_DISCHARGE_TAC =
  MLD_WRAP_SYMBUF_END_TAC `kb:num` THEN
  MLD_WRAP_EMPTY_REGIONS_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;;

let MLD_WRAP_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(MLD_WRAP_RET_TAC THEN NO_TAC) THEN MLD_WRAP_DISCHARGE_TAC;;

let MLD_WRAP_CORRECT_TAC fullth =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC (MP (SPEC_ALL fullth) th)) THEN
  MESON_TAC[MLD_WRAP_RET_DISTINCT];;

let MLD_WRAP_SAFE_TAC fullth =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> SAFE_OF_FULL_TAC (MP (SPEC_ALL fullth) th)) THEN
  MESON_TAC[MLD_WRAP_RET_DISTINCT];;
