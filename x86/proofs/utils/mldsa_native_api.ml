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
(* existential (the random bytes), and the constants of the image that the   *)
(* code reads RIP-relative without an alignment check.                       *)
(* ========================================================================= *)

needs "common/mldsa_native_sign.ml";;
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
