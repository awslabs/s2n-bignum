(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the NTT and inverse NTT of mldsa-native's x86-64  *)
(* code that do not depend on the build, as arm/proofs/utils/                *)
(* mldsa_native_ntt.ml has for AArch64: the table of zetas as the bytes of   *)
(* the read-only data, the Montgomery multiplication as the compiled code    *)
(* does it with scalar registers, and tactics for the lemmas of their FULL   *)
(* proofs.                                                                   *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_scalar.ml";;
needs "common/mldsa_native_poly.ml";;
needs "common/fips204/properties/mldsa_native_ntt.ml";;

(* ------------------------------------------------------------------------- *)
(* The table mld_zetas as 1024 bytes, 4 for each entry, as the binary has it *)
(* in its read-only data. A proof about an image checks that the image has   *)
(* these bytes at the table's address.                                       *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES32_NUM_OF_WORDLIST = prove
 (`!a:int64 (l:int32 list) n j s:x86state.
        read (memory :> bytes(a,4 * n)) s = num_of_wordlist l /\
        LENGTH l = n /\ j < n
        ==> read (memory :> bytes32(word_add a (word(4 * j)))) s = EL j l`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`l:int32 list`; `j:num`] NUM_OF_WORDLIST_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && is_comb(lhs(concl th)) &&
       can (term_match [] `read (c:(x86state,num)component) s`)
             (lhs(concl th))
    then REWRITE_TAC[GSYM th] else failwith "") THEN
  REWRITE_TAC[BYTES32_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `32 * j = 8 * (4 * j)`;
              ARITH_RULE `4294967296 = 2 EXP (8 * 4)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let MLD_ZETAS_LOADED = prove
 (`!z s:x86state.
        bytes_loaded s z mld_zetas_data
        ==> !k. k < 256
                ==> read(memory :> bytes32(word_add z (word(4 * k)))) s =
                    mld_zeta k`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; LENGTH_MLD_ZETAS_DATA;
              MLD_ZETAS_DATA; mld_zeta] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`z:int64`; `MAP iword mld_zetas:int32 list`; `256`;
                 `k:num`; `s:x86state`]
         READ_MEMORY_BYTES32_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_MLD_ZETAS; ARITH] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC EL_MAP THEN
  ASM_REWRITE_TAC[LENGTH_MLD_ZETAS]);;

(* ------------------------------------------------------------------------- *)
(* Linear arithmetic with the assumptions that are about numbers only (any   *)
(* propositional combination of relations between numbers, without words or  *)
(* the state), which in a simulation are few among the many assumptions that *)
(* ASM_ARITH_TAC would also try.                                             *)
(* ------------------------------------------------------------------------- *)

let NUM_ASM_ARITH_TAC =
  let numty = `:num` and boolty = `:bool` in
  let rec numprop tm =
    if is_neg tm then numprop(rand tm)
    else if is_conj tm || is_disj tm || is_imp tm || is_iff tm then
      numprop(lhand tm) && numprop(rand tm)
    else
      exists (fun op -> is_binary op tm &&
                        (let x,_ = dest_binary op tm in type_of x = numty))
             ["=";"<";"<=";">";">="] &&
      forall (fun v -> type_of v = numty) (frees tm) &&
      not(can (find_term (fun t -> is_const t &&
                mem (fst(dest_const t)) ["read";"word";"val"])) tm) in
  W(fun (asl,w) ->
    let asl' = filter (fun (_,th) -> type_of(concl th) = boolty &&
                                     numprop(concl th)) asl in
    MAP_EVERY (MP_TAC o snd) asl' THEN CONV_TAC ARITH_RULE);;

(* ------------------------------------------------------------------------- *)
(* The Montgomery reduction of the 64-bit product p of a coefficient and a   *)
(* zeta, as the compiled code does it with scalar registers: it stores p in  *)
(* the red zone, multiplies the low 32 bits of the stored value by QINV,     *)
(* giving t, and computes p - t * Q with shifts and subtractions before      *)
(* taking the high 32 bits. NTT_MONTRED_LANE gives the result as             *)
(* mld_montgomery_reduce p, as PWACC_MONTRED_LANE                            *)
(* (utils/mldsa_native_pwacc.ml) does for the multiplication of a register.  *)
(* The 32-bit read of the stored value needs the assumption about the 64-bit *)
(* store split into its two halves, which READ_BYTES64_SPLIT_TAC adds.       *)
(* ------------------------------------------------------------------------- *)

let NTT_MONTRED_LANE = prove
 (`!p:int64.
     word_zx
      (word_ishr
        (word_add
          (word_sub
            (word_shl
              (word_sub
                (word_sx(word_zx(word_zx(word_mul (word_subword p (0,32))
                                           (word 58728449):int32):int64)
                         :int32):int64)
                (word_shl
                  (word_sx(word_zx(word_zx(word_mul (word_subword p (0,32))
                                             (word 58728449):int32):int64)
                           :int32):int64)
                  10))
              13)
            (word_sx(word_zx(word_zx(word_mul (word_subword p (0,32))
                                       (word 58728449):int32):int64)
                     :int32):int64))
          p)
        32):int32 =
     mld_montgomery_reduce p`,
  GEN_TAC THEN
  REWRITE_TAC[WORD_BLAST
   `word_subword (p:int64) (0,32):int32 = word_zx p`] THEN
  REWRITE_TAC[mld_montgomery_reduce; WORD_ZX_ZX_32_64_32] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SPEC_TAC(`word_sx(word_mul (word_zx (p:int64)) (word 58728449):int32)
            :int64`,`u:int64`) THEN
  GEN_TAC THEN
  REWRITE_TAC[WORD_BLAST
   `word_zx(word_ishr (v:int64) 32):int32 = word_subword v (32,32)`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_BLAST `word_shl (u:int64) 10 = word_mul u (word 1024)`;
              WORD_BLAST `word_shl (u:int64) 13 = word_mul u (word 8192)`] THEN
  CONV_TAC WORD_RULE);;

let READ_BYTES64_SPLIT_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes64 a) s = v`) (concl th)
    then STRIP_ASSUME_TAC(CONV_RULE (READ_MEMORY_SPLIT_CONV 1) th)
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The events at the end of a simulation that went through lemmas at once    *)
(* (X86_BIGSTEP_TAC), as CONS and APPEND nested to the depth of the lemmas,  *)
(* ending with the events e before it: EVENTS_APPEND_CONV puts them in the   *)
(* form APPEND l e, which EXISTS_E2_TAC (in DISCHARGE_SAFETY_PROPERTY_TAC)   *)
(* needs. EVENTS_APPEND_TAC does so in the goal exists e2. E = APPEND e2 e   *)
(* /\ ... that ENSURES_FINAL_STATE_TAC and ASM_REWRITE_TAC leave for the     *)
(* events E.                                                                 *)
(* ------------------------------------------------------------------------- *)

let EVENTS_APPEND_CONV =
  let cons_var_th = prove
   (`!(h:A) e. CONS h e = APPEND [h] e`, REWRITE_TAC[APPEND])
  and cons_th = prove
   (`!(h:A) l e. CONS h (APPEND l e) = APPEND (CONS h l) e`,
    REWRITE_TAC[APPEND])
  and append_th = prove
   (`!(a:A list) l e. APPEND a (APPEND l e) = APPEND (APPEND a l) e`,
    REWRITE_TAC[APPEND_ASSOC]) in
  let rec conv tm =
    match tm with
      Comb(Comb(Const("CONS",_),_),t) ->
        if is_var t then REWR_CONV cons_var_th tm
        else (RAND_CONV conv THENC REWR_CONV cons_th) tm
    | Comb(Comb(Const("APPEND",_),_),t) ->
        if is_var t then REFL tm
        else (RAND_CONV conv THENC REWR_CONV append_th) tm
    | _ -> failwith "EVENTS_APPEND_CONV" in
  conv;;

let EVENTS_APPEND_TAC =
  CONV_TAC(BINDER_CONV(LAND_CONV(LAND_CONV EVENTS_APPEND_CONV)));;

(* ------------------------------------------------------------------------- *)
(* Go through a lemma at once in a simulation, as X86_SUBROUTINE_SIM_TAC     *)
(* does for a subroutine. EVENTS_BIGSTEP_TAC execth th xs n, at step n of    *)
(* the simulation with execth, instantiates the lemma th, of the form !e x1  *)
(* ... xk. H ==> ensures x86 P Q C with read events s = e in P, with the     *)
(* events so far and the terms xs for x1, ..., xk, proves H from the         *)
(* assumptions and steps to state n by X86_BIGSTEP_TAC, which proves P by    *)
(* ASM_REWRITE_TAC and keeps what C does not change. Q must not state that   *)
(* the code is loaded: X86_BIGSTEP_TAC shows that from C, and fails if it    *)
(* finds such an assumption about the new state first.                       *)
(* ------------------------------------------------------------------------- *)

let EVENTS_BIGSTEP_TAC execth th xs n =
  let ev = vsubst [mk_var("s" ^ string_of_int(n - 1),`:x86state`),
                   `s:x86state`] `read events (s:x86state)` in
  W(fun (asl,w) ->
    let evth = snd(find (fun (_,th) -> let c = concl th in
                     is_eq c && lhs c = ev) asl) in
    MP_TAC(SPECL (rhs(concl evth)::xs) th)) THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; SOME_FLAGS] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN NONOVERLAPPING_TAC;
    ALL_TAC] THEN
  X86_BIGSTEP_TAC execth ("s" ^ string_of_int n);;
