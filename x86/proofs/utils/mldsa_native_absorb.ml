(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics for the proofs of mldsa-native's absorbing of messages *)
(* into Keccak states, as in arm/proofs/utils/mldsa_native_absorb.ml (those  *)
(* of the proof of mlk_keccak_absorb_once of mlkem-native), for the x86      *)
(* state and without the parts for the AArch64 code. Unlike that file, it    *)
(* does not load utils/keccak_fips202.ml, which takes minutes to load, so    *)
(* that the proofs that do not need it load quickly. The tactics at the end  *)
(* are for the FULL proofs of the SHAKE functions, which absorb and squeeze. *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "x86/proofs/consttime.ml";;

(* ------------------------------------------------------------------------- *)
(* Lemmas about the arguments and the blocks.                                *)
(* ------------------------------------------------------------------------- *)

let WORD_ZX_SUB1_SMALL = prove
 (`!r. 0 < r /\ r < 2 EXP 32
       ==> word_zx (word_sub (word_zx (word r:int64):int32) (word 1)):int64 =
           word(r - 1)`,
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; VAL_WORD_SUB_CASES;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE
   `r < 4294967296 ==> r < 18446744073709551616`;
   ARITH_RULE `0 < r ==> 1 <= r`;
   ARITH_RULE `r < 4294967296 ==> r - 1 < 4294967296`;
   ARITH_RULE `r < 4294967296 ==> r - 1 < 18446744073709551616`]);;

let ABSORB_BLOCK_BOUND = prove
 (`!mlen r i. 0 < r /\ i < mlen DIV r ==> r * i + r <= mlen`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`mlen:num`; `r:num`] DIVISION) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> GEN_REWRITE_TAC RAND_CONV [th])
    ASSUME_TAC) THEN
  MATCH_MP_TAC(ARITH_RULE `a <= b ==> a <= b + c`) THEN
  REWRITE_TAC[ARITH_RULE `r * i + r = (i + 1) * r`; LE_MULT_RCANCEL] THEN
  ASM_ARITH_TAC);;

let ABSORB_MOD_EQ = prove
 (`!mlen r. mlen - r * mlen DIV r = mlen MOD r`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`mlen:num`; `r:num`] (CONJUNCT2 DIVISION_SIMP)) THEN
  ARITH_TAC);;

let ABSORB_LOOP_TEST = prove
 (`!mlen r i. 0 < r /\ r * i + r <= mlen
              ==> (r <= mlen - r * (i + 1) <=> i + 1 < mlen DIV r)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `i + 1 < q <=> i + 2 <= q`; LE_RDIV_EQ;
               ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tactics for the arguments and the flags.                                  *)
(* ------------------------------------------------------------------------- *)

(*** The values of the 64-bit words for r and mlen ***)

let ABSORB_VAL_TAC =
  MAP_EVERY (fun t ->
    SUBGOAL_THEN (subst [t,`n:num`] `val(word n:int64) = n`)
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN ASSUME_TAC th) THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
      ALL_TAC])
   [`r:num`; `mlen:num`];;

(*** Case split on tm, deciding the flags of the comparison with it ***)

let ABSORB_CASE_FLAG_TAC tm =
  ASM_CASES_TAC tm THEN
  FIRST_ASSUM(fun cth ->
    if concl cth = tm || concl cth = mk_neg tm then
      RULE_ASSUM_TAC(fun th ->
        if is_iff(concl th) && free_in `ZF` (concl th)
        then REWRITE_RULE[cth] th else th)
    else NO_TAC);;

(*** A 32-bit value n < 2^32 loaded into a 64-bit register, word_zx(word n) ***)

let WORD_ZX_32_64_SMALL = prove
 (`!n. n < 2 EXP 32 ==> word_zx(word n:int32):int64 = word n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD;
    DIMINDEX_32; DIMINDEX_64] THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[MOD_LT;
    ARITH_RULE `n < 4294967296 ==> n < 18446744073709551616`]);;

let ARGS_64_TAC ns =
  MAP_EVERY (fun n ->
    MP_TAC(SPEC n WORD_ZX_32_64_SMALL) THEN
    ANTS_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
      DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))]) ns;;

(*** The state at a as a 1600-bit word, from it as 200 bytes, and a tactic ***)
(*** applied to that word (as in keccakf1600_permute_spec.ml)              ***)

let KECCAK_STATE_AT_TAC a =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("bytes",_),aa))),_)),
           Comb(Const("val",_),_))
        when aa = mk_pair(a,`200`) ->
          ASSUME_TAC(REWRITE_RULE[GSYM READ_MEMORY_WBYTES_1600] th)
    | _ -> NO_TAC);;

let KECCAK_STATE_THEN a (ttac:term->tactic) =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Comb(Const("=",_),
                Comb(Comb(Const("read",_),
                          Comb(Comb(Const(":>",_),Const("memory",_)),
                               Comb(Const("wbytes",_),aa))),_)),v)
        when aa = a -> ttac v
    | _ -> NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Two tactics for the FULL proofs of the SHAKE functions, whose events are  *)
(* given by a template of event functions f_ev_... (CONCRETIZE_F_EVENTS_TAC) *)
(* to be unified with the events of the code. EXISTS_E2_FEV_TAC vars is      *)
(* EXISTS_E2_TAC vars for the subgoal on the events before a call, also      *)
(* allowing the f_ev_... of the template, which these events contain in a    *)
(* loop. UNABBREV_VARS_TAC vs replaces each variable v of vs, introduced by  *)
(* ABBREV_TAC with an assumption t = v, by t everywhere: the events must be  *)
(* functions of the public arguments of the template only when they are      *)
(* unified with it.                                                          *)
(* ------------------------------------------------------------------------- *)

let EXISTS_E2_FEV_TAC vars =
  W(fun (asl,w) ->
    let fevs = filter (fun v -> starts_with "f_ev_" (name_of v)) (frees w) in
    EXISTS_E2_TAC (ref (vars @ fevs)));;

let UNABBREV_VARS_TAC vs =
  MAP_EVERY (fun v ->
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = v && not(is_var(lhs(concl th))))))
   vs;;

(* ------------------------------------------------------------------------- *)
(* DISCHARGE_SAFETY_PROPERTY_SPINE_TAC is DISCHARGE_SAFETY_PROPERTY_TAC for  *)
(* a segment whose precondition gives the memory safety of the events since  *)
(* the start as a whole, e.g. of a loop so far and of a part before it with  *)
(* a conditional. EXISTS_E2_TAC left-associates the APPENDs of the events,   *)
(* so that this whole is no longer a subterm and the tactic for              *)
(* memaccess_inbounds cannot use the fact; APPEND_SPINE_CONV                 *)
(* right-associates the APPENDs along the spine of the list, and removes     *)
(* APPEND [], without changing the parts. The tactic does the same to unify  *)
(* the events with the template when FULL_UNIFY_F_EVENTS_TAC fails on the    *)
(* left-associated form, e.g. for an empty segment at the end of a loop      *)
(* inside such a whole.                                                      *)
(* ------------------------------------------------------------------------- *)

let rec APPEND_SPINE_CONV tm =
  match tm with
    Comb(Comb(Const("APPEND",_),l),r) ->
      (match l with
         Comb(Comb(Const("APPEND",_),_),_) ->
           (GEN_REWRITE_CONV I [GSYM APPEND_ASSOC] THENC APPEND_SPINE_CONV) tm
       | Const("NIL",_) ->
           (GEN_REWRITE_CONV I [CONJUNCT1 APPEND] THENC APPEND_SPINE_CONV) tm
       | _ -> RAND_CONV APPEND_SPINE_CONV tm)
  | Comb(Comb(Const("CONS",_),_),_) -> RAND_CONV APPEND_SPINE_CONV tm
  | _ -> REFL tm;;

let DISCHARGE_SAFETY_PROPERTY_SPINE_TAC =
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
  W(fun (asl,w) ->
    (if is_conj w then
       CONJ_TAC THENL
        [FULL_UNIFY_F_EVENTS_TAC ORELSE
         (REWRITE_TAC[GSYM APPEND_ASSOC] THEN FULL_UNIFY_F_EVENTS_TAC);
         ALL_TAC]
     else ALL_TAC) THEN
    CONV_TAC(RATOR_CONV(RATOR_CONV(RAND_CONV APPEND_SPINE_CONV))) THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC);;
