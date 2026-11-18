(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tactics for the proofs of the K-PKE functions of mlkem-native in the gcc  *)
(* 12 -O2 image, such as mlkem768_indcpa_enc, which call many of the other   *)
(* functions on buffers in their stack frames. Most callees specify their    *)
(* results only up to congruence modulo q and bounds, so after a call the    *)
(* 16-bit values in a buffer are named by a new function (a ghost), with a   *)
(* fact giving the memory in terms of it, which the simulation carries over  *)
(* later calls, and facts about the ghost without the state, derived from    *)
(* the postcondition of the call. Those facts are then combined by lemmas in *)
(* terms of FIPS 203 (see mlkem_native_fips203.ml).                          *)
(* ========================================================================= *)

needs "common/layout.ml";;
needs "common/fips203/properties/mlkem_native_libc.ml";;
needs "common/fips203/properties/mlkem_native_fips203.ml";;
needs "common/consttime.ml";;

(* ------------------------------------------------------------------------- *)
(* Arithmetic using only the bounds on the variables in the goal.            *)
(* ------------------------------------------------------------------------- *)

let INDCPA_ARITH_TAC =
  W(fun (asl,w) ->
    let vs = frees w in
    let ok th =
      let c = concl th in
      (is_binary "<" c || is_binary "<=" c) &&
      type_of(lhand c) = `:num` && is_var(lhand c) &&
      mem (lhand c) vs && is_numeral(rand c) in
    MAP_EVERY (MP_TAC o snd) (filter (ok o snd) asl) THEN ARITH_TAC);;

let INDCPA_HAS_CONST c tm =
  can (find_term (fun t -> match t with Const(c',_) -> c' = c | _ -> false))
      tm;;

let INDCPA_GHOST_SPEC_TAC v idx =
  FIRST_ASSUM(fun th ->
    match concl th with
      Comb(Const("!",_),Abs(_,Comb(Comb(Const("==>",_),_),
        Comb(Comb(Const("=",_),_),Comb(Var(v',_),_))))) when v' = v ->
        MP_TAC(SPEC idx th) THEN ANTS_TAC THENL
         [INDCPA_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)]
    | _ -> NO_TAC);;

let INDCPA_UNGHOST_TAC v =
  W(fun (_,w) ->
    let tms = find_terms (fun t -> is_comb t &&
                 (match rator t with Var(v',_) -> v' = v | _ -> false)) w in
    MAP_EVERY (fun t -> INDCPA_GHOST_SPEC_TAC v (rand t)) tms);;

(*** The postcondition of a call in state st, mentioning cn and src ***)

let INDCPA_IS_POST st cn src th =
  let c = concl th in
  mem st (frees c) && INDCPA_HAS_CONST cn c && mem src (frees c);;

let INDCPA_POST_TAC st cn src f =
  FIRST_ASSUM(f o check (INDCPA_IS_POST st cn src));;

let INDCPA_DROP_POST_TAC st cn src =
  FIRST_X_ASSUM(fun th ->
    if INDCPA_IS_POST st cn src th then ALL_TAC else NO_TAC);;

let INDCPA_DISCARD_LETS_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_let(concl th) then ALL_TAC else NO_TAC));;

let INDCPA_TOBYTES_POST_TAC v n g =
  let l = mk_comb(mk_comb(`list_of_seq:(num->int16)->num->int16 list`,
                          mk_var(v,`:num->int16`)),mk_small_numeral n) in
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_imp(concl th) &&
    can (find_term (fun t -> t = l)) (concl th) &&
    INDCPA_HAS_CONST "num_of_wordlist" (concl th))) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LIST_OF_SEQ_REDUCED THEN EXISTS_TAC g THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN ASM_SIMP_TAC[];
    DISCH_TAC];;

let INDCPA_DROP_MEMSET_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    match concl th with
      Comb(Const("!",_),Abs(_,Comb(Comb(Const("==>",_),_),
        Comb(Comb(Const("=",_),l),Comb(Const("word_zx",_),_)))))
      when INDCPA_HAS_CONST "bytes8" l -> ALL_TAC
    | _ -> NO_TAC));;

let INDCPA_NONCE_TAC n =
  ASSUME_TAC(WORD_REDUCE_CONV
   (mk_comb(`word_zx:int64->byte`,mk_comb(`word:num->int64`,
                                         mk_small_numeral n))));;

let SAFE_EXISTS_RULE rule th =
  let fe,body = dest_exists(concl th) in
  let bth = rule (ASSUME body) in
  CHOOSE (fe,th) (EXISTS (mk_exists(fe,concl bth),fe) bth);;

let CONTAINED_REFL_64 = prove
 (`!(a:int64) n. contained (a,n) (a,n)`,
  REWRITE_TAC[contained; CONTAINED_MODULO_REFL; LE_REFL]);;

let CONTAINED_EMPTY_64 = prove
 (`!(a:int64) b n. contained (a,0) (b,n)`,
  REWRITE_TAC[contained; contained_modulo; LT]);;

(* ------------------------------------------------------------------------- *)
(* ASSUME_CALLEE_SAFETY_TAILED_TAC with the arguments of the theorem rotated *)
(* by specialization rather than by MESON, which is too slow for the general *)
(* theorems for getnoise.                                                    *)
(* ------------------------------------------------------------------------- *)

let ASSUME_CALLEE_SAFETY_TAILED_ALT_TAC =
  let append_lemma = MESON[SAFETY_APPEND_EXISTS]
    `(forall (e:((A)address_uarch_event)list). P e) <=>
      (forall e_tail e. P (APPEND e_tail e))` in
  fun (safety_th:thm) (name:string) ->
    let safety_th' = ONCE_REWRITE_RULE[append_lemma] safety_th in
    let safety_th'' = SAFE_EXISTS_RULE (fun bth ->
      let args,_ = strip_forall(concl bth) in
      GENL ((tl args) @ [hd args]) (SPECL args bth)) safety_th' in
    ASSUME_CALLEE_SAFETY_TAC safety_th'' name;;
