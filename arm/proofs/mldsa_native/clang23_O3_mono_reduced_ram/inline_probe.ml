(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The stack probe of the prologue of a function of the clang 23 build with  *)
(* a frame of more than 4096 bytes, for the proofs of pk_from_sk and         *)
(* keypair_internal: the lemmas and tactics of the proof of                  *)
(* mldsa44_verify_internal (verify_internal_44_proof.ml), with the size N of *)
(* the stack of the statement as a parameter. The stack pointer goes down by *)
(* 4096 at a time to below the frame and is compared (signed) with the       *)
(* aligned frame x9. With 32768 <= val sp0 < 2^63 for the stack pointer sp0  *)
(* at the call and sp = sp0 - N, the values of the signed comparisons are    *)
(* those of the offsets: KGP_SP_BOUNDS_TAC N states val sp + N < 2^63 and    *)
(* 32768 - N <= val sp, and KGP_PROBE_TAC N exec n simulates the instruction *)
(* n and decides a branch on those comparisons.                              *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/inline_sign.ml";;
needs "arm/proofs/utils/mldsa_native_verify.ml";;

let KGP_VAL_ADD = prove
 (`!(sp:int64) n m. n <= val(word_add sp (word n):int64) /\
                    val(word_add sp (word n):int64) < 2 EXP 63 /\ m <= n
    ==> val(word_add sp (word m):int64) = val sp + m /\ val sp + m < 2 EXP 63`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n < 2 EXP 63` ASSUME_TAC THENL [ASM_MESON_TAC[LET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `m < 2 EXP 63` ASSUME_TAC THENL [ASM_MESON_TAC[LET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `val(word n:int64) = n /\ val(word m:int64) = m` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`sp:int64`; `word n:int64`] VAL_WORD_ADD_CASES) THEN
  MP_TAC(ISPECL [`sp:int64`; `word m:int64`] VAL_WORD_ADD_CASES) THEN
  MP_TAC(SPEC `sp:int64` VAL_BOUND_64) THEN
  ASM_REWRITE_TAC[DIMINDEX_64] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_64]) THEN
  REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `val(sp:int64) + n < 2 EXP 64` THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    UNDISCH_TAC `n <= val(word_add sp (word n):int64)` THEN
    UNDISCH_TAC `val(word_add sp (word n):int64) < 2 EXP 63` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let KGP_IVAL_ADD = prove
 (`!s:int64 k. val s + k < 2 EXP 63 ==> ival(word_add s (word k)) = &(val s) + &k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word_add s (word k):int64) = val s + k` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `k < 2 EXP 64` (fun th -> SIMP_TAC[th; MOD_LT]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word_add s (word k):int64) < 2 EXP (dimindex(:64) - 1)`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[IVAL_EQ_VAL; INT_OF_NUM_ADD]);;

(*** val stackpointer + N < 2^63 and 32768 - N <= val stackpointer ***)

let KGP_SP_BOUNDS_TAC n =
  let nt = mk_small_numeral n and lo = mk_small_numeral(32768 - n) in
  MP_TAC(SPECL [`stackpointer:int64`; nt; nt] KGP_VAL_ADD) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN (subst [lo,`LO:num`] `LO <= val(stackpointer:int64)`) ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC];;

let KGP_SP_PC_CONV =
  REWRITE_CONV[VERIF_PTR_SUB; INT_ARITH `!v a b:int. (v + a) - (v + b) = a - b`;
               INT_ARITH `!v a b:int. (v + a) - (v - b) = a + b`;
               INT_ARITH `!v a b:int. (v - a) - (v + b) = --(a + b)`;
               INT_ARITH `!v a b:int. (v - a) - (v - b) = b - a`] THENC
  DEPTH_CONV WORD_RED_CONV THENC
  REWRITE_CONV[INT_OF_NUM_EQ; INT_OF_NUM_LT; ARITH_EQ; ARITH_LT; ARITH_LE;
               INT_LT_REFL; INT_OF_NUM_LE] THENC
  DEPTH_CONV INT_RED_CONV THENC REWRITE_CONV[];;

let KGP_NEGSUB = WORD_RULE `word_sub (s:int64) y = word_add s (word_neg y)`;;

let KGP_NEGADD_CONV tm =
  match tm with
    Comb(Comb(Const("word_add",_),s),Comb(Const("word",_),k))
      when is_numeral k && type_of tm = `:int64` &&
           dest_numeral k >=/ ((Num.num_of_int 2) **/ (Num.num_of_int 63)) ->
      let m = ((Num.num_of_int 2) **/ (Num.num_of_int 64)) -/ dest_numeral k in
      let rhs_tm = mk_comb(mk_comb(`word_sub:int64->int64->int64`,s),
                           mk_comb(`word:num->int64`,mk_numeral m)) in
      prove(mk_eq(tm,rhs_tm),
            REWRITE_TAC[KGP_NEGSUB] THEN
            CONV_TAC(RAND_CONV(RAND_CONV WORD_REDUCE_CONV)) THEN REFL_TAC)
  | _ -> failwith "KGP_NEGADD_CONV";;

let KGP_PROBE_PC_TAC n =
  let nt = mk_small_numeral n and lot = mk_small_numeral(32768 - n) in
  let isadd t = can (term_match [] `ival(word_add (stackpointer:int64) (word k))`) t
  and issub t = can (term_match [] `ival(word_sub (stackpointer:int64) (word k))`) t in
  W(fun (asl,w) ->
    let hyps = end_itlist CONJ (map snd (filter (fun (_,th) ->
      mem (concl th) [subst [nt,`NT:num`] `val(stackpointer:int64) + NT < 2 EXP 63`;
                      subst [lot,`LO:num`] `LO <= val(stackpointer:int64)`]) asl)) in
    let side tm = MP (ARITH_RULE(mk_imp(concl hyps,tm))) hyps in
    RULE_ASSUM_TAC(fun th ->
      let c = concl th in
      if is_eq c && is_comb(lhand c) &&
         rator(lhand c) = `read PC:armstate->int64` &&
         free_in `stackpointer:int64` (rhs c)
      then
        let th1 = CONV_RULE(RAND_CONV(REWRITE_CONV[VERIF_PTR_SUB] THENC
                                      DEPTH_CONV WORD_RED_CONV THENC
                                      DEPTH_CONV KGP_NEGADD_CONV)) th in
        let ts = setify(find_terms (fun t -> isadd t || issub t) (concl th1)) in
        let eqs = map (fun t ->
          let k = rand(rand(rand t)) in
          if isadd t then
            MP (SPECL [`stackpointer:int64`; k] KGP_IVAL_ADD)
               (side (subst [k,`k:num`] `val(stackpointer:int64) + k < 2 EXP 63`))
          else
            MP (SPECL [`stackpointer:int64`; k] IVAL_SP_SUB)
               (side (subst [k,`k:num`]
                 `k <= val(stackpointer:int64) /\ val stackpointer < 2 EXP 63 /\
                  k < 2 EXP 63`))) ts in
        CONV_RULE(RAND_CONV(REWRITE_CONV eqs THENC KGP_SP_PC_CONV)) th1
      else th));;

let KGP_PROBE_TAC nn exec n =
  ARM_STEPS_TAC exec [n] THEN KGP_PROBE_PC_TAC nn;;

