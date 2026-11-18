(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics for the expansion of the matrix (the code for          *)
(* mld_polyvec_matrix_expand_eager): rho is loaded as two 128-bit words and  *)
(* stored, with the indices j and i of an entry as two bytes after it, in    *)
(* buffers of 64 bytes on the stack aligned to 32 bytes (so that their       *)
(* address depends on whether the stack pointer is a multiple of 32), which  *)
(* the sampler reads as 34 bytes. As for mlkem's gen_matrix proofs.          *)
(* ========================================================================= *)

needs "common/mldsa_native_sampling.ml";;
needs "common/fips204/properties/mldsa_native_polyvec.ml";;

let MLD_ALIGNED_16_32 = prove
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

(* ------------------------------------------------------------------------- *)
(* MEXP_BUFFER_ADDRESS_RULE c a b proves, for the address of the buffers in  *)
(* the simulation, sp + c rounded down to 32, that it is sp + a if sp is a   *)
(* multiple of 32 and sp + b otherwise; MEXP_BUFFER_TAC th rewrites the      *)
(* assumptions with that, by the case of the stack pointer.                  *)
(* ------------------------------------------------------------------------- *)

let MEXP_BUFFER_ADDRESS_RULE c a b =
  let tm = subst [mk_small_numeral c,`c:num`; mk_small_numeral a,`a:num`;
                  mk_small_numeral b,`b:num`]
   `!sptr:int64.
        aligned 16 sptr
        ==> word_and (word_add sptr (word c)) (word 18446744073709551584) =
            word_add sptr (word(if aligned 32 sptr then a else b))` in
  prove(tm,
    REWRITE_TAC[MLD_ALIGNED_16_32] THEN GEN_TAC THEN
    COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
    W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let MEXP_BUFFER_TAC bth =
  FIRST_ASSUM(fun th ->
    if concl th = `aligned 32 (stackpointer:int64)` ||
       concl th = `~aligned 32 (stackpointer:int64)`
    then RULE_ASSUM_TAC(REWRITE_RULE
          [REWRITE_RULE[th; ASSUME `aligned 16 (stackpointer:int64)`]
            (SPEC `stackpointer:int64` bth)])
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* The seed of entry (i,j) in the buffer at stackpointer + off, from the two *)
(* halves of rho stored there and the bytes j and i after it (stored as two  *)
(* bytes or as a 16-bit word), and the termination hypothesis for it.        *)
(* ------------------------------------------------------------------------- *)

let MEXP_SP n =
  mk_comb(mk_comb(`word_add:int64->int64->int64`,`stackpointer:int64`),
          mk_comb(`word:num->int64`,mk_small_numeral n));;

let MEXP_SEED i j =
  list_mk_comb(`mld_matrix_seed`,
               [`r:num`; mk_small_numeral i; mk_small_numeral j]);;

let MEXP_HYP_TAC i j =
  FIRST_ASSUM(fun hth ->
    match concl hth with
      Comb(Const("!",_),Abs(Var("i",_),_)) ->
        let th1 = SPECL [mk_small_numeral i; mk_small_numeral j] hth in
        ASSUME_TAC(MP th1 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th1)))))
    | _ -> NO_TAC);;

(*** The postcondition, from those of the calls for each entry ***)

let MEXP_JOIN_TAC n =
  let jth = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
             (GEN `P:num->bool`
               (SPECL [`P:num->bool`; `256`; mk_small_numeral n]
                      VEC_JOIN_ALL)) in
  MATCH_MP_TAC jth THEN
  SIMP_TAC[MLD_POLYVEC_MATRIX_EXPAND_COEFF] THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC POLYVEC_INDEX_CONV THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_SIMP_TAC[]);;
