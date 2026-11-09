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
needs "arm/proofs/utils/mldsa_native_polyvec.ml";;

let MLD_BYTES128_HALVES = prove
 (`!a:int64 n s:armstate.
        read (memory :> bytes(a,32)) s = n
        ==> read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
            read (memory :> bytes128(word_add a (word 16))) s =
            word(n DIV 2 EXP 128)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `340282366920938463463374607431768211456 =
                          2 EXP (8 * 16)`; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let MLD_BYTES_32_OF_HALVES = prove
 (`!a:int64 n s:armstate.
        n < 2 EXP 256 /\
        read (memory :> bytes128 a) s = word(n MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(n DIV 2 EXP 128)
        ==> read (memory :> bytes(a,32)) s = n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `32 = 16 + 16`; READ_BYTES_COMBINE] THEN
  MP_TAC(ISPECL [`a:int64`; `16`; `read memory s`] READ_BYTES_BOUND) THEN
  MP_TAC(ISPECL [`word_add a (word 16):int64`; `16`; `read memory s`]
                READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `n DIV 340282366920938463463374607431768211456 <
                340282366920938463463374607431768211456`
   (fun th -> REWRITE_TAC[MATCH_MP MOD_LT th]) THENL
   [UNDISCH_TAC `n < 2 EXP 256` THEN SIMP_TAC[RDIV_LT_EQ; ARITH_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    MESON_TAC[DIVISION_SIMP; ADD_SYM; MULT_SYM]]);;

let MLD_BYTES2 = prove
 (`(!a s:armstate.
        read (memory :> bytes(a,2)) s =
        val(read (memory :> bytes16 a) s)) /\
   (!a s:armstate.
        read (memory :> bytes(a,2)) s =
        val(read (memory :> bytes8 a) s) +
        256 * val(read (memory :> bytes8(word_add a (word 1))) s))`,
  CONJ_TAC THEN REPEAT GEN_TAC THENL
   [REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
                DIMINDEX_16] THEN
    CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[ARITH_RULE `2 = 1 + 1`; READ_COMPONENT_COMPOSE;
                READ_BYTES_COMBINE; BYTES8_WBYTES; VAL_READ_WBYTES;
                DIMINDEX_8] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC]);;

let MLD_SEED_INPUT = prove
 (`!a:int64 r i j s:armstate.
        r < 2 EXP 256 /\
        read (memory :> bytes128 a) s = word(r MOD 2 EXP 128) /\
        read (memory :> bytes128(word_add a (word 16))) s =
        word(r DIV 2 EXP 128) /\
        read (memory :> bytes(word_add a (word 32),2)) s = j + 256 * i
        ==> read (memory :> bytes(a,34)) s = mld_matrix_seed r i j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `read (memory :> bytes(a,32)) s = r` ASSUME_TAC THENL
   [MATCH_MP_TAC MLD_BYTES_32_OF_HALVES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mld_matrix_seed; ARITH_RULE `34 = 32 + 2`;
              READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

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
   `!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word c)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then a else b))` in
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

let MEXP_INPUT_TAC =
  let th = CONV_RULE NUM_REDUCE_CONV MLD_SEED_INPUT in
  fun off i j s ->
    let sl = MEXP_SP off and a32 = MEXP_SP(off + 32) in
    let n = mk_small_numeral(j + 256 * i) in
    SUBGOAL_THEN
     (mk_eq(list_mk_comb(`read:(armstate,num)component->armstate->num`,
                         [mk_comb(`(:>) memory:(int64->byte,num)component->
                                   (armstate,num)component`,
                                  mk_comb(`bytes:int64#num->
                                           (int64->byte,num)component`,
                                          mk_pair(a32,`2`)));
                          s]),n))
    ASSUME_TAC THENL
     [(REWRITE_TAC[CONJUNCT1 MLD_BYTES2] THEN ASM_REWRITE_TAC[] THEN
       CONV_TAC WORD_REDUCE_CONV THEN NO_TAC) ORELSE
      (REWRITE_TAC[CONJUNCT2 MLD_BYTES2] THEN
       CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
       ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
       CONV_TAC NUM_REDUCE_CONV);
      ALL_TAC] THEN
    MP_TAC(SPECL [sl; `r:num`; mk_small_numeral i; mk_small_numeral j; s]
                 th) THEN
    ANTS_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      DISCH_TAC];;

let MEXP_HYP_TAC i j =
  FIRST_ASSUM(fun hth ->
    match concl hth with
      Comb(Const("!",_),Abs(Var("i",_),_)) ->
        let th1 = SPECL [mk_small_numeral i; mk_small_numeral j] hth in
        ASSUME_TAC(MP th1 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th1)))))
    | _ -> NO_TAC);;

(*** The bound on rho and the termination hypothesis for each entry ***)

let MEXP_SETUP_TAC k l s =
  SUBGOAL_THEN `r < 2 EXP 256` (ASSUME_TAC o CONV_RULE NUM_REDUCE_CONV) THENL
   [FIRST_ASSUM(MP_TAC o SYM o check
     (can (term_match [] `read (memory :> bytes(rho,32)) s = n`) o concl)) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
    MP_TAC(ISPECL [`rho:int64`; `32`; mk_comb(`read memory`,s)]
                  READ_BYTES_BOUND) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[mld_matrix_terminates] o check
    (can (term_match [] `mld_matrix_terminates k l r`) o concl)) THEN
  MAP_EVERY (fun e -> MEXP_HYP_TAC (e / l) (e mod l)) (0--(k * l - 1));;

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
