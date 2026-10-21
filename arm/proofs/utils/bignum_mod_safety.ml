(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proofs of the reductions of a k-digit     *)
(* input x modulo a fixed n-digit modulus (n = 4 or 6), bignum_mod_n256,     *)
(* bignum_mod_p384 etc. These all have the same control flow: a direct       *)
(* writeback of x when k < n, a load of the top n digits of x, and a loop    *)
(* reducing one more digit of x per iteration.                               *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;

(* The safety proof of the core of such a function, given the decoding
   theorem, the number n of digits of the modulus, the PC offset where the
   load of the top digits ends and its number of steps, and the PC offset of
   the end of the main loop and its number of steps per iteration. The code
   for k <= n and after the main loop is the same in all these functions. *)

let BIGNUM_MOD_SAFETY_TAC exec n (pre_end,pre_steps) (loop_end,body_steps) =
  let off i = mk_comb(`(+) (pc:num)`,mk_small_numeral i) in
  let inst = subst [mk_small_numeral n,`n:num`] in
  let small_steps = if n = 4 then [9;12;15;17] else [12;15;18;21;24;26] in
  let f_events =
    let args = [`x:int64`; `z:int64`; `k:int64`; `pc:num`] in
    let fev i = mk_var("f_ev_k" ^ string_of_int i,
                       `:int64->int64->int64->num->(uarch_event)list`) in
    list_mk_abs(args,
      itlist (fun i t -> mk_cond(mk_eq(`val(k:int64)`,mk_small_numeral i),
                                 list_mk_comb(fev i,args),t))
       (0--(n-1))
       (inst `APPEND
               (if val k = n
                then f_ev_top (x:int64) (z:int64) (k:int64) (pc:num)
                else APPEND (f_ev_loop_post x z k pc)
                      (APPEND (ENUMERATEL (val k - n) (f_ev_loop x z k pc))
                              (f_ev_loop_pre x z k pc)))
               (f_ev_pre x z k pc):(uarch_event)list`)) in
  let small_cases =
    let k = `k:num` in
    let cases = map (fun i -> mk_eq(k,mk_small_numeral i)) (0--(n-1))
    and k_lt_n = mk_binary "<" (k,mk_small_numeral n) in
    ARITH_RULE(mk_imp(k_lt_n,list_mk_disj cases)),
    ARITH_RULE(mk_imp(mk_neg k_lt_n,list_mk_conj(map mk_neg cases))) in
  CONCRETIZE_F_EVENTS_TAC f_events THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `k' = val (k:int64)` THEN
  SUBGOAL_THEN `k' < 2 EXP 64` ASSUME_TAC THENL
   [EXPAND_TAC "k'" THEN MATCH_ACCEPT_TAC VAL_BOUND_64; ALL_TAC] THEN

  (*** k < n special cases: writeback of k words directly ***)

  ASM_CASES_TAC (inst `k' < n`) THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (fst small_cases)) THEN
    STRIP_TAC THENL
     (map (fun i ->
        ASM_REWRITE_TAC[ARITH] THEN
        (if i = 0 then ALL_TAC
         else SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL))) THEN
        ARM_SIM_TAC exec (1--el i small_steps) THEN
        DISCHARGE_SAFETY_PROPERTY_TAC)
      (0--(n-1)));
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (snd small_cases)) THEN
  ASM_REWRITE_TAC[] THEN

  (*** Load of the top n digits x[k-n..k-1] ***)

  ENSURES_EVENTS_SEQUENCE_TAC (off pre_end)
   (inst `\s. read X0 s = z /\ read X2 s = x /\ read X1 s = word(k' - n)`) THEN
  CONJ_TAC THENL
   [ARM_SIM_TAC ~canonicalize_pc_diff:false exec (1--pre_steps) THEN
    CONJ_TAC THENL
     [IMP_REWRITE_TAC[GSYM WORD_SUB2] THEN
      EXPAND_TAC "k'" THEN ASM_REWRITE_TAC[WORD_VAL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     (inst `word_add (word_shl (word_sub k (word n)) 3) x:int64 =
            word_add x (word (8 * (k' - n)))`) MP_TAC THENL
     [SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL)) THEN
      IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
       [CONV_TAC WORD_RULE; SIMPLE_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL)) THEN
    REWRITE_TAC[ASSUME `val (k:int64) = k'`] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN

  (*** k = n (no loop) vs n < k (main reduction loop) ***)

  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (ARITH_RULE
   (inst `~(k' < n) ==> k' = n \/ (~(k' = n) /\ n < k')`))) THENL
   [ASM_REWRITE_TAC[SUB_REFL;MULT_0] THEN
    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC exec (1--(n / 2 + 1)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (inst `k' - n`) (off (pre_end + 4)) (off loop_end)
   (inst `\i s. read X0 s = z /\ read X2 s = x /\
                read X1 s = word ((k' - n) - i)`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SIMPLE_ARITH_TAC;

    (*** the loop-entry test ***)
    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC exec [1] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [IMP_REWRITE_TAC[VAL_WORD;DIMINDEX_64;MOD_LT] THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[SUB_0]; ALL_TAC] THEN
    SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL)) THEN
    REWRITE_TAC[ASSUME `val (k:int64) = k'`] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    (*** the writeback after the loop ***)
    ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC exec (1--(n / 2)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  (*** the loop body, reducing one more digit ***)

  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
  ARM_STEPS_TAC exec (1--body_steps) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
    IMP_REWRITE_TAC[VAL_WORD;DIMINDEX_64;MOD_LT] THEN
    REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN SIMPLE_ARITH_TAC;
      SIMPLE_ARITH_TAC;
      SIMPLE_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC];
    ALL_TAC] THEN
  SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL)) THEN
  REWRITE_TAC[ASSUME `val (k:int64) = k'`] THEN
  SUBGOAL_THEN
   (inst `word_sub (word (k' - n - i)) (word 1) = word (k' - n - (i + 1)):int64`)
   SUBST_ALL_TAC THENL
   [IMP_REWRITE_TAC[WORD_SUB2] THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY VAL_INT64_TAC [`k':num`; inst `k' - n`] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;
