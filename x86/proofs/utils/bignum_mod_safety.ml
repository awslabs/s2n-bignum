(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proofs of the x86 reductions of a k-digit *)
(* input x modulo a fixed n-digit modulus (n = 4 or 6), bignum_mod_p256,     *)
(* bignum_mod_n384 etc. These all have the same control flow: a direct       *)
(* writeback of x when k < n, a load of the top n digits of x, and a loop    *)
(* reducing one more digit of x per iteration.                               *)
(* ========================================================================= *)

needs "x86/proofs/consttime.ml";;

(* Containment of a word-indexed byte access buf[j..j+7] within [buf, n * 8]
   whenever j + 8 <= n * 8. Used for the loads of the top digits of x. *)

let BIGNUM_MOD_SAFETY_CONTAINED = prove
 (`!(a:int64) (n:num) (j:num).
      j + 8 <= n * 8
      ==> contained_modulo (2 EXP 64)
            (val(word_add a (word j)),8) (val a, n * 8)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[contained_modulo] THEN
  X_GEN_TAC `d:num` THEN DISCH_TAC THEN EXISTS_TAC `j + d` THEN
  CONJ_TAC THENL
   [ ASM_ARITH_TAC;
     REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
     REWRITE_TAC[CONG] THEN CONV_TAC MOD_DOWN_CONV THEN
     AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC ]);;

let rec BIGNUM_MOD_SAFETY_CONTAIN_TAC g =
  (FIRST [ MATCH_MP_TAC BIGNUM_MOD_SAFETY_CONTAINED THEN SIMPLE_ARITH_TAC;
           DISJ1_TAC THEN BIGNUM_MOD_SAFETY_CONTAIN_TAC;
           DISJ2_TAC THEN BIGNUM_MOD_SAFETY_CONTAIN_TAC ]) g;;

let BIGNUM_MOD_SAFETY_CONS_APPEND = prove
 (`!(h:A) t. CONS h t = APPEND [h] t`, REWRITE_TAC[APPEND]);;

(* The main-loop load reads x[i-1] as word_add x (word (8*(k'-n-i)) - 8),
   with the "- 8" appearing as + (2 EXP 64 - 8) after modular subtraction. *)

let BIGNUM_MOD_SAFETY_OFFSET_DEC = prove
 (`!(x:int64) (a:num). 1 <= a
    ==> word_add x (word (8 * a + (2 EXP 64 - 8))):int64 =
        word_add x (word (8 * (a - 1)))`,
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_EQ; CONG; DIMINDEX_64] THEN
  MP_TAC(ARITH_RULE
   `1 <= a ==> 8 * a + (2 EXP 64 - 8) = 8 * (a - 1) + 1 * 2 EXP 64`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

(* The safety proof of the core of such a function, parameterized like the
   functional-correctness `tac`s by the executable decoding rule and a shift
   of the PC offsets, so that it applies to the System V core (shift 0) and to
   the Windows core (shift 11, the size of its entry shim). The other
   parameters are the number n of digits of the modulus, the register xreg
   holding x after the top digits are loaded, the PC offset where that load
   ends and its number of steps, and the PC offsets of the start and end of
   the main loop and its number of steps per iteration. The code for k <= n
   and after the main loop is the same in all these functions. *)

let BIGNUM_MOD_SAFETY_TAC execth shift n xreg (pre_end,pre_steps)
                          (loop_start,loop_end,body_steps) =
  let off i = mk_comb(`(+) (pc:num)`, mk_small_numeral(i + shift)) in
  let inst = subst [mk_small_numeral n,`n:num`] in
  let inv = subst [xreg,`RCX`] o inst in
  let small_steps = if n = 4 then [12;15;18;20] else [16;19;22;25;28;30] in
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
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `k' = val(k:int64)` THEN
  SUBGOAL_THEN `k' < 2 EXP 64` ASSUME_TAC THENL
   [ EXPAND_TAC "k'" THEN MATCH_ACCEPT_TAC VAL_BOUND_64; ALL_TAC ] THEN

  (*** k < n special cases: writeback of k words directly ***)

  ASM_CASES_TAC (inst `k' < n`) THENL
   [ FIRST_ASSUM(MP_TAC o MATCH_MP (fst small_cases)) THEN
     STRIP_TAC THENL
      (map (fun i ->
         ASM_REWRITE_TAC[ARITH] THEN
         (if i = 0 then ALL_TAC
          else SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL))) THEN
         ENSURES_INIT_TAC "s0" THEN
         X86_STEPS_TAC execth (1--el i small_steps) THEN
         ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
         DISCHARGE_SAFETY_PROPERTY_TAC)
       (0--(n-1)));
     ALL_TAC ] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (snd small_cases)) THEN
  ASM_REWRITE_TAC[] THEN

  (*** Prologue: read the top n digits x[k-n..k-1] ***)

  ENSURES_EVENTS_SEQUENCE_TAC (off pre_end)
   (inv `\s. read RDI s = z /\ read RCX s = x /\
             read RSI s = word(k' - n)`) THEN
  CONJ_TAC THENL
   [ ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC execth (1--pre_steps) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN (inst `word_sub k (word n):int64 = word(k' - n)`)
      ASSUME_TAC THENL
      [ SUBST1_TAC (ISPEC `k:int64` (GSYM WORD_VAL)) THEN ASM_REWRITE_TAC[] THEN
        IMP_REWRITE_TAC[WORD_SUB2] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
     SUBGOAL_THEN (inst `val(word(k' - n):int64) = k' - n`) ASSUME_TAC THENL
      [ MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        SIMPLE_ARITH_TAC; ALL_TAC ] THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[GSYM(ASSUME `val(k:int64) = k'`)] THEN
     GEN_DISCHARGE_SAFETY_PROPERTY_TAC
      (ASM_REWRITE_TAC[] THEN
       REWRITE_TAC[memaccess_inbounds; ALL; EX; FST; SND] THEN
       REPEAT CONJ_TAC THEN BIGNUM_MOD_SAFETY_CONTAIN_TAC);
     ALL_TAC ] THEN

  (*** k = n (no loop) vs n < k (main reduce loop) ***)

  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP (ARITH_RULE
   (inst `~(k' < n) ==> k' = n \/ (~(k' = n) /\ n < k')`))) THENL
   [ ASM_REWRITE_TAC[SUB_REFL; MULT_0] THEN
     ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
     X86_STEPS_TAC execth (1--(n+2)) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     CONV_TAC NUM_REDUCE_CONV THEN DISCHARGE_SAFETY_PROPERTY_TAC;
     ALL_TAC ] THEN
  ASM_REWRITE_TAC[] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC (inst `k' - n`) (off loop_start) (off loop_end)
   (inv `\i s. read RDI s = z /\ read RCX s = x /\
               read RSI s = word((k' - n) - i)`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ (*** loop is nonempty ***)
     SIMPLE_ARITH_TAC;

     (*** pre-block: the loop-entry test/branch ***)
     ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
     X86_STEPS_TAC execth (1--2) THEN
     ENSURES_FINAL_STATE_TAC THEN
     ASM_REWRITE_TAC[SUB_0; ENUMERATEL; APPEND] THEN
     SUBGOAL_THEN (inst `val(word(k' - n):int64) = k' - n`) ASSUME_TAC THENL
      [ MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        SIMPLE_ARITH_TAC; ALL_TAC ] THEN
     SUBGOAL_THEN (inst `~(val(word(k' - n):int64) = 0)`) ASSUME_TAC THENL
      [ ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
     ASM_REWRITE_TAC[] THEN
     SAFE_META_EXISTS_TAC allowed_vars_e THEN
     CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
     W (fun (asl,w) -> (if is_conj w then (CONJ_TAC THENL
        [ CONV_TAC(LAND_CONV(REWR_CONV BIGNUM_MOD_SAFETY_CONS_APPEND)) THEN
          FULL_UNIFY_F_EVENTS_TAC; ALL_TAC ]) else ALL_TAC)) THEN
     ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[memaccess_inbounds; ALL; EX; FST; SND] THEN
     REPEAT CONJ_TAC THEN BIGNUM_MOD_SAFETY_CONTAIN_TAC;

     (*** loop body: reduce one digit ***)
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN
     ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
     X86_STEPS_TAC execth (1--body_steps) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN
      (inst `word_sub (word(k' - n - i)) (word 1):int64 = word(k' - n - (i+1))`)
      ASSUME_TAC THENL
      [ IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
         [ AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC ]; ALL_TAC ] THEN
     SUBGOAL_THEN (inst `val(word(k' - n - i):int64) = k' - n - i`)
      ASSUME_TAC THENL
      [ MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        SIMPLE_ARITH_TAC; ALL_TAC ] THEN
     SUBGOAL_THEN
      (inst `(~(val(word(k' - n - (i+1)):int64) = 0)) <=> i + 1 < k' - n`)
      ASSUME_TAC THENL
      [ IMP_REWRITE_TAC[VAL_WORD_EQ; DIMINDEX_64] THEN SIMPLE_ARITH_TAC;
        ALL_TAC ] THEN
     ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN (inst `8 * (k' - n - i) + 18446744073709551608 =
                         8 * (k' - n - i) + (2 EXP 64 - 8)`) SUBST1_TAC THENL
      [ ARITH_TAC; ALL_TAC ] THEN
     ASM_SIMP_TAC[BIGNUM_MOD_SAFETY_OFFSET_DEC;
                  ARITH_RULE (inst `i < k' - n ==> 1 <= k' - n - i`)] THEN
     SUBGOAL_THEN (inst `k' - n - i - 1 = k' - n - (i + 1)`) SUBST1_TAC THENL
      [ ARITH_TAC; ALL_TAC ] THEN
     CONJ_TAC THENL [ COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC ] THEN
     REWRITE_TAC[GSYM(ASSUME `val(k:int64) = k'`)] THEN
     GEN_DISCHARGE_SAFETY_PROPERTY_TAC
      (REWRITE_TAC[ASSUME `val(k:int64) = k'`]);

     (*** post-block: final writeback ***)
     REWRITE_TAC[SUB_REFL] THEN
     ENSURES_INIT_TAC "s0" THEN STRIP_EXISTS_ASSUM_TAC THEN
     X86_STEPS_TAC execth (1--n) THEN
     ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
     DISCHARGE_SAFETY_PROPERTY_TAC ];;
