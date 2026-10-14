(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proofs of bignum_inv_p256,              *)
(* bignum_inv_sm2, bignum_montinv_p256 and bignum_montinv_sm2, which only  *)
(* differ in the field arithmetic around the same divstep loop.            *)
(* ========================================================================= *)

needs "x86/proofs/consttime.ml";;

(* The safety proof of the core, given its decoding theorem and the safety *)
(* theorem of its local divstep subroutine; the PC of the main loop (its   *)
(* start and its end); and the numbers of steps before the loop, of the    *)
(* loop body after the divstep call, and after the loop.                   *)

let BIGNUM_INV_CORE_SAFETY_TAC core_exec divstep_th
    ~loop_pc ~pre_steps ~body_steps ~post_steps =
  let pcoff off = mk_comb(`(+) (pc:num)`,mk_small_numeral off) in
  (* Prepare the safety theorem of subroutine to be used! This is necessary to
     keep introduction of metavariable in the right order. *)
  ASSUME_CALLEE_SAFETY_TAILED_TAC divstep_th
      "H_DIVSTEP59_SAFE" THEN

  CONCRETIZE_F_EVENTS_TAC
    `\(z:int64) (x:int64) (pc:num) (stackpointer:int64).
      APPEND
        (f_ev_loop_post z x pc stackpointer)
        (APPEND
          (ENUMERATEL 9 (f_ev_loop z x pc stackpointer))
            (f_ev_loop_pre z x pc stackpointer))
      :(uarch_event) list` THEN

  REPEAT META_EXISTS_TAC THEN
  STRIP_TAC (* event e *) THEN

  (* functional correctness *)
  MAP_EVERY X_GEN_TAC
   [`z:int64`; `x:int64`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Set up the main loop invariant ***)

  ENSURES_EVENTS_WHILE_UP2_TAC `9` (pcoff loop_pc) (pcoff loop_pc)
   `\i s.
      read RSP s = stackpointer /\
      read (memory :> bytes64(word_add stackpointer (word 224))) s = z /\
      read (memory :> bytes64(word_add stackpointer (word 176))) s =
      word(10 - i)`
  THEN REPEAT CONJ_TAC THENL [
    ARITH_TAC;

    (*** Initial holding of the invariant ***)

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false core_exec (1--pre_steps) THEN
    CONJ_TAC THENL [WORD_ARITH_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** Main invariant proof ***)

    REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    STRIP_EXISTS_ASSUM_TAC THEN
    (* bigstep *)
    (* safety *)
    USE_THEN "H_DIVSTEP59_SAFE"
      (MP_TAC o SPECL [`e:(uarch_event)list`;`stackpointer:int64`;`pc:num`]) THEN
    (* Finally turn '(forall e_stack_spill. ..) ==> ...' to
         'exists e_stack_spill. .. ==> ...' *)
    ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
    META_EXISTS_TAC THEN
    REWRITE_TAC[SOME_FLAGS] THEN
    ANTS_TAC THENL [FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
    X86_BIGSTEP_TAC core_exec "s1" THENL [
      BINOP_TAC THENL [ UNIFY_REFL_TAC; REFL_TAC ] THEN
      NO_TAC;
      ALL_TAC
    ] THEN

    (*** The trivial fact that we loop back ***)

    X86_STEPS_TAC core_exec (2--4) THEN
    SUBGOAL_THEN
     `word_sub (word (10 - i)) (word 1):int64 = word(10 - (i + 1))`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[ARITH_RULE `10 - (i + 1) = (10 - i) - 1`] THEN
      GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < 9 ==> 1 <= 10 - i`];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(val(word(10 - (i + 1)):int64) = 0)`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
    THENL
     [VAL_INT64_TAC `10 - (i + 1)` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `i < 9` THEN ARITH_TAC;
      ALL_TAC] THEN

    X86_STEPS_TAC core_exec (5--body_steps) THEN

    (*** Finish the simulation before proceeding ***)

    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[COND_ID]; ALL_TAC] THEN
    (* since automation of DISCHARGE_SAFETY_PROPERTY_TAC is insufficient,
       manually write the proof here *)
    SAFE_META_EXISTS_TAC allowed_vars_e THEN
    CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
    CONJ_TAC THENL [
      PURE_REWRITE_TAC[APPEND_NIL;CONJUNCT1 APPEND] THEN
      REWRITE_TAC[APPEND_ASSOC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[ENUMERATEL_ADD1] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      UNIFY_F_EVENTS_TAC; ALL_TAC
    ] THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC;

    ALL_TAC
  ] THEN

  (*** Start on the tail computation, with similar divstep reasoning ***)
  REWRITE_TAC[] THEN
  ENSURES_INIT_TAC "s0" THEN
  STRIP_EXISTS_ASSUM_TAC THEN

  USE_THEN "H_DIVSTEP59_SAFE"
      (MP_TAC o SPECL [`e:(uarch_event)list`;`stackpointer:int64`;`pc:num`]) THEN
  (* Finally turn '(forall e_stack_spill. ..) ==> ...' to
        'exists e_stack_spill. .. ==> ...' *)
  ONCE_REWRITE_TAC[GSYM LEFT_EXISTS_IMP_THM] THEN
  META_EXISTS_TAC THEN
  REWRITE_TAC[SOME_FLAGS] THEN
  ANTS_TAC THENL [FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
  X86_BIGSTEP_TAC core_exec "s1" THENL [
    BINOP_TAC THENL [ UNIFY_REFL_TAC; REFL_TAC ] THEN
    NO_TAC;
    ALL_TAC
  ] THEN

  (*** Complete all the simulation first ***)

  X86_STEPS_TAC core_exec (2--post_steps) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  (* since automation of DISCHARGE_SAFETY_PROPERTY_TAC is insufficient,
      manually write the proof here *)
  SAFE_META_EXISTS_TAC allowed_vars_e THEN
  CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
  CONJ_TAC THENL [
    PURE_REWRITE_TAC[APPEND_NIL;CONJUNCT1 APPEND] THEN
    REWRITE_TAC[APPEND_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN UNIFY_F_EVENTS_TAC; ALL_TAC
  ] THEN
  DISCHARGE_MEMACCESS_INBOUNDS_TAC;;

(* The safety proof of the function, given its code and decoding theorem   *)
(* and the safety theorem of the core, a subroutine at offset 0x11.        *)

let BIGNUM_INV_SAFETY_TAC (tmc,exec) core_th =
  ASSUME_CALLEE_SAFETY_TAC core_th "H_CORE_SAFE" THEN
  META_EXISTS_TAC THEN STRIP_TAC THEN

  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
  REMOVE_THEN "H_CORE_SAFE" (fun safe_th ->
    X86_SUBROUTINE_SIM_TAC
      ((GEN_REWRITE_CONV RAND_CONV [tmc] THENC
        REWRITE_CONV[BUTLAST_CLAUSES])
       (mk_comb(`BUTLAST:byte list->byte list`,lhs(concl tmc))),
       exec,
       0x11,
       (GEN_REWRITE_CONV RAND_CONV [tmc] THENC TRIM_LIST_CONV)
       (mk_comb(`TRIM_LIST (17,18):byte list->byte list`,lhs(concl tmc))),
       safe_th)
      [`e:(uarch_event)list`; `read RDI s`; `read RSI s`;
       `pc + 0x11`; `stackpointer:int64`] 1) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;
