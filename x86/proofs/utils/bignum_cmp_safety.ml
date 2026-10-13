(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proofs of the x86 comparisons bignum_ge,  *)
(* bignum_gt, bignum_le and bignum_lt of an m-digit a with an n-digit b.     *)
(* They all have the same control flow; that of bignum_gt and bignum_le is   *)
(* that of bignum_lt and bignum_ge with the lengths m and n (in RDI and RDX) *)
(* exchanged.                                                                *)
(* ========================================================================= *)

needs "x86/proofs/consttime.ml";;

(* The core has two exits, so the trace of a subroutine variant ends with one
   of two different RET events, which X86_ADD_RETURN_NOSTACK_TAC and
   WINDOWS_X86_WRAP_NOSTACK_TAC cannot express through a single f_events
   metavariable. Instead, as in the correctness proofs, the core and the two
   NOIBT subroutine variants are proved by one tactic with an explicit trace.
   Its parameters are whether m and n are exchanged (swap, for bignum_gt and
   bignum_le), the decoding theorem, the map pcoff from offsets in the core
   to PC terms, the numbers npre and nret of extra instructions at the entry
   and at each exit, the extra arguments fev_args of f_events, the tactic
   intro_tac that introduces the remaining variables and the assumptions, and
   the conjuncts stack_inv about the stack carried by the invariants. *)

let BIGNUM_CMP_SAFE_TAC swap execth pcoff npre nret fev_args intro_tac stack_inv =
  let sw = if swap then
    subst [`n:num`,`m:num`; `m:num`,`n:num`; `RDX`,`RDI`; `RDI`,`RDX`] else I
  and swv = if swap then
    subst [`val(n:int64)`,`val(m:int64)`; `val(m:int64)`,`val(n:int64)`] else I in
  let with_stack t =
    let vs,bod = strip_abs t in
    list_mk_abs(vs,list_mk_conj(conjuncts bod @ stack_inv))
  and entry_steps k = 1--(k + npre)
  and exit_steps k = 1--(k + nret)
  and sim_tac = X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
                  ~canonicalize_pc_diff:false execth in
  let f_events =
    let core =
     let vs,bod = strip_abs
     `\(a:int64) (b:int64) (n:int64) (m:int64) (pc:num).
        if val m < val n then
          APPEND
           (APPEND (f_ev_q2 a b n m pc)
             (APPEND (ENUMERATEL (val n - val m) (f_ev_l2 a b n m pc))
                     (f_ev_p2 a b n m pc)))
           (if val m = 0 then f_ev_s1 a b n m pc
            else APPEND (f_ev_q1 a b n m pc)
                  (APPEND (ENUMERATEL (val m) (f_ev_l1 a b n m pc))
                          (f_ev_p1 a b n m pc)))
        else
          APPEND
           (if val m = val n then f_ev_s4 a b n m pc
            else APPEND (f_ev_q4 a b n m pc)
                  (APPEND (ENUMERATEL (val m - val n) (f_ev_l4 a b n m pc))
                          (f_ev_p4 a b n m pc)))
           (if val n = 0 then f_ev_s3 a b n m pc
            else APPEND (f_ev_q3 a b n m pc)
                  (APPEND (ENUMERATEL (val n) (f_ev_l3 a b n m pc))
                          (f_ev_p3 a b n m pc))) :(uarch_event) list` in
     list_mk_abs(vs,swv bod) in
    let vs,bod = strip_abs core in
    let ext f =
      let rty = funpow (length vs) (snd o dest_fun_ty) (type_of f) in
      mk_var(name_of f,itlist (mk_fun_ty o type_of) (vs @ fev_args) rty) in
    let fevs = filter (starts_with "f_ev" o name_of) (frees bod) in
    list_mk_abs(vs @ fev_args,
      subst (map (fun f -> list_mk_comb(ext f,vs @ fev_args),
                           list_mk_comb(f,vs)) fevs) bod) in
  CONCRETIZE_F_EVENTS_TAC f_events THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  W64_GEN_TAC `m:num` THEN X_GEN_TAC `a:int64` THEN
  W64_GEN_TAC `n:num` THEN MAP_EVERY X_GEN_TAC [`b:int64`; `pc:num`] THEN
  intro_tac THEN
  ASM_CASES_TAC (sw `m < n`) THENL
   [SAFETY_COND_TAC (sw `m < n`) THEN
    SUBGOAL_THEN
     (sw `word_add (word_sub (word m) (word n)) (word n):int64 = word m /\
      word_sub (word n) (word m):int64 = word (n - m) /\
      val (word (n - m):int64) = n - m /\ ~(n - m = 0)`)
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [CONV_TAC WORD_RULE;
        IMP_REWRITE_TAC[WORD_SUB2] THEN UNDISCH_TAC (sw `m < n`) THEN ARITH_TAC;
        MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        UNDISCH_TAC (sw `n < 2 EXP 64`) THEN ARITH_TAC;
        UNDISCH_TAC (sw `m < n`) THEN ARITH_TAC];
      ALL_TAC] THEN
    ENSURES_EVENTS_SEQUENCE_TAC (pcoff 0x54)
     (with_stack
       (sw `\s. read RSI s = a /\ read RCX s = b /\ read RDX s = word (n - m) /\
            read R8 s = word m`)) THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC (sw `m = 0`) THENL
       [SAFETY_COND_TAC (sw `m = 0`) THEN
        FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = (sw `m = 0`))) THEN
        sim_tac (entry_steps 7) THEN
        SAFETY_CLOSE_TAC;
        ALL_TAC] THEN
      SAFETY_COND_TAC (sw `m = 0`) THEN
      ENSURES_EVENTS_WHILE_UP2_TAC (sw `m:num`) (pcoff 0x44) (pcoff 0x54)
       (with_stack
         (sw `\i s. read RSI s = a /\ read RCX s = b /\ read RDX s = word (n - m) /\
                read RDI s = word (m - i) /\ read R8 s = word i`)) THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
        sim_tac (entry_steps 7) THEN
        SAFETY_CLOSE_TAC;
        X_GEN_TAC (sw `i:num`) THEN STRIP_TAC THEN
        SAFETY_UPCOUNT_FACTS_TAC (sw `i:num`) (sw `i:num`) (sw `m:num`) (sw `m:num`) THEN
        SAFETY_DOWNCOUNT_FACTS_TAC (sw `i:num`) (sw `m:num`) THEN
        sim_tac (1--5) THEN
        SAFETY_CLOSE_TAC;
        sim_tac [] THEN
        SAFETY_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];
      ENSURES_EVENTS_WHILE_UP2_TAC (sw `n - m`) (pcoff 0x54) (pcoff 0x65)
       (with_stack
         (sw `\i s. read RSI s = a /\ read RCX s = b /\
                read RDX s = word ((n - m) - i) /\ read R8 s = word (m + i)`)) THEN
      REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[SUB_0; ADD_CLAUSES; ENUMERATEL_APPEND_ZERO] THEN
        sim_tac [] THEN
        SAFETY_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;
        X_GEN_TAC (sw `i:num`) THEN STRIP_TAC THEN
        SAFETY_DOWNCOUNT_FACTS_TAC (sw `i:num`) (sw `n - m`) THEN
        SUBGOAL_THEN
         (sw `val (word (m + i):int64) = m + i /\
          word_add (word (m + i)) (word 1):int64 = word (m + (i + 1)) /\
          m + i < n`)
        STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
            MAP_EVERY UNDISCH_TAC [(sw `i < n - m`); (sw `n < 2 EXP 64`)] THEN ARITH_TAC;
            REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC];
            UNDISCH_TAC (sw `i < n - m`) THEN ARITH_TAC];
          ALL_TAC] THEN
        sim_tac (1--5) THEN
        SAFETY_CLOSE_TAC;
        SAFETY_CARRY_REASSOC_TAC THEN
        sim_tac (exit_steps 2) THEN
        SAFETY_CLOSE_TAC]];
    SAFETY_COND_TAC (sw `m < n`) THEN
      SUBGOAL_THEN
       (sw `word_sub (word m) (word n):int64 = word (m - n) /\
        word_add (word (m - n)) (word 1):int64 = word (m - n + 1)`)
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [IMP_REWRITE_TAC[WORD_SUB2] THEN UNDISCH_TAC (sw `~(m < n)`) THEN ARITH_TAC;
          REWRITE_TAC[GSYM WORD_ADD]];
        ALL_TAC] THEN
      ENSURES_EVENTS_SEQUENCE_TAC (pcoff 0x2d)
       (with_stack
         (sw `\s. read RSI s = a /\ read RCX s = b /\ read RDI s = word (m - n + 1) /\
              read R8 s = word n`)) THEN
      CONJ_TAC THENL
       [ASM_CASES_TAC (sw `n = 0`) THENL
         [SAFETY_COND_TAC (sw `n = 0`) THEN
          FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = (sw `n = 0`))) THEN
          sim_tac (entry_steps 6) THEN
          SAFETY_CLOSE_TAC;
          ALL_TAC] THEN
        SAFETY_COND_TAC (sw `n = 0`) THEN
        ENSURES_EVENTS_WHILE_UP2_TAC (sw `n:num`) (pcoff 0x10) (pcoff 0x20)
         (with_stack
           (sw `\i s. read RSI s = a /\ read RCX s = b /\ read RDI s = word (m - n + 1) /\
                  read RDX s = word (n - i) /\ read R8 s = word i`)) THEN
        REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
          sim_tac (entry_steps 6) THEN
          SAFETY_CLOSE_TAC;
          X_GEN_TAC (sw `i:num`) THEN STRIP_TAC THEN
          SAFETY_UPCOUNT_FACTS_TAC (sw `i:num`) (sw `i:num`) (sw `n:num`) (sw `n:num`) THEN
          SAFETY_DOWNCOUNT_FACTS_TAC (sw `i:num`) (sw `n:num`) THEN
          SUBGOAL_THEN (sw `i < m`) ASSUME_TAC THENL
           [MAP_EVERY UNDISCH_TAC [(sw `i < n`); (sw `~(m < n)`)] THEN ARITH_TAC; ALL_TAC] THEN
          sim_tac (1--5) THEN
          SAFETY_CLOSE_TAC;
          sim_tac (1--1) THEN
          SAFETY_CLOSE_TAC];
        ASM_CASES_TAC (sw `m:num = n`) THENL
         [SAFETY_COND_TAC (sw `m:num = n`) THEN
          SUBGOAL_THEN (sw `m - n + 1 = 1`) ASSUME_TAC THENL
           [UNDISCH_TAC (sw `m:num = n`) THEN ARITH_TAC; ALL_TAC] THEN
          FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = (sw `m:num = n`))) THEN
          sim_tac (exit_steps 4) THEN
          SAFETY_CLOSE_TAC;
          ALL_TAC] THEN
        SAFETY_COND_TAC (sw `m:num = n`) THEN
        ENSURES_EVENTS_WHILE_UP2_TAC (sw `m - n`) (pcoff 0x2d) (pcoff 0x2d)
         (with_stack
           (sw `\i s. read RSI s = a /\ read RCX s = b /\
                  read RDI s = word ((m - n + 1) - i) /\ read R8 s = word (n + i)`)) THEN
        REPEAT CONJ_TAC THENL
         [UNDISCH_TAC (sw `~(m:num = n)`) THEN UNDISCH_TAC (sw `~(m < n)`) THEN ARITH_TAC;
          REWRITE_TAC[SUB_0; ADD_CLAUSES; ENUMERATEL_APPEND_ZERO] THEN
          sim_tac [] THEN
          SAFETY_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC;
          X_GEN_TAC (sw `i:num`) THEN STRIP_TAC THEN
          SUBGOAL_THEN
           (sw `word_sub (word ((m - n + 1) - i)) (word 1):int64 = word (m - n - i) /\
            val (word (m - n - i):int64) = m - n - i /\ ~(m - n - i = 0) /\
            (m - n + 1) - (i + 1) = m - n - i /\
            val (word (n + i):int64) = n + i /\
            word_add (word (n + i)) (word 1):int64 = word (n + (i + 1)) /\
            n + i < m`)
          STRIP_ASSUME_TAC THENL
           [REPEAT CONJ_TAC THENL
             [IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
               [AP_TERM_TAC THEN UNDISCH_TAC (sw `i < m - n`) THEN ARITH_TAC;
                UNDISCH_TAC (sw `i < m - n`) THEN ARITH_TAC];
              MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
              UNDISCH_TAC (sw `m < 2 EXP 64`) THEN ARITH_TAC;
              UNDISCH_TAC (sw `i < m - n`) THEN ARITH_TAC;
              UNDISCH_TAC (sw `i < m - n`) THEN ARITH_TAC;
              MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
              MAP_EVERY UNDISCH_TAC [(sw `i < m - n`); (sw `m < 2 EXP 64`)] THEN ARITH_TAC;
              REWRITE_TAC[GSYM WORD_ADD; ADD_ASSOC];
              UNDISCH_TAC (sw `i < m - n`) THEN ARITH_TAC];
            ALL_TAC] THEN
          sim_tac (1--5) THEN
          SAFETY_CLOSE_TAC;
          SUBGOAL_THEN (sw `(m - n + 1) - (m - n) = 1`) ASSUME_TAC THENL
           [ARITH_TAC; ALL_TAC] THEN
          SAFETY_CARRY_REASSOC_TAC THEN
          sim_tac (exit_steps 4) THEN
          SAFETY_CLOSE_TAC]]];;
