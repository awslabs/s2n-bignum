(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proof of the cores of bignum_cmadd and  *)
(* bignum_cmnegadd, which only differ in the arithmetic of their loops.    *)
(* ========================================================================= *)

needs "x86/proofs/consttime.ml";;

(* The safety proof of the core, given its decoding theorem; the PCs of    *)
(* the start and the end of the multiply-add loop and the numbers of steps *)
(* of its first and later iterations; the number of steps when there is no *)
(* carry word (top_steps) or one (one_carry_steps); and the PCs of the     *)
(* carry loop and the number of steps of its first iteration.              *)

let BIGNUM_CMADD_SAFETY_TAC exec
    ~mul_start ~mul_end ~mul_first ~mul_body ~top_steps ~one_carry_steps
    ~carry_start ~carry_end ~carry_first =
  let pcoff off = mk_comb(`(+) (pc:num)`,mk_small_numeral off) in
  CONCRETIZE_F_EVENTS_TAC
   `\(x:int64) (z:int64) (p:int64) (n:int64) (pc:num).
      if MIN (val n) (val p) = 0 then f_ev_m0 x z p n pc
      else
       APPEND
        (if MIN (val n) (val p) = val p then f_ev_t0 x z p n pc
         else if MIN (val n) (val p) + 1 = val p then f_ev_t1 x z p n pc
         else APPEND (f_ev_tpost x z p n pc)
               (APPEND (ENUMERATEL (val p - (MIN (val n) (val p) + 1))
                                   (f_ev_carry x z p n pc))
                       (f_ev_cpre x z p n pc)))
        (if MIN (val n) (val p) = 1 then f_ev_c1 x z p n pc
         else APPEND []
               (APPEND (ENUMERATEL (MIN (val n) (val p) - 1)
                                   (f_ev_mul x z p n pc))
                       (f_ev_mpre x z p n pc))) :(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  W64_GEN_TAC `p:num` THEN X_GEN_TAC `z:int64` THEN X_GEN_TAC `c:int64` THEN
  W64_GEN_TAC `n:num` THEN MAP_EVERY X_GEN_TAC [`x:int64`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; C_ARGUMENTS; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(if p < n then word p else word n):int64 = word (MIN n p) /\
    val (word (MIN n p):int64) = MIN n p /\ MIN n p <= p /\ MIN n p <= n /\
    word_sub (word p) (word (MIN n p)):int64 = word (p - MIN n p) /\
    val (word (p - MIN n p):int64) = p - MIN n p`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC;
      ARITH_TAC; ARITH_TAC;
      IMP_REWRITE_TAC[WORD_SUB2] THEN ARITH_TAC;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC];
    ALL_TAC] THEN

  (*** The degenerate case MIN n p = 0 ***)

  ASM_CASES_TAC `MIN n p = 0` THENL
   [SAFETY_COND_TAC `MIN n p = 0` THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `MIN n p = 0`)) THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--7) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  SAFETY_COND_TAC `MIN n p = 0` THEN

  (*** The multiply-add (or multiply-subtract) loop over the first MIN n p
       words ***)

  ENSURES_EVENTS_SEQUENCE_TAC (pcoff mul_end)
   `\s. read RDI s = word (p - MIN n p) /\ read RSI s = z /\
        read R10 s = word (MIN n p)` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `MIN n p = 1` THENL
     [SAFETY_COND_TAC `MIN n p = 1` THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o
        check (fun th -> concl th = `MIN n p = 1`)) THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false exec (1--mul_first) THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      ALL_TAC] THEN
    SAFETY_COND_TAC `MIN n p = 1` THEN
    SUBGOAL_THEN
     `1 < MIN n p /\ ~(MIN n p <= 1) /\ MIN n p - 1 + 1 = MIN n p /\
      word_sub (word (MIN n p)) (word 1):int64 = word (MIN n p - 1) /\
      val (word (MIN n p - 1):int64) = MIN n p - 1`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`~(MIN n p = 0)`; `~(MIN n p = 1)`] THEN
        ARITH_TAC;
        MAP_EVERY UNDISCH_TAC [`~(MIN n p = 0)`; `~(MIN n p = 1)`] THEN
        ARITH_TAC;
        MAP_EVERY UNDISCH_TAC [`~(MIN n p = 0)`; `~(MIN n p = 1)`] THEN
        ARITH_TAC;
        IMP_REWRITE_TAC[WORD_SUB2] THEN
        MAP_EVERY UNDISCH_TAC [`~(MIN n p = 0)`; `~(MIN n p = 1)`] THEN
        ARITH_TAC;
        MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
        MAP_EVERY UNDISCH_TAC [`MIN n p <= p`; `p < 2 EXP 64`] THEN
        ARITH_TAC];
      ALL_TAC] THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `MIN n p - 1` (pcoff mul_start) (pcoff mul_end)
     `\i s. read RDI s = word (p - MIN n p) /\ read RSI s = z /\
            read R8 s = x /\ read RCX s = word (MIN n p - 1 - i) /\
            read R10 s = word (i + 1)` THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `1 < MIN n p` THEN ARITH_TAC;
      REWRITE_TAC[SUB_0; ADD_CLAUSES; ENUMERATEL_APPEND_ZERO] THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false exec (1--mul_first) THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SAFETY_DOWNCOUNT_FACTS_TAC `i:num` `MIN n p - 1` THEN
      SAFETY_UPCOUNT_FACTS_TAC `i:num` `i + 1` `MIN n p` `MIN n p - 1` THEN
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false exec (1--mul_body) THEN
      SAFETY_CLOSE_TAC;
      X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
        ~canonicalize_pc_diff:false exec [] THEN
      SAFETY_PEEL_TAC THEN SAFETY_CONCRETE_DISCHARGE_TAC];
    ALL_TAC] THEN

  (*** The carry (or borrow) propagation through the remaining p - MIN n p
       words ***)

  ASM_CASES_TAC `MIN n p = p` THENL
   [SAFETY_COND_TAC `MIN n p = p` THEN
    SUBGOAL_THEN `p - MIN n p = 0` ASSUME_TAC THENL
     [UNDISCH_TAC `MIN n p = p` THEN ARITH_TAC; ALL_TAC] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--top_steps) THEN
    SAFETY_CLOSE_TAC;
    ALL_TAC] THEN
  SAFETY_COND_TAC `MIN n p = p` THEN
  SUBGOAL_THEN
   `MIN n p < p /\ ~(p - MIN n p = 0) /\
    word_add (word (MIN n p)) (word 1):int64 = word (MIN n p + 1) /\
    val (word (MIN n p + 1):int64) = MIN n p + 1 /\
    word_sub (word (p - MIN n p)) (word 1):int64 = word (p - (MIN n p + 1)) /\
    val (word (p - (MIN n p + 1)):int64) = p - (MIN n p + 1)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`~(MIN n p = p)`; `MIN n p <= p`] THEN ARITH_TAC;
      MAP_EVERY UNDISCH_TAC [`~(MIN n p = p)`; `MIN n p <= p`] THEN ARITH_TAC;
      CONV_TAC WORD_RULE;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      MAP_EVERY UNDISCH_TAC
       [`~(MIN n p = p)`; `MIN n p <= p`; `p < 2 EXP 64`] THEN
      ARITH_TAC;
      IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
       [AP_TERM_TAC; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`~(MIN n p = p)`; `MIN n p <= p`] THEN ARITH_TAC;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      UNDISCH_TAC `p < 2 EXP 64` THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `MIN n p + 1 = p` THENL
   [SAFETY_COND_TAC `MIN n p + 1 = p` THEN
    SUBGOAL_THEN `p - (MIN n p + 1) = 0` ASSUME_TAC THENL
     [UNDISCH_TAC `MIN n p + 1 = p` THEN ARITH_TAC; ALL_TAC] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--one_carry_steps) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  SAFETY_COND_TAC `MIN n p + 1 = p` THEN
  SUBGOAL_THEN `MIN n p + 1 < p /\ ~(p - (MIN n p + 1) = 0)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(MIN n p + 1 = p)`; `MIN n p < p`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `p - (MIN n p + 1)` (pcoff carry_start) (pcoff carry_end)
   `\i s. read RDI s = word (p - (MIN n p + 1) - i) /\ read RSI s = z /\
          read R10 s = word (MIN n p + 1 + i)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[SUB_0; ADD_CLAUSES; ENUMERATEL_APPEND_ZERO] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--carry_first) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SAFETY_DOWNCOUNT_FACTS_TAC `i:num` `p - (MIN n p + 1)` THEN
    SAFETY_UPCOUNT_FACTS_TAC `i:num` `MIN n p + 1 + i` `p:num` `p - (MIN n p + 1)` THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--4) THEN
    SAFETY_CLOSE_TAC;
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--2) THEN
    SAFETY_CLOSE_TAC];;
