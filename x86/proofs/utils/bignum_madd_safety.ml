(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proof of the cores of bignum_madd and   *)
(* bignum_mul, which only differ in the final update of each output word.  *)
(* ========================================================================= *)

needs "x86/proofs/consttime.ml";;

(* Helpers for nested loops: reassociation of the expanded outer-loop body
   and beta-reduction of the outer ENUMERATEL body only (bound variable v),
   leaving the instantiated f_events lambdas untouched. *)

let BIGNUM_MADD_REASSOC3 = prove
 (`!a b c d:(uarch_event)list.
     APPEND (APPEND (APPEND a b) c) d = APPEND a (APPEND b (APPEND c d))`,
  REWRITE_TAC[APPEND_ASSOC]);;

(* Normalization of a load address y + 8 * d - 8 + 8 * (c + 1). *)

let BIGNUM_MADD_ADDR_LEMMA = prove
 (`!y:int64 d c.
     word_add (word_add y (word (8 * d + 18446744073709551608)))
              (word (8 * (c + 1))) =
     word_add y (word (8 * (d + c)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  AP_TERM_TAC THEN ONCE_REWRITE_TAC[GSYM WORD_MOD_SIZE] THEN
  REWRITE_TAC[DIMINDEX_64] THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE
   `(8 * d + 18446744073709551608) + 8 * (c + 1) = 8 * (d + c) + 2 EXP 64 * 1`] THEN
  REWRITE_TAC[MOD_MULT_ADD]);;

(* The safety proof of the core, given its decoding theorem, its PCs and   *)
(* its numbers of steps: p = 0 (p0_steps); the outer loop (outer_start,    *)
(* outer_end; outer_first steps before it and outer_exit after it); the    *)
(* computation of the summation range ending at range_end; the inner loop  *)
(* (inner_start, inner_end); and the final update of z[k] (final_steps).   *)

let BIGNUM_MADD_SAFETY_TAC exec
    ~p0_steps ~outer_start ~outer_end ~outer_first ~outer_exit ~range_end
    ~inner_start ~inner_end ~final_steps =
  let pcoff off = mk_comb(`(+) (pc:num)`,mk_small_numeral off) in
  CONCRETIZE_F_EVENTS_TAC
   `\(x:int64) (y:int64) (z:int64) (p:int64) (n:int64) (m:int64) (pc:num).
      if val p = 0 then f_ev_p0 x y z p n m pc
      else
        APPEND (f_ev_opost x y z p n m pc)
         (APPEND
           (ENUMERATEL (val p) (\i.
              APPEND
               (APPEND (f_ev_oepil x y z p n m pc i)
                 (if MIN (i + 1) (val m) <= (i + 1) - val n
                  then f_ev_otriv x y z p n m pc i
                  else APPEND (f_ev_ipost x y z p n m pc i)
                        (APPEND
                          (ENUMERATEL (MIN (i + 1) (val m) - ((i + 1) - val n))
                                      (\j. f_ev_inner x y z p n m pc i j))
                          (f_ev_ipre x y z p n m pc i))))
               (f_ev_oprol x y z p n m pc i)))
           (f_ev_opre x y z p n m pc)) :(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY W64_GEN_TAC [`p:num`; `m:num`; `n:num`] THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `x:int64`; `y:int64`; `pc:num`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The degenerate case p = 0 ***)

  ASM_CASES_TAC `p = 0` THENL
   [SAFETY_COND_TAC `p = 0` THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `p = 0`)) THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--p0_steps) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  SAFETY_COND_TAC `p = 0` THEN
  SUBGOAL_THEN `8 * p < 2 EXP 64 /\ 8 * m < 2 EXP 64 /\ 8 * n < 2 EXP 64`
  STRIP_ASSUME_TAC THENL
   [EVERY_ASSUM(fun th ->
      try MP_TAC
       (MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] NONOVERLAPPING_IMP_SMALL_2) th)
      with Failure _ -> ALL_TAC) THEN
    UNDISCH_TAC `~(p = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN

  (*** The outer loop over the output words ***)

  ENSURES_EVENTS_WHILE_UP2_TAC `p:num` (pcoff outer_start) (pcoff outer_end)
   `\k s. read RDI s = word p /\ read RSI s = word_add z (word (8 * k)) /\
          read RBP s = word m /\ read RCX s = x /\ read R8 s = word n /\
          read R9 s = y /\ read R10 s = word k` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--outer_first) THEN
    SAFETY_CLOSE_TAC;
    ALL_TAC;
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--outer_exit) THEN
    SAFETY_CLOSE_TAC] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ONCE_DEPTH_CONV) [ENUMERATEL_ADD1] THEN
  CONV_TAC(RATOR_CONV(RAND_CONV(ONCE_DEPTH_CONV(BETA_VAR_CONV "i")))) THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ONCE_DEPTH_CONV) [BIGNUM_MADD_REASSOC3] THEN

  (*** The computation of the summation range for output word k ***)

  ENSURES_EVENTS_SEQUENCE_TAC (pcoff range_end)
   `\s. read RDI s = word p /\ read RSI s = word_add z (word (8 * k)) /\
        read RBP s = word m /\ read RCX s = x /\ read R8 s = word n /\
        read R9 s = y /\ read R10 s = word (k + 1) /\
        read RAX s = word ((k + 1) - n) /\ read RBX s = word (MIN (k + 1) m) /\
        read RDX s = word ((k + 1) - MIN (k + 1) m)` THEN
  CONJ_TAC THENL
   [SAFETY_UPCOUNT_FACTS_TAC `k:num` `k:num` `p:num` `p:num` THEN
    SUBGOAL_THEN
     `(if k + 1 < n then word 0 else word_sub (word (k + 1)) (word n)):int64 =
      word ((k + 1) - n) /\
      (if k + 1 < m then word (k + 1) else word m):int64 =
      word (MIN (k + 1) m) /\
      word_sub (word (k + 1)) (word (MIN (k + 1) m)):int64 =
      word ((k + 1) - MIN (k + 1) m)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [COND_CASES_TAC THENL
         [AP_TERM_TAC THEN ASM_ARITH_TAC;
          IMP_REWRITE_TAC[WORD_SUB2] THEN ASM_ARITH_TAC];
        REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN COND_CASES_TAC THEN
        REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
        IMP_REWRITE_TAC[WORD_SUB2] THEN ARITH_TAC];
      ALL_TAC] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--10) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN

  (*** The final update of z[k] and the outer loop test ***)

  SAFETY_POST_REASSOC_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC (pcoff inner_end)
   `\s. read RDI s = word p /\ read RSI s = word_add z (word (8 * k)) /\
        read RBP s = word m /\ read RCX s = x /\ read R8 s = word n /\
        read R9 s = y /\ read R10 s = word (k + 1)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SAFETY_UPCOUNT_FACTS_TAC `k:num` `k:num` `p:num` `p:num` THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--final_steps) THEN
    SAFETY_CLOSE_TAC] THEN

  (*** The inner multiply-accumulate loop, skipped if the sum is empty ***)

  SUBGOAL_THEN
   `val (word (MIN (k + 1) m):int64) = MIN (k + 1) m /\
    val (word ((k + 1) - n):int64) = (k + 1) - n /\
    ((MIN (k + 1) m < (k + 1) - n \/ MIN (k + 1) m = (k + 1) - n) <=>
     MIN (k + 1) m <= (k + 1) - n)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      MAP_EVERY UNDISCH_TAC [`k < p`; `p < 2 EXP 64`] THEN ARITH_TAC;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      MAP_EVERY UNDISCH_TAC [`k < p`; `p < 2 EXP 64`] THEN ARITH_TAC;
      ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `MIN (k + 1) m <= (k + 1) - n` THENL
   [SAFETY_COND_TAC `MIN (k + 1) m <= (k + 1) - n` THEN
    SUBGOAL_THEN
     `(MIN (k + 1) m < (k + 1) - n \/
       val (word_sub (word (MIN (k + 1) m)) (word ((k + 1) - n)):int64) = 0) <=>
      MIN (k + 1) m <= (k + 1) - n`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ARITH_TAC; ALL_TAC] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--2) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  SAFETY_COND_TAC `MIN (k + 1) m <= (k + 1) - n` THEN
  SUBGOAL_THEN
   `word_sub (word (MIN (k + 1) m)) (word ((k + 1) - n)):int64 =
    word (MIN (k + 1) m - ((k + 1) - n)) /\
    val (word (MIN (k + 1) m - ((k + 1) - n)):int64) =
    MIN (k + 1) m - ((k + 1) - n) /\
    val (word ((k + 1) - MIN (k + 1) m):int64) = (k + 1) - MIN (k + 1) m /\
    ~(MIN (k + 1) m < (k + 1) - n) /\
    ~(MIN (k + 1) m - ((k + 1) - n) = 0)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [IMP_REWRITE_TAC[WORD_SUB2] THEN
      UNDISCH_TAC `~(MIN (k + 1) m <= (k + 1) - n)` THEN ARITH_TAC;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      UNDISCH_TAC `m < 2 EXP 64` THEN ARITH_TAC;
      MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      MAP_EVERY UNDISCH_TAC [`k < p`; `p < 2 EXP 64`] THEN ARITH_TAC;
      UNDISCH_TAC `~(MIN (k + 1) m <= (k + 1) - n)` THEN ARITH_TAC;
      UNDISCH_TAC `~(MIN (k + 1) m <= (k + 1) - n)` THEN ARITH_TAC];
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `MIN (k + 1) m - ((k + 1) - n)`
   (pcoff inner_start) (pcoff inner_end)
   `\j s. read RDI s = word p /\ read RSI s = word_add z (word (8 * k)) /\
          read RBP s = word m /\ read RCX s = x /\ read R8 s = word n /\
          read R9 s = y /\ read R10 s = word (k + 1) /\
          read RBX s = word (MIN (k + 1) m - ((k + 1) - n) - j) /\
          read R12 s = word_add x (word (8 * ((k + 1) - n + j))) /\
          read R11 s = word_add y (word (8 * ((k + 1) - MIN (k + 1) m) +
                                         18446744073709551608))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[SUB_0; ADD_CLAUSES; ENUMERATEL_APPEND_ZERO] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--4) THEN
    SAFETY_CLOSE_TAC;
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SAFETY_DOWNCOUNT_FACTS_TAC `j:num` `MIN (k + 1) m - ((k + 1) - n)` THEN
    SUBGOAL_THEN
     `word_add (word_add y (word (8 * ((k + 1) - MIN (k + 1) m) +
                                  18446744073709551608)))
               (word (8 * (MIN (k + 1) m - ((k + 1) - n) - j))):int64 =
      word_add y (word (8 * (((k + 1) - MIN (k + 1) m) +
                             (MIN (k + 1) m - ((k + 1) - n) - (j + 1))))) /\
      ((k + 1) - MIN (k + 1) m) + (MIN (k + 1) m - ((k + 1) - n) - (j + 1)) < n /\
      (k + 1) - n + j < m`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [SUBGOAL_THEN
         `MIN (k + 1) m - ((k + 1) - n) - j =
          (MIN (k + 1) m - ((k + 1) - n) - (j + 1)) + 1`
        SUBST1_TAC THENL
         [UNDISCH_TAC `j < MIN (k + 1) m - ((k + 1) - n)` THEN ARITH_TAC;
          REWRITE_TAC[BIGNUM_MADD_ADDR_LEMMA]];
        UNDISCH_TAC `j < MIN (k + 1) m - ((k + 1) - n)` THEN ARITH_TAC;
        UNDISCH_TAC `j < MIN (k + 1) m - ((k + 1) - n)` THEN ARITH_TAC];
      ALL_TAC] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec (1--8) THEN
    SAFETY_CLOSE_TAC;
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false exec [] THEN
    SAFETY_PEEL_TAC THEN DISCHARGE_SAFETY_PROPERTY_TAC];;
