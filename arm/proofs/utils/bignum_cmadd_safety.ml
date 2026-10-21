(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proofs of bignum_cmadd and              *)
(* bignum_cmnegadd, which only differ in the arithmetic of their loops.    *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;

(* The clamped length computed by the CSEL.                                *)

let BIGNUM_CMADD_CLAMP = prove
 (`(if p <= n then word p else word n):int64 = word(MIN n p)`,
  REWRITE_TAC[ARITH_RULE `MIN n p = if p <= n then p else n`] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

(* The safety proof, given the decoding theorem; the PCs of the start and  *)
(* the end of the multiply-add loop and the numbers of steps of its first  *)
(* and later iterations; the number of steps when there is no carry word   *)
(* (top_steps) or one (one_carry_steps); and the PCs of the carry loop and *)
(* the numbers of steps before and after it. The witness is a case split   *)
(* on whether MIN n p = 0, when the first CBZ jumps to the end, leaving z  *)
(* untouched (f_ev_min0).                                                  *)

let BIGNUM_CMADD_SAFETY_TAC exec
    ~mul_start ~mul_end ~mul_first ~mul_body ~top_steps ~one_carry_steps
    ~carry_start ~carry_end ~carry_first ~carry_exit =
  let pcoff off = mk_comb(`(+) (pc:num)`,mk_small_numeral off) in
  CONCRETIZE_F_EVENTS_TAC
   `\(x:int64) (z:int64) (p:int64) (n:int64) (pc:num) (returnaddress:int64).
      if MIN (val n) (val p) = 0 then f_ev_min0 x z p n pc returnaddress
      else
        APPEND
          (if MIN (val n) (val p) = val p then f_ev_tail0 x z p n pc returnaddress
           else if MIN (val n) (val p) + 1 = val p then f_ev_tail1 x z p n pc returnaddress
           else APPEND (f_ev_padpost x z p n pc returnaddress)
                  (APPEND (ENUMERATEL (val p - MIN (val n) (val p) - 1) (f_ev_pad x z p n pc returnaddress))
                          (f_ev_padpre x z p n pc returnaddress)))
          (if MIN (val n) (val p) = 1 then f_ev_main1 x z p n pc returnaddress
           else APPEND (f_ev_mainpost x z p n pc returnaddress)
                  (APPEND (ENUMERATEL (MIN (val n) (val p) - 1) (f_ev_mainloop x z p n pc returnaddress))
                          (f_ev_mainpre x z p n pc returnaddress)))
      :(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN X_GEN_TAC `e:(uarch_event)list` THEN
  W64_GEN_TAC `p:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `c:num` THEN W64_GEN_TAC `n:num` THEN
  X_GEN_TAC `x:int64` THEN MAP_EVERY X_GEN_TAC [`pc:num`;`returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; NONOVERLAPPING_CLAUSES; fst exec; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `MIN n p = 0` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th]) THENL
   [(*** MIN n p = 0 ***)

    SUBGOAL_THEN `(if p <= n then word p else word n):int64 = word 0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[BIGNUM_CMADD_CLAMP]; ALL_TAC] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--7) THEN
    CONV_TAC(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV) THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** MIN n p > 0 ***)

    SUBGOAL_THEN `8 * p < 2 EXP 64` STRIP_ASSUME_TAC THENL
     [EVERY_ASSUM(fun th -> try MP_TAC (MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] NONOVERLAPPING_IMP_SMALL_2) th) with Failure _ -> ALL_TAC) THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `MIN n p <= p /\ MIN n p <= n` STRIP_ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(p = 0) /\ ~(n = 0) /\ ~(MIN n p = 0)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[ARITH_RULE `MIN n p = 0 <=> n = 0 \/ p = 0`]; ALL_TAC] THEN
    ASSUME_TAC BIGNUM_CMADD_CLAMP THEN
    SUBGOAL_THEN `~(val(word(MIN n p):int64) = 0)` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN IMP_REWRITE_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val(word(MIN n p):int64) = MIN n p` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN IMP_REWRITE_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ENSURES_EVENTS_SEQUENCE_TAC (pcoff mul_end)
     `\s. read X0 s = word(p - MIN n p) /\ read X1 s = z /\
          read X5 s = word(8 * MIN n p) /\ read X30 s = returnaddress` THEN
    CONJ_TAC THENL
     [ (* ===== segment 1: pc -> mul_end ===== *)
       ASM_CASES_TAC `MIN n p = 1` THENL
        [ (* MIN n p = 1: only the peeled iteration, with the CBZ X3 taken to
             mul_end *)
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `val(word_sub (word(MIN n p):int64) (word 1)) = 0` ASSUME_TAC THENL
           [REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
            ASM_REWRITE_TAC[VAL_WORD; VAL_WORD_1; DIMINDEX_64] THEN IMP_REWRITE_TAC[MOD_LT] THEN
            SIMPLE_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `word_sub (word p) (word(MIN n p)):int64 = word(p - MIN n p)` ASSUME_TAC THENL
           [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN COND_CASES_TAC THENL
             [REFL_TAC; POP_ASSUM MP_TAC THEN SIMPLE_ARITH_TAC]; ALL_TAC] THEN
          ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
            exec (1--mul_first) THEN
          ASM_REWRITE_TAC[ARITH_RULE `8 * 1 = 8`] THEN
          SUBGOAL_THEN `word_sub (word p) (word 1):int64 = word(p - 1)` SUBST1_TAC THENL
           [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN COND_CASES_TAC THEN
            ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
          CONV_TAC(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV) THEN
          REWRITE_TAC[GSYM APPEND_ASSOC] THEN
          RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(RAND_CONV(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV)))) THEN
          RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
          DISCHARGE_SAFETY_PROPERTY_TAC;
          (* MIN>=2 *)
          REWRITE_TAC[ASSUME `~(MIN n p = 1)`] THEN
          SUBGOAL_THEN `2 <= MIN n p` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
          ENSURES_EVENTS_WHILE_UP2_TAC `MIN n p - 1` (pcoff mul_start) (pcoff mul_end)
           `\j s. read X0 s = word(p - MIN n p) /\ read X1 s = z /\ read X2 s = word c /\
                  read X3 s = word(MIN n p - 1 - j) /\ read X4 s = x /\
                  read X5 s = word(8 * (j + 1)) /\ read X30 s = returnaddress` THEN
          REWRITE_TAC[LT_NZ] THEN
          CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
          CONJ_TAC THENL
           [ (* the peeled iteration, to mul_start *)
             REWRITE_TAC[SUB_0; MULT_CLAUSES; ADD_0; ENUMERATEL_APPEND_ZERO] THEN
             SUBGOAL_THEN `word_sub (word(MIN n p):int64) (word 1) = word(MIN n p - 1)` ASSUME_TAC THENL
              [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN COND_CASES_TAC THENL
                [REFL_TAC; POP_ASSUM MP_TAC THEN SIMPLE_ARITH_TAC]; ALL_TAC] THEN
             SUBGOAL_THEN `~(MIN n p - 1 = 0)` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
             SUBGOAL_THEN `~(val(word(MIN n p - 1):int64) = 0)` ASSUME_TAC THENL
              [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN IMP_REWRITE_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
             SUBGOAL_THEN `word_sub (word p) (word(MIN n p)):int64 = word(p - MIN n p)` ASSUME_TAC THENL
              [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN COND_CASES_TAC THENL
                [REFL_TAC; POP_ASSUM MP_TAC THEN SIMPLE_ARITH_TAC]; ALL_TAC] THEN
             ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
               exec (1--mul_first) THEN
             ASM_REWRITE_TAC[] THEN
             CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
             CONV_TAC(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV) THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
             RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(RAND_CONV(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV)))) THEN
             RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
             DISCHARGE_SAFETY_PROPERTY_TAC;
             ALL_TAC] THEN
          CONJ_TAC THENL
           [ (* the main loop body, from mul_start *)
             X_GEN_TAC `j:num` THEN STRIP_TAC THEN
             SUBGOAL_THEN `j:num < MIN n p /\ j + 1 < MIN n p` STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
             SUBGOAL_THEN `word_sub (word(MIN n p - 1 - j):int64) (word 1) = word(MIN n p - 1 - (j + 1))` ASSUME_TAC THENL
              [REWRITE_TAC[ARITH_RULE `MIN n p - 1 - (j + 1) = MIN n p - 1 - j - 1`] THEN
               GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN COND_CASES_TAC THENL
                [REFL_TAC; POP_ASSUM MP_TAC THEN SIMPLE_ARITH_TAC]; ALL_TAC] THEN
             SUBGOAL_THEN `val(word(MIN n p - 1 - (j + 1)):int64) = MIN n p - 1 - (j + 1)` ASSUME_TAC THENL
              [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
             SUBGOAL_THEN `val(word(8 * (j + 1)):int64) = 8 * (j + 1)` ASSUME_TAC THENL
              [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
             SUBGOAL_THEN `8 * (j + 1) < 8 * p` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
             SUBGOAL_THEN `8 * (j + 1) < 8 * n` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
             SUBGOAL_THEN `(MIN n p - 1 - (j + 1) = 0 <=> ~(j + 1 < MIN n p - 1))` ASSUME_TAC THENL
              [UNDISCH_TAC `j + 1 < MIN n p` THEN UNDISCH_TAC `2 <= MIN n p` THEN
               SPEC_TAC(`MIN n p`,`m:num`) THEN ARITH_TAC; ALL_TAC] THEN
             ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
               exec (1--mul_body) THEN
             ASM_REWRITE_TAC[] THEN
             REPEAT CONJ_TAC THENL
              [GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN ASM_REWRITE_TAC[];
               REWRITE_TAC[ARITH_RULE `8 * ((j + 1) + 1) = 8 * (j + 1) + 8`] THEN CONV_TAC WORD_RULE;
               ALL_TAC] THEN
             DISCHARGE_SAFETY_PROPERTY_TAC;
             (* the main loop exit: no step, at mul_end *)
             ASM_REWRITE_TAC[] THEN
             SUBGOAL_THEN `8 * (MIN n p - 1 + 1) = 8 * MIN n p` ASSUME_TAC THENL
              [UNDISCH_TAC `2 <= MIN n p` THEN ARITH_TAC; ALL_TAC] THEN
             ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
               exec (1--0) THEN
             ASM_REWRITE_TAC[] THEN
             RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(RAND_CONV(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV)))) THEN
             RULE_ASSUM_TAC(REWRITE_RULE[GSYM APPEND_ASSOC]) THEN
             DISCHARGE_SAFETY_PROPERTY_TAC]];
       (* ===== segment 2: mul_end -> RET, carry tail (3-way), all in MIN n p ===== *)
       W(fun (asl,w) ->
           let mainside = find_term (fun t -> try let cc,_ = dest_cond t in cc = `MIN n p = 1`
                                              with _ -> false) w in
           ABBREV_TAC (mk_eq(mk_var("em",type_of mainside), mainside))) THEN
       GEN_REWRITE_TAC (ONCE_DEPTH_CONV) [GSYM APPEND_ASSOC] THEN
       ASM_CASES_TAC `MIN n p = p` THENL
        [ SUBGOAL_THEN `p - MIN n p = 0` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
          ASM_REWRITE_TAC[] THEN
          ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
            exec (1--top_steps) THEN
          CONV_TAC(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV) THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
          DISCHARGE_SAFETY_PROPERTY_TAC;
          ALL_TAC] THEN
       SUBGOAL_THEN `MIN n p < p` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
       SUBGOAL_THEN `val(word(8 * MIN n p):int64) = 8 * MIN n p` ASSUME_TAC THENL
        [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
       SUBGOAL_THEN `8 * MIN n p < 8 * p` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
       ASM_CASES_TAC `MIN n p + 1 = p` THENL
        [ (* 1 pad word: carry-store incl CBZ taken *)
          SUBGOAL_THEN `p - MIN n p = 1` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
          ASM_REWRITE_TAC[] THEN
          ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
            exec (1--one_carry_steps) THEN
          CONV_TAC(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV) THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
          DISCHARGE_SAFETY_PROPERTY_TAC;
          ALL_TAC] THEN
       SUBGOAL_THEN `MIN n p + 1 < p /\ 0 < p - MIN n p - 1 /\ p - MIN n p - 1 < 2 EXP 64` STRIP_ASSUME_TAC THENL
        [MAP_EVERY UNDISCH_TAC [`~(MIN n p + 1 = p)`; `MIN n p < p`; `MIN n p <= n`; `p < 2 EXP 64`] THEN ARITH_TAC; ALL_TAC] THEN
       ASM_REWRITE_TAC[] THEN
       ENSURES_EVENTS_WHILE_UP2_TAC `p - MIN n p - 1` (pcoff carry_start) (pcoff carry_end)
        `\i s. read X0 s = word(p - MIN n p - 1 - i) /\ read X1 s = z /\
               read X5 s = word(8 * (MIN n p + i)) /\ read X30 s = returnaddress` THEN
       REWRITE_TAC[LT_NZ] THEN
       CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
       CONJ_TAC THENL
        [ (* the carry-store precondition, to carry_start *)
          REWRITE_TAC[SUB_0; ADD_0; ENUMERATEL_APPEND_ZERO] THEN
          SUBGOAL_THEN `~(p - MIN n p = 1)` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `~(val(word(p - MIN n p):int64) = 0)` ASSUME_TAC THENL
           [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN IMP_REWRITE_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `~(val(word_sub (word(p - MIN n p):int64) (word 1)) = 0)` ASSUME_TAC THENL
           [REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN IMP_REWRITE_TAC[VAL_WORD; VAL_WORD_1; DIMINDEX_64; MOD_LT] THEN
            SIMPLE_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `word_sub (word(p - MIN n p):int64) (word 1) = word(p - MIN n p - 1)` ASSUME_TAC THENL
           [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN COND_CASES_TAC THENL
             [REFL_TAC; POP_ASSUM MP_TAC THEN SIMPLE_ARITH_TAC]; ALL_TAC] THEN
          SUBGOAL_THEN `~(val(word(p - MIN n p - 1):int64) = 0)` ASSUME_TAC THENL
           [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN IMP_REWRITE_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
          ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
            exec (1--carry_first) THEN
          ASM_REWRITE_TAC[ARITH_RULE `p - MIN n p - 1 - 0 = p - MIN n p - 1`;
                          ARITH_RULE `MIN n p + 0 = MIN n p`] THEN
          CONV_TAC(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV) THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
          DISCHARGE_SAFETY_PROPERTY_TAC;
          ALL_TAC] THEN
       CONJ_TAC THENL
        [ (* the pad loop body, from carry_start *)
          X_GEN_TAC `i:num` THEN STRIP_TAC THEN
          SUBGOAL_THEN `MIN n p + i < p /\ MIN n p + i + 1 < p` STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `val(word(8 * (MIN n p + i)):int64) = 8 * (MIN n p + i)` ASSUME_TAC THENL
           [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `8 * (MIN n p + i) + 8 < 8 * p` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `word_sub (word(p - MIN n p - 1 - i):int64) (word 1) = word(p - MIN n p - 1 - (i + 1))` ASSUME_TAC THENL
           [REWRITE_TAC[ARITH_RULE `p - MIN n p - 1 - (i + 1) = p - MIN n p - 1 - i - 1`] THEN
            GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN COND_CASES_TAC THENL
             [REFL_TAC; POP_ASSUM MP_TAC THEN SIMPLE_ARITH_TAC]; ALL_TAC] THEN
          SUBGOAL_THEN `val(word(p - MIN n p - 1 - i):int64) = p - MIN n p - 1 - i` ASSUME_TAC THENL
           [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `(p - MIN n p - 1 - (i + 1) = 0 <=> ~(i + 1 < p - MIN n p - 1))` ASSUME_TAC THENL
           [UNDISCH_TAC `i < p - MIN n p - 1` THEN SPEC_TAC(`p - MIN n p - 1`,`m:num`) THEN ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `val(word(p - MIN n p - 1 - (i + 1)):int64) = p - MIN n p - 1 - (i + 1)` ASSUME_TAC THENL
           [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
          ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
            exec (1--6) THEN
          ASM_REWRITE_TAC[] THEN
          REPEAT CONJ_TAC THENL
           [GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN
            AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
            UNDISCH_TAC `i < p - MIN n p - 1` THEN SPEC_TAC(`p - MIN n p - 1`,`m:num`) THEN ARITH_TAC;
            REWRITE_TAC[ARITH_RULE `8 * (MIN n p + i + 1) = 8 * (MIN n p + i) + 8`] THEN CONV_TAC WORD_RULE;
            ALL_TAC] THEN
          DISCHARGE_SAFETY_PROPERTY_TAC;
          (* the pad loop exit at carry_end, then RET *)
          ASM_REWRITE_TAC[] THEN
          ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
            exec (1--carry_exit) THEN
          CONV_TAC(ONCE_DEPTH_CONV CONS_TO_APPEND_CONV) THEN REWRITE_TAC[GSYM APPEND_ASSOC] THEN
          DISCHARGE_SAFETY_PROPERTY_TAC]]];;
