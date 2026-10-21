(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proofs of bignum_modifier and              *)
(* bignum_montifier, whose code is the same except that the main loop runs    *)
(* 2 * k times in bignum_montifier instead of k times.                        *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;

let BIGNUM_MODIFIER_PEEL_TAC (idx_add:term) (cond:term) =
  REPEAT(W(fun (asl,w) -> if is_conj w && not(is_exists w)
          then CONJ_TAC THENL
            [FIRST[GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ASSUME idx_add] THEN
                   GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ASSUME cond] THEN
                   GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN
                   GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_RAND] THEN REFL_TAC;
                   CONV_TAC WORD_RULE];
             ALL_TAC]
          else NO_TAC));;

let BIGNUM_MODIFIER_IDX_FACTS_TAC (v:term) (bnd:term) (bases:term list) =
  let sub t = subst [v,`i:num`; bnd,`k:num`] t in
  VAL_INT64_TAC v THEN
  MAP_EVERY (fun b ->
    SUBGOAL_THEN (subst [b,`b:int64`] (sub `word_add (word_shl (word i:int64) 3) b = word_add b (word(8 * i))`))
      ASSUME_TAC THENL
     [REWRITE_TAC[WORD_SHL_WORD] THEN REWRITE_TAC[ARITH_RULE `2 EXP 3 * m = 8 * m`] THEN CONV_TAC WORD_RULE;
      ALL_TAC]) bases THEN
  SUBGOAL_THEN (sub `val(word(i + 1):int64) = i + 1`) ASSUME_TAC THENL
   [IMP_REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (sub `word_add (word i:int64) (word 1) = word(i + 1)`) ASSUME_TAC THENL
   [CONV_TAC WORD_RULE; ALL_TAC] THEN
  SUBGOAL_THEN (sub `(~(val(word_sub (word(i + 1):int64) (word k)) = 0) <=> i + 1 < k)`) ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN MAP_EVERY VAL_INT64_TAC [sub `i + 1`; `k:num`] THEN
    ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[APPEND_NIL];;

let BIGNUM_MODIFIER_GEN_UPBODY_TAC exec (v:term) (bases:term list) (n:int) =
  X_GEN_TAC v THEN STRIP_TAC THEN
  BIGNUM_MODIFIER_IDX_FACTS_TAC v `k:num` bases THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
    exec (1--n) THEN
  BIGNUM_MODIFIER_PEEL_TAC (subst [v,`i:num`] `word_add (word i:int64) (word 1) = word(i + 1)`)
               (subst [v,`i:num`] `(~(val(word_sub (word(i + 1):int64) (word k)) = 0) <=> i + 1 < k)`) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let BIGNUM_MODIFIER_DOWNCOUNT_FACTS_TAC (cnt:term) (iv:term) =
  let sub t = subst [cnt,`n:num`; iv,`i:num`] t in
  SUBGOAL_THEN (sub `word_sub (word(n - i)) (word 1):int64 = word(n - (i + 1))`) ASSUME_TAC THENL
   [SUBGOAL_THEN (sub `n - i = (n - (i + 1)) + 1`) SUBST1_TAC THENL
     [SIMPLE_ARITH_TAC; CONV_TAC WORD_RULE]; ALL_TAC] THEN
  SUBGOAL_THEN (sub `val(word(n - (i + 1)):int64) = n - (i + 1)`) ASSUME_TAC THENL
   [IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (sub `(~(val(word(n - (i + 1)):int64) = 0) <=> i + 1 < n)`) ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (sub `(~(val(word_sub (word(n - i)) (word 1):int64) = 0) <=> i + 1 < n)`) ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC];;

let BIGNUM_MODIFIER_CLOSE_TAC =
  REPEAT(W(fun (asl,w) ->
    if is_conj w then
      CONJ_TAC THENL
       [FIRST[(REWRITE_TAC[COND_ID] THEN NO_TAC);
              (GEN_REWRITE_TAC RAND_CONV [COND_RAND] THEN ASM_REWRITE_TAC[] THEN NO_TAC);
              (ASM_REWRITE_TAC[] THEN NO_TAC);
              CONV_TAC WORD_RULE];
        ALL_TAC]
    else NO_TAC)) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

let modifier_inv (reg:term) = subst [reg,`X4:(armstate,int64)component`]
  `\i s. read X0 s = word k /\ read X1 s = z /\ read X2 s = m /\ read X3 s = t /\
         read X4 s = word i /\ read X30 s = returnaddress`;;

let BIGNUM_MODIFIER_UPLOOP_TAC exec (head:term) (exitpc:term) (reg:term) (pre_steps:int) (pre_tac:tactic)
                   (bases:term list) (body_steps:int) =
  ENSURES_EVENTS_WHILE_UP2_TAC `k:num` head exitpc (modifier_inv reg) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN pre_tac THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--pre_steps) THEN
    BIGNUM_MODIFIER_CLOSE_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [BIGNUM_MODIFIER_GEN_UPBODY_TAC exec `i:num` bases body_steps; ALL_TAC];;

let BIGNUM_MODIFIER_KM1_FACTS_TAC =
  SUBGOAL_THEN `word_sub (word k) (word 1):int64 = word(k - 1)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [WORD_SUB] THEN COND_CASES_TAC THENL
     [REFL_TAC; POP_ASSUM MP_TAC THEN SIMPLE_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `~(val(word(k - 1):int64) = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN IMP_REWRITE_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun b ->
    SUBGOAL_THEN (subst [b,`b:int64`] `word_add (word_shl (word(k - 1):int64) 3) b = word_add b (word(8 * (k - 1)))`)
      ASSUME_TAC THENL
     [REWRITE_TAC[WORD_SHL_WORD] THEN REWRITE_TAC[ARITH_RULE `2 EXP 3 * m = 8 * m`] THEN CONV_TAC WORD_RULE;
      ALL_TAC]) [`t:int64`; `z:int64`; `m:int64`];;

let modifier_inv2 cnt = subst [cnt,`c:num`]
  `\j s. read X0 s = word k /\ read X1 s = z /\ read X2 s = m /\ read X3 s = t /\
         read X4 s = word(c - i) /\ read X5 s = word j /\ read X30 s = returnaddress`;;

let BIGNUM_MODIFIER_RED_BODY_TAC exec (b:term) =
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 + j < k /\ val(word(1 + j):int64) = 1 + j` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [SIMPLE_ARITH_TAC; IMP_REWRITE_TAC[VAL_WORD; DIMINDEX_64; MOD_LT] THEN SIMPLE_ARITH_TAC]; ALL_TAC] THEN
  VAL_INT64_TAC `j:num` THEN
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
     [REWRITE_TAC[WORD_SHL_WORD] THEN REWRITE_TAC[ARITH_RULE `2 EXP 3 * m = 8 * m`] THEN CONV_TAC WORD_RULE; ALL_TAC])
   [`word_add m (word_shl (word(1 + j):int64) 3) = word_add m (word(8 * (1 + j)))`;
    `word_add (word_shl (word(1 + j):int64) 3) m = word_add m (word(8 * (1 + j)))`;
    (subst [b,`t:int64`] `word_add t (word_shl (word(1 + j):int64) 3) = word_add t (word(8 * (1 + j)))`);
    (subst [b,`t:int64`] `word_add (word_shl (word(1 + j):int64) 3) t = word_add t (word(8 * (1 + j)))`);
    (subst [b,`t:int64`] `word_add t (word_shl (word j:int64) 3) = word_add t (word(8 * j))`);
    (subst [b,`t:int64`] `word_add (word_shl (word j:int64) 3) t = word_add t (word(8 * j))`);
    `word_sub (word(1 + j):int64) (word 1) = word j`;
    `word_add (word(1 + j):int64) (word 1) = word((1 + j) + 1)`] THEN
  SUBGOAL_THEN `(~(val(word_sub (word((1 + j) + 1):int64) (word k)) = 0) <=> j + 1 < k - 1)` ASSUME_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN MAP_EVERY VAL_INT64_TAC [`(1 + j) + 1`; `k:num`] THEN
    ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[APPEND_NIL] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
    exec (1--12) THEN
  BIGNUM_MODIFIER_CLOSE_TAC;;

(* The safety proof of either function, given its decoding theorem exec, the
   number cnt of iterations of its main loop (k or 2 * k) and the number of
   steps for k = 1. *)

let BIGNUM_MODIFIER_SAFETY_TAC exec (cnt:term) (k1_steps:int) =
  CONCRETIZE_F_EVENTS_TAC
   (let vs,bod = strip_abs
   `\(m:int64) (z:int64) (t:int64) (k:int64) (pc:num) (returnaddress:int64).
      if val k = 0 then f_ev_k0 m z t k pc returnaddress
      else if val k = 1 then f_ev_k1 m z t k pc returnaddress
      else (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND
        (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (APPEND (f_ev_p16
        m z t k pc returnaddress) (APPEND (ENUMERATEL (val k) (f_ev_l16 m z t k
        pc returnaddress)) (f_ev_q16 m z t k pc returnaddress))) (APPEND
        (ENUMERATEL (val k) (f_ev_l15 m z t k pc returnaddress)) (f_ev_q15 m z t
        k pc returnaddress))) (APPEND (ENUMERATEL (val k) (\i. (APPEND (f_ev_l14e
        m z t k pc returnaddress i) (APPEND (ENUMERATEL (val k - 1) (\j.
        f_ev_l14b m z t k pc returnaddress i j)) (f_ev_l14p m z t k pc
        returnaddress i))))) (f_ev_q14 m z t k pc returnaddress))) (APPEND
        (ENUMERATEL (val k) (f_ev_l13 m z t k pc returnaddress)) (f_ev_q13 m z t
        k pc returnaddress))) (APPEND (ENUMERATEL (val k - 1) (f_ev_l12 m z t k
        pc returnaddress)) (f_ev_q12 m z t k pc returnaddress))) (APPEND
        (ENUMERATEL c (\i. (APPEND (APPEND (f_ev_l11e m z t k pc
        returnaddress i) (APPEND (ENUMERATEL (val k) (\j. f_ev_l11c m z t k pc
        returnaddress i j)) (f_ev_l11m m z t k pc returnaddress i))) (APPEND
        (ENUMERATEL (val k) (\j. f_ev_l11a m z t k pc returnaddress i j))
        (f_ev_l11p m z t k pc returnaddress i))))) (f_ev_q11 m z t k pc
        returnaddress))) (APPEND (ENUMERATEL (val k) (f_ev_l10 m z t k pc
        returnaddress)) (f_ev_q10 m z t k pc returnaddress))) (APPEND (ENUMERATEL
        (val k) (f_ev_l9 m z t k pc returnaddress)) (f_ev_q9 m z t k pc
        returnaddress))) (APPEND (ENUMERATEL (val k) (f_ev_l8 m z t k pc
        returnaddress)) (f_ev_q8 m z t k pc returnaddress))) (APPEND (ENUMERATEL
        (val k) (f_ev_l7 m z t k pc returnaddress)) (f_ev_q7 m z t k pc
        returnaddress))) (APPEND (ENUMERATEL (val k) (f_ev_l6 m z t k pc
        returnaddress)) (f_ev_q6 m z t k pc returnaddress))) (APPEND (ENUMERATEL
        (val k) (f_ev_l5 m z t k pc returnaddress)) (f_ev_q5 m z t k pc
        returnaddress))) (APPEND (ENUMERATEL (62) (f_ev_l4 m z t k pc
        returnaddress)) (f_ev_q4 m z t k pc returnaddress))) (APPEND (ENUMERATEL
        (val k) (f_ev_l3 m z t k pc returnaddress)) (f_ev_q3 m z t k pc
        returnaddress))) (APPEND (ENUMERATEL (val k - 1) (\i. (APPEND (f_ev_l2e m
        z t k pc returnaddress i) (APPEND (ENUMERATEL (val k) (\j. f_ev_l2b m z t
        k pc returnaddress i j)) (f_ev_l2p m z t k pc returnaddress i)))))
        (f_ev_q2 m z t k pc returnaddress))) (APPEND (ENUMERATEL (val k) (f_ev_l1
        m z t k pc returnaddress)) (f_ev_q1 m z t k pc returnaddress)))
      :(uarch_event) list` in
   list_mk_abs(vs,subst [subst [`val(k:int64)`,`k:num`] cnt,`c:num`] bod)) THEN
  REPEAT META_EXISTS_TAC THEN X_GEN_TAC `e:(uarch_event)list` THEN
  W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `m:int64`; `t:int64`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES; C_ARGUMENTS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  (*** k = 0: CBZ -> RET ***)
  ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--2) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  (*** k = 1: all loops run once (the reciprocal loop 62 times) ***)
  ASM_CASES_TAC `k = 1` THENL
   [ASM_REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--k1_steps) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `8 * k < 2 EXP 64` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ] NONOVERLAPPING_IMP_SMALL_1)) THEN
    ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV; ARITH_TAC];
    ALL_TAC] THEN
  (*** copy m into t, 0x8..0x18 ***)
  BIGNUM_MODIFIER_UPLOOP_TAC exec `pc + 0x8` `pc + 0x1c` `X4` 2 ALL_TAC [`m:int64`; `t:int64`] 5 THEN
  (*** digitwise normalization: outer loop k - 1 times (X4 counting down), inner shuffle loop ***)
  ENSURES_EVENTS_WHILE_UP2_TAC `k - 1` `pc + 0x24` `pc + 0x54`
   `\i s. read X0 s = word k /\ read X1 s = z /\ read X2 s = m /\ read X3 s = t /\
          read X4 s = word((k - 1) - i) /\ read X30 s = returnaddress` THEN
  CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN BIGNUM_MODIFIER_KM1_FACTS_TAC THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--2) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    SAFETY_POST_REASSOC_TAC THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0x30` `pc + 0x4c`
     `\j s. read X0 s = word k /\ read X1 s = z /\ read X2 s = m /\ read X3 s = t /\
            read X4 s = word((k - 1) - i) /\ read X5 s = word j /\ read X30 s = returnaddress` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
      ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--3) THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [BIGNUM_MODIFIER_GEN_UPBODY_TAC exec `j:num` [`t:int64`] 7; ALL_TAC] THEN
    BIGNUM_MODIFIER_DOWNCOUNT_FACTS_TAC `k - 1` `i:num` THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--2) THEN
    BIGNUM_MODIFIER_CLOSE_TAC;
    ALL_TAC] THEN
  (*** bitwise normalization ***)
  SAFETY_CARRY_REASSOC_TAC THEN
  BIGNUM_MODIFIER_UPLOOP_TAC exec `pc + 0x6c` `pc + 0x90` `X4` 6 ALL_TAC [`t:int64`] 9 THEN
  (*** reciprocal estimate, 62 iterations (X4 counting down); preload of t[k-1] ***)
  SAFETY_CARRY_REASSOC_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `62` `pc + 0xa4` `pc + 0xd0`
   `\i s. read X0 s = word k /\ read X1 s = z /\ read X2 s = m /\ read X3 s = t /\
          read X4 s = word(62 - i) /\ read X30 s = returnaddress` THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN BIGNUM_MODIFIER_KM1_FACTS_TAC THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--5) THEN
    BIGNUM_MODIFIER_CLOSE_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN BIGNUM_MODIFIER_DOWNCOUNT_FACTS_TAC `62` `i:num` THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--11) THEN
    BIGNUM_MODIFIER_CLOSE_TAC;
    ALL_TAC] THEN
  (*** multiply, remainder, and two doubling/correction loop pairs ***)
  SAFETY_CARRY_REASSOC_TAC THEN
  BIGNUM_MODIFIER_UPLOOP_TAC exec `pc + 0xe0`  `pc + 0x100` `X4` 4 ALL_TAC [`t:int64`; `z:int64`] 8 THEN
  SAFETY_CARRY_REASSOC_TAC THEN
  BIGNUM_MODIFIER_UPLOOP_TAC exec `pc + 0x114` `pc + 0x134` `X4` 5 ALL_TAC [`t:int64`; `z:int64`] 8 THEN
  SAFETY_CARRY_REASSOC_TAC THEN
  BIGNUM_MODIFIER_UPLOOP_TAC exec `pc + 0x13c` `pc + 0x160` `X5` 2 ALL_TAC [`z:int64`; `t:int64`] 9 THEN
  SAFETY_CARRY_REASSOC_TAC THEN
  BIGNUM_MODIFIER_UPLOOP_TAC exec `pc + 0x16c` `pc + 0x18c` `X5` 3 ALL_TAC [`z:int64`; `t:int64`] 8 THEN
  SAFETY_CARRY_REASSOC_TAC THEN
  BIGNUM_MODIFIER_UPLOOP_TAC exec `pc + 0x194` `pc + 0x1b8` `X5` 2 ALL_TAC [`z:int64`; `t:int64`] 9 THEN
  SAFETY_CARRY_REASSOC_TAC THEN
  BIGNUM_MODIFIER_UPLOOP_TAC exec `pc + 0x1c4` `pc + 0x1e8` `X5` 3 ALL_TAC [`z:int64`; `t:int64`] 9 THEN
  (*** main loop, cnt times (X4 counting down): inner multiply-accumulate then correction ***)
  SAFETY_CARRY_REASSOC_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC cnt `pc + 0x1f0` `pc + 0x260`
   (subst [cnt,`c:num`]
    `\i s. read X0 s = word k /\ read X1 s = z /\ read X2 s = m /\ read X3 s = t /\
           read X4 s = word(c - i) /\ read X30 s = returnaddress`) THEN
  CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--2) THEN
    BIGNUM_MODIFIER_CLOSE_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    SAFETY_POST_REASSOC_TAC THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0x1fc` `pc + 0x228` (modifier_inv2 cnt) THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
      ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--3) THEN
      BIGNUM_MODIFIER_CLOSE_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [BIGNUM_MODIFIER_GEN_UPBODY_TAC exec `j:num` [`z:int64`; `t:int64`] 11; ALL_TAC] THEN
    SAFETY_CARRY_REASSOC_TAC THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0x234` `pc + 0x254` (modifier_inv2 cnt) THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
      ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--3) THEN
      BIGNUM_MODIFIER_CLOSE_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [BIGNUM_MODIFIER_GEN_UPBODY_TAC exec `j:num` [`t:int64`; `z:int64`] 8; ALL_TAC] THEN
    BIGNUM_MODIFIER_DOWNCOUNT_FACTS_TAC cnt `i:num` THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--3) THEN
    BIGNUM_MODIFIER_CLOSE_TAC;
    ALL_TAC] THEN
  (*** Montgomery reduction loop, k - 1 times with index 1 + j ***)
  SAFETY_CARRY_REASSOC_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k - 1` `pc + 0x2b4` `pc + 0x2e4`
   `\j s. read X0 s = word k /\ read X1 s = z /\ read X2 s = m /\ read X3 s = t /\
          read X5 s = word(1 + j) /\ read X30 s = returnaddress` THEN
  CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUB_0; ADD_0; ENUMERATEL_APPEND_ZERO] THEN BIGNUM_MODIFIER_KM1_FACTS_TAC THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--21) THEN
    BIGNUM_MODIFIER_CLOSE_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [BIGNUM_MODIFIER_RED_BODY_TAC exec `t:int64`; ALL_TAC] THEN
  (*** masked subtraction loop ***)
  SAFETY_CARRY_REASSOC_TAC THEN
  BIGNUM_MODIFIER_UPLOOP_TAC exec `pc + 0x2f8` `pc + 0x318` `X5` 5 BIGNUM_MODIFIER_KM1_FACTS_TAC
    [`t:int64`; `m:int64`; `z:int64`] 8 THEN
  (*** Montgomery reduction: outer loop k times (X6 counting down), inner loop k - 1 times ***)
  SAFETY_CARRY_REASSOC_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `k:num` `pc + 0x31c` `pc + 0x384`
   `\i s. read X0 s = word k /\ read X1 s = z /\ read X2 s = m /\ read X3 s = t /\
          read X6 s = word(k - i) /\ read X30 s = returnaddress` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--1) THEN
    BIGNUM_MODIFIER_CLOSE_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[ENUMERATEL_ADD1] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    SAFETY_POST_REASSOC_TAC THEN
    ENSURES_EVENTS_WHILE_UP2_TAC `k - 1` `pc + 0x340` `pc + 0x370`
     `\j s. read X0 s = word k /\ read X1 s = z /\ read X2 s = m /\ read X3 s = t /\
            read X6 s = word(k - i) /\ read X5 s = word(1 + j) /\ read X30 s = returnaddress` THEN
    CONJ_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUB_0; ADD_0; ENUMERATEL_APPEND_ZERO] THEN BIGNUM_MODIFIER_KM1_FACTS_TAC THEN
      ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--9) THEN
      BIGNUM_MODIFIER_CLOSE_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [BIGNUM_MODIFIER_RED_BODY_TAC exec `z:int64`; ALL_TAC] THEN
    BIGNUM_MODIFIER_KM1_FACTS_TAC THEN BIGNUM_MODIFIER_DOWNCOUNT_FACTS_TAC `k:num` `i:num` THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--5) THEN
    BIGNUM_MODIFIER_CLOSE_TAC;
    ALL_TAC] THEN
  (*** comparison loop ***)
  SAFETY_CARRY_REASSOC_TAC THEN
  BIGNUM_MODIFIER_UPLOOP_TAC exec `pc + 0x388` `pc + 0x3a0` `X5` 1 ALL_TAC [`z:int64`; `m:int64`] 6 THEN
  (*** masked subtraction loop, then RET ***)
  SAFETY_CARRY_REASSOC_TAC THEN
  BIGNUM_MODIFIER_UPLOOP_TAC exec `pc + 0x3a8` `pc + 0x3c8` `X5` 2 ALL_TAC [`z:int64`; `m:int64`] 8 THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
      exec (1--1) THEN
  BIGNUM_MODIFIER_CLOSE_TAC;;
