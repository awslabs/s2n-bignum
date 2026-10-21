(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Constant-time and memory safety proofs of the comparisons bignum_ge,      *)
(* bignum_gt, bignum_le and bignum_lt of an m-digit a with an n-digit b. The *)
(* code of bignum_ge and bignum_lt only differs in the final condition, and  *)
(* likewise for bignum_gt and bignum_le, so each pair has one proof, given   *)
(* the decoding theorem exec.                                                *)
(* ========================================================================= *)

needs "arm/proofs/consttime.ml";;

let BIGNUM_GE_LT_SAFE_TAC exec =
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (b:int64) (n:int64) (m:int64) (pc:num) (returnaddress:int64).
      if val n <= val m then
        (APPEND
          (if val n = val m
          then f_ev_xtoploop_neqm a b n m pc returnaddress
          else (APPEND
            (f_ev_xtoploop_nnem_post a b n m pc returnaddress)
            (APPEND
              (ENUMERATEL (val m - val n)
                (f_ev_xtoploop_nnem_loop a b n m pc returnaddress))
              (f_ev_xtoploop_nnem_pre a b n m pc returnaddress))))
          (if val n = 0
          then f_ev_before_xtest_0m a b n m pc returnaddress
          else
            (APPEND
              (f_ev_before_xtest_nm_post a b n m pc returnaddress)
              (APPEND
                (ENUMERATEL (val n) (f_ev_xmainloop_nm a b n m pc returnaddress))
                (f_ev_entry_nm a b n m pc returnaddress)))))
        else
          (APPEND
            (APPEND
              (f_ev_ytoploop_nnem_post a b n m pc returnaddress)
              (APPEND
                (ENUMERATEL (val n - val m)
                  (f_ev_ytoploop_nnem_loop a b n m pc returnaddress))
                (f_ev_ytoploop_nnem_pre a b n m pc returnaddress)))
            (if val m = 0
            then f_ev_before_ytest_0n a b n m pc returnaddress
            else
              (APPEND
                (f_ev_before_ytest_mn_post a b n m pc returnaddress)
                (APPEND
                  (ENUMERATEL (val m) (f_ev_ymainloop_mn a b n m pc returnaddress))
                  (f_ev_entry_mn a b n m pc returnaddress)))))
      :(uarch_event) list` THEN

  REPEAT META_EXISTS_TAC THEN
  STRIP_TAC (* event e *) THEN

  W64_GEN_TAC `m:num` THEN X_GEN_TAC `a:int64` THEN
  W64_GEN_TAC `n:num` THEN X_GEN_TAC `b:int64` THEN
  MAP_EVERY X_GEN_TAC [`pc:num`;`returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; fst exec; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  VAL_INT64_TAC `1` THEN

  (*** Case split following the initial branch, m >= n case then m < n ***)

  ASM_CASES_TAC `n:num <= m` THENL
   [SUBGOAL_THEN `~(m:num < n)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NOT_LT]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN (* simplify n <= m *)
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x28`
     `\s. read X0 s = word (m - n) /\
          read X1 s = a /\
          read X3 s = b /\
          read X4 s = word n /\
          read X30 s = returnaddress` THEN
    CONJ_TAC THENL
     [ASM_CASES_TAC `n = 0` THENL
       [UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN ASM_REWRITE_TAC[SUB_0] THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
            ~canonicalize_pc_diff:false exec (1--4) THEN
        ASM_REWRITE_TAC[WORD_SUB_0] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;

        ALL_TAC]
      THEN
      ASM_REWRITE_TAC[] THEN

      ENSURES_EVENTS_WHILE_UP2_TAC `n:num` `pc + 0x10`
        `pc + 0x28` (* not + 0x24 *)
       `\i s. read X0 s = word (m - n) /\
              read X1 s = a /\
              read X3 s = b /\
              read X2 s = word(n - i) /\
              read X4 s = word i /\
              read X30 s = returnaddress` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [
        ASM_REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
            ~canonicalize_pc_diff:false exec (1--4) THEN
        ASM_REWRITE_TAC[WORD_SUB] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;

        ALL_TAC; (*** Main loop invariant ***)

        (* to postcond *)
        ASM_REWRITE_TAC[] THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
            ~canonicalize_pc_diff:false exec [] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC
      ] THEN

      (* The main loop *)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `i:num < m` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[] THEN
      ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false exec (1--6) THEN
      CONJ_TAC THENL
      [ IMP_REWRITE_TAC[VAL_WORD_SUB_EQ_0;VAL_WORD_EQ;DIMINDEX_64] THEN
        SIMPLE_ARITH_TAC; ALL_TAC ] THEN
      CONJ_TAC THENL
      [ IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
        [ AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC ]; ALL_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;

      (* from BB xtest *)
      (* case when m = n *)
      REWRITE_TAC[] THEN
      ASM_CASES_TAC `m:num = n` THENL
       [(* jump to xskip *)
        UNDISCH_THEN `m:num = n` SUBST_ALL_TAC THEN
        (* remove any discrepancies between the definition of e2 in pre and
           post *)
        ASM_SIMP_TAC[SUB_REFL; LE_REFL; ADD_CLAUSES; VAL_WORD_LT; DIMINDEX_64] THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
            ~canonicalize_pc_diff:false exec (1--3) THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;

        ALL_TAC] THEN

      (* m != n; xtoploop *)
      SUBGOAL_THEN `n:num < m /\ 0 < m - n /\ m - n < 2 EXP 64`
      STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN

      ENSURES_EVENTS_WHILE_UP2_TAC `m - n:num`
       `pc + 0x2c` `pc + 0x40` (* not + 0x3c *)
       `\i s. read X0 s = word (m - n - i) /\
              read X1 s = a /\
              read X4 s = word(n + i) /\
              read X30 s = returnaddress` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [
        SIMPLE_ARITH_TAC;

        (* to header *)
        REWRITE_TAC[SUB_0;ADD_0] THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
            ~canonicalize_pc_diff:false exec (1--1) THEN
        CONJ_TAC THENL [
          ASM_REWRITE_TAC[WORD_SUB;VAL_WORD_SUB_EQ_0] THEN NO_TAC; ALL_TAC
        ] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;

        ALL_TAC; (* main loop *)

        (* to postcond *)
        ASM_SIMP_TAC[SUB_REFL;ARITH_RULE`n <= m ==> n + m - n = m`] THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
            ~canonicalize_pc_diff:false exec (1--2) THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;
      ] THEN

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `i:num < m /\ n + i < m` STRIP_ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `n + i:num` THEN
      REWRITE_TAC[] THEN
      ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false exec (1--5) THEN
      CONJ_TAC THENL [
        IMP_REWRITE_TAC[VAL_WORD_SUB_EQ_0;VAL_WORD_EQ;DIMINDEX_64] THEN
        SIMPLE_ARITH_TAC; ALL_TAC
      ] THEN
      CONJ_TAC THENL
      [ IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
        [ AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC ]; ALL_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC
    ];

    (** case 2. ~ (n <= m) **)
    SUBGOAL_THEN `m < n` ASSUME_TAC THENL [
      SIMPLE_ARITH_TAC; ALL_TAC ] THEN
    ASM_REWRITE_TAC[] THEN

    (* split at ytoploop *)
    ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x6c`
     `\s. read X2 s = word (n - m) /\
          read X1 s = a /\
          read X3 s = b /\
          read X4 s = word m /\
          read X30 s = returnaddress` THEN
    CONJ_TAC THENL [
      ASM_CASES_TAC `m = 0` THENL [
        ASM_REWRITE_TAC[SUB_0] THEN
        SUBGOAL_THEN `0 < n` ASSUME_TAC THENL [SIMPLE_ARITH_TAC;ALL_TAC] THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
            ~canonicalize_pc_diff:false exec (1--5) THEN
        CONJ_TAC THENL [
          REWRITE_TAC[ VAL_WORD_0; VAL_WORD_SUB_EQ_0;
            WORD_RULE`word_add (word_sub (word 0) (word n)) (word n) = word 0`]
          THEN NO_TAC; ALL_TAC ] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;

        ALL_TAC
      ] THEN

      ASM_REWRITE_TAC[] THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `m:num` `pc + 0x54` `pc + 0x6c`
       `\i s. read X2 s = word (n - m) /\
              read X1 s = a /\
              read X3 s = b /\
              read X0 s = word(m - i) /\
              read X4 s = word i /\
              read X30 s = returnaddress` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [
        REWRITE_TAC[SUB_0] THEN
        ASSUME_TAC(WORD_RULE
         `word_add (word_sub (word m) (word n)) (word n):int64 = word m`) THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
            ~canonicalize_pc_diff:false exec (1--6) THEN
        CONJ_TAC THENL [REWRITE_TAC[WORD_SUB] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;

        ALL_TAC; (* main loop *)

        (* postcond *)
        REWRITE_TAC[] THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
            ~canonicalize_pc_diff:false exec [] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC
      ] THEN

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `i:num < n` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `i:num` THEN
      REWRITE_TAC[] THEN
      ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false exec (1--6) THEN

      CONJ_TAC THENL [
        IMP_REWRITE_TAC[VAL_WORD_SUB_EQ_0;VAL_WORD_EQ;DIMINDEX_64] THEN
        SIMPLE_ARITH_TAC; ALL_TAC
      ] THEN
      CONJ_TAC THENL
      [ IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
        [ AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC ]; ALL_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;

      (* ytoploop to ret *)
      SUBGOAL_THEN `~(n = m) /\ m:num < n /\ 0 < n - m /\ n - m < 2 EXP 64`
      STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[WORD_RULE
         `word_add (word_sub (word m) (word n)) (word n):int64 = word m`;
         VAL_WORD_0] THEN
      ENSURES_EVENTS_WHILE_UP2_TAC `n - m:num` `pc + 0x6c`
       `pc + 0x80` (* not pc + 0x7c because this is WHILE_UP2_TAC *)
       `\i s. read X2 s = word (n - m - i) /\
              read X3 s = b /\
              read X4 s = word(m + i) /\
              read X30 s = returnaddress` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [
        SIMPLE_ARITH_TAC;

        REWRITE_TAC[SUB_0; ADD_0] THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
            ~canonicalize_pc_diff:false exec [] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;

        ALL_TAC; (* main loop *)

        (* postcond *)
        REWRITE_TAC[] THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
            ~canonicalize_pc_diff:false exec (1--2) THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;
      ] THEN

      (* main loop *)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `i:num < n /\ m + i < n` STRIP_ASSUME_TAC THENL
        [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      VAL_INT64_TAC `m + i:num` THEN
      ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
          ~canonicalize_pc_diff:false exec (1--5) THEN

      CONJ_TAC THENL [
        IMP_REWRITE_TAC[VAL_WORD_SUB_EQ_0;VAL_WORD_EQ;DIMINDEX_64] THEN
        SIMPLE_ARITH_TAC; ALL_TAC
      ] THEN
      CONJ_TAC THENL
      [ IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL
        [ AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC ]; ALL_TAC] THEN
      CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC
    ]
  ];;

let BIGNUM_GT_LE_SAFE_TAC exec =
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (b:int64) (n:int64) (m:int64) (pc:num) (returnaddress:int64).
      if val m <= val n then
        APPEND
          (if val m = val n then f_ev_x_eqm a b n m pc returnaddress
           else APPEND (f_ev_x2_post a b n m pc returnaddress)
                  (APPEND (ENUMERATEL (val n - val m) (f_ev_x2_loop a b n m pc returnaddress))
                          (f_ev_x2_pre a b n m pc returnaddress)))
          (if val m = 0 then f_ev_x1_0 a b n m pc returnaddress
           else APPEND (f_ev_x1_post a b n m pc returnaddress)
                  (APPEND (ENUMERATEL (val m) (f_ev_x1_loop a b n m pc returnaddress))
                          (f_ev_x1_pre a b n m pc returnaddress)))
      else
        APPEND
          (APPEND (f_ev_y2_post a b n m pc returnaddress)
             (APPEND (ENUMERATEL (val m - val n) (f_ev_y2_loop a b n m pc returnaddress))
                     (f_ev_y2_pre a b n m pc returnaddress)))
          (if val n = 0 then f_ev_y1_0 a b n m pc returnaddress
           else APPEND (f_ev_y1_post a b n m pc returnaddress)
                  (APPEND (ENUMERATEL (val n) (f_ev_y1_loop a b n m pc returnaddress))
                          (f_ev_y1_pre a b n m pc returnaddress)))
      :(uarch_event) list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  W64_GEN_TAC `m:num` THEN X_GEN_TAC `a:int64` THEN
  W64_GEN_TAC `n:num` THEN X_GEN_TAC `b:int64` THEN
  MAP_EVERY X_GEN_TAC [`pc:num`;`returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; fst exec; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  VAL_INT64_TAC `1` THEN

  (*** Case split following the initial branch, m <= n case then n < m ***)

  ASM_CASES_TAC `m:num <= n` THENL
   [ SUBGOAL_THEN `~(n:num < m)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NOT_LT]; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x28`
      `\s. read X2 s = word (n - m) /\ read X3 s = b /\ read X1 s = a /\
           read X4 s = word m /\ read X30 s = returnaddress` THEN
     CONJ_TAC THENL
      [ ASM_CASES_TAC `m = 0` THENL
         [ UNDISCH_THEN `m = 0` SUBST_ALL_TAC THEN ASM_REWRITE_TAC[SUB_0] THEN
           ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
             exec (1--4) THEN ASM_REWRITE_TAC[WORD_SUB_0] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
           ALL_TAC ] THEN
        ASM_REWRITE_TAC[] THEN
        ENSURES_EVENTS_WHILE_UP2_TAC `m:num` `pc + 0x10` `pc + 0x28`
         `\i s. read X2 s = word (n - m) /\ read X3 s = b /\ read X1 s = a /\
                read X0 s = word(m - i) /\ read X4 s = word i /\ read X30 s = returnaddress` THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [ REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
           ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
             exec (1--4) THEN ASM_REWRITE_TAC[WORD_SUB] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
           ALL_TAC;
           ASM_REWRITE_TAC[] THEN
           ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
             exec [] THEN DISCHARGE_SAFETY_PROPERTY_TAC ] THEN
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        SUBGOAL_THEN `i:num < m` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
        VAL_INT64_TAC `i:num` THEN REWRITE_TAC[] THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
          exec (1--6) THEN
        CONJ_TAC THENL [ IMP_REWRITE_TAC[VAL_WORD_SUB_EQ_0;VAL_WORD_EQ;DIMINDEX_64] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
        CONJ_TAC THENL [ IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL [AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC]; ALL_TAC] THEN
        CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;
        REWRITE_TAC[] THEN
        ASM_CASES_TAC `m:num = n` THENL
         [ UNDISCH_THEN `m:num = n` SUBST_ALL_TAC THEN
           ASM_SIMP_TAC[SUB_REFL; LE_REFL; ADD_CLAUSES; VAL_WORD_LT; DIMINDEX_64] THEN
           ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
             exec (1--3) THEN DISCHARGE_SAFETY_PROPERTY_TAC;
           ALL_TAC ] THEN
         SUBGOAL_THEN `m:num < n /\ 0 < n - m /\ n - m < 2 EXP 64` STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
         ASM_REWRITE_TAC[] THEN
         ENSURES_EVENTS_WHILE_UP2_TAC `n - m:num` `pc + 0x2c` `pc + 0x40`
          `\i s. read X2 s = word (n - m - i) /\ read X3 s = b /\ read X4 s = word(m + i) /\ read X30 s = returnaddress` THEN
         ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
          [ SIMPLE_ARITH_TAC;
            REWRITE_TAC[SUB_0; ADD_0] THEN
            ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
              exec (1--1) THEN
            CONJ_TAC THENL [ASM_REWRITE_TAC[WORD_SUB;VAL_WORD_SUB_EQ_0] THEN NO_TAC; ALL_TAC] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
            ALL_TAC;
            ASM_SIMP_TAC[SUB_REFL;ARITH_RULE`m <= n ==> m + n - m = n`] THEN
            ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
              exec (1--2) THEN DISCHARGE_SAFETY_PROPERTY_TAC ] THEN
         X_GEN_TAC `i:num` THEN STRIP_TAC THEN
         SUBGOAL_THEN `i:num < n /\ m + i < n` STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
         VAL_INT64_TAC `m + i:num` THEN REWRITE_TAC[] THEN
         ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
           exec (1--5) THEN
         CONJ_TAC THENL [ IMP_REWRITE_TAC[VAL_WORD_SUB_EQ_0;VAL_WORD_EQ;DIMINDEX_64] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
         CONJ_TAC THENL [ IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL [AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC]; ALL_TAC] THEN
         CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
         DISCHARGE_SAFETY_PROPERTY_TAC ];

     (** case 2. ~ (m <= n), i.e. n < m **)
     SUBGOAL_THEN `n:num < m` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x6c`
      `\s. read X0 s = word (m - n) /\ read X3 s = b /\ read X1 s = a /\
           read X4 s = word n /\ read X30 s = returnaddress` THEN
     CONJ_TAC THENL
      [ ASM_CASES_TAC `n = 0` THENL
         [ UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN ASM_REWRITE_TAC[SUB_0] THEN
           ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
             exec (1--5) THEN
           CONJ_TAC THENL [
             REWRITE_TAC[VAL_WORD_0; VAL_WORD_SUB_EQ_0;
               WORD_RULE `word_add (word_sub (word 0) (word m)) (word m):int64 = word 0`] THEN NO_TAC;
             ALL_TAC] THEN
           DISCHARGE_SAFETY_PROPERTY_TAC;
           ALL_TAC ] THEN
        ASM_REWRITE_TAC[] THEN
        ENSURES_EVENTS_WHILE_UP2_TAC `n:num` `pc + 0x54` `pc + 0x6c`
         `\i s. read X0 s = word (m - n) /\ read X3 s = b /\ read X1 s = a /\
                read X2 s = word(n - i) /\ read X4 s = word i /\ read X30 s = returnaddress` THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [ REWRITE_TAC[SUB_0; ENUMERATEL_APPEND_ZERO] THEN
           ASSUME_TAC(WORD_RULE `word_add (word_sub (word n) (word m)) (word m):int64 = word n`) THEN
           ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
             exec (1--6) THEN
           CONJ_TAC THENL [REWRITE_TAC[WORD_SUB] THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
           ALL_TAC;
           ASM_REWRITE_TAC[] THEN
           ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
             exec [] THEN DISCHARGE_SAFETY_PROPERTY_TAC ] THEN
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        SUBGOAL_THEN `i:num < m` ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
        VAL_INT64_TAC `i:num` THEN REWRITE_TAC[] THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
          exec (1--6) THEN
        CONJ_TAC THENL [ IMP_REWRITE_TAC[VAL_WORD_SUB_EQ_0;VAL_WORD_EQ;DIMINDEX_64] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
        CONJ_TAC THENL [ IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL [AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC]; ALL_TAC] THEN
        CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC;
        SUBGOAL_THEN `~(n = m) /\ n:num < m /\ 0 < m - n /\ m - n < 2 EXP 64` STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[WORD_RULE `word_add (word_sub (word n) (word m)) (word m):int64 = word n`; VAL_WORD_0] THEN
        ENSURES_EVENTS_WHILE_UP2_TAC `m - n:num` `pc + 0x6c` `pc + 0x80`
         `\i s. read X0 s = word (m - n - i) /\ read X1 s = a /\ read X4 s = word(n + i) /\ read X30 s = returnaddress` THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [ SIMPLE_ARITH_TAC;
           REWRITE_TAC[SUB_0; ADD_0] THEN
           ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
             exec [] THEN DISCHARGE_SAFETY_PROPERTY_TAC;
           ALL_TAC;
           REWRITE_TAC[] THEN
           ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
             exec (1--2) THEN DISCHARGE_SAFETY_PROPERTY_TAC ] THEN
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        SUBGOAL_THEN `i:num < m /\ n + i < m` STRIP_ASSUME_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
        VAL_INT64_TAC `n + i:num` THEN
        ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC) ~canonicalize_pc_diff:false
          exec (1--5) THEN
        CONJ_TAC THENL [ IMP_REWRITE_TAC[VAL_WORD_SUB_EQ_0;VAL_WORD_EQ;DIMINDEX_64] THEN SIMPLE_ARITH_TAC; ALL_TAC ] THEN
        CONJ_TAC THENL [ IMP_REWRITE_TAC[WORD_SUB2] THEN CONJ_TAC THENL [AP_TERM_TAC THEN SIMPLE_ARITH_TAC; SIMPLE_ARITH_TAC]; ALL_TAC] THEN
        CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC ] ];;
