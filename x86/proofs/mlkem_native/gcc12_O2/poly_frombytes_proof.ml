(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/gcc12_O2/poly_frombytes_spec.ml";;


let FROMBYTES_LANES = prove
 (FROMBYTES_LANES_STMT,
  let rule = GEN_ALL o CONV_RULE NUM_REDUCE_CONV o SPEC_ALL in
  let l1 = rule(SPECL [`m:num`; `16`; `16`] MOD_MOD)
  and l2 = rule(GSYM(SPECL [`m:num`; `16`; `16`] DIV_MOD))
  and l3 = rule(SPECL [`m:num`; `256`; `16`] DIV_DIV)
  and l4 = rule(GSYM(SPECL [`m:num`; `4096`; `16`] DIV_DIV))
  and l5 = rule(GSYM(SPECL [`m:num`; `256`; `16`] MOD_MULT_MOD))
  and l6 = rule(GSYM(SPECL [`m:num`; `16`; `256`] MOD_MULT_MOD)) in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SPEC_TAC(`n DIV 2 EXP (24 * i)`,`m:num`) THEN
  GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD_JOIN;
     VAL_WORD_SUBWORD; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOD_MOD_REFL; DIV_1; l1; l2; l3] THEN
  REWRITE_TAC[l4] THEN REWRITE_TAC[l5; l6; MOD_MOD_REFL]);;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_CORRECT = prove
 (MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `128` `pc + mlkem_poly_frombytes_loop1` `pc + mlkem_poly_frombytes_loop1_test`
   `\i s. read RDI s = word_add r (word(4 * i)) /\
          read RSI s = word_add a (word(3 * i)) /\
          read R9 s = word_add a (word 384) /\
          read (memory :> bytes(a,384)) s = n /\
          (!j. j < 2 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((n DIV 2 EXP (12 * j)) MOD 2 EXP 12))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body, for three bytes and two coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun k ->
      MP_TAC(SPECL [`a:int64`; `384`; `n:num`; k; `s0:x86state`]
                   READ_MEMORY_BYTES8_OF_NUM) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC])
     [`3 * i`; `3 * i + 1`; `3 * i + 2`] THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--14) THEN
    ADDR_NORM_BYTES16_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC [15] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `3 * (i + 1) = 3 * i + 3`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE
       `j < 2 * (i + 1) <=> j < 2 * i \/ j = 2 * i \/ j = 2 * i + 1`] THEN
      REWRITE_TAC[TAUT `(p \/ q \/ r ==> s) <=>
                        (p ==> s) /\ (q ==> s) /\ (r ==> s)`;
                  FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `2 * 2 * i = 4 * i`;
                  ARITH_RULE `2 * (2 * i + 1) = 4 * i + 2`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[GSYM FROMBYTES_LANES] THEN
      REWRITE_TAC[WORD_VAL_MOD_256; WORD_VAL_MOD_65536] THEN
      CONJ_TAC THEN BYTES_BITBLAST_TAC];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add a (word 384))
                     (word_add a (word (3 * i))):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 128 ==> 3 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 128` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--2) THEN
    PTR_DECIDE_RIP_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `bytes16` (concl th)))]);;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_CORRECT);;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SAFE = time prove
 (MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SAFE_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num).
      APPEND
        (f_ev_epil a r pc)
        (APPEND
          (ENUMERATEL 128 (\i. f_ev_loop a r pc i))
          (f_ev_prol a r pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + mlkem_poly_frombytes_loop1` `pc + mlkem_poly_frombytes_loop1_exit`
    `\i s. read RDI s = word_add r (word(4 * i)) /\
           read RSI s = word_add a (word(3 * i)) /\
           read R9 s = word_add a (word 384)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--2) THEN
    REWRITE_TAC[MULT_0; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--0) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--17) THEN
  SUBGOAL_THEN
   `~(val(word_add a (word 384):int64) =
      val(word_add (word_add a (word (3 * i))) (word 3):int64)) <=>
    i + 1 < 128`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_EQ; GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_EQ; DIMINDEX_64; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 128 ==> 3 * i + 3 < 18446744073709551616`] THEN
    UNDISCH_TAC `i < 128` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`;
                ARITH_RULE `3 * (i + 1) = 3 * i + 3`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_FULL = time prove
 (MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_FULL_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num).
      APPEND
        (f_ev_epil a r pc)
        (APPEND
          (ENUMERATEL 128 (\i. f_ev_loop a r pc i))
          (f_ev_prol a r pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + mlkem_poly_frombytes_loop1` `pc + mlkem_poly_frombytes_loop1_exit`
   `\i s. read RDI s = word_add r (word(4 * i)) /\
          read RSI s = word_add a (word(3 * i)) /\
          read R9 s = word_add a (word 384) /\
          read (memory :> bytes(a,384)) s = n /\
          (!j. j < 2 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((n DIV 2 EXP (12 * j)) MOD 2 EXP 12))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, for three bytes and two coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MAP_EVERY (fun k ->
      MP_TAC(SPECL [`a:int64`; `384`; `n:num`; k; `s0:x86state`]
                   READ_MEMORY_BYTES8_OF_NUM) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC])
     [`3 * i`; `3 * i + 1`; `3 * i + 2`] THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (1--14) THEN
    ADDR_NORM_BYTES16_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC (15--17) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add a (word 384))
                     (word_add (word_add a (word (3 * i))) (word 3)):int64) =
        0) <=>
      i + 1 < 128`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add (word_add a y) z):int64 =
        word_sub x (word_add y z)`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 128 ==> 3 * i + 3 < 18446744073709551616`] THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `3 * (i + 1) = 3 * i + 3`;
                  ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC]) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE
       `j < 2 * (i + 1) <=> j < 2 * i \/ j = 2 * i \/ j = 2 * i + 1`] THEN
      REWRITE_TAC[TAUT `(p \/ q \/ r ==> s) <=>
                        (p ==> s) /\ (q ==> s) /\ (r ==> s)`;
                  FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `2 * 2 * i = 4 * i`;
                  ARITH_RULE `2 * (2 * i + 1) = 4 * i + 2`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[GSYM FROMBYTES_LANES] THEN
      REWRITE_TAC[WORD_VAL_MOD_256; WORD_VAL_MOD_65536] THEN
      CONJ_TAC THEN BYTES_BITBLAST_TAC;
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The loop exit ***)

    REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
        check (fun th -> is_forall(concl th) &&
                         free_in `bytes16` (concl th)));
      DISCHARGE_SAFETY_PROPERTY_TAC]]);;

let MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL = time prove
 (MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_FROMBYTES_GCC12_O2_IMAGE_FULL THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
