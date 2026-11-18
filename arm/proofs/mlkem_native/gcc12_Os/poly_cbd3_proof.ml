(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_Os/poly_cbd3_spec.ml";;


let CBD3_BYTES = prove
 (CBD3_BYTES_STMT,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `192`; `n:num`; `3 * i + j`; `s:armstate`]
                READ_MEMORY_BYTES8_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 8 = 256`] THEN
  REWRITE_TAC[ARITH_RULE `8 * (3 * i + j) = 24 * i + 8 * j`]);;

let SIXBIT_BIT = prove
 (SIXBIT_BIT_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SPEC_TAC(`n DIV 2 EXP m`,`x:num`) THEN GEN_TAC THEN
  GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV) [GSYM(SPEC `2` EXP_1)] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; ARITH_RULE `64 = 2 EXP 6`;
              MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `k < 6 ==> MIN 6 (k + 1) = k + 1`]);;

let CBD3_FIELD = prove
 (CBD3_FIELD_STMT,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                      WORD_RED_CONV)));;

let CBD3_LANE = prove
 (CBD3_LANE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `word_subword (word(n DIV 2 EXP (24 * i)):24 word) (6 * j,6):6 word =
    word((n DIV 2 EXP (6 * (4 * i + j))) MOD 64)`
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o lhand o snd) THEN
    ANTS_TAC THENL
     [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 6 = 64`] THEN
    REWRITE_TAC[ARITH_RULE `24 * i + 6 * j = 6 * (4 * i + j)`];
    ALL_TAC] THEN
  SIMP_TAC[CBD3_FIELD; MOD_LT_EQ; ARITH_EQ] THEN
  SIMP_TAC[SIXBIT_BIT; ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GEN_ALL(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`x:num`; `2`; `32`] MOD_MOD))]);;

let MLKEM_NATIVE_POLY_CBD3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_CBD3_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `n:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `64` `pc + mlkem_poly_cbd3_loop1`
   `pc + mlkem_poly_cbd3_loop1_test`
   `\i s. read X0 s = r /\
          read X1 s = word_add a (word(3 * i)) /\
          read X6 s = word(4 * i) /\
          read X7 s = word 0x249249 /\
          read X30 s = returnaddress /\
          read (memory :> bytes(a,192)) s = n /\
          (!j. j < 4 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   iword(&((n DIV 2 EXP (6 * j)) MOD 2 +
                           (n DIV 2 EXP (6 * j + 1)) MOD 2 +
                           (n DIV 2 EXP (6 * j + 2)) MOD 2) -
                         &((n DIV 2 EXP (6 * j + 3)) MOD 2 +
                           (n DIV 2 EXP (6 * j + 4)) MOD 2 +
                           (n DIV 2 EXP (6 * j + 5)) MOD 2)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_OS_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body, for three bytes and four coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun j ->
      MP_TAC(REWRITE_RULE[ADD_CLAUSES]
       (CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
         (SPECL [`a:int64`; `n:num`; `i:num`; `s0:armstate`;
                 mk_small_numeral j] CBD3_BYTES))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC) (0--2) THEN
    ABBREV_TAC `w:24 word = word(n DIV 2 EXP (24 * i))` THEN
    CBD3_BODY_TAC THEN
    FIRST_ASSUM(fun tth ->
      if can (term_match [] `word(n DIV 2 EXP (24 * i)):24 word = w`)
             (concl tth)
      then MAP_EVERY (fun j -> CBD3_LANE_RULE j tth) (0--3)
      else failwith "CBD3_LANE_RULE") THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `3 * (i + 1) = 3 * i + 3`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN WORD_SMALL_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE
     `j < 4 * (i + 1) <=>
      j < 4 * i \/ j = 4 * i \/ j = 4 * i + 1 \/ j = 4 * i + 2 \/
      j = 4 * i + 3`] THEN
    REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
                FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_OS_EXEC (1--1) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_OS_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_OS_EXEC (1--1) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_OS_EXEC (2--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `bytes16` (concl th)))]);;

let MLKEM_NATIVE_POLY_CBD3_GCC12_OS_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_CBD3_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a r pc returnaddress)
        (APPEND
          (ENUMERATEL 64 (\i. f_ev_loop a r pc returnaddress i))
          (f_ev_prol a r pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_CBD3_GCC12_OS_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `64` `pc + mlkem_poly_cbd3_loop1`
   `pc + mlkem_poly_cbd3_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X0 s = r /\
           read X1 s = word_add a (word(3 * i)) /\
           read X6 s = word(4 * i) /\
           read X7 s = word 0x249249` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_OS_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_CBD3_GCC12_OS_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  CBD3_BODY_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD3_GCC12_OS_EXEC (60--61) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `~(val(word_sub
           (word_zx (word_zx (word_add (word_zx (word (4 * i):int64):int32)
                                       (word 4)):int64):int32)
           (word 256):int32) = 0) <=>
    i + 1 < 64`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD_ZX_GEN; VAL_WORD_ADD; VAL_WORD;
                DIMINDEX_32; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 64 ==> 4 * i < 18446744073709551616 /\ 4 * i < 4294967296 /\
                 4 * i + 4 < 4294967296 /\
                 4 * i + 4 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `3 * (i + 1) = 3 * i + 3`] THEN CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `4 * (i + 1) = 4 * i + 4`] THEN WORD_SMALL_TAC;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
