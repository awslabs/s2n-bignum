(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_cbd2_spec.ml";;


let NIBBLE_BIT = prove
 (NIBBLE_BIT_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SPEC_TAC(`n DIV 2 EXP m`,`x:num`) THEN GEN_TAC THEN
  GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV) [GSYM(SPEC `2` EXP_1)] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; ARITH_RULE `16 = 2 EXP 4`;
              MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `k < 4 ==> MIN 4 (k + 1) = k + 1`]);;

let CBD2_NIBBLE = prove
 (CBD2_NIBBLE_STMT,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                      WORD_RED_CONV)));;

let CBD2_LANE = prove
 (CBD2_LANE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `word_subword (word((n DIV 2 EXP (32 * i)) MOD 4294967296):int32)
                 (4 * j,4):4 word =
    word((n DIV 2 EXP (4 * (8 * i + j))) MOD 16)`
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o lhand o snd) THEN
    ANTS_TAC THENL
     [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`] THEN
    ASM_SIMP_TAC[DIV_MOD_EXP_LOW; ARITH_RULE `j < 8 ==> 4 * j + 4 <= 32`] THEN
    REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 4 = 16`] THEN
    REWRITE_TAC[ARITH_RULE `32 * i + 4 * j = 4 * (8 * i + j)`];
    ALL_TAC] THEN
  SIMP_TAC[CBD2_NIBBLE; MOD_LT_EQ; ARITH_EQ] THEN
  SIMP_TAC[NIBBLE_BIT; ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GEN_ALL(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`x:num`; `2`; `8`] MOD_MOD))]);;

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `n:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[SOME_FLAGS; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `32` `pc + mlkem_poly_cbd2_loop1`
   `pc + mlkem_poly_cbd2_loop1_test`
   `\i s. read X1 s = word i /\
          read X4 s = a /\
          read X5 s = r /\
          read Q3 s = word 0x00030003000300030003000300030003 /\
          read Q5 s = word 0xffffffe2ffffffe6ffffffeaffffffee /\
          read Q6 s = word 0xfffffff2fffffff6fffffffafffffffe /\
          read Q7 s = word 0xffffffe4ffffffe8ffffffecfffffff0 /\
          read Q16 s = word 0xfffffff4fffffff8fffffffc00000000 /\
          read X30 s = returnaddress /\
          read (memory :> bytes(a,128)) s = n /\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   iword(&((n DIV 2 EXP (4 * j)) MOD 2 +
                           (n DIV 2 EXP (4 * j + 1)) MOD 2) -
                         &((n DIV 2 EXP (4 * j + 2)) MOD 2 +
                           (n DIV 2 EXP (4 * j + 3)) MOD 2)))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, with the vectors of shifts from the image ***)

    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP th))
      MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_CONSTANTS THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_EXEC (1--3) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_EXEC (4--6) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_EXEC (7--10) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_EXEC (11--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body, for four bytes and eight coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`a:int64`; `128`; `n:num`; `4 * i`; `s0:armstate`]
                 READ_MEMORY_BYTES32_OF_NUM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `8 * 4 * i = 32 * i`]) THEN
    ABBREV_TAC `t:int32 = word((n DIV 2 EXP (32 * i)) MOD 4294967296)` THEN
    CBD2_INDEX_TAC THEN
    MAP_EVERY (fun k ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_EXEC [k] THEN
      SIMD_SIMPLIFY_TAC[]) (2--18) THEN
    FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
      check (can (term_match [] `read (memory :> bytes128 a) s = x`) o
             concl)) THEN
    FIRST_ASSUM(fun tth ->
      if can (term_match []
               `word((n DIV 2 EXP (32 * i)) MOD 4294967296):int32 = t`)
             (concl tth)
      then DISCH_THEN(fun th ->
             MAP_EVERY (ASSUME_TAC o CBD2_LANE_RULE tth o
                        CONV_RULE(RAND_CONV(SIMD_SIMPLIFY_CONV [])))
                       (CONJUNCTS th))
      else failwith "CBD2_LANE_RULE") THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE
     `j < 8 * (i + 1) <=>
      j < 8 * i \/ j = 8 * i \/ j = 8 * i + 1 \/ j = 8 * i + 2 \/
      j = 8 * i + 3 \/ j = 8 * i + 4 \/ j = 8 * i + 5 \/ j = 8 * i + 6 \/
      j = 8 * i + 7`] THEN
    REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
                FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `2 * 8 * i = 16 * i`] THEN
    REWRITE_TAC(map (fun k ->
      ARITH_RULE(subst [mk_small_numeral k,`k:num`;
                        mk_small_numeral(2 * k),`l:num`]
                       `2 * (8 * i + k) = 16 * i + l`)) (1--7)) THEN
    ASM_REWRITE_TAC[];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_EXEC (2--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `bytes16` (concl th)))]);;

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a r pc returnaddress)
        (APPEND
          (ENUMERATEL 32 (\i. f_ev_loop a r pc returnaddress i))
          (f_ev_prol a r pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              SOME_FLAGS; ALL;
              fst MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem_poly_cbd2_loop1`
   `pc + mlkem_poly_cbd2_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X1 s = word i /\
           read X4 s = a /\
           read X5 s = r` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_EXEC (1--3) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_EXEC (4--6) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_EXEC (7--10) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_EXEC (11--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  CBD2_INDEX_TAC THEN
  MAP_EVERY (fun k ->
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_MONO_EXEC [k] THEN
    SIMD_SIMPLIFY_TAC[]) (2--20) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `~(val(word_add (word i) (word 18446744073709551585):int64) = 0) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    ASM_CASES_TAC `i = 31` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 32 /\ ~(i = 31)
      ==> i + 18446744073709551585 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
