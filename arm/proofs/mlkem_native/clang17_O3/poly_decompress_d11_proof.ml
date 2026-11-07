(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/clang17_O3/poly_decompress_d11_spec.ml";;


let WORD_ADD_2EXP64 = prove
 (WORD_ADD_2EXP64_STMT,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE);;

let DECOMPRESS_D11_ADDR = prove
 (DECOMPRESS_D11_ADDR_STMT,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `5 + 11 * i + 18446744073709551611 = 11 * i + 18446744073709551616`;
              ARITH_RULE `5 + 11 * i + 18446744073709551612 = (11 * i + 1) + 18446744073709551616`;
              ARITH_RULE `5 + 11 * i + 18446744073709551613 = (11 * i + 2) + 18446744073709551616`;
              ARITH_RULE `5 + 11 * i + 18446744073709551614 = (11 * i + 3) + 18446744073709551616`;
              ARITH_RULE `5 + 11 * i + 18446744073709551615 = (11 * i + 4) + 18446744073709551616`;
              ARITH_RULE `5 + 11 * i = 11 * i + 5`;
              ARITH_RULE `5 + 11 * i + 1 = 11 * i + 6`;
              ARITH_RULE `5 + 11 * i + 2 = 11 * i + 7`;
              ARITH_RULE `5 + 11 * i + 3 = 11 * i + 8`;
              ARITH_RULE `5 + 11 * i + 4 = 11 * i + 9`;
              ARITH_RULE `5 + 11 * i + 5 = 11 * i + 10`; WORD_ADD_2EXP64]);;

let DECOMPRESS_D11_STORE_ADDR = prove
 (DECOMPRESS_D11_STORE_ADDR_STMT,
  REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let DECOMPRESS_D11_EVENT_ADDR = prove
 (DECOMPRESS_D11_EVENT_ADDR_STMT,
  SUBGOAL_THEN
   `word 18446744073709551611:int64 = word_neg(word 5) /\
    word 18446744073709551612:int64 = word_neg(word 4) /\
    word 18446744073709551613:int64 = word_neg(word 3) /\
    word 18446744073709551614:int64 = word_neg(word 2) /\
    word 18446744073709551615:int64 = word_neg(word 1)`
  STRIP_ASSUME_TAC THENL [CONV_TAC WORD_REDUCE_CONV; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[WORD_ADD] THEN CONV_TAC WORD_RULE);;

let D11_BYTES = prove
 (D11_BYTES_STMT,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `352`; `n:num`; `11 * i + j`; `s:armstate`]
                READ_MEMORY_BYTES8_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 8 = 256`] THEN
  REWRITE_TAC[ARITH_RULE `8 * (11 * i + j) = 88 * i + 8 * j`]);;

let D11_HALF = prove
 (D11_HALF_STMT,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `352`; `n:num`; `11 * i`; `s:armstate`]
                READ_MEMORY_BYTES16_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[EXP; DIV_1; ARITH_RULE `2 EXP 16 = 65536`] THEN
  REWRITE_TAC[ARITH_RULE `8 * 11 * i = 88 * i`]);;

let D11D_FIELD = prove
 (D11D_FIELD_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 11 11 = 11`] THEN
  ASM_SIMP_TAC[DIV_MOD_EXP_LOW; ARITH_RULE `k < 8 ==> 11 * k + 11 <= 88`] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2048 = 2 EXP 11`] THEN
  REWRITE_TAC[ARITH_RULE `88 * i + 11 * k = 11 * (8 * i + k)`]);;

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `n:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the test at the top of the body ***)

  ENSURES_WHILE_UP2_TAC `32` `pc + mlkem_poly_decompress_d11_loop1`
   `pc + mlkem_poly_decompress_d11_loop1_exit`
   `\i s. read X0 s = r /\
          read X8 s = word(16 * i) /\
          read X9 s = word 3329 /\
          read X10 s = word_add (word_add a (word 5)) (word(11 * i)) /\
          read X11 s = word 1024 /\
          read Q0 s = word 0x70000000a0000000500000008 /\
          read Q1 s = word 0x0d010d010d010d01 /\
          read Q2 s = word 0x78000000400000007e000000700 /\
          read X30 s = returnaddress /\
          read (memory :> bytes(a,352)) s = n /\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((3329 * (n DIV 2 EXP (11 * j)) MOD 2 EXP 11 + 1024)
                        DIV 2048))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, with the constants from the image ***)

    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(fun th -> MAP_EVERY (fun c -> ASSUME_TAC(MATCH_MP c th))
      (CONJUNCTS MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_CONSTANTS)) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC (1--2) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC (3--3) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC (4--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body, for eleven bytes and eight coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun j ->
      MP_TAC(REWRITE_RULE[ADD_CLAUSES]
       (CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
         (SPECL [`a:int64`; `n:num`; `i:num`; `s0:armstate`;
                 mk_small_numeral j] D11_BYTES))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC) (0--10) THEN
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read (memory :> bytes8 x) s = y`) (concl th)
      then REWRITE_RULE[DECOMPRESS_D11_ADDR] th else th) THEN
    ABBREV_TAC `w:88 word = word(n DIV 2 EXP (88 * i))` THEN
    MAP_EVERY (fun k ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC [k] THEN
      SIMD_SIMPLIFY_TAC[]) (1--57) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[DECOMPRESS_D11_STORE_ADDR]) THEN
    RULE_ASSUM_TAC(fun th ->
      if can (term_match [] `read (memory :> bytes16 a) s = x`) (concl th)
      then D11_LANE_FIELD_RULE th else th) THEN
    FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (can (term_match [] `read (memory :> bytes64 a) s = x`) o
             concl)) THEN
    DISCH_THEN(fun th -> MAP_EVERY (ASSUME_TAC o D11_LANE_FIELD_RULE o
                         D11_VEC_LANE_RULE o
                         CONV_RULE(RAND_CONV(SIMD_SIMPLIFY_CONV [])))
                         (CONJUNCTS th)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(val(word_add (word(16 * i)) (word 18446744073709551120):int64) = 0) <=>
      i + 1 < 32`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      ASM_CASES_TAC `i = 31` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 32 /\ ~(i = 31)
        ==> 16 * i + 18446744073709551120 < 18446744073709551616`] THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN
    TRY(FIRST
     [COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC;
      REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE THEN NO_TAC;
      REWRITE_TAC[ARITH_RULE `11 * (i + 1) = 11 * i + 11`] THEN
      CONV_TAC WORD_RULE THEN NO_TAC]) THEN
    REWRITE_TAC[ARITH_RULE
     `j < 8 * (i + 1) <=>
      j < 8 * i \/ j = 8 * i \/ j = 8 * i + 1 \/ j = 8 * i + 2 \/
      j = 8 * i + 3 \/ j = 8 * i + 4 \/ j = 8 * i + 5 \/ j = 8 * i + 6 \/
      j = 8 * i + 7`] THEN
    REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
                FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `2 * 8 * i = 16 * i`;
                ARITH_RULE `2 * (8 * i + 1) = 16 * i + 2`;
                ARITH_RULE `2 * (8 * i + 2) = 16 * i + 4`;
                ARITH_RULE `2 * (8 * i + 3) = 16 * i + 6`;
                ARITH_RULE `2 * (8 * i + 4) = 16 * i + 8`;
                ARITH_RULE `2 * (8 * i + 5) = 16 * i + 10`;
                ARITH_RULE `2 * (8 * i + 6) = 16 * i + 12`;
                ARITH_RULE `2 * (8 * i + 7) = 16 * i + 14`] THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "w" THEN
    REWRITE_TAC(map (fun k ->
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
       (MP (SPECL [`n:num`; `i:num`; mk_small_numeral k] D11D_FIELD)
           (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                         (mk_small_numeral k) `8`))))) (0--7)) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `bytes16` (concl th)))]);;

let MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT,
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
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem_poly_decompress_d11_loop1`
   `pc + mlkem_poly_decompress_d11_loop1_exit`
    `\i s. read X30 s = returnaddress /\
           read X0 s = r /\
           read X8 s = word(16 * i) /\
           read X10 s = word_add (word_add a (word 5)) (word(11 * i))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC (1--2) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC (3--3) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC (4--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC (1--1) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_DECOMPRESS_D11_CLANG17_O3_EXEC (1--57) THEN
  SUBGOAL_THEN
   `~(val(word_add (word(16 * i)) (word 18446744073709551120):int64) = 0) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    ASM_CASES_TAC `i = 31` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 32 /\ ~(i = 31)
      ==> 16 * i + 18446744073709551120 < 18446744073709551616`] THEN
    SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `11 * (i + 1) = 11 * i + 11`;
                ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) THEN
  REWRITE_TAC[DECOMPRESS_D11_EVENT_ADDR] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
