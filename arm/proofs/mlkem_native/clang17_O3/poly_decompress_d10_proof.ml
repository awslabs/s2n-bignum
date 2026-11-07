(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/clang17_O3/poly_decompress_d10_spec.ml";;


let READ_MEMORY_BYTES128_OF_NUM = prove
 (READ_MEMORY_BYTES128_OF_NUM_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[BYTES128_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES;
              VAL_WORD; DIMINDEX_128] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MOD_MOD_REFL] THEN
  REWRITE_TAC[ARITH_RULE `340282366920938463463374607431768211456 =
                          2 EXP (8 * 16)`; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let D10_WIN128 = prove
 (D10_WIN128_STMT,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `320`; `n:num`; `20 * i`; `s:armstate`]
                READ_MEMORY_BYTES128_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[EXP; DIV_1; ARITH_RULE
   `2 EXP 128 = 340282366920938463463374607431768211456`] THEN
  REWRITE_TAC[ARITH_RULE `8 * 20 * i = 160 * i`]);;

let D10_WIN32 = prove
 (D10_WIN32_STMT,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `320`; `n:num`; `20 * i + 16`; `s:armstate`]
                READ_MEMORY_BYTES32_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD;
              ARITH_RULE `2 EXP 32 = 4294967296`] THEN
  REWRITE_TAC[ARITH_RULE `8 * (20 * i + 16) = 160 * i + 128`]);;

let D10D_FIELD = prove
 (D10D_FIELD_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 10 10 = 10`] THEN
  ASM_SIMP_TAC[DIV_MOD_EXP_LOW; ARITH_RULE `k < 16 ==> 10 * k + 10 <= 160`] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `1024 = 2 EXP 10`] THEN
  REWRITE_TAC[ARITH_RULE `160 * i + 10 * k = 10 * (16 * i + k)`]);;

let D10_LOOP_SPLIT = prove
 (D10_LOOP_SPLIT_STMT,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `j < 16 * i` THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j - 16 * i`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`r:int64`; `a:int64`; `n:num`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the test at the end of the body ***)

  ENSURES_WHILE_UP2_TAC `16` `pc + mlkem_poly_decompress_d10_loop2`
   `pc + mlkem_poly_decompress_d10_loop2_exit`
   `\i s. read X0 s = r /\
          read X1 s = word_add a (word(20 * i)) /\
          read X8 s = word(32 * i) /\
          read Q0 s = word 0xffffff0fffffff0affffff05ffffff00 /\
          read Q1 s = word 0xffffffffffffffffffffffff100b0601 /\
          read Q2 s = word 0xffffff03ffffff02ffffff01ffffff00 /\
          read Q3 s = word 0xffffffffffffffffffffffff110c0702 /\
          read Q4 s = word 0xffffffffffffffffffffffff120d0803 /\
          read Q16 s = word 0xffffffffffffffffffffffff130e0904 /\
          read Q5 s = word 0x00000300000003000000030000000300 /\
          read Q6 s = word 0x0d010d010d010d01 /\
          read Q7 s = word 0x000003c0000003c0000003c0000003c0 /\
          read Q17 s = word 0x000003f0000003f0000003f0000003f0 /\
          read Q18 s = word 0x00000d0100000d0100000d0100000d01 /\
          read X30 s = returnaddress /\
          read (memory :> bytes(a,320)) s = n /\
          (!j. j < 16 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((3329 * (n DIV 2 EXP (10 * j)) MOD 2 EXP 10 + 512)
                        DIV 1024))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, with the check for overlap and the constants: the
     *** TBL indices (0xff for a zero byte) in Q0-Q4 and Q16, the masks, and
     *** 3329, with the page of the constants computed by ADRP in steps 1,
     *** 2, 3, 4, 8 and 12 of the vector code ***)

    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(fun th -> MAP_EVERY (fun c -> ASSUME_TAC(MATCH_MP c th))
      (CONJUNCTS MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_CONSTANTS)) THEN
    DD10_CHECK_TAC (fun off ->
      MAP_EVERY (fun k ->
        ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_EXEC
          [k + off] THEN
        (if mem k [1;2;3;4;8;12] then MLKEM_NATIVE_ADRP_TAC else ALL_TAC))
       (1--21)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body, for 20 bytes and 16 coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`a:int64`; `n:num`; `i:num`; `s0:armstate`] D10_WIN128) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`a:int64`; `n:num`; `i:num`; `s0:armstate`] D10_WIN32) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ABBREV_TAC `w:160 word = word(n DIV 2 EXP (160 * i))` THEN
    MAP_EVERY (fun k ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_EXEC [k] THEN
      DD10_SIMD_TAC) (1--71) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> can (term_match [] `read (memory :> bytes64 a) s = x`)
                           (concl th) && free_in `r:int64` (concl th)))) THEN
    REPEAT(DISCH_THEN(fun th -> MAP_EVERY (ASSUME_TAC o D10_LANE_FIELD_RULE o
                         CONV_RULE(RAND_CONV BITS_NORM_CONV))
                         (CONJUNCTS th))) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(val(word_add (word(32 * i)) (word 18446744073709551136):int64) = 0) <=>
      i + 1 < 16`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      ASM_CASES_TAC `i = 15` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 16 /\ ~(i = 15)
        ==> 32 * i + 18446744073709551136 < 18446744073709551616`] THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN
    TRY(FIRST
     [COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC;
      REWRITE_TAC[ARITH_RULE `32 * (i + 1) = 32 * i + 32`] THEN
      CONV_TAC WORD_RULE THEN NO_TAC;
      REWRITE_TAC[ARITH_RULE `20 * (i + 1) = 20 * i + 20`] THEN
      CONV_TAC WORD_RULE THEN NO_TAC]) THEN
    MATCH_MP_TAC D10_LOOP_SPLIT THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; CONV_TAC EXPAND_CASES_CONV] THEN
    REWRITE_TAC[ARITH_RULE `2 * (16 * i + 0) = 32 * i`;
                ARITH_RULE `2 * (16 * i + 1) = 32 * i + 2`;
                ARITH_RULE `2 * (16 * i + 2) = 32 * i + 4`;
                ARITH_RULE `2 * (16 * i + 3) = 32 * i + 6`;
                ARITH_RULE `2 * (16 * i + 4) = 32 * i + 8`;
                ARITH_RULE `2 * (16 * i + 5) = 32 * i + 10`;
                ARITH_RULE `2 * (16 * i + 6) = 32 * i + 12`;
                ARITH_RULE `2 * (16 * i + 7) = 32 * i + 14`;
                ARITH_RULE `2 * (16 * i + 8) = 32 * i + 16`;
                ARITH_RULE `2 * (16 * i + 9) = 32 * i + 18`;
                ARITH_RULE `2 * (16 * i + 10) = 32 * i + 20`;
                ARITH_RULE `2 * (16 * i + 11) = 32 * i + 22`;
                ARITH_RULE `2 * (16 * i + 12) = 32 * i + 24`;
                ARITH_RULE `2 * (16 * i + 13) = 32 * i + 26`;
                ARITH_RULE `2 * (16 * i + 14) = 32 * i + 28`;
                ARITH_RULE `2 * (16 * i + 15) = 32 * i + 30`] THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "w" THEN
    REWRITE_TAC(map (fun k ->
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
       (MP (SPECL [`n:num`; `i:num`; mk_small_numeral k] D10D_FIELD)
           (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                         (mk_small_numeral k) `16`))))) (0--15)) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `bytes16` (concl th)))]);;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a r pc returnaddress)
        (APPEND
          (ENUMERATEL 16 (\i. f_ev_loop a r pc returnaddress i))
          (APPEND
            (f_ev_vec a r pc returnaddress)
            (if val(word_add a (word 320):int64) <= val r
             then f_ev_check1 a r pc returnaddress
             else f_ev_check2 a r pc returnaddress)))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `16` `pc + mlkem_poly_decompress_d10_loop2`
   `pc + mlkem_poly_decompress_d10_loop2_exit`
    `\i s. read X30 s = returnaddress /\
           read X0 s = r /\
           read X1 s = word_add a (word(20 * i)) /\
           read X8 s = word(32 * i)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The check for overlap, and the setup of the vector code ***)

    REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN
    ENSURES_EVENTS_SEQUENCE_TAC `pc + mlkem_poly_decompress_d10_join1`
     `\s. read X0 s = r /\ read X1 s = a /\
          read X30 s = returnaddress` THEN
    CONJ_TAC THENL
     [REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
      DD10_CHECK_TAC (fun _ ->
        ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
        DISCHARGE_SAFETY_PROPERTY_TAC);
      ALL_TAC] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MAP_EVERY (fun k ->
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_EXEC [k] THEN
      (if mem k [1;2;3;4;8;12] then MLKEM_NATIVE_ADRP_TAC else ALL_TAC))
     (1--21) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_EXEC (1--71) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(val(word_add (word(32 * i)) (word 18446744073709551136):int64) = 0) <=>
      i + 1 < 16`
    SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      ASM_CASES_TAC `i = 15` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE
       `i < 16 /\ ~(i = 15)
        ==> 32 * i + 18446744073709551136 < 18446744073709551616`] THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `20 * (i + 1) = 20 * i + 20`;
                  ARITH_RULE `32 * (i + 1) = 32 * i + 32`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The return ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D10_CLANG17_O3_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;
