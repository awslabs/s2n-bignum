(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition of polynomials: the proof (see poly_add_spec.ml).                *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/poly_add_spec.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. Each of the 64 iterations   *)
(* of the loop adds 4 coefficients, loaded and stored as one 128-bit word;   *)
(* the loop test is the end of the body, as ENSURES_EVENTS_WHILE_UP2_TAC     *)
(* requires, and the events of an iteration depend on its index only. The    *)
(* legacy SSE instructions keep the upper half of YMM0, whose initial value  *)
(* is a ghost variable.                                                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(r:int64) (b:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil r b pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 64
            (\i. f_ev_loop r b pc stackpointer returnaddress i))
          (f_ev_prol r b pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `r:int64`; `b:int64`; `x:num->int32`;
    `y:num->int32`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; mld_poly_add;
              fst MLDSA_NATIVE_POLY_ADD_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64` `pc + mldsa_poly_add_loop1`
   `pc + mldsa_poly_add_loop1_exit`
   `\i s. read RDI s = r /\ read RSI s = b /\ read RAX s = word(16 * i) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s =
                   y j) /\
          (!j. 4 * i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                   x j) /\
          (!j. j < 4 * i
               ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                   word_add (x j) (y j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    FULL_INIT_TAC THEN
    X86_STEPS_TAC MLDSA_NATIVE_POLY_ADD_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0] THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
    FULL_INIT_TAC THEN
    SUBGOAL_THEN `aligned 16 (word_add r (word (16 * i)):int64) /\
                  aligned 16 (word_add b (word (16 * i)):int64)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC ALIGNED_WORD_ADD THEN
      ASM_REWRITE_TAC[ALIGNED_WORD; DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
      [MATCH_MP CHUNK4_INPUT_SPLIT (ASSUME `i < 64`)]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[CHUNK4_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!k. k < 4
          ==> read(memory :> bytes32(word_add b (word(4 * (4 * i + k)))))
                s0 = y(4 * i + k)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[CHUNK4_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 2
      `read(memory :> bytes128(word_add r (word(16 * i)))) s0`) THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 2
      `read(memory :> bytes128(word_add b (word(16 * i)))) s0`) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
    VAL_INT64_TAC `16 * i` THEN INDEX_ADDR_TAC THEN
    MAP_EVERY (fun n ->
      X86_STEPS_TAC MLDSA_NATIVE_POLY_ADD_GCC12_O2_EXEC [n] THEN
      SIMD_SIMPLIFY_TAC[]) (1--3) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE (SIMD_SIMPLIFY_CONV []) o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th ->
        can (term_match [] `read (memory :> bytes128 a) s = x`) (concl th) &&
        free_in `r:int64` (concl th))) THEN
    X86_STEPS_TAC MLDSA_NATIVE_POLY_ADD_GCC12_O2_EXEC (4--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
    LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
        CONV_TAC WORD_RULE THEN NO_TAC) THEN
    TRY(REWRITE_TAC[CHUNK4_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC EXPAND_CASES_CONV THEN
        REWRITE_TAC[CHUNK4_ADDR; ADD_CLAUSES] THEN
        CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
        REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    FULL_EXIT_TAC MLDSA_NATIVE_POLY_ADD_GCC12_O2_EXEC 1]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
