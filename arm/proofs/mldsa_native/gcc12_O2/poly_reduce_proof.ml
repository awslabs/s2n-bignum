(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction of the coefficients of a polynomial: the proof (see             *)
(* poly_reduce_spec.ml).                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/poly_reduce_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

(*** The vector of -q = 0xff801fff in each lane, from the read-only data ***)

let MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_CONSTANTS =
  map (fun d -> MLDSA_NATIVE_IMAGE_CONST_RULE d 128)
   [layout "mldsa_poly_reduce_consts"];;

(*** The value computed in each lane: a + t * -q, t = (a + 2^22) >> 23 ***)

let REDUCE32_LANE = prove
 (`!x:int32. word_add x (word_mul (word_ishr (word_add x (word 4194304)) 23)
                                  (word 4286586879)) =
             mld_reduce32 x`,
  REWRITE_TAC[mld_reduce32; WORD_RULE
   `word_sub x (word_mul t c):N word =
    word_add x (word_mul t (word_neg c))`] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. Each of the 64 iterations   *)
(* of the loop reduces 4 coefficients, loaded and stored as one 128-bit      *)
(* word; the loop test is the end of the body, as                            *)
(* ENSURES_EVENTS_WHILE_UP2_TAC requires, and the events of an iteration     *)
(* depend on its index only.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a pc returnaddress)
        (APPEND
          (ENUMERATEL 64 (\i. f_ev_loop a pc returnaddress i))
          (f_ev_prol a pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `x:num->int32`; `pc:num`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; mld_poly_reduce;
              fst MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64` `pc + mldsa_poly_reduce_loop1`
   `pc + mldsa_poly_reduce_loop1_exit`
   `\i s. read X0 s = word_add a (word(16 * i)) /\
          read X1 s = word_add a (word 1024) /\
          read X30 s = returnaddress /\
          read Q2 s = word 0xff801fffff801fffff801fffff801fff /\
          read Q3 s = word 0x00400000004000000040000000400000 /\
          (!j. 4 * i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   x j) /\
          (!j. j < 4 * i
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   mld_reduce32 (x j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, with the vector of -q from the image ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MAP_EVERY (fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP th))
      MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_CONSTANTS THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_EXEC (2--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
      [MATCH_MP CHUNK4_INPUT_SPLIT (ASSUME `i < 64`)]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[CHUNK4_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 2
      `read(memory :> bytes128(word_add a (word(16 * i)))) s0`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
    MAP_EVERY (fun n ->
      ARM_STEPS_TAC MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_EXEC [n] THEN
      SIMD_SIMPLIFY_TAC[]) (1--5) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE (SIMD_SIMPLIFY_CONV []) o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th ->
        can (term_match [] `read (memory :> bytes128 a) s = x`) (concl th) &&
        free_in `a:int64` (concl th))) THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_EXEC (6--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CHUNK4_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      REWRITE_TAC[CHUNK4_ADDR; ADD_CLAUSES] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[REDUCE32_LANE];
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The return ***)

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
       CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
       check (fun th -> is_forall(concl th) &&
                        free_in `mld_reduce32` (concl th)));
      DISCHARGE_SAFETY_PROPERTY_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
