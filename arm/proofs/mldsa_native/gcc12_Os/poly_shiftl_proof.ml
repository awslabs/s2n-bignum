(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication of the coefficients by 2^13: the proof (see                *)
(* poly_shiftl_spec.ml).                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/poly_shiftl_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* The value stored for coefficient a is a << 13, taken from the assumption  *)
(* that the simulation produces, so that it has the zero extensions of the   *)
(* model exactly. Its equality with a * 2^13 is proved by bit-blasting, with *)
(* the coefficient as a variable.                                            *)
(* ------------------------------------------------------------------------- *)

let SHIFTL_LANE_TAC =
  FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if can (term_match [] `read (memory :> bytes32 a) s`) l &&
       free_in `x:num->int32` r then
      let v = `(x:num->int32) i` and y = genvar `:int32` in
      let lemma = prove
       (mk_forall(y,mk_eq(subst[y,v] r,`word_mul (y:int32) (word 8192)`
                          |> subst[y,`y:int32`])),
        GEN_TAC THEN BITBLAST_TAC) in
      ASSUME_TAC(REWRITE_RULE[lemma] th)
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The loop handles one        *)
(* coefficient per iteration; the loop test is the end of the body, as       *)
(* ENSURES_EVENTS_WHILE_UP2_TAC requires, and the events of an iteration     *)
(* depend on its index only. The code addresses the coefficient as           *)
(* [x0, x1, lsl #2], which the model reads as 4 * val(word i); the body      *)
(* first adds val(word i) = i so that the addresses match the invariant.     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_SHIFTL_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_SHIFTL_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a pc returnaddress)
        (APPEND
          (ENUMERATEL 256 (\i. f_ev_loop a pc returnaddress i))
          (f_ev_prol a pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `x:num->int32`; `pc:num`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; mld_poly_shiftl;
              fst MLDSA_NATIVE_POLY_SHIFTL_GCC12_OS_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + mldsa_poly_shiftl_loop1`
   `pc + mldsa_poly_shiftl_loop1_exit`
   `\i s. read X0 s = a /\
          read X1 s = word i /\
          read X30 s = returnaddress /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   x j) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   word_mul (x j) (word 8192))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_SHIFTL_GCC12_OS_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `word_mul:int32->int32->int32` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `val(word i:int64) = i` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_SHIFTL_GCC12_OS_EXEC (1--3) THEN
    SHIFTL_LANE_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_SHIFTL_GCC12_OS_EXEC (4--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
    LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The return ***)

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_SHIFTL_GCC12_OS_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_SHIFTL_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_SHIFTL_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC MLDSA_NATIVE_POLY_SHIFTL_GCC12_OS_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_SHIFTL_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_SHIFTL_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC MLDSA_NATIVE_POLY_SHIFTL_GCC12_OS_IMAGE_SUBROUTINE_FULL);;
