(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Splitting of the coefficients of a polynomial at 2^13: the proof (see     *)
(* poly_power2round_spec.ml).                                                *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/poly_power2round_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* The values stored for coefficient a are, with y = a + 2^12 - 1, the high  *)
(* part y >> 13 at a1 and the low part a - (y & ~(2^13 - 1)) at a0. Their    *)
(* equality with mld_power2round_hi a and mld_power2round_lo a is proved by  *)
(* bit-blasting, with the coefficient as a variable; the terms are taken     *)
(* from the assumptions that the simulation produces, so that they have the  *)
(* zero extensions of the model exactly. The address in the assumption       *)
(* tells the two apart: the high part is stored through `hi`, the low part   *)
(* through `lo`.                                                             *)
(* ------------------------------------------------------------------------- *)

let POWER2ROUND_LANE_TAC hi lo =
  let one th =
    let l,r = dest_eq(concl th) in
    if can (term_match [] `read (memory :> bytes32 a) s`) l &&
       free_in `x:num->int32` r &&
       not(free_in `mld_power2round_hi` r) &&
       not(free_in `mld_power2round_lo` r) then
      let f = if free_in hi l then `mld_power2round_hi`
              else if free_in lo l then `mld_power2round_lo`
              else failwith "POWER2ROUND_LANE_TAC" in
      let v = `(x:num->int32) i` and y = genvar `:int32` in
      let lemma = prove
       (mk_forall(y,mk_eq(subst[y,v] r,mk_comb(f,y))),
        GEN_TAC THEN
        REWRITE_TAC[mld_power2round_hi; mld_power2round_lo] THEN
        BITBLAST_TAC) in
      ASSUME_TAC(REWRITE_RULE[lemma] th)
    else failwith "POWER2ROUND_LANE_TAC" in
  W(fun (asl,w) ->
    let ths = filter (fun th -> can one th) (map snd asl) in
    MAP_EVERY (fun th -> one th) ths);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. Each of the 256             *)
(* iterations of the loop splits one coefficient; the loop test is the end   *)
(* of the body, as ENSURES_EVENTS_WHILE_UP2_TAC requires, and the events of  *)
(* an iteration depend on its index only.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(a1:int64) (a0:int64) (a:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a1 a0 a pc returnaddress)
        (APPEND
          (ENUMERATEL 256 (\i. f_ev_loop a1 a0 a pc returnaddress i))
          (f_ev_prol a1 a0 a pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a1:int64`; `a0:int64`; `a:int64`;
    `x:num->int32`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; PAIRWISE; ALL;
              mld_poly_power2round_hi; mld_poly_power2round_lo;
              fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + mldsa_poly_power2round_loop1`
   `pc + mldsa_poly_power2round_loop1_exit`
   `\i s. read X0 s = a1 /\ read X1 s = a0 /\ read X2 s = a /\
          read X3 s = word(4 * i) /\ read X30 s = returnaddress /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   x j) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a1 (word(4 * j)))) s =
                   mld_power2round_hi (x j)) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a0 (word(4 * j)))) s =
                   mld_power2round_lo (x j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    FULL_INIT_TAC THEN
    ARM_STEPS_TAC EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    CONV_TAC WORD_REDUCE_CONV THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `x:num->int32` (concl th) &&
      free_in `a:int64` (concl th))) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN
    ARM_STEPS_TAC EXEC (1--7) THEN
    POWER2ROUND_LANE_TAC `a1:int64` `a0:int64` THEN
    ARM_STEPS_TAC EXEC (8--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
    LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The return ***)

    FULL_EXIT_TAC EXEC 1]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_FULL);;

(* ------------------------------------------------------------------------- *)
(* The same in place: the invariant states the input coefficients from i on  *)
(* and the results before i at a0. The iteration loads its coefficient       *)
(* before it stores the results.                                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_FULL_INPLACE =
  prove
 (MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_FULL_INPLACE_STMT,
  let EXEC = MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(a1:int64) (a0:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a1 a0 pc returnaddress)
        (APPEND
          (ENUMERATEL 256 (\i. f_ev_loop a1 a0 pc returnaddress i))
          (f_ev_prol a1 a0 pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a1:int64`; `a0:int64`;
    `x:num->int32`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; PAIRWISE; ALL;
              mld_poly_power2round_hi; mld_poly_power2round_lo;
              fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + mldsa_poly_power2round_loop1`
   `pc + mldsa_poly_power2round_loop1_exit`
   `\i s. read X0 s = a1 /\ read X1 s = a0 /\ read X2 s = a0 /\
          read X3 s = word(4 * i) /\ read X30 s = returnaddress /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add a0 (word(4 * j)))) s =
                   x j) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a1 (word(4 * j)))) s =
                   mld_power2round_hi (x j)) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a0 (word(4 * j)))) s =
                   mld_power2round_lo (x j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    FULL_INIT_TAC THEN
    ARM_STEPS_TAC EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    CONV_TAC WORD_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `mld_power2round_hi` (concl th)) &&
        not(free_in `mld_power2round_lo` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ARM_STEPS_TAC EXEC (1--7) THEN
    POWER2ROUND_LANE_TAC `a1:int64` `a0:int64` THEN
    ARM_STEPS_TAC EXEC (8--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
    LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The return ***)

    FULL_EXIT_TAC EXEC 1]);;
