(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Correction of the high parts of the coefficients of a polynomial by       *)
(* hints: the proof (see poly_use_hint_65_spec.ml).                          *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/poly_use_hint_65_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "arm/proofs/utils/mldsa_native_rounding.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The loop handles one        *)
(* coefficient per iteration, with the loop test at the end of the body, as  *)
(* ENSURES_EVENTS_WHILE_UP2_TAC requires. The iteration branches on the hint *)
(* (CBZ), so its events are one of two lists, chosen by whether y i is zero; *)
(* the template of the events has a meta-variable for each, and each path of *)
(* the body instantiates its own after the choice is made with the case      *)
(* assumption (PATH_DISCHARGE_TAC).                                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (h:int64) (y:num->int32) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil a h y pc returnaddress)
        (APPEND
          (ENUMERATEL 256
            (\i. if y i = word 0 then f_ev_zero a h y pc returnaddress i
                 else f_ev_hint a h y pc returnaddress i))
          (f_ev_prol a h y pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `h:int64`; `x:num->int32`;
    `y:num->int32`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; PAIRWISE; ALL; mld_poly_use_hint_32;
              fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + mldsa65_poly_use_hint_loop1`
   `pc + mldsa65_poly_use_hint_loop1_exit`
   `\i s. read X0 s = a /\ read X1 s = h /\ read X6 s = word(4 * i) /\
          read X10 s = word 4190208 /\ read X9 s = word 4286586879 /\
          read X30 s = returnaddress /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   x j) /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add h (word(4 * j)))) s =
                   y j) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   mld_use_hint_32 (x j) (y j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    FULL_INIT_TAC THEN ARM_STEPS_TAC EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, with the loop test, in the two paths of the hint ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `mld_use_hint_32` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o C MP (ASSUME `i < 256`) o SPEC `i:num` o
      check (fun th -> is_forall(concl th) &&
        free_in `y:num->int32` (concl th) &&
        not(free_in `mld_use_hint_32` (concl th)))) THEN
    DISCH_TAC THEN
    ARM_STEPS_TAC EXEC (1--6) THEN
    REG_LANE_TAC `X2` `(x:num->int32) i` `mld_decompose_hi_32`
      [DECOMPOSE_HI_32_ALT] THEN
    ARM_STEPS_TAC EXEC (7--18) THEN
    REG_LANE_TAC `X3` `(x:num->int32) i` `mld_decompose_lo_32`
      [DECOMPOSE_LO_32_ALT; mld_ct_sel] THEN
    ARM_STEPS_TAC EXEC (19--22) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0]) THEN
    BRANCH_CASES_TAC THENL
     [ARM_STEPS_TAC EXEC (23--26); ARM_STEPS_TAC EXEC (23--27)] THEN
    SCALAR_LANE2_TAC `word_add (a:int64) (word(4 * i))` `(x:num->int32) i`
      `(y:num->int32) i` `mld_use_hint_32` [mld_use_hint_32] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
    LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    PATH_DISCHARGE_TAC;

    (*** The return ***)

    FULL_EXIT_TAC EXEC 1]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
