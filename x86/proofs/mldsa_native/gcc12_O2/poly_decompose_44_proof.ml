(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decomposition of the coefficients of a polynomial into high and low       *)
(* parts: the proof (see poly_decompose_44_spec.ml).                         *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/poly_decompose_44_spec.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_rounding.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The loop handles one        *)
(* coefficient per iteration, with the offset 4 * i in RCX; the stored high  *)
(* and low parts are equal to the spec by bit-blasting, with the coefficient *)
(* as a variable (and the high part as a variable for the low part, see      *)
(* SCALAR_LANE_TAC). The loop test is the end of the body, as                *)
(* ENSURES_EVENTS_WHILE_UP2_TAC requires, and the events of an iteration     *)
(* depend on its index only.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(a1:int64) (a0:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil a1 a0 pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 256
            (\i. f_ev_loop a1 a0 pc stackpointer returnaddress i))
          (f_ev_prol a1 a0 pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a1:int64`; `a0:int64`; `x:num->int32`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; PAIRWISE; ALL;
              mld_poly_decompose_hi_88; mld_poly_decompose_lo_88; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + mldsa44_poly_decompose_loop1`
   `pc + mldsa44_poly_decompose_loop1_exit`
   `\i s. read RDI s = a1 /\ read RSI s = a0 /\ read RCX s = word(4 * i) /\
          read R9 s = word 43 /\ read R8 s = word 4190208 /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add a0 (word(4 * j)))) s =
                   x j) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a1 (word(4 * j)))) s =
                   mld_decompose_hi_88 (x j)) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a0 (word(4 * j)))) s =
                   mld_decompose_lo_88 (x j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    FULL_INIT_TAC THEN
    X86_STEPS_TAC EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, with the addresses base + index as in the code ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `mld_decompose_hi_88` (concl th)) &&
        not(free_in `mld_decompose_lo_88` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    VAL_INT64_TAC `4 * i` THEN INDEX4_ADDR_TAC THEN
    X86_STEPS_TAC EXEC (1--24) THEN
    SCALAR_LANE_TAC `word_add (a1:int64) (word(1 * 4 * i))` `(x:num->int32) i`
      `mld_decompose_hi_88` [mld_decompose_hi_88; mld_ct_sel] THEN
    SCALAR_LANE_TAC `word_add (a0:int64) (word(1 * 4 * i))` `(x:num->int32) i`
      `mld_decompose_lo_88` [DECOMPOSE_LO_88_ALT; mld_ct_sel] THEN
    X86_STEPS_TAC EXEC (25--27) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
    FULL_FINAL_TAC [ONE_OUTPUT_SPLIT];

    (*** The return ***)

    FULL_EXIT_TAC EXEC 1]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
