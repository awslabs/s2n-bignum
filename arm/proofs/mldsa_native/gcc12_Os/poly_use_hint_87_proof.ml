(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Correction of the high parts of the coefficients of a polynomial by       *)
(* hints: the proof (see poly_use_hint_87_spec.ml).                          *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/poly_use_hint_87_spec.ml";;
needs "arm/proofs/utils/mldsa_native_polyvec.ml";;
needs "arm/proofs/utils/mldsa_native_rounding.ml";;

(* ------------------------------------------------------------------------- *)
(* The end of one of the paths through an iteration: the stored value equal  *)
(* to the spec under the case assumption, and the branch on the offset back  *)
(* to the loop or out of it.                                                 *)
(* ------------------------------------------------------------------------- *)

let USE_HINT_87_PATH_END_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
  SCALAR_LANE2_TAC `word_add (a:int64) (word(4 * i))` `(x:num->int32) i`
    `(y:num->int32) i` `mld_use_hint_32` [mld_use_hint_32] THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
  LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  PATH_DISCHARGE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The loop handles one        *)
(* coefficient per iteration, by a call of mld_decompose87 with the outputs  *)
(* on the stack, at sp + 16 (low part) and sp + 20 (high part); the loop     *)
(* test is the end of the body, as ENSURES_EVENTS_WHILE_UP2_TAC requires.    *)
(* The iteration branches on the hint (CBZ), so its events are one of two    *)
(* lists, chosen by whether y i is zero; the template of the events has a    *)
(* meta-variable for each, and each path of the body instantiates its own    *)
(* after the choice is made with the case assumption (PATH_DISCHARGE_TAC).   *)
(* The stack protector: the prologue copies the value at the guard to the    *)
(* frame, and the epilogue compares it with the value at the guard, which    *)
(* the loop does not change.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_OS_EXEC in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_DECOMPOSE_87_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_C0" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (h:int64) (y:num->int32) (guard:int64) (pc:num)
      (stackpointer:int64) (returnaddress:int64).
      APPEND
        (f_ev_epil a h y guard pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 256
            (\i. if y i = word 0
                 then f_ev_zero a h y guard pc stackpointer returnaddress i
                 else f_ev_hint a h y guard pc stackpointer returnaddress i))
          (f_ev_prol a h y guard pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              mld_poly_use_hint_32; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + mldsa87_poly_use_hint_loop1`
   `pc + mldsa87_poly_use_hint_loop1_exit`
   `\i s. read X5 s = a /\ read X6 s = h /\ read X4 s = word(4 * i) /\
          read X0 s = word_add stackpointer (word 16) /\
          read X7 s = word_add stackpointer (word 20) /\
          read SP s = stackpointer /\
          read (memory :> bytes64 (word_add (word pc)
                                            (word got_stack_chk_guard)))
               s = guard /\
          read (memory :> bytes64 guard) s = canary /\
          read (memory :> bytes64 stackpointer) s = returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
            canary /\
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

    (*** Initialization: the prologue and the copy of the guard ***)

    FULL_INIT_TAC THEN
    ARM_STEPS_TAC EXEC (1--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC EXEC (4--11) THEN
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
    ARM_STEPS_TAC EXEC (1--4) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc EXEC "H_C0"
     [`read X0 s`; `read X1 s`; `read X2 s`; `pc:num`; `read X30 s`]
     [`pc:num`; `a:int64`; `h:int64`; `y:num->int32`; `guard:int64`;
      `stackpointer:int64`; `returnaddress:int64`; `i:num`] 5 THEN
    ARM_STEPS_TAC EXEC (6--7) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32; VAL_EQ_0]) THEN
    BRANCH_CASES_TAC THENL
     [ARM_STEPS_TAC EXEC (8--11) THEN USE_HINT_87_PATH_END_TAC;
      ARM_STEPS_TAC EXEC (8--18) THEN USE_HINT_87_PATH_END_TAC];

    (*** The check of the stack protector, and the return ***)

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    ARM_STEPS_TAC EXEC (1--1) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC EXEC (2--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM(MATCH_ACCEPT_TAC o
          CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_OS_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_USE_HINT_87_GCC12_OS_IMAGE_SUBROUTINE_FULL);;
