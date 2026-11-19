(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decomposition of the coefficients of a polynomial into high and low       *)
(* parts: the proof (see poly_decompose_44_spec.ml).                         *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/poly_decompose_44_spec.ml";;
needs "arm/proofs/utils/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The loop handles one        *)
(* coefficient per iteration, by a call of mld_decompose44 with the          *)
(* addresses of the coefficient in a0 and of its high part in a1, with the   *)
(* offset 4 * i in X6 (after the increment, in the iteration). The loop test *)
(* is the end of the body, as ENSURES_EVENTS_WHILE_UP2_TAC requires, and the *)
(* events of an iteration depend on its index only. The frame holds the      *)
(* return address, which the loop keeps.                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_OS_EXEC in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_DECOMPOSE_44_GCC12_OS_IMAGE_SUBROUTINE_FULL "H_C0" THEN
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
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              C_RETURN; ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              mld_poly_decompose_hi_88; mld_poly_decompose_lo_88;
              fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256` `pc + mldsa44_poly_decompose_loop1`
   `pc + mldsa44_poly_decompose_loop1_exit`
   `\i s. read X8 s = a1 /\ read X7 s = a0 /\ read X6 s = word(4 * i) /\
          read SP s = stackpointer /\
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

    VEC_FULL_INIT_TAC EXEC 4 [];

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `mld_decompose_hi_88` (concl th)) &&
        not(free_in `mld_decompose_lo_88` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ARM_STEPS_TAC EXEC (1--5) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_ZX_ZX_32_64_32]) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc EXEC "H_C0"
     [`read X0 s`; `read X1 s`; `read X2 s`; `pc:num`; `read X30 s`]
     [`pc:num`; `a1:int64`; `a0:int64`; `stackpointer:int64`;
      `returnaddress:int64`; `i:num`] 6 THEN
    ARM_STEPS_TAC EXEC (7--8) THEN
    FULL_FINAL_TAC [ONE_OUTPUT_SPLIT; WORD_ZX_ZX_32_64_32];

    (*** The return ***)

    FULL_EXIT_TAC EXEC 2]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_OS_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_OS_IMAGE_SUBROUTINE_FULL);;
