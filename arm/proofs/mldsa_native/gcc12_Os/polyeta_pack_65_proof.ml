(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 4 bits per coefficient, of 4 - a: the proof. *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/polyeta_pack_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/zeroize_3_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. Each of the 128 iterations  *)
(* of the loop handles 2 coefficients and 1 byte. After the loop the code    *)
(* stores the last two values to the temporary array on the stack, zeroes it *)
(* with mld_zeroize_3 and checks the stack guard; these stores do not touch  *)
(* the output. The loop test is the end of the body, as                      *)
(* ENSURES_EVENTS_WHILE_UP2_TAC requires, and the events of an iteration     *)
(* depend on its index only.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYETA_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLYETA_PACK_65_GCC12_OS_EXEC in
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_ZEROIZE_3_GCC12_OS_IMAGE_SUBROUTINE_FULL th)
     "H_ZERO") THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(r:int64) (a:int64) (guard:int64) (mf:int64) (pc:num)
      (stackpointer:int64) (returnaddress:int64).
      APPEND
        (f_ev_epil r a guard mf pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 128
            (\i. f_ev_loop r a guard mf pc stackpointer returnaddress i))
          (f_ev_prol r a guard mf pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS; PAIRWISE; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + mldsa65_polyeta_pack_loop1`
   `pc + mldsa65_polyeta_pack_loop1_exit`
   `\i s. read X0 s = r /\
          read X1 s = word_add a (word(8 * i)) /\
          read X4 s = word i /\
          read X5 s = word 4 /\
          read SP s = word_add stackpointer (word 16) /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
          returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 40))) s =
          canary /\
          read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s =
          guard /\
          read (memory :> bytes64 guard) s = canary /\
          read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
          read (memory :> bytes(ea,el)) s = ev /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   x j) /\
          (!j. j < i
               ==> read(memory :> bytes8(word_add r (word j))) s =
                   mld_polyeta_pack_4 x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, saving the return address and the stack guard ***)

    FULL_INIT_TAC THEN
    ARM_STEPS_TAC EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC EXEC (2--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; ADD_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    CHUNK_INPUT_TAC `x:num->int32` 2 THEN
    ARM_STEPS_TAC EXEC (1--12) THEN
    CHUNK_FULL_FINAL_TAC mld_polyeta_pack_4 `x:num->int32`;

    (*** The stores to the stack, the call of mld_zeroize_3, the check ***)
    (*** of the stack guard and the return                            ***)

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    ARM_STEPS_TAC EXEC (1--5) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc EXEC "H_ZERO"
     [`read X0 s`; `8`; `pc:num`; `read SP s`; `read X30 s`]
     [`pc:num`; `r:int64`; `a:int64`; `guard:int64`; `mf:int64`;
      `stackpointer:int64`; `returnaddress:int64`] 6 THEN
    ARM_STEPS_TAC EXEC (7--7) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC EXEC (8--15) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM(MATCH_ACCEPT_TAC o
          CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYETA_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
       MLDSA_NATIVE_POLYETA_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_POLYETA_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYETA_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
       MLDSA_NATIVE_POLYETA_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_FULL) th)));;
