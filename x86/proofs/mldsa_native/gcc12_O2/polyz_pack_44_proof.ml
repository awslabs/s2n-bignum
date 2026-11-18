(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 18 bits per coefficient, of 2^17 - a: the    *)
(* proof.                                                                    *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/polyz_pack_44_spec.ml";;
needs "x86/proofs/utils/mldsa_native_pack.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. Each of the 64 iterations   *)
(* of the loop handles 4 coefficients and 9 bytes, 8 of them stored as one   *)
(* 64-bit word, whose fact is split into facts about the bytes. The          *)
(* registers R13, R12, RBP and RBX are saved in the stack frame, below the   *)
(* return address; after REPEAT_GEN_AND_OFFSET_STACKPTR_TAC, stackpointer is *)
(* the bottom of the frame, 32 bytes below the value of RSP on entry. The    *)
(* loop test is the end of the body, as ENSURES_EVENTS_WHILE_UP2_TAC         *)
(* requires, and the events of an iteration depend on its index only.        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(r:int64) (a:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil r a pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 64
            (\i. f_ev_loop r a pc stackpointer returnaddress i))
          (f_ev_prol r a pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64` `pc + mldsa44_polyz_pack_loop1`
   `pc + mldsa44_polyz_pack_loop1_exit`
   `\i s. read RSI s = word_add r (word(9 * i)) /\
          read RDX s = word_add a (word(16 * i)) /\
          read R8 s = word_add a (word 1024) /\
          read RDI s = word 131072 /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 (word_add stackpointer (word 32))) s =
          returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 24))) s =
          r13_init /\
          read (memory :> bytes64 (word_add stackpointer (word 16))) s =
          r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          rbp_init /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   x j) /\
          (!j. j < 9 * i
               ==> read(memory :> bytes8(word_add r (word j))) s =
                   mld_polyz_pack_17 x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    FULL_INIT_TAC THEN
    X86_STEPS_TAC EXEC (1--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    CHUNK_INPUT_TAC `x:num->int32` 4 THEN
    X86_STEPS_TAC EXEC (1--57) THEN
    ADDR_NORMALIZE_TAC THEN WIDE_STORE_SPLIT_TAC `r:int64` 8 THEN
    CHUNK_FULL_FINAL_TAC mld_polyz_pack_17 `x:num->int32`;

    (*** The return ***)

    FULL_EXIT_TAC EXEC 5]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
