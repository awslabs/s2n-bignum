(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 20 bits per coefficient, of 2^19 - a: the    *)
(* proof.                                                                    *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/polyz_pack_65_spec.ml";;
needs "x86/proofs/utils/mldsa_native_pack.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. Each of the 128 iterations  *)
(* of the loop handles 2 coefficients and 5 bytes, 4 of them stored as one   *)
(* 32-bit word, whose fact is split into facts about the bytes. The register *)
(* RBX is saved in the stack frame, below the return address; after          *)
(* REPEAT_GEN_AND_OFFSET_STACKPTR_TAC, stackpointer is the bottom of the     *)
(* frame, 8 bytes below the value of RSP on entry. The loop test is the end  *)
(* of the body, as ENSURES_EVENTS_WHILE_UP2_TAC requires, and the events of  *)
(* an iteration depend on its index only.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(r:int64) (a:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil r a pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 128
            (\i. f_ev_loop r a pc stackpointer returnaddress i))
          (f_ev_prol r a pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `128` `pc + mldsa65_polyz_pack_loop1`
   `pc + mldsa65_polyz_pack_loop1_exit`
   `\i s. read RSI s = word_add r (word(5 * i)) /\
          read RDI s = word_add a (word(8 * i)) /\
          read R9 s = word_add r (word 640) /\
          read R8 s = word 524288 /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          returnaddress /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   x j) /\
          (!j. j < 5 * i
               ==> read(memory :> bytes8(word_add r (word j))) s =
                   mld_polyz_pack_19 x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    FULL_INIT_TAC THEN
    X86_STEPS_TAC EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    CHUNK_INPUT_TAC `x:num->int32` 2 THEN
    X86_STEPS_TAC EXEC (1--27) THEN
    ADDR_NORMALIZE_TAC THEN WIDE_STORE_SPLIT_TAC `r:int64` 8 THEN
    CHUNK_FULL_FINAL_TAC mld_polyz_pack_19 `x:num->int32`;

    (*** The return ***)

    FULL_EXIT_TAC EXEC 2]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYZ_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
