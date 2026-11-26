(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing with 13 bits per coefficient: the proof.                          *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/polyt0_pack_spec.ml";;
needs "x86/proofs/utils/mldsa_native_pack.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/clang_tools.ml";;

(*** The frame is 56 bytes below the slot of the return address, and the two
     aligned stores are at its bottom and 16 bytes above it ***)

let ALIGN64_LEMMA = prove
 (`aligned 16 (word_add stackpointer (word 64):int64)
   ==> aligned 16 (stackpointer:int64) /\
       aligned 16 (word_add stackpointer (word 16):int64)`,
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. Each of the 32 iterations   *)
(* of the loop handles 8 coefficients and their 13 bytes, which it stores    *)
(* one byte at a time. The registers RBP, R14 and RBX are saved in the stack *)
(* frame, below the return address; the 32 bytes below them are cleared      *)
(* after the loop (the zeroized temporary array). After                      *)
(* REPEAT_GEN_AND_OFFSET_STACKPTR_TAC, stackpointer is the bottom of the     *)
(* frame, 56 bytes below the value of RSP on entry. The loop test is the end *)
(* of the body, as ENSURES_EVENTS_WHILE_UP2_TAC requires, and the events of  *)
(* an iteration depend on its index only.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(r:int64) (a:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil r a pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 32
            (\i. f_ev_loop r a pc stackpointer returnaddress i))
          (f_ev_prol r a pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> STRIP_ASSUME_TAC(MATCH_MP ALIGN64_LEMMA th)) THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mldsa_polyt0_pack_loop1`
   `pc + mldsa_polyt0_pack_loop1_exit`
   `\i s. read RAX s = word(13 * i) /\
          read RDI s = r /\
          read RSI s = word_add (word_add a (word(32 * i))) (word 28) /\
          read RSP s = word_add stackpointer (word 32) /\
          read (memory :> bytes64 (word_add stackpointer (word 56))) s =
          returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 48))) s =
          rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 40))) s =
          r14_init /\
          read (memory :> bytes64 (word_add stackpointer (word 32))) s =
          rbx_init /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   x j) /\
          (!j. j < 13 * i
               ==> read(memory :> bytes8(word_add r (word j))) s =
                   mld_polyt0_pack x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    FULL_INIT_TAC THEN
    X86_STEPS_TAC EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; WORD_ADD_0; ADD_CLAUSES] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    CHUNK_INPUT_TAC `x:num->int32` 8 THEN
    INPUT_ALT_ADDR_TAC `a:int64` THEN
    X86_STEPS_TAC EXEC (1--67) THEN
    VAL_IDX_TAC 13 32 THEN
    CLANG_CHUNK_FINAL_TAC mld_polyt0_pack `x:num->int32` 13;

    (*** The return ***)

    FULL_EXIT_TAC EXEC 17]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
