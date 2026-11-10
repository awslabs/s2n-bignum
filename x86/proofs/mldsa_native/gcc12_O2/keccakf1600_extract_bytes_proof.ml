(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Extraction of bytes from a Keccak state: the proof (see                   *)
(* keccakf1600_extract_bytes_spec.ml). The proof is that of the same code in *)
(* the x86 gcc12_O2 image of mlkem-native, with the return included.         *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/keccakf1600_extract_bytes_spec.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;

let EXTRACT_BYTES_ARGS_TAC =
  ARGS_32_TAC [`off:num`; `len:num`] THEN
  FIRST_ASSUM(fun th ->
    if concl th <> `~(len = 0)` then NO_TAC else
    RULE_ASSUM_TAC(fun th' ->
      if concl th' = concl th then th' else REWRITE_RULE[th] th'));;

(*** The new byte of the result, and the loop test ***)

let EXTRACT_BYTES_BYTE_TAC =
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
  REWRITE_TAC[WORD_ADD; READ_MEMORY_BYTES_SNOC] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_8; DIMINDEX_16;
              DIMINDEX_32; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8 /\ 4294967296 = 2 EXP 32 /\
                          18446744073709551616 = 2 EXP 64`;
              MOD_MOD_EXP_MIN] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MIN_CONV) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; GSYM DIV_DIV] THEN
  SPEC_TAC(`val(S:1600 word) DIV 2 EXP (8 * off)`,`x:num`) THEN
  REWRITE_TAC[MULT_CLAUSES; MOD_MULT_MOD] THEN ARITH_TAC;;

let EXTRACT_BYTES_TEST_TAC =
  SUBGOAL_THEN
   `~(val(word_sub (word len) (word_add (word i) (word 1)):int64) = 0) <=>
    i + 1 < len`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
    SUBGOAL_THEN `len < 2 EXP 64 /\ i + 1 < 2 EXP 64` MP_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[MOD_LT] THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. As in common/fips202.ml,    *)
(* the state is a 1600-bit word S, and the bytes extracted are bytes off to  *)
(* off + len - 1 of it, which as a number are (val S DIV 2 EXP (8 * off))    *)
(* MOD 2 EXP (8 * len). The loop test is the end of the body, as             *)
(* ENSURES_EVENTS_WHILE_UP2_TAC requires; the events depend on the offset    *)
(* and length only. The byte copied in iteration i is loaded from            *)
(* a + (off + 1 * i), as the address from the index register is normalized.  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (d:int64) (off:num) (len:num) (pc:num)
      (stackpointer:int64) (returnaddress:int64).
      if len = 0
      then f_ev_len0 a d off len pc stackpointer returnaddress
      else
        APPEND
          (f_ev_epil a d off len pc stackpointer returnaddress)
          (APPEND
            (ENUMERATEL len
              (\i. f_ev_loop a d off len pc stackpointer returnaddress i))
            (f_ev_prol a d off len pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `d:int64`; `off:num`; `len:num`; `S:1600 word`;
    `pc:num`; `stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              READ_MEMORY_WBYTES_VAL;
              fst MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_DIV_CONV) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The case len = 0, where nothing is done ***)

  ASM_CASES_TAC `len = 0` THEN ASM_REWRITE_TAC[] THENL
   [FULL_INIT_TAC THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN

  (*** The loop invariant, with the loop test at the end of the body ***)

  ENSURES_EVENTS_WHILE_UP2_TAC `len:num`
   `pc + mldsa_keccakf1600_extract_bytes_loop1`
   `pc + mldsa_keccakf1600_extract_bytes_loop1_exit`
   `\i s. read RAX s = word i /\ read RSI s = d /\ read RCX s = word len /\
          read RDI s = word_add a (word off) /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress /\
          read (memory :> bytes(a,200)) s = val(S:1600 word) /\
          read (memory :> bytes(d,i)) s =
          (val S DIV 2 EXP (8 * off)) MOD 2 EXP (8 * i)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Initialization ***)

    FULL_INIT_TAC THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--2) THEN
    EXTRACT_BYTES_ARGS_TAC THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (3--7) THEN
    ARGS_32_TAC [`off:num`; `len:num`] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, copying one byte, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    MP_TAC(SPECL [`a:int64`; `200`; `val(S:1600 word)`; `off + 1 * i`;
                  `s0:x86state`] READ_MEMORY_BYTES8_OF_NUM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC; DISCH_TAC] THEN
    VAL_INT64_TAC `i:num` THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    EXTRACT_BYTES_TEST_TAC THEN
    CONJ_TAC THENL [EXTRACT_BYTES_BYTE_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The return ***)

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    X86_STEPS_TAC MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_EXEC
     (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
