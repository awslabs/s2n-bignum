(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lazy expansion of the matrix: the proof (see                          *)
(* polyvec_matrix_expand_lazy_87_spec.ml).                                   *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_expand_lazy_87_spec.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "x86/proofs/utils/mldsa_native_sampling.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together. The seed is read   *)
(* as two 128-bit words, loaded into the low halves of YMM0 and YMM1, whose  *)
(* values at the start are named so that the facts for them are kept.        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_87_GCC12_O2_REDUCED_RAM_EXEC in
  META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `mat:int64`; `rho:int64`; `r:num`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `read (memory :> bytes(rho,32)) s = r`) (concl th)
    then MP_TAC(MATCH_MP (SPEC `2` MLD_READ_BYTES_CHUNKS)
                 (REWRITE_RULE[ARITH_RULE `32 = 16 * 2`] th)) THEN
         MP_TAC(ISPECL [`rho:int64`; `32`; `read memory (s0:x86state)`]
                       READ_BYTES_BOUND) THEN
         REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; ASSUME(concl th)]
    else NO_TAC) THEN
  DISCH_TAC THEN
  CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  REWRITE_TAC[EXP; DIV_1; WORD_ADD_0] THEN STRIP_TAC THEN
  SAMPLING_GHOST_REGS_TAC [`YMM0`; `YMM1`] "s0" THEN
  X86_STEPS_TAC EXEC (1--5) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SAMPLING_SUBWORD_JOIN_128]) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `32 = 16 * 2`] THEN
    MATCH_MP_TAC MLD_BYTES_OF_CHUNKS THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o check (fun th ->
        can (term_match [] `r < 2 EXP n`) (concl th))) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
      CONV_TAC EXPAND_CASES_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[EXP; DIV_1; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[]];
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL);;
