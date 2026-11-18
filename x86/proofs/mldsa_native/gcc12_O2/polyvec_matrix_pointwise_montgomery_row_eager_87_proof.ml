(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Product of a row of the matrix with a vector, in the NTT domain: the      *)
(* proof (see polyvec_matrix_pointwise_montgomery_row_eager_87_spec.ml).     *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/polyvec_matrix_pointwise_montgomery_row_eager_87_spec.ml";;
needs "x86/proofs/utils/mldsa_native_wrap.ml";;

let ROW_EAGER_87_EXEC =
  MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the address of row *)
(* i is put in the form of the vector functions before the tail call.        *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = ROW_EAGER_87_EXEC in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_C0" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FULL_INIT_TAC THEN
  X86_STEPS_TAC EXEC (1--6) THEN
  ROW_ADDR_TAC `read RSI s6 = word_add mat (word(7168 * i))` THEN
  VEC_SLICE_TAC
   `!j. j < 1792
        ==> read(memory :> bytes32(word_add mat (word(7168 * i + 4 * j))))
              s6 = A(1792 * i + j)` THEN
  FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc EXEC "H_C0"
   [`read RDI s`; `read RSI s`; `read RDX s`;
    `\j. (A:num->int32)(1792 * i + j)`; `y:num->int32`; `pc:num`;
    `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
   [`pc:num`; `t:int64`; `mat:int64`; `v:int64`; `i:num`;
    `stackpointer:int64`; `returnaddress:int64`] 7 THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
