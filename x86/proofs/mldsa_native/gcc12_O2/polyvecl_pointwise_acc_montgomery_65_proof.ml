(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise products of two vectors of 5 polynomials, accumulated and       *)
(* reduced: the proof (see polyvecl_pointwise_acc_montgomery_65_spec.ml).    *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_pointwise_acc_montgomery_65_spec.ml";;
needs "x86/proofs/utils/mldsa_native_pwacc.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. Each of the 256 iterations  *)
(* of the outer loop handles coefficient i of the 5 polynomials, with the    *)
(* inner loop over the polynomials unrolled; the loop test is the end of the *)
(* body, as ENSURES_EVENTS_WHILE_UP2_TAC requires, and the events of an      *)
(* iteration depend on its index only.                                       *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(w:int64) (u:int64) (v:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil w u v pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 256
            (\i. f_ev_loop w u v pc stackpointer returnaddress i))
          (f_ev_prol w u v pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `w:int64`; `u:int64`; `v:int64`;
    `x:num->int32`; `y:num->int32`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL;
              mld_polyvec_pointwise_acc_montgomery; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256`
   `pc + mldsa65_polyvecl_pointwise_acc_montgomery_loop1`
   `pc + mldsa65_polyvecl_pointwise_acc_montgomery_loop1_exit`
   `\i s. read RDX s = word(4 * i) /\
          read RDI s = w /\ read R8 s = u /\ read R9 s = v /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = returnaddress /\
          (!j. j < 1280
               ==> read(memory :> bytes32(word_add u (word(4 * j)))) s =
                   x j) /\
          (!j. j < 1280
               ==> read(memory :> bytes32(word_add v (word(4 * j)))) s =
                   y j) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add w (word(4 * j)))) s =
                   mld_montgomery_reduce (mld_polyvec_dot 5 x y j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    FULL_INIT_TAC THEN X86_STEPS_TAC EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The outer loop body: the setup, the 5 iterations of the inner ***)
    (*** loop, the reduction, the store and the loop test              ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN PWACC_INDEX_VALS_TAC 5 THEN
    PWACC_LOADS_TAC
     (fun p -> if p = 0 then `1 * 4 * i` else
                         mk_comb(`( * ) 1`,mk_binop `(+):num->num->num`
                          `4 * i` (mk_small_numeral(1024 * p))))
     5 THEN
    PWACC_BODY_TAC EXEC 4 5 THEN PWACC_FINAL_TAC;

    (*** The return ***)

    FULL_EXIT_TAC EXEC 1]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
   MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
   MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
