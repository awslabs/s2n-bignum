(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Product of the matrix with a vector, out of the NTT domain: the proof     *)
(* (see polyvec_matrix_pointwise_montgomery_yvec_eager_65_spec.ml).          *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/polyvec_matrix_pointwise_montgomery_yvec_eager_65_spec.ml";;
needs "x86/proofs/utils/mldsa_native_wrap.ml";;

let YVEC_EAGER_65_EXEC =
  MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_O2_EXEC;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together. Before the loop,   *)
(* the bytes of y are given by a ghost, so that the REP MOVSQ gives those of *)
(* the scratch vector (MOVSQ_STEP_TAC), and then its coefficients            *)
(* (VEC_BYTES_EQ_BYTES32); the loop counts the rows in RBX, and the inverse  *)
(* transform is a tail call.                                                 *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = YVEC_EAGER_65_EXEC in
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECL_NTT_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_NTT" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_ROW" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_POLYVECK_INVNTT_TOMONT_65_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_INV" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(w:int64) (mat:int64) (y:int64) (scratch:int64) (pc:num)
      (stackpointer:int64) (returnaddress:int64).
      APPEND
        (f_ev_epil w mat y scratch pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 6
            (\i. f_ev_loop w mat y scratch pc stackpointer returnaddress i))
          (f_ev_prol w mat y scratch pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `6`
   `pc + mldsa65_polyvec_matrix_pointwise_montgomery_yvec_eager_loop1`
   `pc + mldsa65_polyvec_matrix_pointwise_montgomery_yvec_eager_loop1_exit`
   `\i s. read RBX s = word i /\
          read RBP s = word_add w (word(1024 * i)) /\
          read R12 s = scratch /\ read R13 s = mat /\ read R14 s = w /\
          read RSP s = word_add stackpointer (word 96) /\
          read (memory :> bytes64 (word_add stackpointer (word 96))) s =
            rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 104))) s =
            rbp_init /\
          read (memory :> bytes64 (word_add stackpointer (word 112))) s =
            r12_init /\
          read (memory :> bytes64 (word_add stackpointer (word 120))) s =
            r13_init /\
          read (memory :> bytes64 (word_add stackpointer (word 128))) s =
            r14_init /\
          read (memory :> bytes64 (word_add stackpointer (word 136))) s =
            returnaddress /\
          (!j. j < 7680
               ==> read(memory :> bytes32(word_add mat (word(4 * j)))) s =
                   A j) /\
          (!j. j < 1280
               ==> read(memory :> bytes32(word_add scratch (word(4 * j)))) s =
                   mld_polyvec_map mld_poly_ntt z j) /\
          (!j. j < 256 * i
               ==> read(memory :> bytes32(word_add w (word(4 * j)))) s =
                   mld_polyvec_matrix_pointwise_montgomery 5 A
                    (mld_polyvec_map mld_poly_ntt z) j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** The copy of y to the scratch vector and its transform ***)

    GHOST_INTRO_TAC `yb:num` `read (memory :> bytes(y,5120))` THEN
    FULL_INIT_TAC THEN X86_STEPS_TAC EXEC (1--13) THEN
    MOVSQ_STEP_TAC EXEC 14 640 THEN
    MP_TAC(SPECL [`scratch:int64`; `y:int64`; `1280`; `s14:x86state`;
                  `s14:x86state`] VEC_BYTES_EQ_BYTES32) THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV NUM_MULT_CONV)) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `!j. j < 1280
          ==> read (memory :> bytes32 (word_add scratch (word (4 * j)))) s14 =
              z j`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    X86_STEPS_TAC EXEC (15--16) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc EXEC "H_NTT"
     [`read RDI s`; `z:num->int32`; `pc:num`; `read RSP s`;
      `read (memory :> bytes64 (read RSP s)) s`]
     [`pc:num`; `w:int64`; `mat:int64`; `y:int64`; `scratch:int64`;
      `stackpointer:int64`; `returnaddress:int64`] 17 THEN
    X86_STEPS_TAC EXEC (18--18) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, with the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN X86_STEPS_TAC EXEC (1--5) THEN
    SUBGOAL_THEN `word_zx(word_zx(word i:int64):int32):int64 = word i`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [MATCH_MP_TAC WORD_ZX_ZX_SMALL THEN CONV_TAC NUM_REDUCE_CONV THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc EXEC "H_ROW"
     [`read RDI s`; `read RSI s`; `read RDX s`; `A:num->int32`;
      `mld_polyvec_map mld_poly_ntt (z:num->int32)`; `i:num`; `pc:num`;
      `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
     [`pc:num`; `w:int64`; `mat:int64`; `y:int64`; `scratch:int64`;
      `stackpointer:int64`; `returnaddress:int64`; `i:num`] 6 THEN
    X86_STEPS_TAC EXEC (7--7) THEN
    SUBGOAL_THEN
     `word_zx(word_add (word_zx(word i:int64):int32) (word 1)):int64 =
      word(i + 1)`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [MATCH_MP_TAC WORD_ZX_ADD_SMALL THEN CONV_TAC NUM_REDUCE_CONV THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    X86_STEPS_TAC EXEC (8--10) THEN
    VEC_FULL_FINAL_TAC [MLD_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_COEFF];

    (*** The tail call of the inverse transform ***)

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    X86_STEPS_TAC EXEC (1--7) THEN
    RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_O2_mc EXEC "H_INV"
     [`read RDI s`;
      `mld_polyvec_matrix_pointwise_montgomery 5 A
        (mld_polyvec_map mld_poly_ntt (z:num->int32))`;
      `pc:num`; `read RSP s`; `read (memory :> bytes64 (read RSP s)) s`]
     [`pc:num`; `w:int64`; `mat:int64`; `y:int64`; `scratch:int64`;
      `stackpointer:int64`; `returnaddress:int64`] 8 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
