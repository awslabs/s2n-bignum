(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise products of two vectors of 7 polynomials, accumulated and       *)
(* reduced: the proof (see polyvecl_pointwise_acc_montgomery_87_spec.ml).    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_pointwise_acc_montgomery_87_spec.ml";;
needs "arm/proofs/utils/mldsa_native_pwacc.ml";;

(*** The vectors of -q = 0xff801fff and q^-1 mod 2^32 = 0x3802001 ***)

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_CONSTANTS =
  map (fun d -> MLDSA_NATIVE_IMAGE_CONST_RULE d 128)
   [layout "mldsa87_polyvecl_pointwise_acc_montgomery_const1";
    layout "mldsa87_polyvecl_pointwise_acc_montgomery_const2"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. Each of the 64 iterations   *)
(* of the outer loop handles coefficients 4 * i, ..., 4 * i + 3 of the 7     *)
(* polynomials, with the inner loop over the polynomials unrolled; the loop  *)
(* test is the end of the body, as ENSURES_EVENTS_WHILE_UP2_TAC requires,    *)
(* and the events of an iteration depend on its index only.                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(w:int64) (u:int64) (v:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil w u v pc returnaddress)
        (APPEND
          (ENUMERATEL 64 (\i. f_ev_loop w u v pc returnaddress i))
          (f_ev_prol w u v pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `w:int64`; `u:int64`; `v:int64`;
    `x:num->int32`; `y:num->int32`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL;
              mld_polyvec_pointwise_acc_montgomery; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64`
   `pc + mldsa87_polyvecl_pointwise_acc_montgomery_loop1`
   `pc + mldsa87_polyvecl_pointwise_acc_montgomery_loop1_exit`
   `\i s. read X1 s = word(16 * i) /\ read X4 s = word 7168 /\
          read X5 s = v /\ read X6 s = u /\ read X7 s = w /\
          read X30 s = returnaddress /\
          read Q4 s = word 0xff801fffff801fffff801fffff801fff /\
          read Q5 s = word 0x03802001038020010380200103802001 /\
          (!j. j < 1792
               ==> read(memory :> bytes32(word_add u (word(4 * j)))) s =
                   x j) /\
          (!j. j < 1792
               ==> read(memory :> bytes32(word_add v (word(4 * j)))) s =
                   y j) /\
          (!j. j < 4 * i
               ==> read(memory :> bytes32(word_add w (word(4 * j)))) s =
                   mld_montgomery_reduce (mld_polyvec_dot 7 x y j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, with the vectors of constants from the image ***)

    FULL_INIT_TAC THEN
    MAP_EVERY (fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP th))
     MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_CONSTANTS THEN
    ARM_STEPS_TAC EXEC (1--2) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC EXEC (3--6) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC EXEC (7--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The outer loop body: the setup, the 7 iterations of the inner ***)
    (*** loop, the reduction, the store and the loop test              ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN PWACC_BODY_TAC EXEC 7 64 THEN PWACC_FINAL_TAC;

    (*** The return ***)

    FULL_EXIT_TAC EXEC 1]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
