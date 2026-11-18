(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise Montgomery multiplication: the proof (see                       *)
(* poly_pointwise_montgomery_spec.ml).                                       *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/poly_pointwise_montgomery_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

(*** The vectors of -q = 0xff801fff and q^-1 mod 2^32 = 0x3802001 ***)

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_CONSTANTS =
  map (fun d -> MLDSA_NATIVE_IMAGE_CONST_RULE d 128)
   [layout "mldsa_poly_pointwise_montgomery_const1";
    layout "mldsa_poly_pointwise_montgomery_const2"];;

(* ------------------------------------------------------------------------- *)
(* The value computed in each lane from the 64-bit product p: with           *)
(* t = (low 32 bits of p) * q^-1 mod 2^32, the high 32 bits of p + t * -q,   *)
(* as SMULL, UZP1, MUL, SMLAL and UZP2 compute it.                           *)
(* ------------------------------------------------------------------------- *)

let MONTRED_LANE = prove
 (`!p:int64.
     word_subword
      (word_add (word_mul (word_sx (word_mul (word_subword p (0,32))
                                             (word 58728449):int32))
                          (word 18446744073701171199))
                p) (32,32) =
     mld_montgomery_reduce p`,
  GEN_TAC THEN REWRITE_TAC[mld_montgomery_reduce] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `word_subword (p:int64) (0,32):int32 = word_zx p`
  SUBST1_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SPEC_TAC(`word_sx(word_mul (word_zx (p:int64)) (word 58728449):int32)
            :int64`,`t:int64`) THEN
  REWRITE_TAC[WORD_RULE
   `word_sub p (word_mul t c):N word =
    word_add (word_mul t (word_neg c)) p`] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. Each of the 64 iterations   *)
(* of the loop multiplies 4 coefficients, loaded and stored as one 128-bit   *)
(* word; the loop test is the end of the body, as                            *)
(* ENSURES_EVENTS_WHILE_UP2_TAC requires, and the events of an iteration     *)
(* depend on its index only.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_EXEC in
  CONCRETIZE_F_EVENTS_TAC
    `\(r:int64) (b:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil r b pc returnaddress)
        (APPEND
          (ENUMERATEL 64 (\i. f_ev_loop r b pc returnaddress i))
          (f_ev_prol r b pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `r:int64`; `b:int64`; `x:num->int32`;
    `y:num->int32`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; mld_poly_pointwise_montgomery;
              fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `64`
   `pc + mldsa_poly_pointwise_montgomery_loop1`
   `pc + mldsa_poly_pointwise_montgomery_loop1_exit`
   `\i s. read X0 s = r /\ read X1 s = b /\ read X2 s = word(16 * i) /\
          read X30 s = returnaddress /\
          read Q3 s = word 0xff801fffff801fffff801fffff801fff /\
          read Q4 s = word 0x03802001038020010380200103802001 /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s =
                   y j) /\
          (!j. 4 * i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                   x j) /\
          (!j. j < 4 * i
               ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                   mld_montgomery_reduce
                    (word_mul (word_sx (x j)) (word_sx (y j))))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, with the vectors of constants from the image ***)

    FULL_INIT_TAC THEN
    MAP_EVERY (fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP th))
      MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_CONSTANTS THEN
    ARM_STEPS_TAC EXEC (1--1) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC EXEC (2--3) THEN MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC EXEC (4--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body, with the loop test; the code multiplies y j by x j ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    VEC4_LOOP_BODY_TAC EXEC 11 THEN ARM_STEPS_TAC EXEC (12--13) THEN
    VEC4_FULL_FINAL_TAC [MONTRED_LANE] (REWRITE_TAC[WORD_MUL_SYM]);

    (*** The return ***)

    FULL_EXIT_TAC EXEC 1]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
