(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise Montgomery multiplication of polynomials: the proof (see        *)
(* poly_pointwise_montgomery_spec.ml).                                       *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/poly_pointwise_montgomery_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;


(* ------------------------------------------------------------------------- *)
(* The value stored for coefficients a and b is the high 32 bits of          *)
(* p + t * -q, with p = a * b the 64-bit product, as SMULL, MUL, SMADDL and  *)
(* ASR compute it, where t is the low half of p times q^-1 mod 2^32 and the  *)
(* model writes the sums as additions of the integer values. Its equality    *)
(* with mld_montgomery_reduce p is proved with p, t and the whole sum as     *)
(* variables, for the term taken from the assumption that the simulation     *)
(* produces, so that it has the zero extensions of the model exactly.        *)
(* ------------------------------------------------------------------------- *)

let IWORD_MUL_SX = prove
 (`!a:int32 b:int32. iword(ival a * ival b):int64 = word_mul (word_sx a) (word_sx b)`,
  REWRITE_TAC[IWORD_INT_MUL; word_sx]);;

let MONTRED_LANE_TAC =
  FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if can (term_match [] `read (memory :> bytes32 a) s`) l &&
       free_in `x:num->int32` r && free_in `y:num->int32` r then
      let y1 = `y1:int32` and y2 = `y2:int32` in
      let lemma = prove
       (mk_forall(y1,mk_forall(y2,mk_eq(
          subst [y1,`(x:num->int32) i`; y2,`(y:num->int32) i`] r,
          `mld_montgomery_reduce (word_mul (word_sx (y1:int32))
                                           (word_sx (y2:int32)))`))),
        REPEAT GEN_TAC THEN REWRITE_TAC[mld_montgomery_reduce] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        REWRITE_TAC[WORD_ZX_ZX_32_64_32; INT_ADD_LID; ADD_CLAUSES;
                    IWORD_MUL_SX] THEN
        SPEC_TAC(`word_mul (word_sx (y1:int32)) (word_sx (y2:int32)):int64`,
                 `p:int64`) THEN
        GEN_TAC THEN
        REWRITE_TAC[WORD_RULE
         `word(val(x:int32) * c):int32 = word_mul x (word c)`] THEN
        SPEC_TAC(`word_mul (word_zx (p:int64)) (word 58728449):int32`,
                 `t:int32`) THEN
        GEN_TAC THEN
        SUBGOAL_THEN `ival (t:int32) = ival (word_sx t:int64)` SUBST1_TAC THENL
         [MATCH_MP_TAC(GSYM(ISPEC `t:int32` IVAL_WORD_SX)) THEN
          REWRITE_TAC[DIMINDEX_32; DIMINDEX_64] THEN
          CONV_TAC NUM_REDUCE_CONV;
          ALL_TAC] THEN
        SPEC_TAC(`word_sx (t:int32):int64`,`u:int64`) THEN GEN_TAC THEN
        SUBGOAL_THEN
         `iword(ival p + ival u * -- &8380417):int64 =
          word_sub p (word_mul u (word 8380417))`
        SUBST1_TAC THENL
         [REWRITE_TAC[IWORD_INT_ADD; IWORD_INT_MUL; IWORD_IVAL;
                      IWORD_INT_NEG; GSYM word_sub] THEN
          CONV_TAC WORD_RULE;
          ALL_TAC] THEN
        SPEC_TAC(`word_sub p (word_mul u (word 8380417)):int64`,
                 `v:int64`) THEN
        GEN_TAC THEN BITBLAST_TAC) in
      ASSUME_TAC(REWRITE_RULE[lemma] th)
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. Each of the 256 iterations  *)
(* of the loop adds one coefficient;                                         *)
(* the loop test is the end of the body, as ENSURES_EVENTS_WHILE_UP2_TAC     *)
(* requires, and the events of an iteration depend on its index only.        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  prove
 (MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(r:int64) (b:int64) (pc:num) (returnaddress:int64).
      APPEND
        (f_ev_epil r b pc returnaddress)
        (APPEND
          (ENUMERATEL 256 (\i. f_ev_loop r b pc returnaddress i))
          (f_ev_prol r b pc returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `r:int64`; `b:int64`; `x:num->int32`;
    `y:num->int32`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; mld_poly_pointwise_montgomery;
              fst MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `256`
   `pc + mldsa_poly_pointwise_montgomery_loop1`
   `pc + mldsa_poly_pointwise_montgomery_loop1_exit`
   `\i s. read X0 s = r /\ read X1 s = b /\ read X2 s = word(4 * i) /\
          read X30 s = returnaddress /\ read X5 s = word 4286586879 /\
          read X6 s = word 58728449 /\
          (!j. j < 256
               ==> read(memory :> bytes32(word_add b (word(4 * j)))) s =
                   y j) /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                   x j) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add r (word(4 * j)))) s =
                   mld_montgomery_reduce
                    (word_mul (word_sx (x j)) (word_sx (y j))))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_EXEC
      (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0] THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `y:num->int32` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `read(memory :> bytes32(word_add b (word(4 * i)))) s0 = y i`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o
        check (fun th -> is_forall(concl th) &&
                         free_in `y:num->int32` (concl th) &&
                         free_in `b:int64` (concl th) &&
                         not(free_in `x:num->int32` (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_EXEC
      (1--7) THEN
    MONTRED_LANE_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_EXEC
      (8--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
    LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_EXEC
      (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  prove
 (MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_IMAGE_SUBROUTINE_FULL);;
