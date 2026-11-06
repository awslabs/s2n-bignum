(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition of q to the negative coefficients: the proof (see                *)
(* poly_caddq_spec.ml).                                                      *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/poly_caddq_spec.ml";;

(* ------------------------------------------------------------------------- *)
(* The value stored for coefficient a is a ^ ((a ^ (a + q)) & m), where the  *)
(* mask m is all ones if a is negative and zero otherwise. Its equality      *)
(* with mld_caddq a is proved by bit-blasting, with the coefficient as a     *)
(* variable; the term is taken from the assumption that the simulation       *)
(* produces, so that it has the zero extensions of the model exactly.        *)
(* ------------------------------------------------------------------------- *)

let CADDQ_LANE_TAC =
  FIRST_X_ASSUM(fun th ->
    let l,r = dest_eq(concl th) in
    if can (term_match [] `read (memory :> bytes32 a) s`) l &&
       free_in `x:num->int32` r then
      let v = `(x:num->int32) i` and y = genvar `:int32` in
      let lemma = prove
       (mk_forall(y,mk_eq(subst[y,v] r,mk_comb(`mld_caddq`,y))),
        GEN_TAC THEN REWRITE_TAC[mld_caddq; GSYM MSB_IVAL; DIMINDEX_32] THEN
        CONV_TAC NUM_REDUCE_CONV THEN BITBLAST_TAC) in
      ASSUME_TAC(REWRITE_RULE[lemma] th)
    else NO_TAC);;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The loop handles one coefficient per iteration.        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CADDQ_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLY_CADDQ_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `x:num->int32`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; mld_poly_caddq] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `256` `pc + mldsa_poly_caddq_loop1`
   `pc + mldsa_poly_caddq_loop1_test`
   `\i s. read X0 s = word_add a (word(4 * i)) /\
          read X4 s = word_add a (word 1024) /\
          read X30 s = returnaddress /\
          read X5 s = word 8380417 /\
          (!j. i <= j /\ j < 256
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   x j) /\
          (!j. j < i
               ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                   mld_caddq (x j))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_CADDQ_GCC12_O2_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[];

    (*** The loop body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ONE_INPUT_SPLIT] o
      check (fun th -> is_forall(concl th) &&
        free_in `x:num->int32` (concl th) &&
        not(free_in `mld_caddq` (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_CADDQ_GCC12_O2_EXEC (1--8) THEN
    CADDQ_LANE_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
    CONV_TAC WORD_RULE;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_CADDQ_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_CADDQ_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_CADDQ_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLDSA_NATIVE_POLY_CADDQ_GCC12_O2_EXEC (2--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      check (fun th -> is_forall(concl th) &&
                       free_in `mld_caddq` (concl th)))]);;
