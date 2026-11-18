(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the FULL proofs of the functions on vectors of polynomials of   *)
(* mldsa-native (polyvec.c), which call a function on polynomials for each   *)
(* polynomial of the vector in turn.                                         *)
(*                                                                           *)
(* A vector is given as in common/mldsa_native_polyvec.ml by its elements    *)
(* (coefficients, or bytes for packed polynomials), n for each polynomial,   *)
(* those of polynomial i being n * i + k for k < n. The proofs of the loops  *)
(* over the polynomials use invariants with, for each vector that is         *)
(* written, a fact for the polynomials already done and one for the rest:    *)
(*                                                                           *)
(*      (!j. j < n * i ==> read (c (a j)) s = y j) /\                        *)
(*      (!j. n * i <= j /\ j < n * m ==> read (c (a j)) s = x j)             *)
(*                                                                           *)
(* where a j is the address of element j. Before the call for polynomial i,  *)
(* VEC_SLICE_TAC gives the precondition of the callee for it, and            *)
(* VEC_REST_TAC the fact for the polynomials after it, which, like the one   *)
(* for those before it, the simulation of the call keeps. After the call,    *)
(* VEC_JOIN_TAC gives the first fact for i + 1 from those for i and the      *)
(* postcondition of the callee.                                              *)
(* ========================================================================= *)

(* The part that depends on AArch64; the rest is in                          *)
(* common/fips204/properties/mldsa_native_polyvec.ml.                        *)

needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "common/fips204/properties/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* The facts for polynomial i of a vector and for those after it, as         *)
(* instances of a fact for more of the vector: VEC_SLICE_TAC tm proves tm,   *)
(* of the form !j. j < n ==> read (c (a j)) s = x(n * i + j), from an        *)
(* assumption !j. P j ==> read (c (a' j)) s = x j, with the address of       *)
(* element n * i + j normalized as in the simulation, and VEC_REST_TAC tm    *)
(* proves tm, of the form !j. Q j ==> R j, from an assumption                *)
(* !j. P j ==> R j where Q implies P.                                        *)
(* ------------------------------------------------------------------------- *)

let VEC_SLICE_TAC tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    W(fun (asl,w) ->
      let idx = rand(rhs w) in
      FIRST_ASSUM(fun th ->
        MP_TAC(SPEC idx th) THEN
        REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC));
    ALL_TAC];;

let VEC_REST_TAC tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_ARITH_TAC);
    ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* A vector copied with memcpy: VEC_BYTES_EQ_BYTES32 gives the coefficients  *)
(* of the copy from the equality of the bytes of the two vectors that the    *)
(* contract of memcpy gives.                                                 *)
(* ------------------------------------------------------------------------- *)

let VEC_BYTES_EQ_BYTES32 = prove
 (`!a b n (s:armstate) (s1:armstate).
        read (memory :> bytes(a,4 * n)) s = read (memory :> bytes(b,4 * n)) s1
        ==> !j. j < n
                ==> read (memory :> bytes32(word_add a (word(4 * j)))) s =
                    read (memory :> bytes32(word_add b (word(4 * j)))) s1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bytes32; READ_COMPONENT_COMPOSE; asword; through; read] THEN
  AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM
   `\x. (x DIV 2 EXP (8 * (4 * j))) MOD 2 EXP (8 * 4)`) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_DIV; READ_BYTES_MOD] THEN
  SUBGOAL_THEN `MIN (4 * n - 4 * j) 4 = 4` SUBST1_TAC THENL
   [UNDISCH_TAC `j < n` THEN ARITH_TAC; REWRITE_TAC[]]);;

let VEC_FULL_EXIT_TAC execth n ths =
  REWRITE_TAC[] THEN FULL_INIT_TAC THEN ARM_STEPS_TAC execth (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC ths THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_ASSUM(MATCH_ACCEPT_TAC o
        CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(* ------------------------------------------------------------------------- *)
(* The initialization of such a loop, simulating the n instructions before   *)
(* it, where the invariant for 0 follows from the precondition after         *)
(* rewriting with ths.                                                       *)
(* ------------------------------------------------------------------------- *)

let VEC_FULL_INIT_TAC execth n ths =
  FULL_INIT_TAC THEN ARM_STEPS_TAC execth (1--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC ths THEN
  REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
  ASM_REWRITE_TAC[] THEN DISCHARGE_SAFETY_PROPERTY_TAC;;
