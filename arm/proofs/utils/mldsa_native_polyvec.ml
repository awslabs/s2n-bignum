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

needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "common/mldsa_native_polyvec.ml";;

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
(* The fact for the polynomials before i + 1, from that for those before i   *)
(* and the postcondition of the callee for polynomial i: VEC_JOIN_TAC ths    *)
(* reduces a goal !j. j < n * (i + 1) ==> P j to the cases j < n * i, which  *)
(* it proves from the assumptions, and j = n * i + k for k < n, which it     *)
(* proves from the assumptions after rewriting with ths and the lemmas of    *)
(* common/mldsa_native_polyvec.ml, which give element n * i + k of a lifted  *)
(* function, and with the address normalized as in the simulation.           *)
(* ------------------------------------------------------------------------- *)

let VEC_JOIN_POLY = prove
 (`!(P:num->bool) n i.
        (!j. j < n * i ==> P j) /\ (!k. k < n ==> P(n * i + k))
        ==> !j. j < n * (i + 1) ==> P j`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `j < n * i` THEN ASM_SIMP_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j - n * i`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let VEC_JOIN_TAC ths =
  MATCH_MP_TAC VEC_JOIN_POLY THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC(ths @ [MLD_POLYVEC_MAP_COEFF; MLD_POLYVEC_PACK_COEFF;
                        MLD_POLYVEC_UNPACK_COEFF; mld_poly_of]) THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* The same for all k polynomials at once, for the unrolled loops of         *)
(* ML-DSA-44: VEC_UNROLL_JOIN_TAC n k ths reduces a goal                     *)
(* !j. j < n * k ==> P j to the cases j = n * i + l for i < k and l < n,     *)
(* rewritten as by VEC_JOIN_TAC ths and with the indices evaluated, and      *)
(* proves them from the assumptions (POLYVEC_SPLIT_TAC k of                  *)
(* utils/mlkem_native_image.ml gives the preconditions of the calls).        *)
(* ------------------------------------------------------------------------- *)

let VEC_JOIN_ALL = prove
 (`!(P:num->bool) n k.
        (!i. i < k ==> !l. l < n ==> P(n * i + l)) ==> !j. j < n * k ==> P j`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THENL [ASM_MESON_TAC[MULT_CLAUSES; LT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j DIV n`) THEN
  ASM_SIMP_TAC[RDIV_LT_EQ] THEN
  DISCH_THEN(MP_TAC o SPEC `j MOD n`) THEN
  ASM_REWRITE_TAC[MOD_LT_EQ; DIVISION_SIMP]);;

let VEC_UNROLL_JOIN_TAC n k ths =
  let jth = CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
             (GEN `P:num->bool`
               (SPECL [`P:num->bool`; mk_small_numeral n; mk_small_numeral k]
                      VEC_JOIN_ALL)) in
  MATCH_MP_TAC jth THEN
  SIMP_TAC(ths @ [MLD_POLYVEC_MAP_COEFF; MLD_POLYVEC_PACK_COEFF;
                  MLD_POLYVEC_UNPACK_COEFF; mld_poly_of]) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC POLYVEC_INDEX_CONV THEN
  REPEAT CONJ_TAC THEN ASM_SIMP_TAC[ETA_AX];;

(* ------------------------------------------------------------------------- *)
(* The end of the body of a loop over the polynomials, after the loop test:  *)
(* as FULL_FINAL_TAC ths, also proving the facts for the polynomials done    *)
(* with VEC_JOIN_TAC ths. VEC_FULL_EXIT_TAC execth n ths is FULL_EXIT_TAC    *)
(* execth n with the rewriting with ths, e.g. for a result accumulated in a  *)
(* register.                                                                 *)
(* ------------------------------------------------------------------------- *)

let VEC_FULL_FINAL_TAC ths =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC ths THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(VEC_JOIN_TAC ths THEN NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

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
