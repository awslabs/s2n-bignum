(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of mldsa-native's compiled code that do not depend   *)
(* on the build. The tactics for flags, small 32-bit numbers and ensures     *)
(* goals are those of utils/mlkem_native.ml, which is not loaded here since  *)
(* it loads common/mlkem_mldsa.ml, which the mldsa-native proofs do not      *)
(* need.                                                                     *)
(* ========================================================================= *)

(* The part that depends on AArch64; the rest is in                          *)
(* common/fips204/properties/mldsa_native.ml.                                *)

needs "arm/proofs/base.ml";;
needs "common/fips204/properties/mldsa_native.ml";;

let W32_DECIDE_FLAGS_TAC =
  W32_SMALL_TAC THEN
  CMP_FLAGS_TAC `word_sub (word x) (word y):int32` WORD_CMP_32_FLAGS;;

let SIMD_SIMPLIFY_TAC unfold_defs =
  let arm_simdable =
    can (term_match [] `read X (s:armstate):int128 = whatever`) in
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o
    CONV_RULE(RAND_CONV (SIMD_SIMPLIFY_CONV unfold_defs)) o
    check (arm_simdable o concl)));;

(* ------------------------------------------------------------------------- *)
(* The body of a loop that the compiler has vectorized, handling the four    *)
(* coefficients 4 * i, ..., 4 * i + 3 of some polynomials in iteration i     *)
(* with one 128-bit load or store for each. The invariant of such a loop     *)
(* states, for each polynomial x at a that the loop reads, either            *)
(*                                                                           *)
(*   !j. 4 * i <= j /\ j < 256                                               *)
(*       ==> read(memory :> bytes32(word_add a (word(4 * j)))) s = x j       *)
(*                                                                           *)
(* if the loop overwrites it, or the same for j < 256 if it does not.        *)
(* VEC4_LOOP_BODY_TAC exec n, at the start of the body (after                *)
(* ENSURES_INIT_TAC "s0"), takes the four coefficients of each such          *)
(* polynomial as one 128-bit value, simulates n instructions, simplifying    *)
(* the lanes of each result, and splits each 128-bit store at an address     *)
(* word_add a (word(16 * i)) into four 32-bit values again. A fact for the   *)
(* coefficients from 4 * (i + 1) on is kept for each overwritten input.      *)
(* ------------------------------------------------------------------------- *)

let VEC4_LOOP_BODY_TAC =
  let pat_rw = `!j. 4 * i <= j /\ j < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * j)))) s0 =
                        (x:num->int32) j`
  and pat_ro = `!j. j < 256
                    ==> read(memory :> bytes32(word_add a (word(4 * j)))) s0 =
                        (x:num->int32) j`
  and pat_lane0 = `read (memory :> bytes32 (word_add a (word(16 * i)))) s0`
  and pat_store = `read (memory :> bytes128 (word_add a (word(16 * i)))) s = x`
  and merge_tm = `read (memory :> bytes128 A) s0`
  and a_tm = `A:int64` and j_tm = `j:num` and k_tm = `k:num`
  and j4_tm = `4 * i + k` and k4_tm = `k < 4` in
  let lanes_tac =
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[CHUNK4_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC in
  let split_rw th =
    MP_TAC(GEN_REWRITE_RULE I
            [MATCH_MP CHUNK4_INPUT_SPLIT (ASSUME `i < 64`)] th) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN lanes_tac
  and split_ro th =
    let eqn = rand(snd(dest_forall(concl th))) in
    let t = mk_forall(k_tm,mk_imp(k4_tm,subst [j4_tm,j_tm] eqn)) in
    SUBGOAL_THEN t MP_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC th THEN ASM_ARITH_TAC;
      lanes_tac] in
  fun execth n ->
    W(fun (asl,w) ->
      let rws = filter (can (term_match [] pat_rw) o concl o snd) asl
      and ros = filter (can (term_match [] pat_ro) o concl o snd) asl in
      MAP_EVERY (fun (_,th) -> UNDISCH_THEN (concl th) split_rw) rws THEN
      MAP_EVERY (fun (_,th) -> split_ro th) ros) THEN
    W(fun (asl,w) ->
      let addrs = setify (mapfilter (fun (_,th) ->
        let l = lhand(concl th) in
        if can (term_match [] pat_lane0) l then rand(rand(rand(rator l)))
        else failwith "") asl) in
      MAP_EVERY (fun a ->
        MP_TAC(READ_MEMORY_MERGE_CONV 2 (subst [a,a_tm] merge_tm))) addrs) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes32 a) s = x`] THEN
    MAP_EVERY (fun k ->
      ARM_STEPS_TAC execth [k] THEN SIMD_SIMPLIFY_TAC[]) (1--n) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(SIMD_SIMPLIFY_CONV []) o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> can (term_match [] pat_store) (concl th) &&
                       not(free_in `s0:armstate` (concl th)))));;

(*** The exit of a loop whose test compares pointers or offsets with the ***)
(*** same base, as ENSURES_WHILE_UP_TAC leaves it; LOOP_EXIT_TAC n       ***)
(*** simulates the n instructions from the test to the return.           ***)

let LOOP_EXIT_TAC execth n =
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC execth (1--1) THEN PTR_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC execth (2--n) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN
  FIRST_ASSUM(MATCH_ACCEPT_TAC o CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV));;
