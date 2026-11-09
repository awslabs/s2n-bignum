(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the FULL proofs of mldsa44_polyvecl_pointwise_acc_montgomery    *)
(* and its versions for ML-DSA-65 and ML-DSA-87: the pointwise products of   *)
(* two vectors of L = 4, 5 or 7 polynomials, accumulated and reduced         *)
(* (mld_polyvec_pointwise_acc_montgomery L of                                *)
(* common/mldsa_native_polyvec.ml). The compiler has vectorized the three in *)
(* the same way: iteration i of the outer loop handles coefficients 4 * i,   *)
(* ..., 4 * i + 3 of each polynomial, with an inner loop over the L          *)
(* polynomials that loads them from both vectors as 128-bit words and        *)
(* accumulates the 64-bit products with SMLAL and SMLAL2, then the           *)
(* Montgomery reduction of the four sums with vectors of q^-1 mod 2^32 and   *)
(* -q, and one 128-bit store. The proofs simulate the inner loop unrolled.   *)
(* ========================================================================= *)

needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "common/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* The value computed in each lane from the 64-bit sum p: with               *)
(* t = (low 32 bits of p) * q^-1 mod 2^32, the high 32 bits of p + t * -q,   *)
(* as UZP1, MUL, SMLAL and UZP2 compute it.                                  *)
(* ------------------------------------------------------------------------- *)

let PWACC_MONTRED_LANE = prove
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
(* The sum mld_polyvec_dot n x y i for a numeral n, unfolded into the n      *)
(* products in the order of the C loop.                                      *)
(* ------------------------------------------------------------------------- *)

let PWACC_DOT_CONV =
  let th0 = CONJUNCT1 mld_polyvec_dot and th1 = CONJUNCT2 mld_polyvec_dot in
  let rec conv tm =
    match tm with
      Comb(Comb(Comb(Comb(Const("mld_polyvec_dot",_),n),_),_),_) ->
        if n = `0` then REWR_CONV th0 tm else
        (RATOR_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV num_CONV))) THENC
         REWR_CONV th1 THENC LAND_CONV conv) tm
    | _ -> failwith "PWACC_DOT_CONV" in
  conv;;

(* ------------------------------------------------------------------------- *)
(* The 128-bit words that iteration i loads from a vector of n coefficients  *)
(* at a, one for each polynomial p: PWACC_INPUT_LANES gives the four         *)
(* coefficients of polynomial p handled in iteration i, at the address of    *)
(* the load (normalized as in the simulation by PWACC_LOADS_TAC). At the     *)
(* start of the body of iteration i (after FULL_INIT_TAC), PWACC_LOADS_TAC l *)
(* takes each assumption !j. j < n ==> read (bytes32 (a + 4 * j)) s0 = x j   *)
(* with n a numeral and gives the 128-bit words of polynomials 0, ..., l - 1 *)
(* of the vector as assumptions.                                             *)
(* ------------------------------------------------------------------------- *)

let PWACC_INPUT_LANES = prove
 (`!a (x:num->int32) (s:armstate) n.
        (!j. j < n
             ==> read(memory :> bytes32(word_add a (word(4 * j)))) s = x j)
        ==> !p i. 256 * p + 4 * i + 4 <= n
                  ==> !k. k < 4
                          ==> read(memory :> bytes32
                               (word_add (word_add a (word(16 * i + 1024 * p)))
                                         (word(4 * k)))) s =
                              x(256 * p + 4 * i + k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `word_add (word_add a (word(16 * i + 1024 * p))) (word(4 * k)):int64 =
    word_add a (word(4 * (256 * p + 4 * i + k)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let PWACC_LOADS_TAC =
  let pat = `!j. j < n
                 ==> read(memory :> bytes32(word_add a (word(4 * j)))) s0 =
                     (x:num->int32) j`
  and norm = NUM_REDUCE_CONV THENC
             REWRITE_CONV[ADD_CLAUSES; MULT_CLAUSES; WORD_ADD_0]
  and base_tm = `word_add (a:int64) (word(16 * i + 1024 * p))`
  and merge_tm = `read (memory :> bytes128 A) s0` and a_tm = `A:int64` in
  fun l ->
    W(fun (asl,w) ->
      let ths = filter (fun th ->
        try is_numeral(instantiate (term_match [] pat (concl th)) `n:num`)
        with Failure _ -> false) (map snd asl) in
      MAP_EVERY (fun th ->
        let a = instantiate (term_match [] pat (concl th)) `a:int64` in
        MAP_EVERY (fun p ->
          let base = rhs(concl(norm(subst
                       [a,`a:int64`; mk_small_numeral p,`p:num`] base_tm))) in
          MP_TAC(SPECL [mk_small_numeral p; `i:num`]
                  (MATCH_MP PWACC_INPUT_LANES th)) THEN
          ANTS_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
          CONV_TAC(LAND_CONV(EXPAND_CASES_CONV THENC norm)) THEN
          STRIP_TAC THEN
          MP_TAC(READ_MEMORY_MERGE_CONV 2 (subst [base,a_tm] merge_tm)) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
          DISCARD_MATCHING_ASSUMPTIONS
           [`read (memory :> bytes32 (word_add a b)) s0 = x`])
         (0--(l-1))) ths);;

(* ------------------------------------------------------------------------- *)
(* The body of iteration i of the outer loop, after FULL_INIT_TAC: the loads *)
(* for the l polynomials, the simulation of its n instructions, simplifying  *)
(* the lanes of each result, and the 128-bit store at w + 16 * i split into  *)
(* four 32-bit values. PWACC_FINAL_TAC then ends it as VEC4_FULL_FINAL_TAC   *)
(* does, with the lanes as Montgomery reductions of the sums of products of  *)
(* mld_polyvec_dot, unfolded and put in the same order as the code's.        *)
(* ------------------------------------------------------------------------- *)

let PWACC_BODY_TAC =
  let pat_store = `read (memory :> bytes128 (word_add a (word(16 * i)))) s = x`
  and s0 = `s0:armstate` in
  fun execth l n ->
    PWACC_LOADS_TAC l THEN
    MAP_EVERY (fun k ->
      ARM_STEPS_TAC execth [k] THEN SIMD_SIMPLIFY_TAC[]) (1--n) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      CONV_RULE(SIMD_SIMPLIFY_CONV []) o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (fun th -> can (term_match [] pat_store) (concl th) &&
                       not(free_in s0 (concl th)))));;

let PWACC_FINAL_TAC =
  VEC4_FULL_FINAL_TAC [PWACC_MONTRED_LANE]
   (CONV_TAC(ONCE_DEPTH_CONV PWACC_DOT_CONV) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0] THEN
    REWRITE_TAC[WORD_ADD_AC; WORD_MUL_SYM]);;
