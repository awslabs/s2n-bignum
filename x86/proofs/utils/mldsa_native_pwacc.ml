(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the FULL proofs of mldsa44_polyvecl_pointwise_acc_montgomery    *)
(* and its versions for ML-DSA-65 and ML-DSA-87: the pointwise products of   *)
(* two vectors of L = 4, 5 or 7 polynomials, accumulated and reduced         *)
(* (mld_polyvec_pointwise_acc_montgomery L of                                *)
(* common/mldsa_native_polyvec.ml), as for AArch64                           *)
(* (arm/proofs/utils/mldsa_native_pwacc.ml). The x86 code computes one       *)
(* coefficient at a time: iteration i of the outer loop, with the index 4 *  *)
(* i in RDX, has an inner loop over the L polynomials that loads coefficient *)
(* i of each from both vectors, sign-extended, and accumulates the 64-bit    *)
(* products in RSI, then the Montgomery reduction of the sum, with the       *)
(* multiplication by q done with shifts, and one 32-bit store. The proofs    *)
(* simulate the inner loop unrolled.                                         *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "common/mldsa_native_polyvec.ml";;

(* ------------------------------------------------------------------------- *)
(* The value computed from the 64-bit sum p: with t = (low 32 bits of p) *   *)
(* q^-1 mod 2^32, computed with a 32-bit IMUL and sign-extended, the high 32 *)
(* bits of p - t * q, with t * q computed as ((t << 10) - t) << 13 + t (here *)
(* as the negation, ((t - (t << 10)) << 13) - t, added to p).                *)
(* ------------------------------------------------------------------------- *)

let PWACC_MONTRED_LANE = prove
 (`!p:int64.
     word_zx
      (word_ishr
        (word_add
          (word_sub
            (word_shl
              (word_sub
                (word_sx(word_zx(word_zx(word_mul (word_zx p)
                                           (word 58728449):int32):int64)
                         :int32):int64)
                (word_shl
                  (word_sx(word_zx(word_zx(word_mul (word_zx p)
                                             (word 58728449):int32):int64)
                           :int32):int64)
                  10))
              13)
            (word_sx(word_zx(word_zx(word_mul (word_zx p)
                                       (word 58728449):int32):int64)
                     :int32):int64))
          p)
        32):int32 =
     mld_montgomery_reduce p`,
  GEN_TAC THEN REWRITE_TAC[mld_montgomery_reduce; WORD_ZX_ZX_32_64_32] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SPEC_TAC(`word_sx(word_mul (word_zx (p:int64)) (word 58728449):int32)
            :int64`,`u:int64`) THEN
  GEN_TAC THEN
  REWRITE_TAC[WORD_BLAST
   `word_zx(word_ishr (v:int64) 32):int32 = word_subword v (32,32)`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[WORD_BLAST `word_shl (u:int64) 10 = word_mul u (word 1024)`;
              WORD_BLAST `word_shl (u:int64) 13 = word_mul u (word 8192)`] THEN
  CONV_TAC WORD_RULE);;

(* ------------------------------------------------------------------------- *)
(* The sum mld_polyvec_dot n x y i for a numeral n, unfolded into the n      *)
(* products in the order of the C loop, which is also that of the code.      *)
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
(* The loads of iteration i. The code addresses coefficient i of polynomial  *)
(* p of a vector at a as a + 1 * n, with n the value of an index register    *)
(* (base + index addressing), and the simulation normalizes the address.     *)
(* PWACC_LOADS_TAC off l, at the start of the body of iteration i (after     *)
(* FULL_INIT_TAC), takes each assumption                                     *)
(*                                                                           *)
(*      !j. j < n ==> read (memory :> bytes32 (a + 4 * j)) s0 = x j          *)
(*                                                                           *)
(* with n a numeral and adds read (memory :> bytes32 (a + off p)) s0 =       *)
(* x(256 * p + i) for p = 0, ..., l - 1, where off p is the offset of the    *)
(* load in the simulation (with 1024 * p evaluated). For the code that       *)
(* counts the index register from 4 * i up by 1024 (ML-DSA-44 and 65), it    *)
(* also adds the values of the index register as numbers, from which the     *)
(* simulation computes the addresses: val(word(4 * i)) = 4 * i and           *)
(* val(word_add (word(4 * i)) (word(1024 * p))) = 4 * i + 1024 * p.          *)
(* ------------------------------------------------------------------------- *)

let VAL_WORD_ADD_SMALL = prove
 (`!n k. n + k < 2 EXP 64 ==> val(word_add (word n) (word k):int64) = n + k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]);;

let PWACC_INDEX_VALS_TAC l =
  VAL_INT64_TAC `4 * i` THEN
  MAP_EVERY (fun p ->
    let tm = subst [mk_small_numeral(1024 * p),`k:num`]
      `val(word_add (word(4 * i)) (word k):int64) = 4 * i + k` in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_ADD_SMALL THEN CONV_TAC NUM_REDUCE_CONV THEN
      SIMPLE_ARITH_TAC;
      ALL_TAC]) (1--(l-1));;

let PWACC_LOADS_TAC =
  let pat = `!j. j < n
                 ==> read(memory :> bytes32(word_add a (word(4 * j)))) s0 =
                     (x:num->int32) j`
  and read_tm = `read(memory :> bytes32(word_add a (word n))) s0 = y`
  and plus_tm = `(+):num->num->num` and times_tm = `( * ):num->num->num` in
  fun (off:int->term) l ->
    W(fun (asl,w) ->
      let ths = filter (fun th ->
        try is_numeral(instantiate (term_match [] pat (concl th)) `n:num`)
        with Failure _ -> false) (map snd asl) in
      MAP_EVERY (fun th ->
        let ins = term_match [] pat (concl th) in
        let a = instantiate ins `a:int64`
        and x = instantiate ins `x:num->int32` in
        MAP_EVERY (fun p ->
          let idx = if p = 0 then `i:num` else
            mk_binop plus_tm (mk_small_numeral(256 * p)) `i:num` in
          let tm = subst [a,`a:int64`; off p,`n:num`; mk_comb(x,idx),`y:int32`]
                     read_tm in
          let eqn = mk_eq(mk_binop plus_tm `4 * i`
                            (mk_small_numeral(1024 * p)),
                          mk_binop times_tm `4` idx) in
          SUBGOAL_THEN tm ASSUME_TAC THENL
           [REWRITE_TAC[MULT_CLAUSES; GSYM ADD_ASSOC] THEN
            (if p = 0 then ALL_TAC else SUBST1_TAC(ARITH_RULE eqn)) THEN
            FIRST_ASSUM MATCH_MP_TAC THEN SIMPLE_ARITH_TAC;
            ALL_TAC]) (0--(l-1))) ths);;

(* ------------------------------------------------------------------------- *)
(* The body of iteration i of the outer loop, after the loads: the setup     *)
(* instructions (n of them), the l iterations of the inner loop, each of 7   *)
(* instructions ending with its test, decided with PTR_DECIDE_RIP_TAC where  *)
(* the code compares two registers offset from the same value, then the 11   *)
(* instructions of the reduction and the store, whose value is rewritten as  *)
(* mld_montgomery_reduce of the sum, and the 3 of the outer loop test.       *)
(* PWACC_FINAL_TAC ends the iteration, as FULL_FINAL_TAC does, with the sum  *)
(* of mld_polyvec_dot unfolded.                                              *)
(* ------------------------------------------------------------------------- *)

let PWACC_BODY_TAC execth n l =
  X86_STEPS_TAC execth (1--n) THEN
  MAP_EVERY (fun p ->
    X86_STEPS_TAC execth ((n+7*p+1)--(n+7*p+7)) THEN PTR_DECIDE_RIP_TAC)
   (0--(l-1)) THEN
  X86_STEPS_TAC execth ((n+7*l+1)--(n+7*l+11)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[PWACC_MONTRED_LANE]) THEN
  X86_STEPS_TAC execth ((n+7*l+12)--(n+7*l+14));;

let PWACC_FINAL_TAC =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ONE_OUTPUT_SPLIT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(CONV_TAC(ONCE_DEPTH_CONV PWACC_DOT_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0] THEN
      NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;
