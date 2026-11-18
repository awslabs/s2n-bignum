(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of mldsa-native's x86-64 compiled code that do not   *)
(* depend on the build. These are the tools of the AArch64 proofs in         *)
(* arm/proofs/utils/mldsa_native.ml that are not about the AArch64 model,    *)
(* and the tools of the x86-64 proofs of mlkem-native for the alignment and  *)
(* the addresses of the operands of SSE instructions.                        *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;
needs "common/fips204/properties/mldsa_native.ml";;

(* ------------------------------------------------------------------------- *)
(* Reasoning about 32-bit operations on small numbers, which the compiled    *)
(* code uses for loop counters and indices, and about the flags set when     *)
(* they or pointers with the same base are compared.                         *)
(* ------------------------------------------------------------------------- *)

let W32_DECIDE_FLAGS_TAC =
  W32_SMALL_TAC THEN
  CMP_FLAGS_TAC `word_sub (word x) (word y):int32` WORD_CMP_32_FLAGS;;
(* ------------------------------------------------------------------------- *)
(* Simplify the lanes of SIMD registers after a step, as SIMD_SIMPLIFY_CONV  *)
(* and SIMD_SIMPLIFY_TAC in common/mlkem_mldsa.ml do (copied here so as not  *)
(* to load that file).                                                       *)
(* ------------------------------------------------------------------------- *)

let SIMD_SIMPLIFY_TAC unfold_defs =
  let x86_simdable =
    can (term_match [] `read X (s:x86state):int256 = whatever`) in
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o
    CONV_RULE(RAND_CONV (SIMD_SIMPLIFY_CONV unfold_defs)) o
    check (x86_simdable o concl)));;

(* ------------------------------------------------------------------------- *)
(* Decide the test at the end of an iteration of a loop over the             *)
(* polynomials, which compares a pointer with its final value, both offsets  *)
(* from the same base, after the conditional jump. This evaluates the        *)
(* condition in the resulting instruction pointer and in the events.         *)
(* ------------------------------------------------------------------------- *)

let PTR_DECIDE_RIP_TAC =
  let wth = WORD_RULE
   `word_sub (word_add a x) (word_add a y):int64 = word_sub x y` in
  let pat = `val(word_sub (word_add a x) (word_add a y):int64) = 0` in
  let is_test t =
    let t' = if is_neg t then rand t else t in
    can (term_match [] pat) t' in
  let tconv = REWRITE_CONV[wth] THENC WORD_REDUCE_CONV THENC
              NUM_REDUCE_CONV in
  let conv t =
    if is_cond t && is_test(lhand(rator t)) then
      (RATOR_CONV(LAND_CONV tconv) THENC REWRITE_CONV[]) t
    else failwith "PTR_DECIDE_RIP_TAC" in
  RULE_ASSUM_TAC(fun th ->
    if can (find_term (can conv)) (concl th)
    then CONV_RULE(ONCE_DEPTH_CONV conv) th else th);;

(* ------------------------------------------------------------------------- *)
(* ALIGNED_OFFSETS_TAC a k [n1; ...] adds aligned k (word_add a (word ni))   *)
(* to the assumptions for each ni, a multiple of k, given aligned k a there, *)
(* e.g. for the polynomials of an aligned vector.                            *)
(* ------------------------------------------------------------------------- *)

let ALIGNED_OFFSETS_TAC a k ns =
  MAP_EVERY (fun n ->
    let tm = list_mk_comb(`aligned:num->int64->bool`,
       [mk_small_numeral k;
        mk_comb(mk_comb(`word_add:int64->int64->int64`,a),
                mk_comb(`word:num->int64`,mk_small_numeral n))]) in
    SUBGOAL_THEN tm ASSUME_TAC THENL
     [CONV_TAC NORMALIZE_ALIGNED_WORD_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC]) ns;;

(* ------------------------------------------------------------------------- *)
(* For a vector instruction with a memory operand at base + index, the       *)
(* address is computed as word_add a (word(1 * n)) when the index register   *)
(* is word n, so INDEX_ADDR_TAC restates the assumptions about the 128-bit   *)
(* words at word_add a (word(16 * i)), and their alignment, in that form.    *)
(* ------------------------------------------------------------------------- *)

let INDEX_ADDR_TAC =
  let pth = ARITH_RULE `16 * i = 1 * 16 * i` in
  RULE_ASSUM_TAC(fun th ->
    let c = concl th in
    if can (term_match []
          `read (memory :> bytes128 (word_add a (word(16 * i)))) s = v`) c ||
       can (term_match [] `aligned 16 (word_add a (word(16 * i)):int64)`) c
    then ONCE_REWRITE_RULE[pth] th else th);;
