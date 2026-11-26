(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the clang 23 build of mldsa-native, whose code    *)
(* addresses memory differently from gcc's:                                  *)
(*                                                                           *)
(*  - An index register holds word(c * i), so that the simulation addresses  *)
(*    a byte at word_add r (word(1 * val(word(c * i)) + k)); the facts about *)
(*    the stores must have val(word(c * i)) replaced by c * i before the     *)
(*    outputs of the iteration are compared with the specification           *)
(*    (VAL_IDX_TAC). Without it, the facts that mention the old state  *)
(*    s0 through such an address are dropped by DISCARD_OLDSTATE_TAC.        *)
(*  - A loop of a chunk of B outputs per iteration is finished by            *)
(*    CLANG_CHUNK_FINAL_TAC, as CHUNK_FULL_FINAL_TAC of                      *)
(*    x86/proofs/utils/mldsa_native_pack.ml, but with the rules for the      *)
(*    division and remainder of B * i + c by B for c < B given as theorems,  *)
(*    where its SIMP_TAC with DIVMOD_CHUNK does not terminate in reasonable  *)
(*    time on the terms that the clang code gives.                           *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_pack.ml";;

(*** val(word(c * i)) = c * i, for c * i below 2^64, from a bound on i ***)

let VAL_WORD_MUL_IDX = prove
 (`!c i. c * i < 2 EXP 64 ==> val(word(c * i):int64) = c * i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]);;

(*** val(word(c * i)) = c * i, using i < n among the assumptions ***)

let VAL_IDX_TAC c n =
  let cn = mk_small_numeral c and nn = mk_small_numeral n in
  let ilt = mk_comb(mk_comb(`(<):num->num->bool`,`i:num`),nn) in
  SUBGOAL_THEN (mk_eq(mk_comb(`val:int64->num`,
                              mk_comb(`word:num->int64`,
                                      mk_binop `( * ):num->num->num` cn `i:num`)),
                      mk_binop `( * ):num->num->num` cn `i:num`))
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; MULT_CLAUSES]) THEN
              ASSUME_TAC th) THENL
   [MATCH_MP_TAC(SPECL [cn; `i:num`] VAL_WORD_MUL_IDX) THEN
    FIRST_X_ASSUM(fun th ->
      if concl th = ilt then MP_TAC th else failwith "VAL_IDX_TAC") THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    ALL_TAC];;

(*** The facts (B * i + c) DIV B = i and (B * i + c) MOD B = c ***)

let chunk_rules b =
  end_itlist CONJ (map (fun c ->
    prove(subst [mk_small_numeral b,`b:num`; mk_small_numeral c,`c:num`]
            `(b * i + c) DIV b = i /\ (b * i + c) MOD b = c`,
          SIMP_TAC[DIVMOD_CHUNK; ARITH])) (0--(b-1)));;

(*** The end of an iteration that writes b outputs, as CHUNK_FULL_FINAL_TAC
     with the rules for b ***)

let CLANG_CHUNK_FINAL_TAC fdef (x:term) b =
  let rules = chunk_rules b in
  ADDR_NORMALIZE_TAC THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC[CHUNK_OUTPUT_SPLIT; CHUNK_OUTPUT_SPLIT_1] THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      REWRITE_TAC[fdef] THEN
      REWRITE_TAC[rules] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_CLAUSES; LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_REWRITE_TAC[WORD_VAL_MOD_256; WORD_VAL_DIV_256_MOD_256] THEN
      REPEAT CONJ_TAC THEN APP_BLAST_TAC x THEN
      NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The loads through an index register that holds word(c * i), as in
     movzx ecx, BYTE PTR [rsi+rax*1+k], which the simulation addresses as
     word_add a (word(1 * val(word(c * i)) + k)) (and with no + k for
     k = 0): for the m facts that CHUNK_INPUT_TAC gives about
     read (memory :> bytesN (word_add a (word(c * i + k)))) s0 = y k, with
     the element y k = f (c * i + k) of the input f, add the same facts at
     those addresses. ***)

let IDX_LOAD_ALT_TAC (bytesn:string) (a:string) (f:string) c n m =
  let valeq = Printf.sprintf "val(word(%d * i):int64) = %d * i" c c in
  EVERY(map (fun k ->
    let addr =
      if k = 0 then Printf.sprintf "1 * val(word(%d * i):int64)" c
      else Printf.sprintf "1 * val(word(%d * i):int64) + %d" c k in
    let v = if k = 0 then Printf.sprintf "%s (%d * i)" f c
            else Printf.sprintf "%s (%d * i + %d)" f c k in
    let t = parse_term(Printf.sprintf
      "read (memory :> %s (word_add %s (word(%s)))) s0 = %s"
      bytesn a addr v) in
    SUBGOAL_THEN t ASSUME_TAC THENL
     [SUBGOAL_THEN (parse_term valeq) SUBST1_TAC THENL
       [MATCH_MP_TAC(SPECL [mk_small_numeral c; `i:num`] VAL_WORD_MUL_IDX) THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        FIRST_X_ASSUM(fun th ->
          if concl th = mk_comb(mk_comb(`(<):num->num->bool`,`i:num`),
                                mk_small_numeral n)
          then MP_TAC th else failwith "IDX_LOAD_ALT_TAC") THEN
        ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[MULT_CLAUSES] THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC]) (0--(m-1)));;
