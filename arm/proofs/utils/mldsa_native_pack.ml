(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the packing and unpacking loops of mldsa-native,  *)
(* which handle a group of C coefficients and B bytes in each iteration i:   *)
(* coefficients C * i + k and bytes B * i + k.                               *)
(* ========================================================================= *)

needs "arm/proofs/utils/mldsa_native.ml";;

(*** Splitting off the B outputs of an iteration (with j < i for B = 1), and
     the indices of an iteration ***)

let CHUNK_OUTPUT_SPLIT = prove
 (`!P B i. (!j. j < B * (i + 1) ==> P j) <=>
           (!j. j < B * i ==> P j) /\ (!k. k < B ==> P(B * i + k))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ASM_ARITH_TAC;
    STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `j < B * i` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j - B * i`) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(j < B * i) ==> B * i + (j - B * i) = j`] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `j < B * (i + 1)` THEN UNDISCH_TAC `~(j < B * i)` THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN ARITH_TAC]);;

let CHUNK_OUTPUT_SPLIT_1 = prove
 (`!P i. (!j. j < i + 1 ==> P j) <=>
         (!j. j < i ==> P j) /\ (!k. k < 1 ==> P(i + k))`,
  REWRITE_TAC[ARITH_RULE `k < 1 <=> k = 0`; FORALL_UNWIND_THM2; ADD_CLAUSES;
              ARITH_RULE `j < i + 1 <=> j < i \/ j = i`] THEN
  MESON_TAC[]);;

let DIVMOD_CHUNK = prove
 (`!B i k. k < B ==> (B * i + k) DIV B = i /\ (B * i + k) MOD B = k`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `k:num`;
    MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `i:num`] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The inputs of iteration i at the start of the body (after                 *)
(* ENSURES_INIT_TAC "s0"): from a fact                                       *)
(*                                                                           *)
(*   !j. j < n ==> read(memory :> bytesW(word_add a (word(S * j)))) s0 = x j *)
(*                                                                           *)
(* about the input x at a, with S the size of an element (4 for int32, 1 for *)
(* bytes, with word j instead of word(1 * j)), the facts for elements        *)
(* C * i + k, k < C, with their addresses in the form the simulation uses,   *)
(* word_add a (word(S * C * i + S * k)) (and i for 1 * i when C = 1).        *)
(* ------------------------------------------------------------------------- *)

let CHUNK_INPUT_TAC (x:term) (c:int) =
  let k_tm = `k:num` and i_tm = `i:num` in
  let conv =
    EXPAND_CASES_CONV THENC
    REWRITE_CONV[ADD_CLAUSES; LEFT_ADD_DISTRIB; MULT_ASSOC] THENC
    ONCE_DEPTH_CONV NUM_MULT_CONV THENC
    REWRITE_CONV[ADD_CLAUSES; MULT_CLAUSES; WORD_ADD_0] THENC
    ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV in
  FIRST_ASSUM(fun th ->
    if not(is_forall(concl th) && free_in x (concl th)) then NO_TAC else
    let j,bod = dest_forall(concl th) in
    let eqn = rand bod in
    let ck = mk_binop `(+):num->num->num`
              (mk_binop `( * ):num->num->num` (mk_small_numeral c) i_tm)
              k_tm in
    let t = mk_forall(k_tm,mk_imp(mk_binop `(<):num->num->bool` k_tm
                                    (mk_small_numeral c),
                                  subst [ck,j] eqn)) in
    SUBGOAL_THEN t (STRIP_ASSUME_TAC o CONV_RULE conv) THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC th THEN ASM_ARITH_TAC;
      ALL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* An equation between word expressions in the values x t of the inputs,     *)
(* by bit-blasting with each x t as a variable.                              *)
(* ------------------------------------------------------------------------- *)

let APP_BLAST_TAC (f:term) =
  W(fun (asl,w) ->
    let apps = setify (find_terms (fun t -> is_comb t && rator t = f) w) in
    let vs = map (fun t -> genvar(type_of t)) apps in
    let th = BITBLAST_RULE (subst (zip vs apps) w) in
    ACCEPT_TAC (INST (zip apps vs) th));;

(* ------------------------------------------------------------------------- *)
(* Where the code stores several outputs at r with one 64-bit or 128-bit     *)
(* store, split the fact about the wide store at word_add r e into facts     *)
(* about the outputs, of W = 8 or 32 bits, at word_add r (word(e + k)), with *)
(* the constants of e + k added up.                                          *)
(* ------------------------------------------------------------------------- *)

let WIDE_STORE_SPLIT_TAC (r:term) (w:int) =
  let split name k =
    REPEAT(FIRST_X_ASSUM(fun th ->
      let c = concl th in
      try let l,_ = dest_eq c in
          let comp = rand(rator l) in
          let bytesf,addr = dest_comb(rand comp) in
          let a0,_ = dest_binop `word_add:int64->int64->int64` addr in
          if fst(dest_const bytesf) = name && a0 = r then
            STRIP_ASSUME_TAC
             (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                        ONCE_DEPTH_CONV
                         (CHANGED_CONV(REWRITE_CONV[GSYM ADD_ASSOC]) THENC
                          NUM_REDUCE_CONV))
                (CONV_RULE(READ_MEMORY_SPLIT_CONV k) th))
          else NO_TAC
      with Failure _ -> NO_TAC)) in
  if w = 8 then split "bytes128" 4 THEN split "bytes64" 3
  else if w = 32 then split "bytes128" 2 THEN split "bytes64" 1
  else failwith "WIDE_STORE_SPLIT_TAC";;

(* ------------------------------------------------------------------------- *)
(* Where the code loads a byte of a 32-bit input at a, add facts about the   *)
(* 4 bytes of each 32-bit input fact of the iteration, keeping the facts.    *)
(* ------------------------------------------------------------------------- *)

let INPUT_BYTES_SPLIT_TAC (a:term) =
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let l,_ = dest_eq(concl th) in
      let bytesf,addr = dest_comb(rand(rand(rator l))) in
      let a0,_ = dest_binop `word_add:int64->int64->int64` addr in
      if fst(dest_const bytesf) = "bytes32" && a0 = a then
        CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
          (CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th)
      else failwith "INPUT_BYTES_SPLIT_TAC") asl in
    MAP_EVERY STRIP_ASSUME_TAC ths);;

(* ------------------------------------------------------------------------- *)
(* The end of the body of iteration i of a loop that writes B outputs at r,  *)
(* r + S * j for output j, in the order of the spec function f with          *)
(* definition fdef: the invariant for i + 1, with the new outputs, as        *)
(* computed by the simulation, equal to f x (B * i + k) by bit-blasting      *)
(* with the inputs x t as variables.                                         *)
(* ------------------------------------------------------------------------- *)

let CHUNK_FINAL_TAC fdef (x:term) =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  REWRITE_TAC[CHUNK_OUTPUT_SPLIT; CHUNK_OUTPUT_SPLIT_1] THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[fdef] THEN
  SIMP_TAC[DIVMOD_CHUNK; ARITH] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ADD_CLAUSES; LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN APP_BLAST_TAC x;;
