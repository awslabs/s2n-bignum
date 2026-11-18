(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the packing and unpacking loops of mldsa-native,  *)
(* which handle a group of C coefficients and B bytes in each iteration i:   *)
(* coefficients C * i + k and bytes B * i + k.                               *)
(* ========================================================================= *)

(* The part that depends on AArch64; the rest is in                          *)
(* common/fips204/properties/mldsa_native_pack.ml.                           *)

needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;
needs "common/fips204/properties/mldsa_native_pack.ml";;

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

(*** The same in a FULL proof, where the loop test is the end of the body ***)
(*** (see utils/mldsa_native_full.ml): also the PC after the branch and   ***)
(*** the events of the iteration                                          ***)

let CHUNK_FULL_FINAL_TAC fdef (x:term) =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC[CHUNK_OUTPUT_SPLIT; CHUNK_OUTPUT_SPLIT_1] THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      REWRITE_TAC[fdef] THEN
      SIMP_TAC[DIVMOD_CHUNK; ARITH] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_CLAUSES; LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN APP_BLAST_TAC x THEN
      NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;
