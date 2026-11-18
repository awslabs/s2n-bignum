(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the packing and unpacking loops of mldsa-native,  *)
(* which handle a group of C coefficients and B bytes in each iteration i:   *)
(* coefficients C * i + k and bytes B * i + k. These are the tools of        *)
(* arm/proofs/utils/mldsa_native_pack.ml for the x86 model (but for          *)
(* CHUNK_FINAL_TAC, for correctness proofs alone, which the x86 proofs do    *)
(* not use), with some for the addresses and the byte registers of the x86   *)
(* code.                                                                     *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;
needs "common/fips204/properties/mldsa_native_pack.ml";;

(* ------------------------------------------------------------------------- *)
(* Where the code stores several outputs at r with one 32-bit, 64-bit or     *)
(* 128-bit store, split the fact about the wide store at word_add r e into   *)
(* facts about the outputs, of W = 8 or 32 bits, at                          *)
(* word_add r (word(e + k)), with the constants of e + k added up.           *)
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
  if w = 8 then
    split "bytes128" 4 THEN split "bytes64" 3 THEN split "bytes32" 2
  else if w = 32 then split "bytes128" 2 THEN split "bytes64" 1
  else failwith "WIDE_STORE_SPLIT_TAC";;

(* ------------------------------------------------------------------------- *)
(* Where the code loads a byte of a 32-bit input at a, add facts about the   *)
(* 4 bytes of each 32-bit input fact of the iteration, keeping the facts,    *)
(* with the constants of the offsets added up.                               *)
(* ------------------------------------------------------------------------- *)

let INPUT_BYTES_SPLIT_TAC (a:term) =
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let l,_ = dest_eq(concl th) in
      let bytesf,addr = dest_comb(rand(rand(rator l))) in
      let a0,_ = dest_binop `word_add:int64->int64->int64` addr in
      if fst(dest_const bytesf) = "bytes32" && a0 = a then
        CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                  ONCE_DEPTH_CONV
                   (CHANGED_CONV(REWRITE_CONV[GSYM ADD_ASSOC]) THENC
                    NUM_REDUCE_CONV))
          (CONV_RULE(READ_MEMORY_SPLIT_CONV 2) th)
      else failwith "INPUT_BYTES_SPLIT_TAC") asl in
    MAP_EVERY STRIP_ASSUME_TAC ths);;

(* ------------------------------------------------------------------------- *)
(* The x86 code often advances a pointer p = word_add a (word(S * i)) by the *)
(* size of a group at the start of the body and then addresses the elements  *)
(* at negative displacements from it, and the simulation then leaves their   *)
(* addresses in the form word_add (word_add a (word(S * i))) (word k) rather *)
(* than word_add a (word(S * i + k)), the form of the facts from             *)
(* CHUNK_INPUT_TAC and INPUT_BYTES_SPLIT_TAC. INPUT_ALT_ADDR_TAC a adds a    *)
(* copy of each fact about memory at word_add a (word(m + k)), k a numeral,  *)
(* with the address in the first form, so that the reads find their values   *)
(* in either form. At the end of the body, ADDR_NORMALIZE_TAC puts the       *)
(* addresses of the facts about the new state, such as those of the stores,  *)
(* in the second form, the form of the outputs in the invariant.             *)
(* ------------------------------------------------------------------------- *)

let WORD_ADD_SPLIT_ADDR = prove
 (`!a:int64 m n. word_add a (word(m + n)) =
                 word_add (word_add a (word m)) (word n)`,
  REWRITE_TAC[WORD_ADD; WORD_ADD_ASSOC]);;

let INPUT_ALT_ADDR_TAC (a:term) =
  let rule = GEN_REWRITE_RULE
    (LAND_CONV o RATOR_CONV o RAND_CONV o RAND_CONV o RAND_CONV)
    [WORD_ADD_SPLIT_ADDR] in
  W(fun (asl,w) ->
    let ths = mapfilter (fun (_,th) ->
      let l,_ = dest_eq(concl th) in
      let addr = rand(rand(rand(rator l))) in
      let a0,off = dest_binop `word_add:int64->int64->int64` addr in
      let s = rand off in
      if a0 = a && is_binary "+" s && is_numeral(rand s) then rule th
      else failwith "INPUT_ALT_ADDR_TAC") asl in
    MAP_EVERY ASSUME_TAC ths);;

let ADDR_NORMALIZE_TAC =
  let pat = `read (memory :> c) (s:x86state) = v` in
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] pat) (concl th) then
      CONV_RULE(LAND_CONV(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)) th
    else th);;

(* ------------------------------------------------------------------------- *)
(* The simulation gives the low byte of a register with value v as           *)
(* word(val v MOD 256) (as in the x86 mlkem-native proofs), and its second   *)
(* byte (AH, BH, CH or DH) as word((val v DIV 256) MOD 256).                 *)
(* ------------------------------------------------------------------------- *)

let WORD_VAL_MOD_256 = prove
 (`!x:N word. word (val x MOD 256):byte = word_zx x`,
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `256 = 2 EXP 8`] THEN
  REWRITE_TAC[GSYM DIMINDEX_8; WORD_MOD_SIZE; word_zx]);;

let WORD_VAL_DIV_256_MOD_256 = prove
 (`!x:N word. word((val x DIV 256) MOD 256):byte = word_subword x (8,8)`,
  REWRITE_TAC[word_subword] THEN CONV_TAC NUM_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The end of the body of iteration i of a loop that writes B outputs at r,  *)
(* r + S * j for output j, in the order of the spec function f with          *)
(* definition fdef, in a FULL proof, where the loop test is the end of the   *)
(* body (see utils/mldsa_native_full.ml): the invariant for i + 1, with the  *)
(* new outputs, as computed by the simulation, equal to f x (B * i + k) by   *)
(* bit-blasting with the inputs x t as variables, the instruction pointer    *)
(* after the branch and the events of the iteration. The addresses of the    *)
(* facts about memory are first put in the form of the invariant by          *)
(* ADDR_NORMALIZE_TAC, and the bytes of registers in the values rewritten    *)
(* with the two lemmas above.                                                *)
(* ------------------------------------------------------------------------- *)

let CHUNK_FULL_FINAL_TAC fdef (x:term) =
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
      SIMP_TAC[DIVMOD_CHUNK; ARITH] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_CLAUSES; LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_REWRITE_TAC[WORD_VAL_MOD_256; WORD_VAL_DIV_256_MOD_256] THEN
      REPEAT CONJ_TAC THEN APP_BLAST_TAC x THEN
      NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;
