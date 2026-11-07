(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Initialization of a SHAKE256 context: the proof (see                      *)
(* shake256_init_spec.ml).                                                   *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_O2/shake256_init_spec.ml";;

let MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  let zl = mk_list(replicate `word 0:int64` 25,`:int64`) in
  let zth = prove
   (mk_eq(`0`,mk_comb(`num_of_wordlist:int64 list->num`,zl)),
    REWRITE_TAC[num_of_wordlist; VAL_WORD_0] THEN ARITH_TAC) in
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  REPEAT STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLDSA_NATIVE_SHAKE256_INIT_GCC12_O2_EXEC
   (1--10) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[READ_MEMORY_WBYTES_1600; VAL_WORD_0] THEN
  RULE_ASSUM_TAC(fun th ->
    if can (term_match [] `read (memory :> bytes128 a) s = word 0`) (concl th)
    then CONV_RULE(READ_MEMORY_SPLIT_CONV 1 THENC
                   ONCE_DEPTH_CONV WORD_REDUCE_CONV) th
    else th) THEN
  GEN_REWRITE_TAC RAND_CONV [zth] THEN
  CONV_TAC BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV THEN
  REWRITE_TAC[GSYM BYTES64_WBYTES] THEN ASM_REWRITE_TAC[]);;
