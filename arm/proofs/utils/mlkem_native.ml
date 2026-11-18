(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics shared by the proofs of code compiled from the C       *)
(* implementation in mlkem-native (see arm/mlkem_native/README.md).          *)
(* ========================================================================= *)

(* The part that depends on AArch64; the rest is in                          *)
(* common/fips203/properties/mlkem_native.ml.                                *)

needs "arm/proofs/base.ml";;
needs "common/mlkem_mldsa.ml";;
needs "common/fips203/properties/mlkem_native.ml";;

(* ------------------------------------------------------------------------- *)
(* Reading arrays given as lists, and building byte arrays incrementally.    *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_BYTES16_NUM_OF_WORDLIST = prove
 (`!a:int64 (l:int16 list) n j s:armstate.
        read (memory :> bytes(a,2 * n)) s = num_of_wordlist l /\
        LENGTH l = n /\ j < n
        ==> read (memory :> bytes16(word_add a (word(2 * j)))) s = EL j l`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`l:int16 list`; `j:num`] NUM_OF_WORDLIST_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && is_comb(lhs(concl th)) &&
       can (term_match [] `read c s`) (lhs(concl th))
    then REWRITE_TAC[GSYM th] else failwith "") THEN
  REWRITE_TAC[BYTES16_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `16 * j = 8 * (2 * j)`;
              ARITH_RULE `65536 = 2 EXP (8 * 2)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let READ_MEMORY_BYTES_SNOC = prove
 (`!x:int64 n s:armstate.
        read (memory :> bytes(x,n + 1)) s =
        read (memory :> bytes(x,n)) s +
        2 EXP (8 * n) * val(read (memory :> bytes8(word_add x (word n))) s)`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE; READ_BYTES_BYTES8]);;

let MLK_ZETAS_LOADED = prove
 (`!z s. bytes_loaded s (word z) mlk_zetas_data
         ==> !k. k < 128
                 ==> read(memory :> bytes16(word_add (word z) (word(2 * k))))
                     s = iword(EL k mlk_zetas)`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; LENGTH_MLK_ZETAS_DATA;
              MLK_ZETAS_DATA] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`word z:int64`; `MAP iword mlk_zetas:int16 list`; `128`;
                 `k:num`; `s:armstate`]
         READ_MEMORY_BYTES16_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_MLK_ZETAS; ARITH] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC EL_MAP THEN
  ASM_REWRITE_TAC[LENGTH_MLK_ZETAS]);;

let W32_DECIDE_FLAGS_TAC =
  W32_SMALL_TAC THEN
  CMP_FLAGS_TAC `word_sub (word x) (word y):int32` WORD_CMP_32_FLAGS;;
