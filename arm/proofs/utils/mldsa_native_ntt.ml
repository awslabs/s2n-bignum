(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Tools for the proofs of the NTT and inverse NTT of mldsa-native that do   *)
(* not depend on the build: the table of zetas as the bytes of the           *)
(* read-only data, the Montgomery multiplication as the compiled code does   *)
(* it with scalar registers, and tactics for the lemmas of their FULL        *)
(* proofs.                                                                   *)
(* ========================================================================= *)

(* The part that depends on AArch64; the rest is in                          *)
(* common/fips204/properties/mldsa_native_ntt.ml.                            *)

needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_poly.ml";;
needs "common/fips204/properties/mldsa_native_ntt.ml";;

let READ_MEMORY_BYTES32_NUM_OF_WORDLIST = prove
 (`!a:int64 (l:int32 list) n j s:armstate.
        read (memory :> bytes(a,4 * n)) s = num_of_wordlist l /\
        LENGTH l = n /\ j < n
        ==> read (memory :> bytes32(word_add a (word(4 * j)))) s = EL j l`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN
  MP_TAC(ISPECL [`l:int32 list`; `j:num`] NUM_OF_WORDLIST_EL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && is_comb(lhs(concl th)) &&
       can (term_match [] `read c s`) (lhs(concl th))
    then REWRITE_TAC[GSYM th] else failwith "") THEN
  REWRITE_TAC[BYTES32_WBYTES; READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  REWRITE_TAC[DIMINDEX_32] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `32 * j = 8 * (4 * j)`;
              ARITH_RULE `4294967296 = 2 EXP (8 * 4)`;
              READ_BYTES_DIV; READ_BYTES_MOD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[PAIR_EQ] THEN ASM_ARITH_TAC);;

let MLD_ZETAS_LOADED = prove
 (`!z s. bytes_loaded s z mld_zetas_data
         ==> !k. k < 256
                 ==> read(memory :> bytes32(word_add z (word(4 * k)))) s =
                     mld_zeta k`,
  REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES; LENGTH_MLD_ZETAS_DATA;
              MLD_ZETAS_DATA; mld_zeta] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`z:int64`; `MAP iword mld_zetas:int32 list`; `256`;
                 `k:num`; `s:armstate`]
         READ_MEMORY_BYTES32_NUM_OF_WORDLIST) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; LENGTH_MLD_ZETAS; ARITH] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC EL_MAP THEN
  ASM_REWRITE_TAC[LENGTH_MLD_ZETAS]);;
