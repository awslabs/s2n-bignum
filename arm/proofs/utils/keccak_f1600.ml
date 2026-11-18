(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Keccak-f[1600] on a state in the memory of an AArch64 state: if the 25    *)
(* lanes at address a are the 24 rounds "keccak 24" of keccak_spec.ml on the *)
(* lanes of a 1600-bit word S, then wbytes reads keccak_f1600 S of           *)
(* common/fips202/fips202.ml at a (KECCAK_F1600_MEMORY). It rests on         *)
(* KECCAK_F1600_BRIDGE of common/fips202/properties/keccak_f1600.ml, which   *)
(* relates keccak_f1600 to "keccak 24". The lemmas about the padding and the *)
(* sponge are in keccak_fips202.ml, which loads this file.                   *)
(* ========================================================================= *)

needs "common/par.ml";;
needs "common/fips202/properties/fips202_properties.ml";;
needs "arm/proofs/utils/keccak_spec.ml";;
needs "common/fips202/properties/keccak_f1600.ml";;

let READ_MEMORY_WBYTES_KECCAK = prove
 (`!a (S:1600 word) s:armstate.
        read (memory :> wbytes a) s = S <=>
        wordlist_from_memory(a,25) s =
        (wordlist_of_num 25 (val S):int64 list)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM VAL_EQ] THEN
  REWRITE_TAC[WORDLIST_FROM_MEMORY] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `num_of_wordlist:int64 list->num`) THEN
  REWRITE_TAC[NUM_OF_WORDLIST_OF_NUM; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `S:1600 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`] THEN
  MP_TAC(ISPECL [`a:int64`; `200`; `read memory (s:armstate)`]
                READ_BYTES_BOUND) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT]);;

let WORDLIST_FROM_MEMORY_KECCAK = prove
 (`!a l s:armstate.
        wordlist_from_memory(a,25) s = l
        ==> read (memory :> wbytes a) s = keccak_state(keccak_table l)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SIMP_TAC[KECCAK_STATE_TABLE; LENGTH_WORDLIST_FROM_MEMORY] THEN
  GEN_REWRITE_TAC I [GSYM VAL_EQ] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; VAL_READ_WBYTES; VAL_WORD] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE; NUM_OF_WORDLIST_FROM_MEMORY;
              DIMINDEX_8; DIMINDEX_64; DIMINDEX_CONV `dimindex(:1600)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  MP_TAC(ISPECL [`a:int64`; `200`; `read memory (s:armstate)`]
                READ_BYTES_BOUND) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The permutation of a state in memory, in the form of the code proofs.     *)
(* ------------------------------------------------------------------------- *)

let KECCAK_F1600_MEMORY = prove
 (`!a (S:1600 word) s:armstate.
        wordlist_from_memory(a,25) s = keccak 24 (wordlist_of_num 25 (val S))
        ==> read (memory :> wbytes a) s = keccak_f1600 S`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP WORDLIST_FROM_MEMORY_KECCAK) THEN
  W(MP_TAC o PART_MATCH (rand o rand) KECCAK_F1600_BRIDGE o lhand o snd) THEN
  REWRITE_TAC[LENGTH_WORDLIST_OF_NUM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN
  SIMP_TAC[KECCAK_STATE_TABLE; LENGTH_WORDLIST_OF_NUM] THEN
  REWRITE_TAC[NUM_OF_WORDLIST_OF_NUM; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPEC `S:1600 word` VAL_BOUND) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:1600)`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOD_LT; WORD_VAL]);;
