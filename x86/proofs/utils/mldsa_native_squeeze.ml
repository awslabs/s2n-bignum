(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas for the proofs of mldsa-native's squeezing of bytes from a SHAKE   *)
(* context (shake128_squeeze and shake256_squeeze): the bytes that one call  *)
(* of mldsa_keccakf1600_extract_bytes copies are a run of the bytes          *)
(* mld_keccak_squeeze_byte of common/mldsa_native_fips202.ml. These are the  *)
(* lemmas of arm/proofs/utils/mldsa_native_squeeze.ml, which do not depend   *)
(* on the machine.                                                           *)
(* ========================================================================= *)

needs "x86/proofs/utils/mldsa_native_absorb.ml";;
needs "x86/proofs/utils/keccak_fips202.ml";;
needs "common/mldsa_native_fips202.ml";;

let SQUEEZE_DIMINDEX_1600 = DIMINDEX_CONV `dimindex(:1600)`;;

(*** n bytes of a state from byte p on, as a number ***)

let NUM_OF_BYTELIST_STATE_BYTES_OFFSET = prove
 (`!(S:1600 word) p n.
        p + n <= 200
        ==> num_of_bytelist(list_of_seq (\i. word_subword S (8 * (p + i),8))
                                        n) =
            (val S DIV 2 EXP (8 * p)) MOD 2 EXP (8 * n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `val(word(val(S:1600 word) DIV 2 EXP (8 * p)):1600 word) =
                val S DIV 2 EXP (8 * p)` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[SQUEEZE_DIMINDEX_1600] THEN
    TRANS_TAC LET_TRANS `val(S:1600 word)` THEN REWRITE_TAC[DIV_LE] THEN
    MP_TAC(ISPEC `S:1600 word` VAL_BOUND) THEN
    REWRITE_TAC[SQUEEZE_DIMINDEX_1600];
    ALL_TAC] THEN
  MP_TAC(SPECL [`word(val(S:1600 word) DIV 2 EXP (8 * p)):1600 word`; `n:num`]
    NUM_OF_BYTELIST_STATE_BYTES) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
  MATCH_MP_TAC LIST_OF_SEQ_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[word_subword] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; LEFT_ADD_DISTRIB]);;

(*** The i squeezed bytes from offset off of the output on, when they     ***)
(*** all come from the state after B permutations, from its byte p on     ***)

let SQUEEZE_CHUNK = prove
 (`!r (S:1600 word) pos off B p i.
        0 < r /\ r <= 200 /\ pos + off = r * B + p /\ p + i <= r
        ==> num_of_bytelist
             (list_of_seq (\j. mld_keccak_squeeze_byte r S pos (off + j)) i) =
            (val(keccak_squeeze B S) DIV 2 EXP (8 * p)) MOD 2 EXP (8 * i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`keccak_squeeze B (S:1600 word)`; `p:num`; `i:num`]
    NUM_OF_BYTELIST_STATE_BYTES_OFFSET) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[mld_keccak_squeeze_byte] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN `pos + off + j = r * B + (p + j)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(r * B + (p + j)) DIV r = B /\ (r * B + (p + j)) MOD r = p + j`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `p + j`;
      MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `B:num`] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_ARITH_TAC;
    REFL_TAC]);;

(*** The same from the start of the output and of the state ***)

let SQUEEZE_CHUNK_0 = prove
 (`!r (S:1600 word) pos i.
        0 < r /\ r <= 200 /\ pos + i <= r
        ==> num_of_bytelist
             (list_of_seq (mld_keccak_squeeze_byte r S pos) i) =
            (val S DIV 2 EXP (8 * pos)) MOD 2 EXP (8 * i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`r:num`; `S:1600 word`; `pos:num`; `0`; `0`; `pos:num`;
                `i:num`] SQUEEZE_CHUNK) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; keccak_squeeze; ETA_AX]);;

(*** The value of a 64-bit word below the size of the address space ***)

let SQUEEZE_VAL_WORD_LE = prove
 (`!x n. x <= n /\ 204 + n <= 18446744073709551616
         ==> val(word x:int64) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
  REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC);;
