(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* NIST GHASH definitions: bit_reflect128, nist_dot, nist_ghash.             *)
(*                                                                           *)
(* Lightweight file containing only definitions and simple lemmas, without   *)
(* the heavy polynomial algebra proofs. The full NIST ↔ POLYVAL bridge       *)
(* (Gueron Proposition 1) lives in common/ghash_nist_bridge.ml.              *)
(* ========================================================================= *)

needs "common/ghash.ml";;

(* ========================================================================= *)
(* bit_reflect128: bit-reversal on 128-bit words (bit i ↦ bit 127-i).        *)
(* ========================================================================= *)

let bit_reflect128 = new_definition
  `bit_reflect128 (a:int128) : int128 = word_reversefields 1 a`;;

(* bit i (bit_reflect128 a) <=> bit (127 - i) a, for i < 128                 *)
let BIT_REFLECT128 = prove
 (`!a:int128. !i. i < 128
    ==> (bit i (bit_reflect128 a) <=> bit (127 - i) a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bit_reflect128; BIT_WORD_REVERSEFIELDS] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[ARITH_RULE `i < 128 ==> i < 1 * 128`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* bit_reflect128 is an involution                                           *)
let REFLECT128_INVOLUTION = prove
 (`!a:int128. bit_reflect128 (bit_reflect128 a) = a`,
  GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[BIT_REFLECT128] THEN
  SUBGOAL_THEN `127 - i < 128` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[BIT_REFLECT128] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

(* bit_reflect128 distributes over XOR                                       *)
let REFLECT128_XOR = prove
 (`!a b:int128. bit_reflect128 (word_xor a b) =
                word_xor (bit_reflect128 a) (bit_reflect128 b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[BIT_REFLECT128; BIT_WORD_XOR; DIMINDEX_128;
               ARITH_RULE `i < 128 ==> 127 - i < 128`]);;

(* bit_reflect128 of zero is zero                                            *)
let REFLECT128_0 = prove
 (`bit_reflect128 (word 0 : int128) = word 0`,
  REWRITE_TAC[WORD_EQ_BITS_ALT] THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[BIT_REFLECT128; BIT_WORD_0]);;

(* Helper: bit index must be < 128 for 128-bit words                         *)
let BIT_LT_128 = prove
 (`!(w:int128) i. bit i w ==> i < 128`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_LT; NOT_CLAUSES] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`w:int128`; `i:num`] BIT_TRIVIAL) THEN
  REWRITE_TAC[DIMINDEX_128] THEN ASM_REWRITE_TAC[]);;

let BIT_TRIVIAL_128 = prove
 (`!(w:int128) i. 128 <= i ==> ~bit i w`,
  MESON_TAC[BIT_LT_128; NOT_LT]);;

(* ========================================================================= *)
(* nist_dot: NIST GF(2^128) multiply (SP 800-38D Section 6.3).               *)
(* Bit-reflect inputs, carry-less multiply, reduce mod P(x), reflect result. *)
(* ========================================================================= *)

let nist_dot = new_definition
  `nist_dot (a:int128) (b:int128) : int128 =
   bit_reflect128(ghash_reduce(word_pmul (bit_reflect128 a) (bit_reflect128 b)))`;;

(* ========================================================================= *)
(* nist_ghash: recursive GHASH per NIST SP 800-38D Algorithm 2.              *)
(* ========================================================================= *)

let nist_ghash = define
 `nist_ghash (h:int128) (acc:int128) [] = acc /\
  nist_ghash h acc (CONS x xs) =
    nist_ghash h (nist_dot (word_xor acc x) h) xs`;;

let NIST_GHASH_NIL = prove
 (`!h acc. nist_ghash h acc [] = acc`,
  REWRITE_TAC[nist_ghash]);;

let NIST_GHASH_CONS = prove
 (`!h acc x xs. nist_ghash h acc (CONS x xs) =
                nist_ghash h (nist_dot (word_xor acc x) h) xs`,
  REWRITE_TAC[nist_ghash]);;
