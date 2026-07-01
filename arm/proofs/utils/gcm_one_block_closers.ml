(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)
(* ========================================================================= *)
(* 1-block GHASH and partial-block closers for the AES-256-GCM band proof.   *)
(* Pure algebra (no machine code, no symbolic simulation).                   *)
(* ========================================================================= *)

needs "arm/proofs/utils/gcm_aesgcm_nblock_helpers.ml";;

(* ===== 1-block GHASH Karatsuba spec ====================================== *)
(* Base case: the spec and its two direct bridges (to polyval_dot, then to    *)
(* ghash_polyval_acc) live together; there is no GHASH_1BLOCK_AS_NBLOCK.       *)

let ghash_1block_karatsuba = new_definition
 `ghash_1block_karatsuba (input:int128) (h:int128) (hk:int128) : int128 =
  let a_lo:64 word = word_subword input (0,64) in
  let a_hi:64 word = word_subword input (64,64) in
  let h_lo:64 word = word_subword h (0,64) in
  let h_hi:64 word = word_subword h (64,64) in
  let hk_lo:64 word = word_subword hk (0,64) in
  let pl:int128 = word_pmul a_lo h_hi in
  let ph:int128 = word_pmul a_hi h_lo in
  let pm:int128 = word_pmul (word_xor a_lo a_hi) hk_lo in
  let mid:int128 = word_xor (word_xor pm ph) pl in
  let a:64 word = word_subword pl (0,64) in
  let b:64 word = word_xor (word_subword pl (64,64)) (word_subword mid (0,64)) in
  let c:64 word = word_xor (word_subword ph (0,64)) (word_subword mid (64,64)) in
  let d:64 word = word_subword ph (64,64) in
  let w:64 word = word 13979173243358019584 in
  let wa:128 word = word_pmul a w in
  let wa_lo:64 word = word_subword wa (0,64) in
  let wa_hi:64 word = word_subword wa (64,64) in
  let v:64 word = word_xor b wa_lo in
  let u:64 word = word_xor (word_xor c a) wa_hi in
  let wv:128 word = word_pmul v w in
  let wv_lo:64 word = word_subword wv (0,64) in
  let wv_hi:64 word = word_subword wv (64,64) in
  let f:64 word = word_xor u wv_lo in
  let g:64 word = word_xor (word_xor d v) wv_hi in
  word_reversefields 8 (word_join g f : 128 word)`;;

let GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT = prove(
  `!(input:int128) (h:int128) (hk:int128).
    word_subword hk (0,64):(64)word = karatsuba_mid h
    ==> ghash_1block_karatsuba input (word_swaphalves128 h) hk =
        word_reversefields 8 (polyval_dot input h)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[ghash_1block_karatsuba; LET_DEF; LET_END_DEF;
              SWAPHALVES128_SUBWORD_LO; SWAPHALVES128_SUBWORD_HI;
              REWRITE_RULE[LET_DEF; LET_END_DEF] POLYVAL_DOT_KARATSUBA] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ASM_REWRITE_TAC[karatsuba_mid] THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  CONV_TAC(TOP_DEPTH_CONV PMUL_NORM_CONV) THEN
  REWRITE_TAC[WORD_XOR_ASSOC] THEN
  REWRITE_TAC[GSYM WORD_XOR_ASSOC] THEN
  REWRITE_TAC[WORD_SUBWORD_XOR_COMM] THEN
  REWRITE_TAC[WORD_XOR_ASSOC]);;

let GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_ACC = prove
 (`!(b1:int128) (h:int128) (hk:int128).
    word_subword hk (0,64):(64)word = karatsuba_mid h
    ==> ghash_1block_karatsuba b1 (word_swaphalves128 h) hk =
        word_reversefields 8 (polyval_reduce_prop3 (word_pmul b1 h : 256 word))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[GHASH_1BLOCK_KARATSUBA_EQ_POLYVAL_DOT] THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC(ISPEC `128` MOD_POLYVAL_CANCEL_VARPOW) THEN
  MATCH_MP_TAC MOD_POLYVAL_TRANS THEN
  EXISTS_TAC `ring_mul bool_poly (poly_of_word (b1:int128)) (poly_of_word (h:int128))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[POLYVAL_DOT_CORRECT];
    ONCE_REWRITE_TAC[MOD_POLYVAL_SYM] THEN
    MP_TAC(ISPECL [`word_pmul (b1:int128) (h:int128) : 256 word`] POLYVAL_REDUCE_PROP3_CORRECT) THEN
    REWRITE_TAC[POLY_OF_WORD_PMUL_2N]]);;

(* ===== Per-block ciphertext closers + partial-final-block helpers ======== *)

(* The returned byte length: x9 = (8*byte_len) >> 3 = byte_len for byte_len <= 16. *)
let ONE_BLOCK_USHR_BYTELEN = prove
 (`!byte_len. byte_len <= 16
     ==> word_ushr (word (8 * byte_len):int64) 3 = word byte_len`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[word_ushr] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `val (word (8 * byte_len):int64) = 8 * byte_len` SUBST1_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ARITH_TAC);;

(* The masked ciphertext written by the bif store: masking the already-masked
   block again with the same mask is idempotent. *)
let ONE_BLOCK_MASK_IDEM = prove
 (`!(ct:int128) (mask:int128).
     word_and (word_and mask ct) mask = word_and ct mask`,
  CONV_TAC WORD_BITWISE_RULE);;

(* Ciphertext closure, 1-block instance (ivec_1 = ivec, no gcm_ctr_inc). *)
let GCM_1BLOCK_CT1_STEP_TAC = GCM_NBLOCK_CT1_STEP_TAC 1;;
