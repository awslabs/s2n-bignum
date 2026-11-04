(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES-GCM specification per NIST SP 800-38D.                                *)
(*                                                                           *)
(* Defines inc32 (Sec 6.2), GCTR (Alg 3), GF(2^128) mul (Alg 1/Sec 6.3),     *)
(* GHASH (Alg 2), GCM-AE (Alg 4), GCM-AD (Alg 5).                            *)
(* Simplified to 96-bit IVs, full 128-bit blocks, and pre-expanded keys.     *)
(* GCTR/GCM-AE/GCM-AD take the block cipher as a parameter, so the same      *)
(* definitions serve AES-128 and AES-256 (from common/fips197.ml).           *)
(*                                                                           *)
(* The GF(2^128) multiply and GHASH fold are reused from                     *)
(* common/ghash_nist_defs.ml (nist_dot, nist_ghash) rather than redefined    *)
(* here, so there is a single definition of each in common/.  The            *)
(* conversions evaluate the definitions on concrete blocks; the known-answer *)
(* tests that use them are in common/gcm_kats.ml.                            *)
(* ========================================================================= *)

needs "common/fips197.ml";;
needs "common/ghash_nist_defs.ml";;
needs "common/karatsuba_pmul.ml";;

(* ========================================================================= *)
(* inc32: increment the rightmost 32 bits of a 128-bit block (SP 800-38D     *)
(* Section 6.2). The leftmost 96 bits are unchanged.                         *)
(* ========================================================================= *)

let inc32 = new_definition
  `inc32 (cb:128 word) : 128 word =
    let top96:96 word = word_subword cb (32,96) in
    let bot32:32 word = word_subword cb (0,32) in
    word_join top96 (word_add bot32 (word 1 : 32 word)) : 128 word`;;

let INC32_CONV =
  REWRITE_CONV [inc32] THENC
  TOP_DEPTH_CONV let_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

(* ========================================================================= *)
(* GCTR: NIST SP 800-38D Algorithm 3 (counter-mode encryption).              *)
(*                                                                           *)
(* Operates on full 128-bit blocks. Partial last block handling is deferred  *)
(* to the GCM-AE/AD layer. The block cipher enc is a parameter (instantiate  *)
(* with aes128_cipher or aes256_cipher from fips197.ml).                     *)
(* ========================================================================= *)

let gctr = define
  `gctr (enc:(128 word)->((128 word) list)->(128 word))
        (ks:(128 word) list) (icb:128 word) ([] : (128 word) list) =
     ([] : (128 word) list) /\
   gctr enc ks icb (CONS x rest) =
     CONS (word_xor x (enc icb ks)) (gctr enc ks (inc32 icb) rest)`;;

let GCTR_STEP_CONV cipher_def ks_def =
  ONCE_REWRITE_CONV [gctr] THENC
  REWRITE_CONV [ks_def] THENC
  ONCE_DEPTH_CONV (FIPS197_ENCRYPT_CONV cipher_def ks_def) THENC
  DEPTH_CONV WORD_RED_CONV THENC
  ONCE_DEPTH_CONV (REWRITE_CONV [inc32] THENC
    TOP_DEPTH_CONV let_CONV THENC
    DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV));;

let rec GCTR_CONV cipher_def ks_def tm =
  try
    let th = GCTR_STEP_CONV cipher_def ks_def tm in
    let rhs = rand (concl th) in
    (try let th2 = RAND_CONV (GCTR_CONV cipher_def ks_def) rhs in TRANS th th2
     with _ -> th)
  with _ -> REWRITE_CONV [gctr] tm;;

let GCTR_STEP_FAST_CONV cipher_def ks_def =
  ONCE_REWRITE_CONV [gctr] THENC
  REWRITE_CONV [ks_def] THENC
  ONCE_DEPTH_CONV (FIPS197_ENCRYPT_FAST_CONV cipher_def ks_def) THENC
  DEPTH_CONV WORD_RED_CONV THENC
  ONCE_DEPTH_CONV (REWRITE_CONV [inc32] THENC
    TOP_DEPTH_CONV let_CONV THENC
    DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV));;

let rec GCTR_FAST_CONV cipher_def ks_def tm =
  try
    let th = GCTR_STEP_FAST_CONV cipher_def ks_def tm in
    let rhs = rand (concl th) in
    (try let th2 = RAND_CONV (GCTR_FAST_CONV cipher_def ks_def) rhs in TRANS th th2
     with _ -> th)
  with _ -> REWRITE_CONV [gctr] tm;;

(* ========================================================================= *)
(* GF(2^128) multiplication: NIST SP 800-38D Section 6.3.                    *)
(*                                                                           *)
(* Multiplication in GF(2^128) with irreducible polynomial                   *)
(* P(x) = x^128 + x^7 + x^2 + x + 1.                                         *)
(*                                                                           *)
(* NIST uses reflected bit ordering (bit 0 = MSB = coefficient of x^0):      *)
(* bit-reverse inputs, carry-less multiply, reduce mod P(x), bit-reverse     *)
(* the result. This is exactly nist_dot from common/ghash_nist_defs.ml, so   *)
(* we reuse it here instead of defining a separate constant.                 *)
(* ========================================================================= *)

let WORD_PMUL_128_CONV =
  let karatsuba = REWRITE_RULE [LET_DEF; LET_END_DEF] PMUL_KARATSUBA in
  REWR_CONV karatsuba THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
  DEPTH_CONV WORD_PMUL_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let NIST_DOT_CONV =
  REWRITE_CONV [nist_dot; bit_reflect128; ghash_reduce; ghash_reduce1] THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
  ONCE_DEPTH_CONV WORD_PMUL_128_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
  ONCE_DEPTH_CONV WORD_PMUL_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
  TRY_CONV(ONCE_DEPTH_CONV WORD_PMUL_CONV THENC
           DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV));;

(* ========================================================================= *)
(* GHASH: NIST SP 800-38D Algorithm 2.                                       *)
(*                                                                           *)
(* GHASH(H, X_1 || ... || X_m) iterates nist_dot:                            *)
(*   Y_0 = 0, Y_i = nist_dot(Y_{i-1} XOR X_i, H).                            *)
(* This is nist_ghash from common/ghash_nist_defs.ml, reused here.           *)
(* Conversions for stepping it on concrete blocks live here.                 *)
(* ========================================================================= *)

let NIST_GHASH_STEP_CONV =
  ONCE_REWRITE_CONV [nist_ghash] THENC
  DEPTH_CONV WORD_RED_CONV THENC
  ONCE_DEPTH_CONV NIST_DOT_CONV;;

(* Fold a whole block list by repeating NIST_GHASH_STEP_CONV until no progress.
   CHANGED_CONV makes the step fail once the term is fully reduced (the base
   case nist_ghash h acc [] -> acc, then a bare word), so REPEATC terminates.
   (An earlier `STEP THENC TRY_CONV NIST_GHASH_CONV` form looped forever: the
   step conv never fails, so the TRY_CONV recursion never stopped.) *)
let NIST_GHASH_CONV = REPEATC (CHANGED_CONV NIST_GHASH_STEP_CONV);;

(* ========================================================================= *)
(* GCM-AE: NIST SP 800-38D Algorithm 4 (authenticated encryption).           *)
(*                                                                           *)
(* Simplified to 96-bit IV, full 128-bit blocks, and 128-bit tag.            *)
(* Key schedule is pre-expanded. Returns (ciphertext, tag).                  *)
(* ========================================================================= *)

let gcm_ae = new_definition
 `gcm_ae (enc:(128 word)->((128 word) list)->(128 word))
         (ks:(128 word) list) (iv:96 word)
         (P:(128 word) list) (A:(128 word) list) =
  let H = enc (word 0) ks in
  let J0 : 128 word = word_join iv (word 1 : 32 word) in
  let C = gctr enc ks (inc32 J0) P in
  let len_block : 128 word =
    word_join (word (128 * LENGTH A) : 64 word)
              (word (128 * LENGTH C) : 64 word) in
  let S = nist_ghash H (word 0) (APPEND A (APPEND C [len_block])) in
  let tag = word_xor S (enc J0 ks) in
  (C, tag)`;;

(* ========================================================================= *)
(* GCM-AD: NIST SP 800-38D Algorithm 5 (authenticated decryption).           *)
(*                                                                           *)
(* Returns SOME plaintext if tag verifies, NONE otherwise.                   *)
(* ========================================================================= *)

let gcm_ad = new_definition
 `gcm_ad (enc:(128 word)->((128 word) list)->(128 word))
         (ks:(128 word) list) (iv:96 word)
         (C:(128 word) list) (A:(128 word) list) (tag:128 word) =
  let H = enc (word 0) ks in
  let J0 : 128 word = word_join iv (word 1 : 32 word) in
  let P = gctr enc ks (inc32 J0) C in
  let len_block : 128 word =
    word_join (word (128 * LENGTH A) : 64 word)
              (word (128 * LENGTH C) : 64 word) in
  let S = nist_ghash H (word 0) (APPEND A (APPEND C [len_block])) in
  let tag' = word_xor S (enc J0 ks) in
  if tag' = tag then SOME P else NONE`;;

(* ========================================================================= *)
(* Evaluation of gcm_ae and gcm_ad on concrete arguments: the bound terms    *)
(* of the definitions' lets are evaluated in order (the cipher with the fast *)
(* conversion, GCTR block by block, GHASH by NIST_GHASH_CONV) and then       *)
(* substituted.  cipher_def is aes128_cipher or aes256_cipher, and ks_def    *)
(* the definition of the key schedule constant used.                         *)
(* ========================================================================= *)

let GCM_GROUND_CONV cipher_def ks_def =
  let encc = FIPS197_ENCRYPT_FAST_CONV cipher_def ks_def
  and gctrc = GCTR_FAST_CONV cipher_def ks_def in
  let cipher_tm = repeat rator (lhs(snd(strip_forall(concl cipher_def))))
  and ks_tm = lhs(concl ks_def) in
  let enc_conv tm =
    match tm with
      Comb(Comb(c,x),k) when c = cipher_tm && k = ks_tm && frees x = [] ->
        encc tm
    | _ -> failwith "enc_conv" in
  let gctr_conv tm =
    match strip_comb tm with
      Const("gctr",_),[_;_;_;_] when frees tm = [] ->
        (RATOR_CONV(RAND_CONV(TRY_CONV INC32_CONV)) THENC gctrc) tm
    | _ -> failwith "gctr_conv" in
  let ghash_conv tm =
    match strip_comb tm with
      Const("nist_ghash",_),[_;_;_] when frees tm = [] ->
        (REWRITE_CONV[APPEND] THENC NIST_GHASH_CONV) tm
    | _ -> failwith "ghash_conv" in
  REWRITE_CONV[LENGTH] THENC
  DEPTH_CONV (NUM_RED_CONV ORELSEC WORD_RED_CONV) THENC
  ONCE_DEPTH_CONV gctr_conv THENC
  ONCE_DEPTH_CONV enc_conv THENC
  ONCE_DEPTH_CONV ghash_conv THENC
  DEPTH_CONV (NUM_RED_CONV ORELSEC WORD_RED_CONV);;

let rec GCM_LETS_CONV conv tm =
  if is_let tm then (RAND_CONV conv THENC let_CONV THENC GCM_LETS_CONV conv) tm
  else conv tm;;

let GCM_AE_CONV cipher_def ks_def =
  REWRITE_CONV[gcm_ae] THENC
  GCM_LETS_CONV (GCM_GROUND_CONV cipher_def ks_def);;

let GCM_AD_CONV cipher_def ks_def =
  REWRITE_CONV[gcm_ad] THENC
  GCM_LETS_CONV (GCM_GROUND_CONV cipher_def ks_def) THENC
  REWRITE_CONV[COND_CLAUSES];;
