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
(* here, so there is a single definition of each in common/.                 *)
(* ========================================================================= *)

needs "common/fips197.ml";;
needs "common/ghash.ml";;
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
(* Key schedule for NIST SP 800-38D Test Case 3 (AES-128).                   *)
(* Key: 0xFEFFE9928665731C6D6A8F9467308308                                   *)
(* ========================================================================= *)

let NIST_TC3_KEY_SCHEDULE = new_definition
  `NIST_TC3_KEY_SCHEDULE : (128 word) list =
    [ word 0xFEFFE9928665731C6D6A8F9467308308
    ; word 0xFB13D9177D76AA0B101C259F772CA697
    ; word 0x883751E2F541FBE9E55DDE76927178E1
    ; word 0x2F8BA9ADDACA52443F978C32ADE6F4D3
    ; word 0xA934CF3873FE9D7C4C69114EE18FE59D
    ; word 0xCAED91C0B9130CBCF57A1DF214F5F86F
    ; word 0x0CAC393AB5BF358640C528745430D01B
    ; word 0x48DC961AFD63A39CBDA68BE8E9965BF3
    ; word 0x58E59B04A58638981820B370F1B6E883
    ; word 0x0D7E77A5A8F84F3DB0D8FC4D416E14CE
    ; word 0xA484FC260C7CB31BBCA44F56FDCA5B98
    ]`;;

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

let rec NIST_GHASH_CONV tm =
  (NIST_GHASH_STEP_CONV THENC TRY_CONV NIST_GHASH_CONV) tm;;

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
(* KATs (Known Answer Tests)                                                 *)
(* ========================================================================= *)

(* ========================================================================= *)
(* inc32 KATs (<1s each)                                                     *)
(* ========================================================================= *)

prove(`inc32 (word 0x00000000000000000000000000000001 : 128 word) =
       word 0x00000000000000000000000000000002`,
  CONV_TAC(LAND_CONV INC32_CONV) THEN REFL_TAC);;

prove(`inc32 (word 0xCAFEBABE00000000DECAF00000000001 : 128 word) =
       word 0xCAFEBABE00000000DECAF00000000002`,
  CONV_TAC(LAND_CONV INC32_CONV) THEN REFL_TAC);;

prove(`inc32 (word 0x00000000000000000000000FFFFFFFFF : 128 word) =
       word 0x00000000000000000000000F00000000`,
  CONV_TAC(LAND_CONV INC32_CONV) THEN REFL_TAC);;

prove(`inc32 (word 0xFEEDFACEDEADBEEFFEEDFACEFFFFFFFF : 128 word) =
       word 0xFEEDFACEDEADBEEFFEEDFACE00000000`,
  CONV_TAC(LAND_CONV INC32_CONV) THEN REFL_TAC);;

(* ========================================================================= *)
(* Slower KATs below - commented out for fast loading, run interactively.    *)
(* ========================================================================= *)

(*

(* ========================================================================= *)
(* GF(2^128) multiplication KATs (deconstructed, ~15-30s each)               *)
(* ========================================================================= *)

let gf128_kat_0 = NIST_DOT_CONV
  `nist_dot (word 0x000000000000000000000000DEADBEEF)
             (word 0x00000000000000000000000000000000 : 128 word)`;;

let gf128_kat_1 = NIST_DOT_CONV
  `nist_dot (word 0x0388DACE60B6A392F328C2B971B2FE78)
             (word 0x80000000000000000000000000000000 : 128 word)`;;

let gf128_kat_2 = NIST_DOT_CONV
  `nist_dot (word 0x66E94BD4EF8A2C3B884CFA59CA342B2E)
             (word 0x66E94BD4EF8A2C3B884CFA59CA342B2E : 128 word)`;;

let gf128_kat_3 = NIST_DOT_CONV
  `nist_dot (word 0x0388DACE60B6A392F328C2B971B2FE78)
             (word 0x66E94BD4EF8A2C3B884CFA59CA342B2E : 128 word)`;;

(* ========================================================================= *)
(* GHASH KATs (deconstructed one step at a time)                             *)
(* ========================================================================= *)

(* nist_ghash(H, [0]) = nist_dot(0 XOR 0, H) = 0 *)
let ghash_kat_1 = NIST_GHASH_STEP_CONV
  `nist_ghash (word 0x66E94BD4EF8A2C3B884CFA59CA342B2E) (word 0)
         [word 0 : 128 word]`;;
let ghash_kat_1_done = CONV_RULE (RAND_CONV (REWRITE_CONV [nist_ghash])) ghash_kat_1;;

(* nist_ghash(H, [C]) where C = AES(0,0) = 0x0388DACE... *)
let ghash_kat_2 = NIST_GHASH_STEP_CONV
  `nist_ghash (word 0x66E94BD4EF8A2C3B884CFA59CA342B2E) (word 0)
         [word 0x0388DACE60B6A392F328C2B971B2FE78 : 128 word]`;;
let ghash_kat_2_done = CONV_RULE (RAND_CONV (REWRITE_CONV [nist_ghash])) ghash_kat_2;;

(* 2-block GHASH: each step individually *)
let ghash_2blk_step0 = NIST_GHASH_STEP_CONV
  `nist_ghash (word 0xB83B533708BF535D0AA6E52980D53B78) (word 0)
         [ word 0x42831EC2217774244B7221B784D0D49C
         ; word 0xE3AA212F2C02A4E035C17E2329ACA12E : 128 word]`;;
let ghash_2blk_step1 = CONV_RULE (RAND_CONV NIST_GHASH_STEP_CONV) ghash_2blk_step0;;
let ghash_2blk_done = CONV_RULE (RAND_CONV (REWRITE_CONV [nist_ghash])) ghash_2blk_step1;;

(* ========================================================================= *)
(* GCTR KATs (deconstructed, ~7s each with FAST_CONV)                        *)
(* ========================================================================= *)

let gctr_kat_1 = GCTR_FAST_CONV aes128_cipher AESAVS_ZERO_KEY_128_SCHEDULE
  `gctr aes128_cipher AESAVS_ZERO_KEY_128_SCHEDULE (word 2 : 128 word)
        [word 0 : 128 word]`;;

let gctr_kat_2 = GCTR_FAST_CONV aes128_cipher NIST_TC3_KEY_SCHEDULE
  `gctr aes128_cipher NIST_TC3_KEY_SCHEDULE
        (word 0xCAFEBABEFACEDBADDECAF88800000002 : 128 word)
        [word 0xD9313225F88406E5A55909C5AFF5269A : 128 word]`;;

let gctr_kat_3 = GCTR_FAST_CONV aes128_cipher NIST_TC3_KEY_SCHEDULE
  `gctr aes128_cipher NIST_TC3_KEY_SCHEDULE
        (word 0xCAFEBABEFACEDBADDECAF88800000002 : 128 word)
        [ word 0xD9313225F88406E5A55909C5AFF5269A
        ; word 0x86A7A9531534F7DA2E4C303D8A318A72 : 128 word]`;;

(* ------------------------------------------------------------------------- *)
(* GCM tag = S XOR E(K,J0). mk_tag builds this XOR from the computed GHASH   *)
(* and E(K,J0) theorems.                                                     *)
(* ------------------------------------------------------------------------- *)
let mk_tag s_thm ej0_thm =
  WORD_RED_CONV (mk_comb (mk_comb
    (`word_xor:(128 word)->(128 word)->(128 word)`,
     rand (concl s_thm)), rand (concl ej0_thm)));;

(* ========================================================================= *)
(* Test Case 1: AES-128, empty P, empty A, 96-bit IV                         *)
(* Key: 0x00000000000000000000000000000000                                   *)
(* IV:  0x000000000000000000000000                                           *)
(* T:   0x58e2fccefa7e3061367f1d57a4e7455a                                   *)
(*                                                                           *)
(* Deconstructed: H, len_block GHASH, tag XOR.                               *)
(* ========================================================================= *)

let tc1_H = FIPS197_ENCRYPT_FAST_CONV aes128_cipher AESAVS_ZERO_KEY_128_SCHEDULE
  `aes128_cipher (word 0 : 128 word) AESAVS_ZERO_KEY_128_SCHEDULE`;;

(* With empty P and empty A: nist_ghash H 0 [len_block] where len_block = 0 *)
let tc1_ghash = NIST_GHASH_STEP_CONV
  `nist_ghash (word 0x66E94BD4EF8A2C3B884CFA59CA342B2E) (word 0 : 128 word)
         [word 0 : 128 word]`;;
let tc1_ghash_done = CONV_RULE (RAND_CONV (REWRITE_CONV [nist_ghash])) tc1_ghash;;

let tc1_aes_j0 = FIPS197_ENCRYPT_FAST_CONV aes128_cipher AESAVS_ZERO_KEY_128_SCHEDULE
  `aes128_cipher (word 1 : 128 word) AESAVS_ZERO_KEY_128_SCHEDULE`;;

let tc1_tag = mk_tag tc1_ghash_done tc1_aes_j0;;
(* T = 0x58e2fccefa7e3061367f1d57a4e7455a *)

(* ========================================================================= *)
(* Test Case 2: AES-128, 1-block P, empty A                                  *)
(* Key: 0x00000000000000000000000000000000                                   *)
(* IV:  0x000000000000000000000000                                           *)
(* P:   0x00000000000000000000000000000000                                   *)
(* C:   0x0388dace60b6a392f328c2b971b2fe78                                   *)
(* T:   0xab6e47d42cec13bdf53a67b21257bddf                                   *)
(* ========================================================================= *)

let tc2_H = FIPS197_ENCRYPT_FAST_CONV aes128_cipher AESAVS_ZERO_KEY_128_SCHEDULE
  `aes128_cipher (word 0 : 128 word) AESAVS_ZERO_KEY_128_SCHEDULE`;;

let tc2_gctr = GCTR_FAST_CONV aes128_cipher AESAVS_ZERO_KEY_128_SCHEDULE
  `gctr aes128_cipher AESAVS_ZERO_KEY_128_SCHEDULE (word 2 : 128 word)
        [word 0 : 128 word]`;;

(* nist_ghash H 0 [C; len_block] — two GHASH steps *)
let tc2_gh0 = NIST_GHASH_STEP_CONV
  `nist_ghash (word 0x66E94BD4EF8A2C3B884CFA59CA342B2E) (word 0 : 128 word)
         [word 0x0388DACE60B6A392F328C2B971B2FE78; word 128]`;;
let tc2_gh1 = CONV_RULE (RAND_CONV NIST_GHASH_STEP_CONV) tc2_gh0;;
let tc2_ghash = CONV_RULE (RAND_CONV (REWRITE_CONV [nist_ghash])) tc2_gh1;;

let tc2_aes_j0 = FIPS197_ENCRYPT_FAST_CONV aes128_cipher AESAVS_ZERO_KEY_128_SCHEDULE
  `aes128_cipher (word 1 : 128 word) AESAVS_ZERO_KEY_128_SCHEDULE`;;

let tc2_tag = mk_tag tc2_ghash tc2_aes_j0;;
(* T = 0xab6e47d42cec13bdf53a67b21257bddf *)

(* ========================================================================= *)
(* Test Case 3: AES-128, 4-block P, empty A                                  *)
(* Key: 0xfeffe9928665731c6d6a8f9467308308                                   *)
(* IV:  0xcafebabefacedbaddecaf888                                           *)
(* P:   d9313225...b16aedf5aa0de657ba637b391aafd255 (4 blocks)               *)
(* C:   42831ec2...1ba30b396a0aac973d58e091473f5985 (4 blocks)               *)
(* T:   0x4d5c2af327cd64a62cf35abd2ba6fab4                                   *)
(* ========================================================================= *)

let tc3_H = FIPS197_ENCRYPT_FAST_CONV aes128_cipher NIST_TC3_KEY_SCHEDULE
  `aes128_cipher (word 0 : 128 word) NIST_TC3_KEY_SCHEDULE`;;

let tc3_J0 = WORD_RED_CONV
  `word_join ((word:num->96 word) 0xcafebabefacedbaddecaf888)
             ((word:num->32 word) 1) : 128 word`;;

let tc3_inc32_J0 = INC32_CONV
  `inc32 (word 0xCAFEBABEFACEDBADDECAF88800000001 : 128 word)`;;

(* GCTR: 4 blocks, one AES call at a time *)
let tc3_gctr = GCTR_FAST_CONV aes128_cipher NIST_TC3_KEY_SCHEDULE
  `gctr aes128_cipher NIST_TC3_KEY_SCHEDULE
        (word 0xCAFEBABEFACEDBADDECAF88800000002 : 128 word)
        [ word 0xD9313225F88406E5A55909C5AFF5269A
        ; word 0x86A7A9531534F7DA2E4C303D8A318A72
        ; word 0x1C3C0C95956809532FCF0E2449A6B525
        ; word 0xB16AEDF5AA0DE657BA637B391AAFD255 ]`;;

(* GHASH: 5 blocks (4 ciphertext + 1 len_block), one step at a time *)
let tc3_gh0 = NIST_GHASH_STEP_CONV
  `nist_ghash (word 0xB83B533708BF535D0AA6E52980D53B78) (word 0 : 128 word)
         [ word 0x42831EC2217774244B7221B784D0D49C
         ; word 0xE3AA212F2C02A4E035C17E2329ACA12E
         ; word 0x21D514B25466931C7D8F6A5AAC84AA05
         ; word 0x1BA30B396A0AAC973D58E091473F5985
         ; word 0x00000000000000000000000000000200 ]`;;
let tc3_gh1 = CONV_RULE (RAND_CONV NIST_GHASH_STEP_CONV) tc3_gh0;;
let tc3_gh2 = CONV_RULE (RAND_CONV NIST_GHASH_STEP_CONV) tc3_gh1;;
let tc3_gh3 = CONV_RULE (RAND_CONV NIST_GHASH_STEP_CONV) tc3_gh2;;
let tc3_gh4 = CONV_RULE (RAND_CONV NIST_GHASH_STEP_CONV) tc3_gh3;;
let tc3_ghash = CONV_RULE (RAND_CONV (REWRITE_CONV [nist_ghash])) tc3_gh4;;

let tc3_aes_j0 = FIPS197_ENCRYPT_FAST_CONV aes128_cipher NIST_TC3_KEY_SCHEDULE
  `aes128_cipher (word 0xCAFEBABEFACEDBADDECAF88800000001 : 128 word)
                 NIST_TC3_KEY_SCHEDULE`;;

let tc3_tag = mk_tag tc3_ghash tc3_aes_j0;;
(* T = 0x4d5c2af327cd64a62cf35abd2ba6fab4 *)

(* ========================================================================= *)
(* Test Case 13: AES-256, empty P, empty A, 96-bit IV                        *)
(* Key: 0x0000...0000 (32 bytes)                                             *)
(* IV:  0x000000000000000000000000                                           *)
(* T:   0x530f8afbc74536b9a963b4f1c4cb738b                                   *)
(*                                                                           *)
(* AES-256 analogue of TC1: exercises gctr/gcm_ae with aes256_cipher.        *)
(* Deconstructed: H, len_block GHASH, tag XOR.                               *)
(* ========================================================================= *)

let tc13_H = FIPS197_ENCRYPT_FAST_CONV aes256_cipher AESAVS_ZERO_KEY_256_SCHEDULE
  `aes256_cipher (word 0 : 128 word) AESAVS_ZERO_KEY_256_SCHEDULE`;;
(* H = 0xdc95c078a2408989ad48a21492842087 *)

(* With empty P and empty A: nist_ghash H 0 [len_block] where len_block = 0 *)
let tc13_ghash = NIST_GHASH_STEP_CONV
  `nist_ghash (word 0xdc95c078a2408989ad48a21492842087) (word 0 : 128 word)
         [word 0 : 128 word]`;;
let tc13_ghash_done = CONV_RULE (RAND_CONV (REWRITE_CONV [nist_ghash])) tc13_ghash;;

let tc13_aes_j0 = FIPS197_ENCRYPT_FAST_CONV aes256_cipher AESAVS_ZERO_KEY_256_SCHEDULE
  `aes256_cipher (word 1 : 128 word) AESAVS_ZERO_KEY_256_SCHEDULE`;;
(* E(K,J0) = 0x530f8afbc74536b9a963b4f1c4cb738b *)

let tc13_tag = mk_tag tc13_ghash_done tc13_aes_j0;;
(* T = 0x530f8afbc74536b9a963b4f1c4cb738b *)

(* ========================================================================= *)
(* Test Case 14: AES-256, 1-block P, empty A                                 *)
(* Key: 0x0000...0000 (32 bytes)                                             *)
(* IV:  0x000000000000000000000000                                           *)
(* P:   0x00000000000000000000000000000000                                   *)
(* C:   0xcea7403d4d606b6e074ec5d3baf39d18                                   *)
(* T:   0xd0d1c8a799996bf0265b98b5d48ab919                                   *)
(* ========================================================================= *)

let tc14_H = FIPS197_ENCRYPT_FAST_CONV aes256_cipher AESAVS_ZERO_KEY_256_SCHEDULE
  `aes256_cipher (word 0 : 128 word) AESAVS_ZERO_KEY_256_SCHEDULE`;;

let tc14_gctr = GCTR_FAST_CONV aes256_cipher AESAVS_ZERO_KEY_256_SCHEDULE
  `gctr aes256_cipher AESAVS_ZERO_KEY_256_SCHEDULE (word 2 : 128 word)
        [word 0 : 128 word]`;;
(* C = 0xcea7403d4d606b6e074ec5d3baf39d18 *)

(* nist_ghash H 0 [C; len_block] — two GHASH steps *)
let tc14_gh0 = NIST_GHASH_STEP_CONV
  `nist_ghash (word 0xdc95c078a2408989ad48a21492842087) (word 0 : 128 word)
         [word 0xcea7403d4d606b6e074ec5d3baf39d18; word 128]`;;
let tc14_gh1 = CONV_RULE (RAND_CONV NIST_GHASH_STEP_CONV) tc14_gh0;;
let tc14_ghash = CONV_RULE (RAND_CONV (REWRITE_CONV [nist_ghash])) tc14_gh1;;
(* S = 0x83de425c5edc5d498f382c441041ca92 *)

let tc14_aes_j0 = FIPS197_ENCRYPT_FAST_CONV aes256_cipher AESAVS_ZERO_KEY_256_SCHEDULE
  `aes256_cipher (word 1 : 128 word) AESAVS_ZERO_KEY_256_SCHEDULE`;;

let tc14_tag = mk_tag tc14_ghash tc14_aes_j0;;
(* T = 0xd0d1c8a799996bf0265b98b5d48ab919 *)

(* ========================================================================= *)
(* Test Case 16: AES-256, 4-block P, empty A                                 *)
(* Key: 0xFEFFE992...67308308 repeated (32 bytes)                            *)
(* IV:  0xcafebabefacedbaddecaf888                                           *)
(* P:   d9313225...b16aedf5aa0de657ba637b391aafd255 (4 blocks)               *)
(* C:   522dc1f0...c5f61e6393ba7a0abcc9f662898015ad (4 blocks)               *)
(* T:   0xb094dac5d93471bdec1a502270e3cc6c                                   *)
(*                                                                           *)
(* AES-256 analogue of TC3: exercises the full pipeline (multi-block gctr    *)
(* and 5-block GHASH) with aes256_cipher and a non-trivial key/IV.           *)
(* ========================================================================= *)

let tc16_H = FIPS197_ENCRYPT_FAST_CONV aes256_cipher NIST_TC16_KEY_SCHEDULE
  `aes256_cipher (word 0 : 128 word) NIST_TC16_KEY_SCHEDULE`;;
(* H = 0xacbef20579b4b8ebce889bac8732dad7 *)

let tc16_J0 = WORD_RED_CONV
  `word_join ((word:num->96 word) 0xcafebabefacedbaddecaf888)
             ((word:num->32 word) 1) : 128 word`;;

let tc16_inc32_J0 = INC32_CONV
  `inc32 (word 0xCAFEBABEFACEDBADDECAF88800000001 : 128 word)`;;

(* GCTR: 4 blocks, one AES call at a time *)
let tc16_gctr = GCTR_FAST_CONV aes256_cipher NIST_TC16_KEY_SCHEDULE
  `gctr aes256_cipher NIST_TC16_KEY_SCHEDULE
        (word 0xCAFEBABEFACEDBADDECAF88800000002 : 128 word)
        [ word 0xD9313225F88406E5A55909C5AFF5269A
        ; word 0x86A7A9531534F7DA2E4C303D8A318A72
        ; word 0x1C3C0C95956809532FCF0E2449A6B525
        ; word 0xB16AEDF5AA0DE657BA637B391AAFD255 ]`;;
(* C = 522dc1f0.. 643a8cdc.. 8cb08e48.. c5f61e63.. *)

(* GHASH: 5 blocks (4 ciphertext + 1 len_block), one step at a time *)
let tc16_gh0 = NIST_GHASH_STEP_CONV
  `nist_ghash (word 0xacbef20579b4b8ebce889bac8732dad7) (word 0 : 128 word)
         [ word 0x522DC1F099567D07F47F37A32A84427D
         ; word 0x643A8CDCBFE5C0C97598A2BD2555D1AA
         ; word 0x8CB08E48590DBB3DA7B08B1056828838
         ; word 0xC5F61E6393BA7A0ABCC9F662898015AD
         ; word 0x00000000000000000000000000000200 ]`;;
let tc16_gh1 = CONV_RULE (RAND_CONV NIST_GHASH_STEP_CONV) tc16_gh0;;
let tc16_gh2 = CONV_RULE (RAND_CONV NIST_GHASH_STEP_CONV) tc16_gh1;;
let tc16_gh3 = CONV_RULE (RAND_CONV NIST_GHASH_STEP_CONV) tc16_gh2;;
let tc16_gh4 = CONV_RULE (RAND_CONV NIST_GHASH_STEP_CONV) tc16_gh3;;
let tc16_ghash = CONV_RULE (RAND_CONV (REWRITE_CONV [nist_ghash])) tc16_gh4;;
(* S = 0x4db870d37cb75fcb46097c36230d1612 *)

let tc16_aes_j0 = FIPS197_ENCRYPT_FAST_CONV aes256_cipher NIST_TC16_KEY_SCHEDULE
  `aes256_cipher (word 0xCAFEBABEFACEDBADDECAF88800000001 : 128 word)
                 NIST_TC16_KEY_SCHEDULE`;;

let tc16_tag = mk_tag tc16_ghash tc16_aes_j0;;
(* T = 0xb094dac5d93471bdec1a502270e3cc6c *)

*)
