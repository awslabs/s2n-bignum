(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* AES-128-GCM specification per NIST SP 800-38D.                            *)
(*                                                                           *)
(* Defines inc32 (Sec 6.2), GCTR (Alg 3), GF(2^128) mul (Alg 1/Sec 6.3),     *)
(* GHASH (Alg 2), GCM-AE (Alg 4), GCM-AD (Alg 5).                            *)
(* Simplified to 96-bit IVs, full 128-bit blocks, and pre-expanded keys.     *)
(* AES cipher comes from common/fips197.ml.                                  *)
(* ========================================================================= *)

needs "common/fips197.ml";;
needs "common/ghash.ml";;
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
(* to the GCM-AE/AD layer. Uses AES-128 cipher from fips197.ml.              *)
(* ========================================================================= *)

let gctr = define
  `gctr (ks:(128 word) list) (icb:128 word) ([] : (128 word) list) =
     ([] : (128 word) list) /\
   gctr ks icb (CONS x rest) =
     CONS (word_xor x (aes128_cipher icb ks)) (gctr ks (inc32 icb) rest)`;;

let GCTR_STEP_CONV ks_def =
  ONCE_REWRITE_CONV [gctr] THENC
  REWRITE_CONV [ks_def] THENC
  ONCE_DEPTH_CONV (FIPS197_ENCRYPT_CONV aes128_cipher ks_def) THENC
  DEPTH_CONV WORD_RED_CONV THENC
  ONCE_DEPTH_CONV (REWRITE_CONV [inc32] THENC
    TOP_DEPTH_CONV let_CONV THENC
    DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV));;

let rec GCTR_CONV ks_def tm =
  try
    let th = GCTR_STEP_CONV ks_def tm in
    let rhs = rand (concl th) in
    (try let th2 = RAND_CONV (GCTR_CONV ks_def) rhs in TRANS th th2
     with _ -> th)
  with _ -> REWRITE_CONV [gctr] tm;;

let GCTR_STEP_FAST_CONV ks_def =
  ONCE_REWRITE_CONV [gctr] THENC
  REWRITE_CONV [ks_def] THENC
  ONCE_DEPTH_CONV (FIPS197_ENCRYPT_FAST_CONV aes128_cipher ks_def) THENC
  DEPTH_CONV WORD_RED_CONV THENC
  ONCE_DEPTH_CONV (REWRITE_CONV [inc32] THENC
    TOP_DEPTH_CONV let_CONV THENC
    DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV));;

let rec GCTR_FAST_CONV ks_def tm =
  try
    let th = GCTR_STEP_FAST_CONV ks_def tm in
    let rhs = rand (concl th) in
    (try let th2 = RAND_CONV (GCTR_FAST_CONV ks_def) rhs in TRANS th th2
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
(* NIST uses reflected bit ordering (bit 0 = MSB = coefficient of x^0).      *)
(* We implement this as: bit-reverse inputs, carry-less multiply, reduce     *)
(* mod P(x) using ghash_reduce from common/ghash.ml, then bit-reverse the    *)
(* result. The reduction polynomial 0x87 = x^7+x^2+x+1 is the low part       *)
(* of P(x).                                                                  *)
(* ========================================================================= *)

let bitrev128 = new_definition
 `bitrev128 (x:128 word) : 128 word = word_reversefields 1 x`;;

let gf128_mul = new_definition
 `gf128_mul (X:128 word) (Y:128 word) : 128 word =
  bitrev128 (ghash_reduce (word_pmul (bitrev128 X) (bitrev128 Y) : 256 word))`;;

let WORD_PMUL_128_CONV =
  let karatsuba = REWRITE_RULE [LET_DEF; LET_END_DEF] PMUL_KARATSUBA in
  REWR_CONV karatsuba THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV) THENC
  DEPTH_CONV WORD_PMUL_CONV THENC
  DEPTH_CONV (WORD_RED_CONV ORELSEC NUM_RED_CONV);;

let GF128_MUL_CONV =
  REWRITE_CONV [gf128_mul; bitrev128; ghash_reduce; ghash_reduce1] THENC
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
(* GHASH(H, X_1 || ... || X_m) iterates gf128_mul:                           *)
(*   Y_0 = 0, Y_i = gf128_mul(Y_{i-1} XOR X_i, H).                           *)
(* Takes an initial accumulator Y (normally word 0) for generality.          *)
(* ========================================================================= *)

let ghash = define
  `ghash (H:128 word) (Y:128 word) ([] : (128 word) list) = Y /\
   ghash H Y (CONS x rest) = ghash H (gf128_mul (word_xor Y x) H) rest`;;

let GHASH_STEP_CONV =
  ONCE_REWRITE_CONV [ghash] THENC
  DEPTH_CONV WORD_RED_CONV THENC
  ONCE_DEPTH_CONV GF128_MUL_CONV;;

let rec GHASH_CONV tm =
  (GHASH_STEP_CONV THENC TRY_CONV GHASH_CONV) tm;;

(* ========================================================================= *)
(* GCM-AE: NIST SP 800-38D Algorithm 4 (authenticated encryption).           *)
(*                                                                           *)
(* Simplified to 96-bit IV, full 128-bit blocks, and 128-bit tag.            *)
(* Key schedule is pre-expanded. Returns (ciphertext, tag).                  *)
(* ========================================================================= *)

let gcm_ae = new_definition
 `gcm_ae (ks:(128 word) list) (iv:96 word)
         (P:(128 word) list) (A:(128 word) list) =
  let H = aes128_cipher (word 0) ks in
  let J0 : 128 word = word_join iv (word 1 : 32 word) in
  let C = gctr ks (inc32 J0) P in
  let len_block : 128 word =
    word_join (word (128 * LENGTH A) : 64 word)
              (word (128 * LENGTH C) : 64 word) in
  let S = ghash H (word 0) (APPEND A (APPEND C [len_block])) in
  let tag = word_xor S (aes128_cipher J0 ks) in
  (C, tag)`;;

(* ========================================================================= *)
(* GCM-AD: NIST SP 800-38D Algorithm 5 (authenticated decryption).           *)
(*                                                                           *)
(* Returns SOME plaintext if tag verifies, NONE otherwise.                   *)
(* ========================================================================= *)

let gcm_ad = new_definition
 `gcm_ad (ks:(128 word) list) (iv:96 word)
         (C:(128 word) list) (A:(128 word) list) (tag:128 word) =
  let H = aes128_cipher (word 0) ks in
  let J0 : 128 word = word_join iv (word 1 : 32 word) in
  let P = gctr ks (inc32 J0) C in
  let len_block : 128 word =
    word_join (word (128 * LENGTH A) : 64 word)
              (word (128 * LENGTH C) : 64 word) in
  let S = ghash H (word 0) (APPEND A (APPEND C [len_block])) in
  let tag' = word_xor S (aes128_cipher J0 ks) in
  if tag' = tag then SOME P else NONE`;;

(* ========================================================================= *)
(* KATs (Known Answer Tests)                                                 *)
(*                                                                           *)
(* Commented out for fast loading. Run interactively as needed.              *)
(* To run: evaluate the contents of this block in a HOL Light session        *)
(* after loading this file.                                                  *)
(* ========================================================================= *)

(*

(* ========================================================================= *)
(* inc32 KATs (trivial, <1s each)                                            *)
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
(* GF(2^128) multiplication KATs (deconstructed, ~15-30s each)               *)
(* ========================================================================= *)

let gf128_kat_0 = GF128_MUL_CONV
  `gf128_mul (word 0x000000000000000000000000DEADBEEF)
             (word 0x00000000000000000000000000000000 : 128 word)`;;

let gf128_kat_1 = GF128_MUL_CONV
  `gf128_mul (word 0x0388DACE60B6A392F328C2B971B2FE78)
             (word 0x80000000000000000000000000000000 : 128 word)`;;

let gf128_kat_2 = GF128_MUL_CONV
  `gf128_mul (word 0x66E94BD4EF8A2C3B884CFA59CA342B2E)
             (word 0x66E94BD4EF8A2C3B884CFA59CA342B2E : 128 word)`;;

let gf128_kat_3 = GF128_MUL_CONV
  `gf128_mul (word 0x0388DACE60B6A392F328C2B971B2FE78)
             (word 0x66E94BD4EF8A2C3B884CFA59CA342B2E : 128 word)`;;

(* ========================================================================= *)
(* GHASH KATs (deconstructed one step at a time)                             *)
(* ========================================================================= *)

(* ghash(H, [0]) = gf128_mul(0 XOR 0, H) = 0 *)
let ghash_kat_1 = GHASH_STEP_CONV
  `ghash (word 0x66E94BD4EF8A2C3B884CFA59CA342B2E) (word 0)
         [word 0 : 128 word]`;;
let ghash_kat_1_done = CONV_RULE (RAND_CONV (REWRITE_CONV [ghash])) ghash_kat_1;;

(* ghash(H, [C]) where C = AES(0,0) = 0x0388DACE... *)
let ghash_kat_2 = GHASH_STEP_CONV
  `ghash (word 0x66E94BD4EF8A2C3B884CFA59CA342B2E) (word 0)
         [word 0x0388DACE60B6A392F328C2B971B2FE78 : 128 word]`;;
let ghash_kat_2_done = CONV_RULE (RAND_CONV (REWRITE_CONV [ghash])) ghash_kat_2;;

(* 2-block GHASH: each step individually *)
let ghash_2blk_step0 = GHASH_STEP_CONV
  `ghash (word 0xB83B533708BF535D0AA6E52980D53B78) (word 0)
         [ word 0x42831EC2217774244B7221B784D0D49C
         ; word 0xE3AA212F2C02A4E035C17E2329ACA12E : 128 word]`;;
let ghash_2blk_step1 = CONV_RULE (RAND_CONV GHASH_STEP_CONV) ghash_2blk_step0;;
let ghash_2blk_done = CONV_RULE (RAND_CONV (REWRITE_CONV [ghash])) ghash_2blk_step1;;

(* ========================================================================= *)
(* GCTR KATs (deconstructed, ~7s each with FAST_CONV)                        *)
(* ========================================================================= *)

let gctr_kat_1 = GCTR_FAST_CONV AESAVS_ZERO_KEY_128_SCHEDULE
  `gctr AESAVS_ZERO_KEY_128_SCHEDULE (word 2 : 128 word)
        [word 0 : 128 word]`;;

let gctr_kat_2 = GCTR_FAST_CONV NIST_TC3_KEY_SCHEDULE
  `gctr NIST_TC3_KEY_SCHEDULE
        (word 0xCAFEBABEFACEDBADDECAF88800000002 : 128 word)
        [word 0xD9313225F88406E5A55909C5AFF5269A : 128 word]`;;

let gctr_kat_3 = GCTR_FAST_CONV NIST_TC3_KEY_SCHEDULE
  `gctr NIST_TC3_KEY_SCHEDULE
        (word 0xCAFEBABEFACEDBADDECAF88800000002 : 128 word)
        [ word 0xD9313225F88406E5A55909C5AFF5269A
        ; word 0x86A7A9531534F7DA2E4C303D8A318A72 : 128 word]`;;

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

(* With empty P and empty A: ghash H 0 [len_block] where len_block = 0 *)
let tc1_ghash = GHASH_STEP_CONV
  `ghash (word 0x66E94BD4EF8A2C3B884CFA59CA342B2E) (word 0 : 128 word)
         [word 0 : 128 word]`;;
let tc1_ghash_done = CONV_RULE (RAND_CONV (REWRITE_CONV [ghash])) tc1_ghash;;

let tc1_aes_j0 = FIPS197_ENCRYPT_FAST_CONV aes128_cipher AESAVS_ZERO_KEY_128_SCHEDULE
  `aes128_cipher (word 1 : 128 word) AESAVS_ZERO_KEY_128_SCHEDULE`;;

let tc1_tag = WORD_RED_CONV
  `word_xor (word 0 : 128 word)
            (word 0x58e2fccefa7e3061367f1d57a4e7455a : 128 word)`;;

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

let tc2_gctr = GCTR_FAST_CONV AESAVS_ZERO_KEY_128_SCHEDULE
  `gctr AESAVS_ZERO_KEY_128_SCHEDULE (word 2 : 128 word) [word 0 : 128 word]`;;

(* ghash H 0 [C; len_block] — two GHASH steps *)
let tc2_gh0 = GHASH_STEP_CONV
  `ghash (word 0x66E94BD4EF8A2C3B884CFA59CA342B2E) (word 0 : 128 word)
         [word 0x0388DACE60B6A392F328C2B971B2FE78; word 128]`;;
let tc2_gh1 = CONV_RULE (RAND_CONV GHASH_STEP_CONV) tc2_gh0;;
let tc2_ghash = CONV_RULE (RAND_CONV (REWRITE_CONV [ghash])) tc2_gh1;;

let tc2_aes_j0 = FIPS197_ENCRYPT_FAST_CONV aes128_cipher AESAVS_ZERO_KEY_128_SCHEDULE
  `aes128_cipher (word 1 : 128 word) AESAVS_ZERO_KEY_128_SCHEDULE`;;

let tc2_tag = WORD_RED_CONV
  `word_xor (word 0xF38CDD5A332ED7AEAD6E85B4F2F6FF20 : 128 word)
            (word 0x58e2fccefa7e3061367f1d57a4e7455a : 128 word)`;;
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
let tc3_gctr = GCTR_FAST_CONV NIST_TC3_KEY_SCHEDULE
  `gctr NIST_TC3_KEY_SCHEDULE
        (word 0xCAFEBABEFACEDBADDECAF88800000002 : 128 word)
        [ word 0xD9313225F88406E5A55909C5AFF5269A
        ; word 0x86A7A9531534F7DA2E4C303D8A318A72
        ; word 0x1C3C0C95956809532FCF0E2449A6B525
        ; word 0xB16AEDF5AA0DE657BA637B391AAFD255 ]`;;

(* GHASH: 5 blocks (4 ciphertext + 1 len_block), one step at a time *)
let tc3_gh0 = GHASH_STEP_CONV
  `ghash (word 0xB83B533708BF535D0AA6E52980D53B78) (word 0 : 128 word)
         [ word 0x42831EC2217774244B7221B784D0D49C
         ; word 0xE3AA212F2C02A4E035C17E2329ACA12E
         ; word 0x21D514B25466931C7D8F6A5AAC84AA05
         ; word 0x1BA30B396A0AAC973D58E091473F5985
         ; word 0x00000000000000000000000000000200 ]`;;
let tc3_gh1 = CONV_RULE (RAND_CONV GHASH_STEP_CONV) tc3_gh0;;
let tc3_gh2 = CONV_RULE (RAND_CONV GHASH_STEP_CONV) tc3_gh1;;
let tc3_gh3 = CONV_RULE (RAND_CONV GHASH_STEP_CONV) tc3_gh2;;
let tc3_gh4 = CONV_RULE (RAND_CONV GHASH_STEP_CONV) tc3_gh3;;
let tc3_ghash = CONV_RULE (RAND_CONV (REWRITE_CONV [ghash])) tc3_gh4;;

let tc3_aes_j0 = FIPS197_ENCRYPT_FAST_CONV aes128_cipher NIST_TC3_KEY_SCHEDULE
  `aes128_cipher (word 0xCAFEBABEFACEDBADDECAF88800000001 : 128 word)
                 NIST_TC3_KEY_SCHEDULE`;;

let tc3_tag = WORD_RED_CONV
  `word_xor (word 0x7F1B32B81B820D02614F8895AC1D4EAC : 128 word)
            (word 0x3247184B3C4F69A44DBCD22887BBB418 : 128 word)`;;
(* T = 0x4d5c2af327cd64a62cf35abd2ba6fab4 *)

*)
