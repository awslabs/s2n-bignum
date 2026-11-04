(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Known-answer tests of the NIST SP 800-38D definitions in common/gcm.ml:   *)
(* inc32, GCTR, and whole GCM-AE and GCM-AD evaluations for the test cases   *)
(* of McGrew and Viega, "The Galois/Counter Mode of Operation (GCM)", that   *)
(* have a 96-bit IV and whole blocks (Test Cases 1-3 for AES-128 and 13-15   *)
(* for AES-256).  No proof depends on them, so they are checked once, by     *)
(* arm/proofs/aes_gcm_spec_checks.ml.                                        *)
(* ========================================================================= *)

needs "common/fips197.ml";;
needs "common/gcm.ml";;

(* ========================================================================= *)
(* inc32                                                                     *)
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
(* The AES-128 key of Test Case 3, 0xfeffe9928665731c6d6a8f9467308308,       *)
(* and its expanded key schedule                                             *)
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

prove(`aes128_key_expansion (word 0xfeffe9928665731c6d6a8f9467308308) =
       NIST_TC3_KEY_SCHEDULE`,
  REWRITE_TAC[NIST_TC3_KEY_SCHEDULE] THEN
  CONV_TAC(LAND_CONV AES128_KEY_EXPANSION_CONV) THEN REFL_TAC);;

(* ========================================================================= *)
(* GCTR, through the conversion without lookup tables (GCTR_CONV), on the    *)
(* one block of Test Case 2                                                  *)
(* ========================================================================= *)

prove(`gctr aes128_cipher AESAVS_ZERO_KEY_128_SCHEDULE (word 2) [word 0] =
       [word 0x0388dace60b6a392f328c2b971b2fe78]`,
  CONV_TAC(LAND_CONV(GCTR_CONV aes128_cipher
                       AESAVS_ZERO_KEY_128_SCHEDULE)) THEN
  REFL_TAC);;

(* ========================================================================= *)
(* GCM-AE: Test Cases 1-3 (AES-128) and 13-15 (AES-256)                      *)
(* ========================================================================= *)

let GCM_AE_TC1 = prove
 (`gcm_ae aes128_cipher AESAVS_ZERO_KEY_128_SCHEDULE (word 0)
     [] [] =
   ([],
    word 0x58e2fccefa7e3061367f1d57a4e7455a)`,
  CONV_TAC(LAND_CONV(GCM_AE_CONV aes128_cipher
                       AESAVS_ZERO_KEY_128_SCHEDULE)) THEN
  REFL_TAC);;

let GCM_AE_TC2 = prove
 (`gcm_ae aes128_cipher AESAVS_ZERO_KEY_128_SCHEDULE (word 0)
     [word 0] [] =
   ([word 0x0388dace60b6a392f328c2b971b2fe78],
    word 0xab6e47d42cec13bdf53a67b21257bddf)`,
  CONV_TAC(LAND_CONV(GCM_AE_CONV aes128_cipher
                       AESAVS_ZERO_KEY_128_SCHEDULE)) THEN
  REFL_TAC);;

let GCM_AE_TC3 = prove
 (`gcm_ae aes128_cipher NIST_TC3_KEY_SCHEDULE
     (word 0xcafebabefacedbaddecaf888)
     [word 0xd9313225f88406e5a55909c5aff5269a;
      word 0x86a7a9531534f7da2e4c303d8a318a72;
      word 0x1c3c0c95956809532fcf0e2449a6b525;
      word 0xb16aedf5aa0de657ba637b391aafd255] [] =
   ([word 0x42831ec2217774244b7221b784d0d49c;
     word 0xe3aa212f2c02a4e035c17e2329aca12e;
     word 0x21d514b25466931c7d8f6a5aac84aa05;
     word 0x1ba30b396a0aac973d58e091473f5985],
    word 0x4d5c2af327cd64a62cf35abd2ba6fab4)`,
  CONV_TAC(LAND_CONV(GCM_AE_CONV aes128_cipher
                       NIST_TC3_KEY_SCHEDULE)) THEN
  REFL_TAC);;

let GCM_AE_TC13 = prove
 (`gcm_ae aes256_cipher AESAVS_ZERO_KEY_256_SCHEDULE (word 0)
     [] [] =
   ([],
    word 0x530f8afbc74536b9a963b4f1c4cb738b)`,
  CONV_TAC(LAND_CONV(GCM_AE_CONV aes256_cipher
                       AESAVS_ZERO_KEY_256_SCHEDULE)) THEN
  REFL_TAC);;

let GCM_AE_TC14 = prove
 (`gcm_ae aes256_cipher AESAVS_ZERO_KEY_256_SCHEDULE (word 0)
     [word 0] [] =
   ([word 0xcea7403d4d606b6e074ec5d3baf39d18],
    word 0xd0d1c8a799996bf0265b98b5d48ab919)`,
  CONV_TAC(LAND_CONV(GCM_AE_CONV aes256_cipher
                       AESAVS_ZERO_KEY_256_SCHEDULE)) THEN
  REFL_TAC);;

let GCM_AE_TC15 = prove
 (`gcm_ae aes256_cipher NIST_TC15_KEY_SCHEDULE
     (word 0xcafebabefacedbaddecaf888)
     [word 0xd9313225f88406e5a55909c5aff5269a;
      word 0x86a7a9531534f7da2e4c303d8a318a72;
      word 0x1c3c0c95956809532fcf0e2449a6b525;
      word 0xb16aedf5aa0de657ba637b391aafd255] [] =
   ([word 0x522dc1f099567d07f47f37a32a84427d;
     word 0x643a8cdcbfe5c0c97598a2bd2555d1aa;
     word 0x8cb08e48590dbb3da7b08b1056828838;
     word 0xc5f61e6393ba7a0abcc9f662898015ad],
    word 0xb094dac5d93471bdec1a502270e3cc6c)`,
  CONV_TAC(LAND_CONV(GCM_AE_CONV aes256_cipher
                       NIST_TC15_KEY_SCHEDULE)) THEN
  REFL_TAC);;

(* ========================================================================= *)
(* GCM-AD: Test Case 3 decrypts with its tag, and fails with the last bit of *)
(* the tag flipped                                                           *)
(* ========================================================================= *)

let GCM_AD_TC3 = prove
 (`gcm_ad aes128_cipher NIST_TC3_KEY_SCHEDULE (word 0xcafebabefacedbaddecaf888)
     [word 0x42831ec2217774244b7221b784d0d49c;
      word 0xe3aa212f2c02a4e035c17e2329aca12e;
      word 0x21d514b25466931c7d8f6a5aac84aa05;
      word 0x1ba30b396a0aac973d58e091473f5985] []
     (word 0x4d5c2af327cd64a62cf35abd2ba6fab4) =
   SOME [word 0xd9313225f88406e5a55909c5aff5269a;
         word 0x86a7a9531534f7da2e4c303d8a318a72;
         word 0x1c3c0c95956809532fcf0e2449a6b525;
         word 0xb16aedf5aa0de657ba637b391aafd255]`,
  CONV_TAC(LAND_CONV(GCM_AD_CONV aes128_cipher
                       NIST_TC3_KEY_SCHEDULE)) THEN
  REFL_TAC);;

let GCM_AD_TC3_BAD_TAG = prove
 (`gcm_ad aes128_cipher NIST_TC3_KEY_SCHEDULE (word 0xcafebabefacedbaddecaf888)
     [word 0x42831ec2217774244b7221b784d0d49c;
      word 0xe3aa212f2c02a4e035c17e2329aca12e;
      word 0x21d514b25466931c7d8f6a5aac84aa05;
      word 0x1ba30b396a0aac973d58e091473f5985] []
     (word 0x4d5c2af327cd64a62cf35abd2ba6fab5) =
   NONE`,
  CONV_TAC(LAND_CONV(GCM_AD_CONV aes128_cipher
                       NIST_TC3_KEY_SCHEDULE)) THEN
  REFL_TAC);;
