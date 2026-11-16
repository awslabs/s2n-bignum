(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Known-answer tests of the FIPS 197 AES definitions in common/fips197.ml:  *)
(* the key expansion, the round steps and whole encryptions under the        *)
(* expanded key schedules defined there.  No proof depends on them, so they  *)
(* are checked once, by arm/proofs/aes_gcm_spec_checks.ml, and not at every  *)
(* load of common/fips197.ml.                                                *)
(* ========================================================================= *)

needs "common/fips197.ml";;

(* ========================================================================= *)
(* KAT: AES-128 Key Expansion (FIPS 197 Appendix A.1)                        *)
(* Key = 2b7e1516 28aed2a6 abf71588 09cf4f3c                                 *)
(* ========================================================================= *)

prove(`aes128_kexp_round 0
        (word 0x2b7e1516, word 0x28aed2a6, word 0xabf71588, word 0x09cf4f3c) =
       (word 0xa0fafe17, word 0x88542cb1, word 0x23a33939, word 0x2a6c7605)`,
  CONV_TAC(LAND_CONV AES128_KEXP_ROUND_CONV) THEN REFL_TAC);;

prove(`aes128_kexp_round 9
       (aes128_kexp_round 8
        (aes128_kexp_round 7
         (aes128_kexp_round 6
          (aes128_kexp_round 5
           (aes128_kexp_round 4
            (aes128_kexp_round 3
             (aes128_kexp_round 2
              (aes128_kexp_round 1
                (aes128_kexp_round 0
                  (word 0x2b7e1516, word 0x28aed2a6,
                   word 0xabf71588, word 0x09cf4f3c)))))))))) =
       (word 0xd014f9a8, word 0xc9ee2589, word 0xe13f0cc8, word 0xb6630ca6)`,
  CONV_TAC(LAND_CONV(
    itlist (fun _ c -> RAND_CONV c THENC AES128_KEXP_ROUND_CONV)
           (1--10) ALL_CONV)) THEN
  REFL_TAC);;

prove(`aes128_key_expansion (word 0x2b7e151628aed2a6abf7158809cf4f3c) =
       AES128_APPENDIX_B_KEY_SCHEDULE`,
  REWRITE_TAC[AES128_APPENDIX_B_KEY_SCHEDULE] THEN
  CONV_TAC(LAND_CONV AES128_KEY_EXPANSION_CONV) THEN REFL_TAC);;

(* ========================================================================= *)
(* KAT: AES-256 Key Expansion (FIPS 197 Appendix A.3)                        *)
(* Key = 603deb10 15ca71be 2b73aef0 857d7781                                 *)
(*       1f352c07 3b6108d7 2d9810a3 0914dff4                                 *)
(* ========================================================================= *)

prove(`aes256_kexp_round 0
        ((word 0x603deb10, word 0x15ca71be, word 0x2b73aef0, word 0x857d7781),
         (word 0x1f352c07, word 0x3b6108d7, word 0x2d9810a3, word 0x0914dff4)) =
       ((word 0x9ba35411, word 0x8e6925af, word 0xa51a8b5f, word 0x2067fcde),
        (word 0xa8b09c1a, word 0x93d194cd, word 0xbe49846e, word 0xb75d5b9a))`,
  CONV_TAC(LAND_CONV AES256_KEXP_ROUND_CONV) THEN REFL_TAC);;

prove(`aes256_kexp_last 6
       (aes256_kexp_round 5
        (aes256_kexp_round 4
         (aes256_kexp_round 3
          (aes256_kexp_round 2
           (aes256_kexp_round 1
            (aes256_kexp_round 0
              ((word 0x603deb10, word 0x15ca71be,
                word 0x2b73aef0, word 0x857d7781),
               (word 0x1f352c07, word 0x3b6108d7,
                word 0x2d9810a3, word 0x0914dff4)))))))) =
       (word 0xfe4890d1, word 0xe6188d0b, word 0x046df344, word 0x706c631e)`,
  CONV_TAC(LAND_CONV(
    itlist (fun _ c -> RAND_CONV c THENC AES256_KEXP_ROUND_CONV)
           (1--6) ALL_CONV THENC
    AES256_KEXP_LAST_CONV)) THEN
  REFL_TAC);;

let AES256_CORE_KEY_SCHEDULE = new_definition
  `AES256_CORE_KEY_SCHEDULE:(128 word) list =
    [ word 0x603DEB1015CA71BE2B73AEF0857D7781
    ; word 0x1F352C073B6108D72D9810A30914DFF4
    ; word 0x9BA354118E6925AFA51A8B5F2067FCDE
    ; word 0xA8B09C1A93D194CDBE49846EB75D5B9A
    ; word 0xD59AECB85BF3C917FEE94248DE8EBE96
    ; word 0xB5A9328A2678A647983122292F6C79B3
    ; word 0x812C81ADDADF48BA24360AF2FAB8B464
    ; word 0x98C5BFC9BEBD198E268C3BA709E04214
    ; word 0x68007BACB2DF331696E939E46C518D80
    ; word 0xC814E20476A9FB8A5025C02D59C58239
    ; word 0xDE1369676CCC5A71FA2563959674EE15
    ; word 0x5886CA5D2E2F31D77E0AF1FA27CF73C3
    ; word 0x749C47AB18501DDAE2757E4F7401905A
    ; word 0xCAFAAAE3E4D59B349ADF6ACEBD10190D
    ; word 0xFE4890D1E6188D0B046DF344706C631E
    ]`;;

prove(`aes256_key_expansion (word 0x603deb1015ca71be2b73aef0857d7781)
                            (word 0x1f352c073b6108d72d9810a30914dff4) =
       AES256_CORE_KEY_SCHEDULE`,
  REWRITE_TAC[AES256_CORE_KEY_SCHEDULE] THEN
  CONV_TAC(LAND_CONV AES256_KEY_EXPANSION_CONV) THEN REFL_TAC);;

(* ========================================================================= *)
(* KAT: the steps of round 1 of FIPS 197 Appendix B                          *)
(* ========================================================================= *)

(* FIPS 197 Appendix B, Round 1 SubBytes *)
prove(`fips197_sub_bytes (word 0x193de3bea0f4e22b9ac68d2ae9f84808) =
       word 0xd42711aee0bf98f1b8b45de51e415230`,
  CONV_TAC(LAND_CONV FIPS197_SUB_BYTES_CONV) THEN REFL_TAC);;

(* FIPS 197 Appendix B, Round 1 ShiftRows *)
prove(`fips197_shift_rows (word 0xd42711aee0bf98f1b8b45de51e415230) =
       word 0xd4bf5d30e0b452aeb84111f11e2798e5`,
  CONV_TAC(LAND_CONV FIPS197_SHIFT_ROWS_CONV) THEN REFL_TAC);;

(* FIPS 197 Appendix B, Round 1 MixColumns *)
prove(`fips197_mix_columns (word 0xd4bf5d30e0b452aeb84111f11e2798e5) =
       word 0x046681e5e0cb199a48f8d37a2806264c`,
  CONV_TAC(LAND_CONV FIPS197_MIX_COLUMNS_CONV) THEN REFL_TAC);;

(* FIPS 197 Appendix B, Round 1 AddRoundKey (just XOR) *)
prove(`word_xor (word 0x046681e5e0cb199a48f8d37a2806264c : 128 word)
                (word 0xa0fafe1788542cb123a339392a6c7605 : 128 word) =
       word 0xa49c7ff2689f352b6b5bea43026a5049`,
  CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN REFL_TAC);;

(* ========================================================================= *)
(* KAT: AES-128 encryption (FIPS 197 Appendix B)                             *)
(* Plaintext:  0x3243f6a8885a308d313198a2e0370734                            *)
(* Key:        0x2b7e151628aed2a6abf7158809cf4f3c                            *)
(* Ciphertext: 0x3925841d02dc09fbdc118597196a0b32                            *)
(* ========================================================================= *)

prove(`aes128_cipher (word 0x3243f6a8885a308d313198a2e0370734)
                     AES128_APPENDIX_B_KEY_SCHEDULE =
       word 0x3925841d02dc09fbdc118597196a0b32`,
  CONV_TAC(LAND_CONV(FIPS197_ENCRYPT_FAST_CONV aes128_cipher
    AES128_APPENDIX_B_KEY_SCHEDULE)) THEN REFL_TAC);;

(* ========================================================================= *)
(* KAT: AES-256 encryption (NIST AES_Core256 / FIPS 197 Appendix A.3)        *)
(* Key:        0x603deb1015ca71be2b73aef0857d7781                            *)
(*             1f352c073b6108d72d9810a30914dff4                              *)
(* Plaintext:  0x6bc1bee22e409f96e93d7e117393172a                            *)
(* Ciphertext: 0xf3eed1bdb5d2a03c064b5a7e3db181f8                            *)
(* ========================================================================= *)

prove(`aes256_cipher (word 0x6bc1bee22e409f96e93d7e117393172a)
                     AES256_CORE_KEY_SCHEDULE =
       word 0xf3eed1bdb5d2a03c064b5a7e3db181f8`,
  CONV_TAC(LAND_CONV(FIPS197_ENCRYPT_FAST_CONV aes256_cipher
    AES256_CORE_KEY_SCHEDULE)) THEN REFL_TAC);;

(* ========================================================================= *)
(* KAT: AES-128 with the all-zero key (AESAVS Appendix B, GFSbox)            *)
(* ========================================================================= *)

(* The first GFSbox vector *)
prove(`aes128_cipher (word 0xf34481ec3cc627bacd5dc3fb08f273e6)
                     AESAVS_ZERO_KEY_128_SCHEDULE =
       word 0x0336763e966d92595a567cc9ce537f5e`,
  CONV_TAC(LAND_CONV(FIPS197_ENCRYPT_FAST_CONV aes128_cipher
    AESAVS_ZERO_KEY_128_SCHEDULE)) THEN REFL_TAC);;

(* H = AES_K(0) for McGrew-Viega GCM Test Cases 1 and 2 *)
prove(`aes128_cipher (word 0x00000000000000000000000000000000)
                     AESAVS_ZERO_KEY_128_SCHEDULE =
       word 0x66e94bd4ef8a2c3b884cfa59ca342b2e`,
  CONV_TAC(LAND_CONV(FIPS197_ENCRYPT_FAST_CONV aes128_cipher
    AESAVS_ZERO_KEY_128_SCHEDULE)) THEN REFL_TAC);;

(* ========================================================================= *)
(* KAT: AES-256 with the all-zero key                                        *)
(* ========================================================================= *)

(* H = AES_K(0) for McGrew-Viega GCM Test Cases 13 and 14 *)
prove(`aes256_cipher (word 0x00000000000000000000000000000000)
                     AESAVS_ZERO_KEY_256_SCHEDULE =
       word 0xdc95c078a2408989ad48a21492842087`,
  CONV_TAC(LAND_CONV(FIPS197_ENCRYPT_FAST_CONV aes256_cipher
    AESAVS_ZERO_KEY_256_SCHEDULE)) THEN REFL_TAC);;

(* The first AES-256 GFSbox vector (AESAVS Appendix B) *)
prove(`aes256_cipher (word 0x014730f80ac625fe84f026c60bfd547d)
                     AESAVS_ZERO_KEY_256_SCHEDULE =
       word 0x5c9d844ed46f9885085e5d6a4f94c7d7`,
  CONV_TAC(LAND_CONV(FIPS197_ENCRYPT_FAST_CONV aes256_cipher
    AESAVS_ZERO_KEY_256_SCHEDULE)) THEN REFL_TAC);;

(* ========================================================================= *)
(* KAT: AES-256 with the McGrew-Viega GCM Test Case 15 key                   *)
(* ========================================================================= *)

(* E(K,J0), where J0 = IV || 1 = 0xCAFEBABEFACEDBADDECAF88800000001 *)
prove(`aes256_cipher (word 0xCAFEBABEFACEDBADDECAF88800000001)
                     NIST_TC15_KEY_SCHEDULE =
       word 0xfd2caa16a5832e76aa132c1453eeda7e`,
  CONV_TAC(LAND_CONV(FIPS197_ENCRYPT_FAST_CONV aes256_cipher
    NIST_TC15_KEY_SCHEDULE)) THEN REFL_TAC);;

(* E(K,0) = H, the GHASH subkey *)
prove(`aes256_cipher (word 0x00000000000000000000000000000000)
                     NIST_TC15_KEY_SCHEDULE =
       word 0xacbef20579b4b8ebce889bac8732dad7`,
  CONV_TAC(LAND_CONV(FIPS197_ENCRYPT_FAST_CONV aes256_cipher
    NIST_TC15_KEY_SCHEDULE)) THEN REFL_TAC);;
