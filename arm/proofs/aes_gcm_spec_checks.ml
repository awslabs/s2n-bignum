(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Checks of the AES-GCM specification files that no proof depends on, run   *)
(* once by "make proofs" (see arm/Makefile) rather than at every load of the *)
(* specification by the AES-GCM proofs.                                      *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(* The GHASH and POLYVAL polynomials are irreducible over GF(2).             *)

needs "common/gf128_irreducible.ml";;

(* Known-answer tests of FIPS 197 AES and of NIST SP 800-38D GCM.            *)

needs "common/fips197_kats.ml";;
needs "common/gcm_kats.ml";;

(* The GHASH key tables of the 8-way kernels at four keys.                   *)

needs "arm/proofs/utils/aes_gcm_common.ml";;

(* ========================================================================= *)
(* Known-answer instances of htable_mem_8, the GHASH key-table predicate of  *)
(* arm/proofs/utils/aes_gcm_spec.ml, at four concrete keys.                  *)
(*                                                                           *)
(* In the shared AES-GCM vocabulary the GHASH key is H = aesN_cipher (word   *)
(* 0) rk, with rk the FIPS-197 key schedule, and the key-table precondition  *)
(* of the 8-way kernels is htable_mem_8 (ghash_twist H) htable_p s.  Below   *)
(* that precondition is evaluated by HTABLE_MEM_8_KEY_CONV, for the all-zero *)
(* AES-128 and AES-256 keys, the FIPS-197 Appendix B AES-128 key and the     *)
(* AES-256 key of GCM test case 15 (the key schedules of common/fips197.ml), *)
(* to the 12 table entries.  They are the bytes AWS-LC's gcm_init_v8 writes  *)
(* for those keys, and the bytes ref_gcm_init_htable writes in the C test    *)
(* aes_gcm_htable (tests/test.c), so they tie the precondition to the real   *)
(* table: stated with a wrong H, such as the byte-reversed ones at the end,  *)
(* it does not match them.  The 8-way proofs evaluate the same precondition  *)
(* at the all-zero key in their *_ZERO_KEY_CORRECT theorems                  *)
(* (ALT_ZERO_KEY_RULE).                                                      *)
(* ========================================================================= *)

(* All-zero key: H = 66e94bd4ef8a2c3b884cfa59ca342b2e. *)

let HTABLE_MEM_8_AESAVS_ZERO_KEY_128 = prove
 (`!ptr s.
     htable_mem_8
       (ghash_twist (aes128_cipher (word 0) AESAVS_ZERO_KEY_128_SCHEDULE))
       ptr s <=>
     read (memory :> bytes128 ptr) s =
       word 0x1099f4b39468565ccdd297a9df145877 /\
     read (memory :> bytes128 (word_add ptr (word 16))) s =
       word 0x62d81a7fe5da3296dd4b631a4b7c0e2b /\
     read (memory :> bytes128 (word_add ptr (word 32))) s =
       word 0xea0b3a488cb9209b88d320376963120d /\
     read (memory :> bytes128 (word_add ptr (word 48))) s =
       word 0x35c1a04f8bfb23958695e702c322faf9 /\
     read (memory :> bytes128 (word_add ptr (word 64))) s =
       word 0xb2261b4d0cb1e020b354474d48d9d96c /\
     read (memory :> bytes128 (word_add ptr (word 80))) s =
       word 0xe4adc23e440c7165568bd97348bd9145 /\
     read (memory :> bytes128 (word_add ptr (word 96))) s =
       word 0x7d845b630bb0a55df9151b1f632d10b4 /\
     read (memory :> bytes128 (word_add ptr (word 112))) s =
       word 0xa674eba8f9d7f2508491407c689db5e9 /\
     read (memory :> bytes128 (word_add ptr (word 128))) s =
       word 0x4af32418184aee1eec87cfb0e19d1c4e /\
     read (memory :> bytes128 (word_add ptr (word 144))) s =
       word 0xf109e6e0b31d1eee7d1998bcfc545474 /\
     read (memory :> bytes128 (word_add ptr (word 160))) s =
       word 0x7498729da40cd2808c107e5c4f494a9a /\
     read (memory :> bytes128 (word_add ptr (word 176))) s =
       word 0xa47c653dfbeac924d0e417a05fe61ba4`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(HTABLE_MEM_8_KEY_CONV aes128_cipher
                       AESAVS_ZERO_KEY_128_SCHEDULE)) THEN
  REFL_TAC);;

(* FIPS-197 Appendix B key 2b7e151628aed2a6abf7158809cf4f3c:                 *)
(* H = 7df76b0c1ab899b33e42f047b91b546f.                                     *)

let HTABLE_MEM_8_AES128_APPENDIX_B_KEY = prove
 (`!ptr s.
     htable_mem_8
       (ghash_twist (aes128_cipher (word 0) AES128_APPENDIX_B_KEY_SCHEDULE))
       ptr s <=>
     read (memory :> bytes128 ptr) s =
       word 0x7c85e08f7236a8defbeed61835713366 /\
     read (memory :> bytes128 (word_add ptr (word 16))) s =
       word 0xed6f9f19824188b7876b369747479bb8 /\
     read (memory :> bytes128 (word_add ptr (word 32))) s =
       word 0x75fc1bd05afdf91d989384c9d8bc71aa /\
     read (memory :> bytes128 (word_add ptr (word 48))) s =
       word 0x079dada037f75a219393f2f6b5901aa5 /\
     read (memory :> bytes128 (word_add ptr (word 64))) s =
       word 0x5c266e54fcbe70c8940e5f5682674084 /\
     read (memory :> bytes128 (word_add ptr (word 80))) s =
       word 0x4cd5a7571d1a07eb10f3c903e1a47723 /\
     read (memory :> bytes128 (word_add ptr (word 96))) s =
       word 0x1868d687e354011277b65543fd05070d /\
     read (memory :> bytes128 (word_add ptr (word 112))) s =
       word 0x90da1b5ab6308b846fde83c41e51061f /\
     read (memory :> bytes128 (word_add ptr (word 128))) s =
       word 0x43c1c170f6d1cb18d31bda2a40e1409c /\
     read (memory :> bytes128 (word_add ptr (word 144))) s =
       word 0x71a7fa7ec9a2db6a9942b75d8497af5b /\
     read (memory :> bytes128 (word_add ptr (word 160))) s =
       word 0xdff6bfdf58dc7226e8e54d234d357431 /\
     read (memory :> bytes128 (word_add ptr (word 176))) s =
       word 0xbfae27a59d0f85db6058987ac5d3f7fd`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(HTABLE_MEM_8_KEY_CONV aes128_cipher
                       AES128_APPENDIX_B_KEY_SCHEDULE)) THEN
  REFL_TAC);;

(* The byte-reversed key word_reversefields 8 H (the little-endian reading   *)
(* of AES_K(0^128)) describes a different table: at the all-zero key none of *)
(* its 12 entries equals the real one, so a key-table precondition stated    *)
(* with it is not satisfied by the table AWS-LC's gcm_init_v8 builds.        *)

let HTABLE_MEM_8_AESAVS_ZERO_KEY_128_REVERSED_H = prove
 (`!ptr s.
     htable_mem_8
       (ghash_twist (aes128_cipher (word 0) AESAVS_ZERO_KEY_128_SCHEDULE))
       ptr s
     ==> ~htable_mem_8
            (ghash_twist (word_reversefields 8
               (aes128_cipher (word 0) AESAVS_ZERO_KEY_128_SCHEDULE)))
            ptr s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HTABLE_MEM_8_AESAVS_ZERO_KEY_128] THEN
  CONV_TAC(RAND_CONV(RAND_CONV(HTABLE_MEM_8_KEY_CONV aes128_cipher
                                 AESAVS_ZERO_KEY_128_SCHEDULE))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;

(* All-zero key: H = dc95c078a2408989ad48a21492842087. *)

let HTABLE_MEM_8_AESAVS_ZERO_KEY_256 = prove
 (`!ptr s.
     htable_mem_8
       (ghash_twist (aes256_cipher (word 0) AESAVS_ZERO_KEY_256_SCHEDULE))
       ptr s <=>
     read (memory :> bytes128 ptr) s =
       word 0x5a9144292508410f7b2b80f144811313 /\
     read (memory :> bytes128 (word_add ptr (word 16))) s =
       word 0x18815f770318b11721bac4d86189521c /\
     read (memory :> bytes128 (word_add ptr (word 32))) s =
       word 0x5505a2719d24c36f4d84fd069e3c7278 /\
     read (memory :> bytes128 (word_add ptr (word 48))) s =
       word 0x8cc3bf92b3c5611f175e7336e8418ee0 /\
     read (memory :> bytes128 (word_add ptr (word 64))) s =
       word 0xba81c249997cd6fd9b9dcca45b84efff /\
     read (memory :> bytes128 (word_add ptr (word 80))) s =
       word 0xf27b604459a2c40248faa20dc0de12ff /\
     read (memory :> bytes128 (word_add ptr (word 96))) s =
       word 0xf39c9203a58c04ab9eb1c1ebb05c4519 /\
     read (memory :> bytes128 (word_add ptr (word 112))) s =
       word 0x1ea16b4e105889f96d2d53e815d041b2 /\
     read (memory :> bytes128 (word_add ptr (word 128))) s =
       word 0x2a0cb6bcb97d97a834adddf2a9251e51 /\
     read (memory :> bytes128 (word_add ptr (word 144))) s =
       word 0xa14610bf3e3af4c23287a42fbc7357c2 /\
     read (memory :> bytes128 (word_add ptr (word 160))) s =
       word 0x19ae23037094693f93c1b4908249a300 /\
     read (memory :> bytes128 (word_add ptr (word 176))) s =
       word 0x6d9364db65b87552743d47d8152c1c6d`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(HTABLE_MEM_8_KEY_CONV aes256_cipher
                       AESAVS_ZERO_KEY_256_SCHEDULE)) THEN
  REFL_TAC);;

(* GCM test case 15 key: H = acbef20579b4b8ebce889bac8732dad7. *)

let HTABLE_MEM_8_NIST_TC15_KEY = prove
 (`!ptr s.
     htable_mem_8
       (ghash_twist (aes256_cipher (word 0) NIST_TC15_KEY_SCHEDULE))
       ptr s <=>
     read (memory :> bytes128 ptr) s =
       word 0x9d1137590e65b5af9b7de40af36971d7 /\
     read (memory :> bytes128 (word_add ptr (word 16))) s =
       word 0x6250d1e611963320066cd353fd0cc478 /\
     read (memory :> bytes128 (word_add ptr (word 32))) s =
       word 0x176ea7748156c4f7753e769290c0f7d7 /\
     read (memory :> bytes128 (word_add ptr (word 48))) s =
       word 0x4dacf0715be378138f106846b8c7ae56 /\
     read (memory :> bytes128 (word_add ptr (word 64))) s =
       word 0xa11c7beedb2faa97c2bc9837e324d645 /\
     read (memory :> bytes128 (word_add ptr (word 80))) s =
       word 0x11818ff911a91b65b09df417ca86b1f2 /\
     read (memory :> bytes128 (word_add ptr (word 96))) s =
       word 0x90b5acfc5229d0fae997267d30d323f3 /\
     read (memory :> bytes128 (word_add ptr (word 112))) s =
       word 0x5ad8655f4ae49a2f79228a8162faf309 /\
     read (memory :> bytes128 (word_add ptr (word 128))) s =
       word 0x9ad471bb94ce90d0c00c14e4de2a0aff /\
     read (memory :> bytes128 (word_add ptr (word 144))) s =
       word 0xd230a7e922dc7379c75ff4dd09d4a3be /\
     read (memory :> bytes128 (word_add ptr (word 160))) s =
       word 0xfd00063de14f053f156f53342b08d0c7 /\
     read (memory :> bytes128 (word_add ptr (word 176))) s =
       word 0x1387f5ed06b50431ee87f3d0e7fa010e`,
  REPEAT GEN_TAC THEN
  CONV_TAC(LAND_CONV(HTABLE_MEM_8_KEY_CONV aes256_cipher
                       NIST_TC15_KEY_SCHEDULE)) THEN
  REFL_TAC);;

(* The byte-reversed key word_reversefields 8 H (the little-endian reading   *)
(* of AES_K(0^128)) describes a different table: at the all-zero key none of *)
(* its 12 entries equals the real one, so a key-table precondition stated    *)
(* with it is not satisfied by the table AWS-LC's gcm_init_v8 builds.        *)

let HTABLE_MEM_8_AESAVS_ZERO_KEY_256_REVERSED_H = prove
 (`!ptr s.
     htable_mem_8
       (ghash_twist (aes256_cipher (word 0) AESAVS_ZERO_KEY_256_SCHEDULE))
       ptr s
     ==> ~htable_mem_8
            (ghash_twist (word_reversefields 8
               (aes256_cipher (word 0) AESAVS_ZERO_KEY_256_SCHEDULE)))
            ptr s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HTABLE_MEM_8_AESAVS_ZERO_KEY_256] THEN
  CONV_TAC(RAND_CONV(RAND_CONV(HTABLE_MEM_8_KEY_CONV aes256_cipher
                                 AESAVS_ZERO_KEY_256_SCHEDULE))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC WORD_REDUCE_CONV);;


List.iter (fun th -> Printf.printf "%s\n" (string_of_thm th))
  [RING_IRREDUCIBLE_GHASH_POLYNOMIAL; RING_IRREDUCIBLE_POLYVAL_POLYNOMIAL;
   GCM_AE_TC1; GCM_AE_TC2; GCM_AE_TC3; GCM_AE_TC13; GCM_AE_TC14; GCM_AE_TC15;
   GCM_AD_TC3; GCM_AD_TC3_BAD_TAG;
   HTABLE_MEM_8_AESAVS_ZERO_KEY_128; HTABLE_MEM_8_AES128_APPENDIX_B_KEY;
   HTABLE_MEM_8_AESAVS_ZERO_KEY_128_REVERSED_H;
   HTABLE_MEM_8_AESAVS_ZERO_KEY_256; HTABLE_MEM_8_NIST_TC15_KEY;
   HTABLE_MEM_8_AESAVS_ZERO_KEY_256_REVERSED_H];;
