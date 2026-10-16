(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Known-answer instances of htable_mem_8 at two concrete AES-256 keys.      *)
(*                                                                           *)
(* In the shared AES-GCM vocabulary the GHASH key is                         *)
(* H = aes256_cipher (word 0) rk, with rk the FIPS-197 key schedule, and the *)
(* key table precondition of the 8-way kernels is                            *)
(* htable_mem_8 (ghash_twist H) htbl_p s.  Below that precondition is        *)
(* evaluated, for the all-zero key and for the McGrew-Viega GCM test case 15 *)
(* key (the key schedules of common/fips197.ml), to the 12 table entries.    *)
(* They are the bytes gcm_init_v8 writes for those keys, and the bytes       *)
(* ref_gcm_init_htable writes in the C test "aes_gcm_htable" (tests/test.c), *)
(* so they tie the precondition to the real table: stated with a wrong H,    *)
(* such as the byte-reversed one at the end, it does not match them.         *)
(* ========================================================================= *)

needs "arm/proofs/utils/aes_gcm_common.ml";;

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
(* with it is not satisfied by the table gcm_init_v8 builds.                 *)

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
