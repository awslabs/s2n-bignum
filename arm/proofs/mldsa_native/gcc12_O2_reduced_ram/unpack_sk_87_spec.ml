(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a secret key: the statement. This is the code for            *)
(* mldsa87_unpack_sk (mld_unpack_sk in packing.c) from mldsa-native's        *)
(* portable C implementation compiled by gcc 12 with -O2 and                 *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md). With                  *)
(* MLD_CONFIG_REDUCE_RAM, s1, s2 and t0 are kept packed in the secret key    *)
(* (mld_sk_s1hat_lazy and so on, in polyvec_lazy.h): the code copies rho,    *)
(* key and tr out of the 4896 bytes of the secret key with 128-bit loads and *)
(* stores, and stores the addresses of the packed s1, s2 and t0 in the       *)
(* secret key to the structures at s1, s2 and t0. It is verified in the      *)
(* whole image (see libmldsa.ml) and shown to be constant time and memory    *)
(* safe.                                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa87_unpack_sk:
       +0x0: ldp     q0, q1, [x6]
       +0x4: add     x7, x6, #0x40
       +0x8: add     x10, x6, #0x80
       +0xc: add     x9, x6, #0x320
      +0x10: add     x8, x6, #0x620
      +0x14: stp     q0, q1, [x0]
      +0x18: ldp     q0, q1, [x6, #32]
      +0x1c: stp     q0, q1, [x2]
      +0x20: ldp     q0, q1, [x7]
      +0x24: stp     q0, q1, [x1]
      +0x28: ldp     q0, q1, [x7, #32]
      +0x2c: stp     q0, q1, [x1, #32]
      +0x30: str     x10, [x4]
      +0x34: str     x9, [x5]
      +0x38: str     x8, [x3]
      +0x3c: ret
 ***)

let MLDSA_NATIVE_UNPACK_SK_87_GCC12_O2_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa87_unpack_sk"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The secret key at sk, given byte by byte by skb, has rho,    *)
(* key and tr in its first 128 bytes, then the packed polynomials of s1 (7   *)
(* of 96 bytes each, from byte 128), s2 (8, from byte 800) and t0 (8 of 416  *)
(* bytes, from byte 1568). The bytes of rho, tr and key are copied to rho,   *)
(* tr and key, and the addresses of the packed s1, s2 and t0 are stored at   *)
(* s1, s2 and t0. The outputs are disjoint from each other, the code and the *)
(* secret key.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!rho tr key t0 s1 s2 sk skb pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,8); (s1,8); (s2,8)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,8); (s1,8); (s2,8)]
         [(word pc,libmldsa_size); (sk,4896)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read PC s = word (pc + mldsa87_unpack_sk) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [rho; tr; key; t0; s1; s2; sk] s /\
                  (!j. j < 4896
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           skb j))
             (\s. read PC s = returnaddress /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add rho (word j))) s =
                           skb j) /\
                  (!j. j < 64
                       ==> read(memory :> bytes8(word_add tr (word j))) s =
                           skb(64 + j)) /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add key (word j))) s =
                           skb(32 + j)) /\
                  read(memory :> bytes64 s1) s = word_add sk (word 128) /\
                  read(memory :> bytes64 s2) s = word_add sk (word 800) /\
                  read(memory :> bytes64 t0) s = word_add sk (word 1568))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(rho,32); memory :> bytes(tr,64);
                memory :> bytes(key,32); memory :> bytes(t0,8);
                memory :> bytes(s1,8); memory :> bytes(s2,8)])`;;

let MLDSA_NATIVE_UNPACK_SK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_UNPACK_SK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* secret key and the outputs, which are only written.                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e rho tr key t0 s1 s2 sk skb pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,8); (s1,8); (s2,8)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,8); (s1,8); (s2,8)]
         [(word pc,libmldsa_size); (sk,4896)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read PC s = word (pc + mldsa87_unpack_sk) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [rho; tr; key; t0; s1; s2; sk] s /\
                  (!j. j < 4896
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           skb j) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add rho (word j))) s =
                           skb j) /\
                  (!j. j < 64
                       ==> read(memory :> bytes8(word_add tr (word j))) s =
                           skb(64 + j)) /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add key (word j))) s =
                           skb(32 + j)) /\
                  read(memory :> bytes64 s1) s = word_add sk (word 128) /\
                  read(memory :> bytes64 s2) s = word_add sk (word 800) /\
                  read(memory :> bytes64 t0) s = word_add sk (word 1568) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events rho tr key t0 s1 s2 sk pc returnaddress /\
                     memaccess_inbounds e2
                      [sk,4896]
                      [rho,32; tr,64; key,32; t0,8; s1,8; s2,8]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(rho,32); memory :> bytes(tr,64);
                memory :> bytes(key,32); memory :> bytes(t0,8);
                memory :> bytes(s1,8); memory :> bytes(s2,8)])`;;

let MLDSA_NATIVE_UNPACK_SK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_UNPACK_SK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e rho tr key t0 s1 s2 sk pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,8); (s1,8); (s2,8)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,8); (s1,8); (s2,8)]
         [(word pc,libmldsa_size); (sk,4896)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read PC s = word (pc + mldsa87_unpack_sk) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [rho; tr; key; t0; s1; s2; sk] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events rho tr key t0 s1 s2 sk pc returnaddress /\
                     memaccess_inbounds e2
                      [sk,4896]
                      [rho,32; tr,64; key,32; t0,8; s1,8; s2,8]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(rho,32); memory :> bytes(tr,64);
                memory :> bytes(key,32); memory :> bytes(t0,8);
                memory :> bytes(s1,8); memory :> bytes(s2,8)])`;;

let MLDSA_NATIVE_UNPACK_SK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_UNPACK_SK_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
