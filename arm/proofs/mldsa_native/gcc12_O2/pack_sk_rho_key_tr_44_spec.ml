(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Copying rho, K and tr to the start of a secret key: the statement. This   *)
(* is the code for mldsa44_pack_sk_rho_key_tr (mld_pack_sk_rho_key_tr in     *)
(* packing.c) from mldsa-native's portable C implementation compiled by gcc  *)
(* 12 with -O2 (see mldsa_native/README.md), in which the three calls of     *)
(* memcpy are inlined. It is verified in the whole image (see libmldsa.ml),  *)
(* and shown to be constant time and memory safe.                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_pack_sk_rho_key_tr:
       +0x0: ldp     q0, q1, [x1]
       +0x4: add     x4, x0, #0x40
       +0x8: stp     q0, q1, [x0]
       +0xc: ldp     q0, q1, [x3]
      +0x10: stp     q0, q1, [x0, #32]
      +0x14: ldp     q0, q1, [x2]
      +0x18: stp     q0, q1, [x4]
      +0x1c: ldp     q0, q1, [x2, #32]
      +0x20: stp     q0, q1, [x4, #32]
      +0x24: ret
 ***)

let MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_pack_sk_rho_key_tr"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The 32 bytes r of rho, the 64 bytes t of tr and the 32 bytes *)
(* k of the key, which may not overlap the first 128 bytes of the secret key *)
(* at sk, become its bytes 0 to 31, 64 to 127 and 32 to 63.                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!sk rho tr key r t k pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (sk,128))
            [(word pc,libmldsa_size); (rho,32); (tr,64); (key,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_pack_sk_rho_key_tr) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [sk; rho; tr; key] s /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add rho (word j))) s =
                           r j) /\
                  (!j. j < 64
                       ==> read(memory :> bytes8(word_add tr (word j))) s =
                           t j) /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add key (word j))) s =
                           k j))
             (\s. read PC s = returnaddress /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           r j) /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add sk (word(32 + j))))
                             s = k j) /\
                  (!j. j < 64
                       ==> read(memory :> bytes8(word_add sk (word(64 + j))))
                             s = t j))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(sk,128)])`;;

let MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the writes within the outputs.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e sk rho tr key r t k pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (sk,128))
            [(word pc,libmldsa_size); (rho,32); (tr,64); (key,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_pack_sk_rho_key_tr) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [sk; rho; tr; key] s /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add rho (word j))) s =
                           r j) /\
                  (!j. j < 64
                       ==> read(memory :> bytes8(word_add tr (word j))) s =
                           t j) /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add key (word j))) s =
                           k j) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           r j) /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add sk (word(32 + j))))
                             s = k j) /\
                  (!j. j < 64
                       ==> read(memory :> bytes8(word_add sk (word(64 + j))))
                             s = t j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events sk rho tr key pc returnaddress /\
                     memaccess_inbounds e2
                      [rho,32; tr,64; key,32; sk,128]
                      [sk,128]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(sk,128)])`;;

let MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e sk rho tr key pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (sk,128))
            [(word pc,libmldsa_size); (rho,32); (tr,64); (key,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_pack_sk_rho_key_tr) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [sk; rho; tr; key] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events sk rho tr key pc returnaddress /\
                     memaccess_inbounds e2
                      [rho,32; tr,64; key,32; sk,128]
                      [sk,128]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(sk,128)])`;;

let MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
