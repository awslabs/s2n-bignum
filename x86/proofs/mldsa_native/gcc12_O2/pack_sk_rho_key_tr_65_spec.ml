(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Copying rho, K and tr to the start of a secret key: the statement. This   *)
(* is the code for mldsa65_pack_sk_rho_key_tr (mld_pack_sk_rho_key_tr in     *)
(* packing.c) from mldsa-native's portable C implementation compiled by gcc  *)
(* 12 with -O2 (see mldsa_native/README.md), in which the three calls of     *)
(* memcpy are inlined. It is verified in the whole image (see libmldsa.ml),  *)
(* and shown to be constant time and memory safe.                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_pack_sk_rho_key_tr:
       +0x0  movdqu  xmm0, XMMWORD PTR [rsi]
       +0x4  movups  XMMWORD PTR [rdi], xmm0
       +0x7  movdqu  xmm1, XMMWORD PTR [rsi+0x10]
       +0xc  movups  XMMWORD PTR [rdi+0x10], xmm1
      +0x10  movdqu  xmm2, XMMWORD PTR [rcx]
      +0x14  movups  XMMWORD PTR [rdi+0x20], xmm2
      +0x18  movdqu  xmm3, XMMWORD PTR [rcx+0x10]
      +0x1d  movups  XMMWORD PTR [rdi+0x30], xmm3
      +0x21  movdqu  xmm4, XMMWORD PTR [rdx]
      +0x25  movups  XMMWORD PTR [rdi+0x40], xmm4
      +0x29  movdqu  xmm5, XMMWORD PTR [rdx+0x10]
      +0x2e  movups  XMMWORD PTR [rdi+0x50], xmm5
      +0x32  movdqu  xmm6, XMMWORD PTR [rdx+0x20]
      +0x37  movups  XMMWORD PTR [rdi+0x60], xmm6
      +0x3b  movdqu  xmm7, XMMWORD PTR [rdx+0x30]
      +0x40  movups  XMMWORD PTR [rdi+0x70], xmm7
     ret:
      +0x44  ret
 ***)

let MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_65_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_pack_sk_rho_key_tr"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The 32 bytes r of rho, the 64 bytes t of tr and the 32 bytes *)
(* k of the key, which may not overlap the first 128 bytes of the secret key *)
(* at sk, become its bytes 0 to 31, 64 to 127 and 32 to 63.                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!sk rho tr key r t k pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (sk,128))
            [(word pc,libmldsa_size); (rho,32); (tr,64); (key,32);
             (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_pack_sk_rho_key_tr) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
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
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           r j) /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add sk (word(32 + j))))
                             s = k j) /\
                  (!j. j < 64
                       ==> read(memory :> bytes8(word_add sk (word(64 + j))))
                             s = t j))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(sk,128)])`;;

let MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the slot of the return address, and the writes     *)
(* within the outputs.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e sk rho tr key r t k pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (sk,128))
            [(word pc,libmldsa_size); (rho,32); (tr,64); (key,32);
             (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_pack_sk_rho_key_tr) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
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
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
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
                     e2 = f_events sk rho tr key pc stackpointer
                                   returnaddress /\
                     memaccess_inbounds e2
                       [rho,32; tr,64; key,32; sk,128; stackpointer,8]
                       [sk,128]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(sk,128)])`;;

let MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e sk rho tr key pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (sk,128))
            [(word pc,libmldsa_size); (rho,32); (tr,64); (key,32);
             (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_pack_sk_rho_key_tr) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [sk; rho; tr; key] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events sk rho tr key pc stackpointer
                                   returnaddress /\
                     memaccess_inbounds e2
                       [rho,32; tr,64; key,32; sk,128; stackpointer,8]
                       [sk,128]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(sk,128)])`;;

let MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_PACK_SK_RHO_KEY_TR_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
