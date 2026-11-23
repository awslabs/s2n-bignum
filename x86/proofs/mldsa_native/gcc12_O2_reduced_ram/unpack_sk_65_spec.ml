(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a secret key, lazily: the statement. This is the code for    *)
(* mldsa65_unpack_sk (mld_unpack_sk in packing.c) from mldsa-native's        *)
(* portable C implementation compiled by gcc 12 with -O2 and                 *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md). In this configuration *)
(* the vectors s1, s2 and t0 of the secret key are not unpacked: their       *)
(* structures (mld_sk_s1hat_lazy and so on, see polyvec_lazy.h) only borrow  *)
(* the packed polynomials, and signing unpacks and transforms each           *)
(* polynomial when it is needed. So the code copies rho, key and tr out of   *)
(* the 4032 bytes of the secret key with 128-bit loads and stores, and       *)
(* stores the addresses of the packed s1, s2 and t0 in the secret key in the *)
(* structures. Its seventh argument, the address of the secret key, is on    *)
(* the stack, as the System V ABI passes it. It is verified in the whole     *)
(* image (see libmldsa.ml) and shown to be constant time and memory safe.    *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa65_unpack_sk:
       +0x0  mov     rax, QWORD PTR [rsp+0x8]
       +0x5  movdqu  xmm0, XMMWORD PTR [rax]
       +0x9  movups  XMMWORD PTR [rdi], xmm0
       +0xc  movdqu  xmm1, XMMWORD PTR [rax+0x10]
      +0x11  movups  XMMWORD PTR [rdi+0x10], xmm1
      +0x15  movdqu  xmm2, XMMWORD PTR [rax+0x20]
      +0x1a  movups  XMMWORD PTR [rdx], xmm2
      +0x1d  movdqu  xmm3, XMMWORD PTR [rax+0x30]
      +0x22  movups  XMMWORD PTR [rdx+0x10], xmm3
      +0x26  movdqu  xmm4, XMMWORD PTR [rax+0x40]
      +0x2b  lea     rdx, [rax+0x80]
      +0x32  movups  XMMWORD PTR [rsi], xmm4
      +0x35  movdqu  xmm5, XMMWORD PTR [rax+0x50]
      +0x3a  movups  XMMWORD PTR [rsi+0x10], xmm5
      +0x3e  movdqu  xmm6, XMMWORD PTR [rax+0x60]
      +0x43  movups  XMMWORD PTR [rsi+0x20], xmm6
      +0x47  movdqu  xmm7, XMMWORD PTR [rax+0x70]
      +0x4c  movups  XMMWORD PTR [rsi+0x30], xmm7
      +0x50  mov     QWORD PTR [r8], rdx
      +0x53  lea     rdx, [rax+0x300]
      +0x5a  add     rax, 0x600
      +0x60  mov     QWORD PTR [r9], rdx
      +0x63  mov     QWORD PTR [rcx], rax
     ret:
      +0x66  ret
 ***)

let MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa65_unpack_sk"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The secret key at sk, given byte by byte by skb, has rho,    *)
(* key and tr in its first 128 bytes, then the packed polynomials of s1 (5   *)
(* of 128 bytes each, from byte 128), s2 (6, from byte 768) and t0 (6 of 416 *)
(* bytes, from byte 1536). The bytes of rho, tr and key are copied to rho,   *)
(* tr and key, and the addresses sk + 128, sk + 768 and sk + 1536 stored in  *)
(* the structures (one address of 8 bytes each) at s1, s2 and t0. The        *)
(* address sk is the seventh argument, in the 8 bytes above the return       *)
(* address. The function uses no stack. The outputs are disjoint from each   *)
(* other, the code, the secret key and the slots of the return address and   *)
(* of sk.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!rho tr key t0 s1 s2 sk skb pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,8); (s1,8); (s2,8)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,8); (s1,8); (s2,8)]
         [(word pc,libmldsa_size); (sk,4032); (stackpointer,8);
          (word_add stackpointer (word 8),8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_unpack_sk) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [rho; tr; key; t0; s1; s2] s /\
                  read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                    sk /\
                  (!j. j < 4032
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           skb j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add rho (word j))) s =
                           skb j) /\
                  (!j. j < 64
                       ==> read(memory :> bytes8(word_add tr (word j))) s =
                           skb(64 + j)) /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add key (word j))) s =
                           skb(32 + j)) /\
                  read (memory :> bytes64 s1) s = word_add sk (word 128) /\
                  read (memory :> bytes64 s2) s = word_add sk (word 768) /\
                  read (memory :> bytes64 t0) s = word_add sk (word 1536))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(rho,32); memory :> bytes(tr,64);
                memory :> bytes(key,32); memory :> bytes(t0,8);
                memory :> bytes(s1,8); memory :> bytes(s2,8)])`;;

let MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* secret key and the slots of the return address and of sk, and the writes  *)
(* within the outputs.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e rho tr key t0 s1 s2 sk skb pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,8); (s1,8); (s2,8)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,8); (s1,8); (s2,8)]
         [(word pc,libmldsa_size); (sk,4032); (stackpointer,8);
          (word_add stackpointer (word 8),8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_unpack_sk) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [rho; tr; key; t0; s1; s2] s /\
                  read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                    sk /\
                  (!j. j < 4032
                       ==> read(memory :> bytes8(word_add sk (word j))) s =
                           skb j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add rho (word j))) s =
                           skb j) /\
                  (!j. j < 64
                       ==> read(memory :> bytes8(word_add tr (word j))) s =
                           skb(64 + j)) /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add key (word j))) s =
                           skb(32 + j)) /\
                  read (memory :> bytes64 s1) s = word_add sk (word 128) /\
                  read (memory :> bytes64 s2) s = word_add sk (word 768) /\
                  read (memory :> bytes64 t0) s = word_add sk (word 1536) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events rho tr key t0 s1 s2 sk pc stackpointer
                                   returnaddress /\
                     memaccess_inbounds e2
                      [sk,4032; stackpointer,8; word_add stackpointer (word 8),8]
                      [rho,32; tr,64; key,32; t0,8; s1,8; s2,8]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(rho,32); memory :> bytes(tr,64);
                memory :> bytes(key,32); memory :> bytes(t0,8);
                memory :> bytes(s1,8); memory :> bytes(s2,8)])`;;

let MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e rho tr key t0 s1 s2 sk pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,8); (s1,8); (s2,8)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,8); (s1,8); (s2,8)]
         [(word pc,libmldsa_size); (sk,4032); (stackpointer,8);
          (word_add stackpointer (word 8),8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa65_unpack_sk) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [rho; tr; key; t0; s1; s2] s /\
                  read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                    sk /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events rho tr key t0 s1 s2 sk pc stackpointer
                                   returnaddress /\
                     memaccess_inbounds e2
                      [sk,4032; stackpointer,8; word_add stackpointer (word 8),8]
                      [rho,32; tr,64; key,32; t0,8; s1,8; s2,8]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(rho,32); memory :> bytes(tr,64);
                memory :> bytes(key,32); memory :> bytes(t0,8);
                memory :> bytes(s1,8); memory :> bytes(s2,8)])`;;

let MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
