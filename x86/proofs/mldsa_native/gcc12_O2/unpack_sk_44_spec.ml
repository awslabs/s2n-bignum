(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a secret key: the statement. This is the code for            *)
(* mldsa44_unpack_sk (mld_unpack_sk in packing.c) from mldsa-native's        *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mldsa_native/README.md): it copies rho, key and tr out of the 2560 bytes  *)
(* of the secret key with 128-bit loads and stores, and unpacks the 4        *)
(* polynomials of s1, the 4 of s2 and the 4 of t0 and transforms them to the *)
(* NTT domain, calling mldsa44_polyvecl_unpack_eta, mldsa44_polyvecl_ntt,    *)
(* mldsa44_polyveck_unpack_eta and mldsa44_polyveck_ntt, then                *)
(* mldsa_polyt0_unpack for each polynomial of t0 in a loop and               *)
(* mldsa44_polyveck_ntt in a tail call. Its seventh argument, the address of *)
(* the secret key, is on the stack, as the System V ABI passes it. It is     *)
(* verified in the whole image (see libmldsa.ml) against mld_polyvec_map     *)
(* mld_poly_ntt and mld_polyvec_unpack of common/mldsa_native_polyvec.ml,    *)
(* using the theorems for the callees, and shown to be constant time and     *)
(* memory safe.                                                              *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_unpack_eta_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_ntt_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyveck_unpack_eta_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyveck_ntt_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyt0_unpack_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_unpack_sk:
       +0x0  push    r13
       +0x2  mov     r13, rcx
       +0x5  push    r12
       +0x7  mov     r12, r8
       +0xa  push    rbp
       +0xb  push    rbx
       +0xc  mov     rbx, r9
       +0xf  sub     rsp, 0x8
      +0x13  mov     rbp, QWORD PTR [rsp+0x30]
      +0x18  movdqu  xmm0, XMMWORD PTR [rbp+0x0]
      +0x1d  movups  XMMWORD PTR [rdi], xmm0
      +0x20  movdqu  xmm1, XMMWORD PTR [rbp+0x10]
      +0x25  movups  XMMWORD PTR [rdi+0x10], xmm1
      +0x29  movdqu  xmm2, XMMWORD PTR [rbp+0x20]
      +0x2e  mov     rdi, r8
      +0x31  movups  XMMWORD PTR [rdx], xmm2
      +0x34  movdqu  xmm3, XMMWORD PTR [rbp+0x30]
      +0x39  movups  XMMWORD PTR [rdx+0x10], xmm3
      +0x3d  movdqu  xmm4, XMMWORD PTR [rbp+0x40]
      +0x42  movups  XMMWORD PTR [rsi], xmm4
      +0x45  movdqu  xmm5, XMMWORD PTR [rbp+0x50]
      +0x4a  movups  XMMWORD PTR [rsi+0x10], xmm5
      +0x4e  movdqu  xmm6, XMMWORD PTR [rbp+0x60]
      +0x53  movups  XMMWORD PTR [rsi+0x20], xmm6
      +0x57  movdqu  xmm7, XMMWORD PTR [rbp+0x70]
      +0x5c  movups  XMMWORD PTR [rsi+0x30], xmm7
      +0x60  lea     rsi, [rbp+0x80]
      +0x67  call    mldsa44_polyvecl_unpack_eta
     after_mldsa44_polyvecl_unpack_eta:
      +0x6c  mov     rdi, r12
      +0x6f  mov     r12, r13
      +0x72  call    mldsa44_polyvecl_ntt
     after_mldsa44_polyvecl_ntt:
      +0x77  lea     rsi, [rbp+0x200]
      +0x7e  mov     rdi, rbx
      +0x81  call    mldsa44_polyveck_unpack_eta
     after_mldsa44_polyveck_unpack_eta:
      +0x86  mov     rdi, rbx
      +0x89  lea     rbx, [rbp+0x380]
      +0x90  add     rbp, 0xa00
      +0x97  call    mldsa44_polyveck_ntt
     loop1: after_mldsa44_polyveck_ntt:
      +0x9c  mov     rsi, rbx
      +0x9f  mov     rdi, r12
      +0xa2  add     rbx, 0x1a0
      +0xa9  add     r12, 0x400
      +0xb0  call    mldsa_polyt0_unpack
     loop1_test: after_mldsa_polyt0_unpack:
      +0xb5  cmp     rbx, rbp
     loop1_back:
      +0xb8  jne     loop1
     loop1_exit:
      +0xba  add     rsp, 0x8
      +0xbe  mov     rdi, r13
      +0xc1  pop     rbx
      +0xc2  pop     rbp
      +0xc3  pop     r12
      +0xc5  pop     r13
      +0xc7  jmp     mldsa44_polyveck_ntt
 ***)

let MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_unpack_sk"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The secret key at sk, given byte by byte by skb, has rho,    *)
(* key and tr in its first 128 bytes, then the packed polynomials of s1 (4   *)
(* of 96 bytes each, from byte 128), s2 (4, from byte 512) and t0 (4 of 416  *)
(* bytes, from byte 896). The bytes of rho, tr and key are copied to rho, tr *)
(* and key, and the vectors of the unpacked polynomials of t0, s1 and s2 in  *)
(* the NTT domain to t0, s1 and s2, with 256 coefficients of 32 bits for     *)
(* each polynomial (see common/mldsa_native_polyvec.ml). The address sk is   *)
(* the seventh argument, in the 8 bytes above the return address. The        *)
(* outputs and the stack frame, of the function and its callees, are         *)
(* disjoint from each other, the code and the secret key, and the outputs    *)
(* from the slots of the return address and of sk. The stack frame is the 40 *)
(* bytes where the function saves RBX, RBP, R12 and R13 and keeps 8 more,    *)
(* the slot below them for the return address of a call, and the 72 bytes    *)
(* below that of mldsa44_polyvecl_ntt (120 bytes in all).                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!rho tr key t0 s1 s2 sk skb pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,4096); (s1,4096); (s2,4096);
          (word_sub stackpointer (word 120),120)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,4096); (s1,4096); (s2,4096);
          (word_sub stackpointer (word 120),120)]
         [(word pc,libmldsa_size); (sk,2560)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,4096); (s1,4096); (s2,4096)]
         [(stackpointer,8); (word_add stackpointer (word 8),8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_unpack_sk) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [rho; tr; key; t0; s1; s2] s /\
                  read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                    sk /\
                  (!j. j < 2560
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
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add t0 (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 416 mld_polyt0_unpack
                              (\j. skb(896 + j))) i) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add s1 (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                              (\j. skb(128 + j))) i) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add s2 (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                              (\j. skb(512 + j))) i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(rho,32);
                memory :> bytes(tr,64);
                memory :> bytes(key,32);
                memory :> bytes(t0,4096);
                memory :> bytes(s1,4096);
                memory :> bytes(s2,4096);
                memory :> bytes(word_sub stackpointer (word 120),120)])`;;

let MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* secret key, t0, s1, s2, the table of the NTT, the stack frame and the     *)
(* slots of the return address and of sk (the copies rho, tr and key are     *)
(* only written), and the writes within the outputs and the stack frame.     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e rho tr key t0 s1 s2 sk skb pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,4096); (s1,4096); (s2,4096);
          (word_sub stackpointer (word 120),120)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,4096); (s1,4096); (s2,4096);
          (word_sub stackpointer (word 120),120)]
         [(word pc,libmldsa_size); (sk,2560)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,4096); (s1,4096); (s2,4096)]
         [(stackpointer,8); (word_add stackpointer (word 8),8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_unpack_sk) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [rho; tr; key; t0; s1; s2] s /\
                  read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                    sk /\
                  (!j. j < 2560
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
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add t0 (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 416 mld_polyt0_unpack
                              (\j. skb(896 + j))) i) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add s1 (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                              (\j. skb(128 + j))) i) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add s2 (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 96 mld_polyeta_unpack_2
                              (\j. skb(512 + j))) i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events rho tr key t0 s1 s2 sk pc
                                 (word_sub stackpointer (word 120))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [sk,2560; t0,4096; s1,4096; s2,4096;
                       word(pc + rodata_mld_zetas),1024;
                       word_sub stackpointer (word 120),120; stackpointer,8;
                       word_add stackpointer (word 8),8]
                      [rho,32; tr,64; key,32; t0,4096; s1,4096; s2,4096;
                       word_sub stackpointer (word 120),120]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(rho,32);
                memory :> bytes(tr,64);
                memory :> bytes(key,32);
                memory :> bytes(t0,4096);
                memory :> bytes(s1,4096);
                memory :> bytes(s2,4096);
                memory :> bytes(word_sub stackpointer (word 120),120)])`;;

let MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e rho tr key t0 s1 s2 sk pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,4096); (s1,4096); (s2,4096);
          (word_sub stackpointer (word 120),120)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,4096); (s1,4096); (s2,4096);
          (word_sub stackpointer (word 120),120)]
         [(word pc,libmldsa_size); (sk,2560)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,4096); (s1,4096); (s2,4096)]
         [(stackpointer,8); (word_add stackpointer (word 8),8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_unpack_sk) /\
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
                     e2 = f_events rho tr key t0 s1 s2 sk pc
                                 (word_sub stackpointer (word 120))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [sk,2560; t0,4096; s1,4096; s2,4096;
                       word(pc + rodata_mld_zetas),1024;
                       word_sub stackpointer (word 120),120; stackpointer,8;
                       word_add stackpointer (word 8),8]
                      [rho,32; tr,64; key,32; t0,4096; s1,4096; s2,4096;
                       word_sub stackpointer (word 120),120]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(rho,32);
                memory :> bytes(tr,64);
                memory :> bytes(key,32);
                memory :> bytes(t0,4096);
                memory :> bytes(s1,4096);
                memory :> bytes(s2,4096);
                memory :> bytes(word_sub stackpointer (word 120),120)])`;;

let MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_UNPACK_SK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
