(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a secret key: the statement. This is the code for            *)
(* mldsa65_unpack_sk (mld_unpack_sk in packing.c) from mldsa-native's        *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mldsa_native/README.md): it copies rho, key and tr out of the 4032 bytes  *)
(* of the secret key with 128-bit loads and stores, and unpacks the 5        *)
(* polynomials of s1, the 6 of s2 and the 6 of t0 and transforms them to the *)
(* NTT domain, calling mldsa65_polyvecl_unpack_eta, mldsa65_polyvecl_ntt,    *)
(* mldsa65_polyveck_unpack_eta and mldsa65_polyveck_ntt, then                *)
(* mldsa_polyt0_unpack for each polynomial of t0 in a loop and               *)
(* mldsa65_polyveck_ntt in a tail call. Its seventh argument, the address of *)
(* the secret key, is on the stack, as the System V ABI passes it. It is     *)
(* verified in the whole image (see libmldsa.ml) against mld_polyvec_map     *)
(* mld_poly_ntt and mld_polyvec_unpack of common/mldsa_native_polyvec.ml,    *)
(* using the theorems for the callees, and shown to be constant time and     *)
(* memory safe.                                                              *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_unpack_eta_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_ntt_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyveck_unpack_eta_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyveck_ntt_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyt0_unpack_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_unpack_sk:
       +0x0  push    r13
       +0x2  mov     r13, rcx
       +0x5  push    r12
       +0x7  push    rbp
       +0x8  mov     rbp, r8
       +0xb  push    rbx
       +0xc  mov     rbx, r9
       +0xf  sub     rsp, 0x8
      +0x13  mov     r12, QWORD PTR [rsp+0x30]
      +0x18  movdqu  xmm0, XMMWORD PTR [r12]
      +0x1e  movups  XMMWORD PTR [rdi], xmm0
      +0x21  movdqu  xmm1, XMMWORD PTR [r12+0x10]
      +0x28  movups  XMMWORD PTR [rdi+0x10], xmm1
      +0x2c  movdqu  xmm2, XMMWORD PTR [r12+0x20]
      +0x33  mov     rdi, r8
      +0x36  movups  XMMWORD PTR [rdx], xmm2
      +0x39  movdqu  xmm3, XMMWORD PTR [r12+0x30]
      +0x40  movups  XMMWORD PTR [rdx+0x10], xmm3
      +0x44  movdqu  xmm4, XMMWORD PTR [r12+0x40]
      +0x4b  movups  XMMWORD PTR [rsi], xmm4
      +0x4e  movdqu  xmm5, XMMWORD PTR [r12+0x50]
      +0x55  movups  XMMWORD PTR [rsi+0x10], xmm5
      +0x59  movdqu  xmm6, XMMWORD PTR [r12+0x60]
      +0x60  movups  XMMWORD PTR [rsi+0x20], xmm6
      +0x64  movdqu  xmm7, XMMWORD PTR [r12+0x70]
      +0x6b  movups  XMMWORD PTR [rsi+0x30], xmm7
      +0x6f  lea     rsi, [r12+0x80]
      +0x77  call    mldsa65_polyvecl_unpack_eta
     after_mldsa65_polyvecl_unpack_eta:
      +0x7c  mov     rdi, rbp
      +0x7f  mov     rbp, r13
      +0x82  call    mldsa65_polyvecl_ntt
     after_mldsa65_polyvecl_ntt:
      +0x87  lea     rsi, [r12+0x300]
      +0x8f  mov     rdi, rbx
      +0x92  call    mldsa65_polyveck_unpack_eta
     after_mldsa65_polyveck_unpack_eta:
      +0x97  mov     rdi, rbx
      +0x9a  lea     rbx, [r12+0x600]
      +0xa2  add     r12, 0xfc0
      +0xa9  call    mldsa65_polyveck_ntt
     after_mldsa65_polyveck_ntt:
      +0xae  xchg    ax, ax
     loop1:
      +0xb0  mov     rsi, rbx
      +0xb3  mov     rdi, rbp
      +0xb6  add     rbx, 0x1a0
      +0xbd  add     rbp, 0x400
      +0xc4  call    mldsa_polyt0_unpack
     loop1_test: after_mldsa_polyt0_unpack:
      +0xc9  cmp     rbx, r12
     loop1_back:
      +0xcc  jne     loop1
     loop1_exit:
      +0xce  add     rsp, 0x8
      +0xd2  mov     rdi, r13
      +0xd5  pop     rbx
      +0xd6  pop     rbp
      +0xd7  pop     r12
      +0xd9  pop     r13
      +0xdb  jmp     mldsa65_polyveck_ntt
 ***)

let MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_unpack_sk"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The secret key at sk, given byte by byte by skb, has rho,    *)
(* key and tr in its first 128 bytes, then the packed polynomials of s1 (5   *)
(* of 128 bytes each, from byte 128), s2 (6, from byte 768) and t0 (6 of 416 *)
(* bytes, from byte 1536). The bytes of rho, tr and key are copied to rho,   *)
(* tr and key, and the vectors of the unpacked polynomials of t0, s1 and s2  *)
(* in the NTT domain to t0, s1 and s2, with 256 coefficients of 32 bits for  *)
(* each polynomial (see common/mldsa_native_polyvec.ml). The address sk is   *)
(* the seventh argument, in the 8 bytes above the return address. The        *)
(* outputs and the stack frame, of the function and its callees, are         *)
(* disjoint from each other, the code and the secret key, and the outputs    *)
(* from the slots of the return address and of sk. The stack frame is the 40 *)
(* bytes where the function saves RBX, RBP, R12 and R13 and keeps 8 more,    *)
(* the slot below them for the return address of a call, and the 88 bytes    *)
(* below that of mldsa65_polyvecl_ntt (136 bytes in all).                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!rho tr key t0 s1 s2 sk skb pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,6144); (s1,5120); (s2,6144);
          (word_sub stackpointer (word 136),136)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,6144); (s1,5120); (s2,6144);
          (word_sub stackpointer (word 136),136)]
         [(word pc,libmldsa_size); (sk,4032)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,6144); (s1,5120); (s2,6144)]
         [(stackpointer,8); (word_add stackpointer (word 8),8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
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
                  (!i. i < 1536
                       ==> read(memory :> bytes32(word_add t0 (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 416 mld_polyt0_unpack
                              (\j. skb(1536 + j))) i) /\
                  (!i. i < 1280
                       ==> read(memory :> bytes32(word_add s1 (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 128 mld_polyeta_unpack_4
                              (\j. skb(128 + j))) i) /\
                  (!i. i < 1536
                       ==> read(memory :> bytes32(word_add s2 (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 128 mld_polyeta_unpack_4
                              (\j. skb(768 + j))) i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(rho,32);
                memory :> bytes(tr,64);
                memory :> bytes(key,32);
                memory :> bytes(t0,6144);
                memory :> bytes(s1,5120);
                memory :> bytes(s2,6144);
                memory :> bytes(word_sub stackpointer (word 136),136)])`;;

let MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* secret key, t0, s1, s2, the table of the NTT, the stack frame and the     *)
(* slots of the return address and of sk (the copies rho, tr and key are     *)
(* only written), and the writes within the outputs and the stack frame.     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e rho tr key t0 s1 s2 sk skb pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,6144); (s1,5120); (s2,6144);
          (word_sub stackpointer (word 136),136)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,6144); (s1,5120); (s2,6144);
          (word_sub stackpointer (word 136),136)]
         [(word pc,libmldsa_size); (sk,4032)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,6144); (s1,5120); (s2,6144)]
         [(stackpointer,8); (word_add stackpointer (word 8),8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
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
                  (!i. i < 1536
                       ==> read(memory :> bytes32(word_add t0 (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 416 mld_polyt0_unpack
                              (\j. skb(1536 + j))) i) /\
                  (!i. i < 1280
                       ==> read(memory :> bytes32(word_add s1 (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 128 mld_polyeta_unpack_4
                              (\j. skb(128 + j))) i) /\
                  (!i. i < 1536
                       ==> read(memory :> bytes32(word_add s2 (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_ntt
                            (mld_polyvec_unpack 128 mld_polyeta_unpack_4
                              (\j. skb(768 + j))) i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events rho tr key t0 s1 s2 sk pc
                                 (word_sub stackpointer (word 136))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [sk,4032; t0,6144; s1,5120; s2,6144;
                       word(pc + rodata_mld_zetas),1024;
                       word_sub stackpointer (word 136),136; stackpointer,8;
                       word_add stackpointer (word 8),8]
                      [rho,32; tr,64; key,32; t0,6144; s1,5120; s2,6144;
                       word_sub stackpointer (word 136),136]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(rho,32);
                memory :> bytes(tr,64);
                memory :> bytes(key,32);
                memory :> bytes(t0,6144);
                memory :> bytes(s1,5120);
                memory :> bytes(s2,6144);
                memory :> bytes(word_sub stackpointer (word 136),136)])`;;

let MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e rho tr key t0 s1 s2 sk pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,6144); (s1,5120); (s2,6144);
          (word_sub stackpointer (word 136),136)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,6144); (s1,5120); (s2,6144);
          (word_sub stackpointer (word 136),136)]
         [(word pc,libmldsa_size); (sk,4032)] /\
        ALLPAIRS nonoverlapping
         [(rho,32); (tr,64); (key,32); (t0,6144); (s1,5120); (s2,6144)]
         [(stackpointer,8); (word_add stackpointer (word 8),8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
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
                     e2 = f_events rho tr key t0 s1 s2 sk pc
                                 (word_sub stackpointer (word 136))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [sk,4032; t0,6144; s1,5120; s2,6144;
                       word(pc + rodata_mld_zetas),1024;
                       word_sub stackpointer (word 136),136; stackpointer,8;
                       word_add stackpointer (word 8),8]
                      [rho,32; tr,64; key,32; t0,6144; s1,5120; s2,6144;
                       word_sub stackpointer (word 136),136]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(rho,32);
                memory :> bytes(tr,64);
                memory :> bytes(key,32);
                memory :> bytes(t0,6144);
                memory :> bytes(s1,5120);
                memory :> bytes(s2,6144);
                memory :> bytes(word_sub stackpointer (word 136),136)])`;;

let MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_UNPACK_SK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
