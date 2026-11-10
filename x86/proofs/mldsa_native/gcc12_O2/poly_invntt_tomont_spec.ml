(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse number-theoretic transform with the factor mont / 256: the        *)
(* statement. This is the code for mldsa_poly_invntt_tomont                  *)
(* (mld_poly_invntt_tomont in poly.c, which calls the _c version) from       *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2      *)
(* (see mldsa_native/README.md): three nested loops over the 8 layers, their *)
(* blocks and the butterflies of a block, with the table mld_zetas from the  *)
(* read-only data, then a loop that scales the coefficients one at a time.   *)
(* It is verified in the whole image (see libmldsa.ml) against               *)
(* mld_poly_invntt_tomont of common/mldsa_native_poly.ml. It is also shown   *)
(* to be constant time and memory safe.                                      *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_poly.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_invntt_tomont:
       +0x0  push    r15
       +0x2  mov     rax, rdi
       +0x5  mov     ecx, 0x8
       +0xa  push    r14
       +0xc  push    r13
       +0xe  lea     r13, [rip+0x97cb]
                     // rodata_mld_zetas
      +0x15  push    r12
      +0x17  push    rbp
      +0x18  lea     rbp, [rdi+0x4]
      +0x1c  push    rbx
      +0x1d  nop     DWORD PTR [rax]
     loop1:
      +0x20  mov     esi, 0x100
      +0x25  mov     edi, 0x1
      +0x2a  xor     edx, edx
      +0x2c  mov     r15d, ecx
      +0x2f  shr     esi, cl
      +0x31  shl     edi, cl
      +0x33  sub     edi, 0x1
      +0x36  lea     r8d, [rsi+rsi*1]
      +0x3a  nop     WORD PTR [rax+rax*1+0x0]
     loop2:
      +0x40  mov     ecx, edi
      +0x42  sub     edi, 0x1
      +0x45  mov     ecx, DWORD PTR [r13+rcx*4+0x0]
      +0x4a  neg     ecx
      +0x4c  cmp     edx, esi
      +0x4e  jae     join1
      +0x54  mov     r9d, esi
      +0x57  mov     r10d, edx
      +0x5a  movsxd  rcx, ecx
      +0x5d  lea     r11, [rax+r9*4]
      +0x61  mov     r9d, esi
      +0x64  lea     rbx, [rax+r10*4]
      +0x68  sub     r9d, edx
      +0x6b  sub     r9d, 0x1
      +0x6f  add     r9, r10
      +0x72  lea     r14, [rbp+r9*4+0x0]
      +0x77  nop     WORD PTR [rax+rax*1+0x0]
     loop3:
      +0x80  mov     r9d, DWORD PTR [rbx]
      +0x83  mov     r10d, DWORD PTR [r11]
      +0x86  add     rbx, 0x4
      +0x8a  add     r11, 0x4
      +0x8e  add     r10d, r9d
      +0x91  mov     DWORD PTR [rbx-0x4], r10d
      +0x95  sub     r9d, DWORD PTR [r11-0x4]
      +0x99  movsxd  r9, r9d
      +0x9c  imul    r9, rcx
      +0xa0  mov     QWORD PTR [rsp-0x8], r9
      +0xa5  imul    r10d, DWORD PTR [rsp-0x8], 0x3802001
      +0xae  movsxd  r10, r10d
      +0xb1  mov     r9, r10
      +0xb4  mov     r12, r10
      +0xb7  shl     r9, 0xa
      +0xbb  sub     r12, r9
      +0xbe  mov     r9, r12
      +0xc1  shl     r9, 0xd
      +0xc5  sub     r9, r10
      +0xc8  mov     r10, QWORD PTR [rsp-0x8]
      +0xcd  add     r9, r10
      +0xd0  sar     r9, 0x20
      +0xd4  mov     DWORD PTR [r11-0x4], r9d
     loop3_test:
      +0xd8  cmp     r14, rbx
     loop3_back:
      +0xdb  jne     loop3
     join1: loop3_exit:
      +0xdd  add     edx, r8d
      +0xe0  add     esi, r8d
     loop2_test:
      +0xe3  cmp     edx, 0xff
     loop2_back:
      +0xe9  jbe     loop2
     loop2_exit:
      +0xef  mov     ecx, r15d
     loop1_test:
      +0xf2  sub     ecx, 0x1
     loop1_back:
      +0xf5  jne     loop1
     loop1_exit:
      +0xfb  lea     r8, [rax+0x400]
     +0x102  nop     WORD PTR [rax+rax*1+0x0]
     loop4:
     +0x108  movsxd  rsi, DWORD PTR [rax]
     +0x10b  add     rax, 0x4
     +0x10f  imul    rsi, rsi, 0xa3fa
     +0x116  imul    ecx, esi, 0x3802001
     +0x11c  movsxd  rcx, ecx
     +0x11f  mov     rdi, rcx
     +0x122  mov     rdx, rcx
     +0x125  shl     rdi, 0xa
     +0x129  sub     rdx, rdi
     +0x12c  shl     rdx, 0xd
     +0x130  sub     rdx, rcx
     +0x133  add     rdx, rsi
     +0x136  sar     rdx, 0x20
     +0x13a  mov     DWORD PTR [rax-0x4], edx
     loop4_test:
     +0x13d  cmp     r8, rax
     loop4_back:
     +0x140  jne     loop4
     loop4_exit:
     +0x142  pop     rbx
     +0x143  pop     rbp
     +0x144  pop     r12
     +0x146  pop     r13
     +0x148  pop     r14
     +0x14a  pop     r15
     ret:
     +0x14c  ret
 ***)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_poly_invntt_tomont"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomial x at a, 256 coefficients of 32 bits each,     *)
(* becomes mld_poly_invntt_tomont x. The function saves RBX, RBP and R12-R15 *)
(* below the return address and keeps a temporary in the 8 bytes below them  *)
(* (the red zone), the stack frame of 56 bytes.                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 56),56); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 56),56)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_invntt_tomont) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i))))
                            s = mld_poly_invntt_tomont x i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 56),56)])`;;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* polynomial, the table of zetas in the image, the stack frame and the slot *)
(* of the return address, and the writes within the polynomial and the stack *)
(* frame.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 56),56); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 56),56)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_invntt_tomont) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = mld_poly_invntt_tomont x i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc (word_sub stackpointer (word 56))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; word(pc + rodata_mld_zetas),1024;
                       word_sub stackpointer (word 56),56; stackpointer,8]
                      [a,1024; word_sub stackpointer (word 56),56]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 56),56)])`;;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 56),56); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 56),56)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_invntt_tomont) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc (word_sub stackpointer (word 56))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; word(pc + rodata_mld_zetas),1024;
                       word_sub stackpointer (word 56),56; stackpointer,8]
                      [a,1024; word_sub stackpointer (word 56),56]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 56),56)])`;;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
