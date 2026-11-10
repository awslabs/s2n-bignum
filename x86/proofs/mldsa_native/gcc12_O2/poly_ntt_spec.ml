(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number-theoretic transform: the statement. This is the code for   *)
(* mldsa_poly_ntt (mld_poly_ntt in poly.c, which calls mld_poly_ntt_c) from  *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2      *)
(* (see mldsa_native/README.md): three nested loops over the 8 layers, the   *)
(* blocks of a layer and the butterflies of a block, with the table          *)
(* mld_zetas from the read-only data. It is verified in the whole image (see *)
(* libmldsa.ml) against mld_poly_ntt of common/mldsa_native_poly.ml. It is   *)
(* also shown to be constant time and memory safe.                           *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_poly.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_ntt:
       +0x0  push    r15
       +0x2  xor     ecx, ecx
       +0x4  push    r14
       +0x6  push    r13
       +0x8  push    r12
       +0xa  mov     r12, rdi
       +0xd  mov     edi, 0x64f7
      +0x12  push    rbp
      +0x13  lea     r14, [r12+0x4]
      +0x18  lea     rbp, [rip+0x98d1]
                     // rodata_mld_zetas
      +0x1f  mov     r13, r12
      +0x22  push    rbx
      +0x23  nop     DWORD PTR [rax+rax*1+0x0]
     join1:
      +0x28  lea     r8d, [rcx+0x1]
      +0x2c  mov     esi, 0x1
      +0x31  mov     edx, 0x100
      +0x36  xor     eax, eax
      +0x38  shl     esi, cl
      +0x3a  mov     ecx, r8d
      +0x3d  mov     ebx, r8d
      +0x40  shr     edx, cl
      +0x42  lea     r9d, [rdx+rdx*1]
      +0x46  cs nop  WORD PTR [rax+rax*1+0x0]
     loop1:
      +0x50  add     esi, 0x1
      +0x53  cmp     eax, edx
      +0x55  jae     join2
      +0x57  mov     ecx, edx
      +0x59  mov     r10d, eax
      +0x5c  sub     ecx, eax
      +0x5e  lea     r8, [r13+r10*4+0x0]
      +0x63  sub     ecx, 0x1
      +0x66  add     rcx, r10
      +0x69  lea     r12, [r14+rcx*4]
      +0x6d  mov     ecx, edx
      +0x6f  sub     rcx, r10
      +0x72  nop     WORD PTR [rax+rax*1+0x0]
     loop2:
      +0x78  movsxd  r10, DWORD PTR [r8+rcx*4]
      +0x7c  imul    r10, rdi
      +0x80  mov     QWORD PTR [rsp-0x8], r10
      +0x85  imul    r10d, DWORD PTR [rsp-0x8], 0x3802001
      +0x8e  movsxd  r10, r10d
      +0x91  mov     r11, r10
      +0x94  mov     r15, r10
      +0x97  shl     r11, 0xa
      +0x9b  sub     r15, r11
      +0x9e  mov     r11, r15
      +0xa1  shl     r11, 0xd
      +0xa5  sub     r11, r10
      +0xa8  mov     r10, QWORD PTR [rsp-0x8]
      +0xad  add     r11, r10
      +0xb0  mov     r10d, DWORD PTR [r8]
      +0xb3  sar     r11, 0x20
      +0xb7  sub     r10d, r11d
      +0xba  mov     DWORD PTR [r8+rcx*4], r10d
      +0xbe  add     DWORD PTR [r8], r11d
      +0xc1  add     r8, 0x4
     loop2_test:
      +0xc5  cmp     r12, r8
     loop2_back:
      +0xc8  jne     loop2
     join2: loop2_exit:
      +0xca  add     eax, r9d
      +0xcd  add     edx, r9d
     loop1_test:
      +0xd0  cmp     eax, 0xff
      +0xd5  ja      join3
     loop1_next:
      +0xd7  mov     ecx, esi
      +0xd9  movsxd  rdi, DWORD PTR [rbp+rcx*4+0x0]
     loop1_back:
      +0xde  jmp     loop1
      +0xe3  nop     DWORD PTR [rax+rax*1+0x0]
     join3: loop1_exit:
      +0xe8  cmp     ebx, 0x8
      +0xeb  je      +0x102
      +0xed  mov     ecx, ebx
      +0xef  mov     eax, 0x1
      +0xf4  shl     eax, cl
      +0xf6  mov     ecx, ebx
      +0xf8  movsxd  rdi, DWORD PTR [rbp+rax*4+0x0]
      +0xfd  jmp     join1
     +0x102  pop     rbx
     +0x103  pop     rbp
     +0x104  pop     r12
     +0x106  pop     r13
     +0x108  pop     r14
     +0x10a  pop     r15
     ret:
     +0x10c  ret
 ***)

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_poly_ntt"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomial x at a, 256 coefficients of 32 bits each,     *)
(* becomes mld_poly_ntt x. The function saves RBX, RBP and R12-R15 below the *)
(* return address and keeps a temporary in the 8 bytes below them (the red   *)
(* zone), the stack frame of 56 bytes.                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 56),56); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 56),56)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_ntt) /\
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
                            s = mld_poly_ntt x i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 56),56)])`;;

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* polynomial, the table of zetas in the image, the stack frame and the slot *)
(* of the return address, and the writes within the polynomial and the stack *)
(* frame.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
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
                  read RIP s = word (pc + mldsa_poly_ntt) /\
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
                             s = mld_poly_ntt x i) /\
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

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
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
                  read RIP s = word (pc + mldsa_poly_ntt) /\
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

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
