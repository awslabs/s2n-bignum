(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 13 bits per coefficient, of 2^12 - a: the    *)
(* statement. This is the code for mldsa_polyt0_pack (mld_polyt0_pack in     *)
(* poly.c) from mldsa-native's portable C implementation compiled by gcc 12  *)
(* with -O2 (see mldsa_native/README.md), which writes 13 bytes for each 8   *)
(* coefficients, as one 64-bit word, one byte and one 32-bit word. It is     *)
(* verified in the whole image (see libmldsa.ml) against mld_polyt0_pack of  *)
(* common/mldsa_native_packing.ml, byte by byte. It is also shown to be      *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_packing.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_polyt0_pack:
       +0x0  push    r15
       +0x2  lea     rax, [rsi+0x400]
       +0x9  mov     rdx, rsi
       +0xc  mov     ecx, 0x1000
      +0x11  push    r14
      +0x13  push    r13
      +0x15  push    r12
      +0x17  push    rbp
      +0x18  push    rbx
      +0x19  mov     rbx, rdi
      +0x1c  mov     QWORD PTR [rsp-0x8], rax
      +0x21  nop     DWORD PTR [rax+0x0]
     loop1:
      +0x28  mov     r13d, ecx
      +0x2b  mov     r9d, ecx
      +0x2e  sub     r13d, DWORD PTR [rdx]
      +0x31  sub     r9d, DWORD PTR [rdx+0x4]
      +0x35  mov     r11d, r13d
      +0x38  mov     r8d, r9d
      +0x3b  mov     r10d, ecx
      +0x3e  sub     r10d, DWORD PTR [rdx+0x8]
      +0x42  shr     r11d, 0x8
      +0x46  shl     r8d, 0x5
      +0x4a  mov     r14d, r9d
      +0x4d  mov     eax, ecx
      +0x4f  or      r8d, r11d
      +0x52  sub     eax, DWORD PTR [rdx+0xc]
      +0x55  lea     r11d, [r10*4+0x0]
      +0x5d  mov     edi, ecx
      +0x5f  shr     r9d, 0xb
      +0x63  sub     edi, DWORD PTR [rdx+0x10]
      +0x66  shr     r10d, 0x6
      +0x6a  mov     r15d, eax
      +0x6d  or      r9d, r11d
      +0x70  mov     r11d, eax
      +0x73  shr     eax, 0x9
      +0x76  mov     r12d, ecx
      +0x79  shl     r11d, 0x7
      +0x7d  shr     r15d, 1
      +0x80  sub     r12d, DWORD PTR [rdx+0x14]
      +0x84  mov     esi, ecx
      +0x86  or      r10d, r11d
      +0x89  mov     r11d, edi
      +0x8c  movzx   r15d, r15b
      +0x90  shr     r14d, 0x3
      +0x94  shl     r11d, 0x4
      +0x98  sub     esi, DWORD PTR [rdx+0x18]
      +0x9b  mov     ebp, ecx
      +0x9d  sub     ebp, DWORD PTR [rdx+0x1c]
      +0xa0  or      r11d, eax
      +0xa3  mov     eax, edi
      +0xa5  shr     eax, 0x4
      +0xa8  movzx   r11d, r11b
      +0xac  movzx   eax, al
      +0xaf  shl     rax, 0x8
      +0xb3  or      rax, r11
      +0xb6  movzx   r11d, r10b
      +0xba  shl     rax, 0x8
      +0xbe  or      rax, r15
      +0xc1  shl     rax, 0x8
      +0xc5  mov     r10, rax
      +0xc8  movzx   eax, r9b
      +0xcc  or      r10, r11
      +0xcf  shl     r10, 0x8
      +0xd3  mov     r9, r10
      +0xd6  or      r9, rax
      +0xd9  movzx   eax, r14b
      +0xdd  mov     r14, r9
      +0xe0  mov     r9d, esi
      +0xe3  shl     r14, 0x8
      +0xe7  or      r14, rax
      +0xea  movzx   eax, r8b
      +0xee  shl     r14, 0x8
      +0xf2  shr     edi, 0xc
      +0xf5  add     rdx, 0x20
      +0xf9  add     rbx, 0xd
      +0xfd  mov     r8, r14
     +0x100  shr     r9d, 0x2
     +0x104  or      r8, rax
     +0x107  movzx   eax, r13b
     +0x10b  shl     r8, 0x8
     +0x10f  mov     r13, r8
     +0x112  mov     r8d, esi
     +0x115  shr     esi, 0xa
     +0x118  or      r13, rax
     +0x11b  lea     eax, [r12+r12*1]
     +0x11f  shl     r8d, 0x6
     +0x123  or      eax, edi
     +0x125  lea     edi, [rbp*8+0x0]
     +0x12c  shr     r12d, 0x7
     +0x130  mov     QWORD PTR [rbx-0xd], r13
     +0x134  or      edi, esi
     +0x136  movzx   esi, r9b
     +0x13a  or      r8d, r12d
     +0x13d  movzx   eax, al
     +0x140  movzx   edi, dil
     +0x144  shr     ebp, 0x5
     +0x147  shl     edi, 0x8
     +0x14a  mov     BYTE PTR [rbx-0x1], bpl
     +0x14e  or      edi, esi
     +0x150  movzx   esi, r8b
     +0x154  shl     edi, 0x8
     +0x157  or      edi, esi
     +0x159  shl     edi, 0x8
     +0x15c  or      edi, eax
     +0x15e  mov     DWORD PTR [rbx-0x5], edi
     loop1_test:
     +0x161  cmp     QWORD PTR [rsp-0x8], rdx
     loop1_back:
     +0x166  jne     loop1
     loop1_exit:
     +0x16c  pop     rbx
     +0x16d  pop     rbp
     +0x16e  pop     r12
     +0x170  pop     r13
     +0x172  pop     r14
     +0x174  pop     r15
     ret:
     +0x176  ret
 ***)

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_polyt0_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The function saves R15, R14, R13, R12, RBP and RBX, which it *)
(* uses, in the 48 bytes below the return address, and keeps the end of the  *)
(* input in the 8 bytes below them, in the red zone.                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,416))
            [(word pc,libmldsa_size); (a,1024);
             (word_sub stackpointer (word 56),56); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),56))
            [(word pc,libmldsa_size); (a,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyt0_pack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !j. j < 416
                      ==> read(memory :> bytes8(word_add r (word j))) s =
                          mld_polyt0_pack x j)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,416);
                memory :> bytes(word_sub stackpointer (word 56),56)])`;;

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs, the stack frame and the slot of the return address,   *)
(* and the writes within the outputs and the stack frame.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,416))
            [(word pc,libmldsa_size); (a,1024);
             (word_sub stackpointer (word 56),56); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),56))
            [(word pc,libmldsa_size); (a,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyt0_pack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!j. j < 416
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyt0_pack x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc (word_sub stackpointer (word 56))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [a,1024; r,416; word_sub stackpointer (word 56),56;
                        stackpointer,8]
                       [r,416; word_sub stackpointer (word 56),56]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,416);
                memory :> bytes(word_sub stackpointer (word 56),56)])`;;

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,416))
            [(word pc,libmldsa_size); (a,1024);
             (word_sub stackpointer (word 56),56); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 56),56))
            [(word pc,libmldsa_size); (a,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyt0_pack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc (word_sub stackpointer (word 56))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [a,1024; r,416; word_sub stackpointer (word 56),56;
                        stackpointer,8]
                       [r,416; word_sub stackpointer (word 56),56]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,416);
                memory :> bytes(word_sub stackpointer (word 56),56)])`;;

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
