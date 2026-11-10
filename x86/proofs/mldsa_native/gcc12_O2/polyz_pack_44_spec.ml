(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 18 bits per coefficient, of 2^17 - a: the    *)
(* statement. This is the code for mldsa44_polyz_pack (mld_polyz_pack in     *)
(* poly_kl.c with MLDSA_GAMMA1 = 2^17, for ML-DSA-44) from mldsa-native's    *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mldsa_native/README.md), which writes 9 bytes for each 4 coefficients, 8  *)
(* of them as one 64-bit word assembled in RAX. It is verified in the whole  *)
(* image (see libmldsa.ml) against mld_polyz_pack_17 of                      *)
(* common/mldsa_native_packing.ml, byte by byte. It is also shown to be      *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_packing.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyz_pack:
       +0x0  push    r13
       +0x2  mov     rdx, rsi
       +0x5  mov     rsi, rdi
       +0x8  mov     edi, 0x20000
       +0xd  push    r12
       +0xf  lea     r8, [rdx+0x400]
      +0x16  push    rbp
      +0x17  push    rbx
      +0x18  nop     DWORD PTR [rax+rax*1+0x0]
     loop1:
      +0x20  mov     r9d, edi
      +0x23  sub     r9d, DWORD PTR [rdx]
      +0x26  mov     ebp, edi
      +0x28  mov     eax, edi
      +0x2a  sub     ebp, DWORD PTR [rdx+0x4]
      +0x2d  sub     eax, DWORD PTR [rdx+0x8]
      +0x30  mov     ebx, r9d
      +0x33  mov     ecx, edi
      +0x35  shr     ebx, 0x10
      +0x38  sub     ecx, DWORD PTR [rdx+0xc]
      +0x3b  mov     r12d, eax
      +0x3e  mov     r10d, r9d
      +0x41  shl     r12d, 0x4
      +0x45  mov     r13d, ecx
      +0x48  shr     r10d, 0x8
      +0x4c  movzx   r9d, r9b
      +0x50  lea     r11d, [rbp*4+0x0]
      +0x58  shl     r13d, 0x6
      +0x5c  movzx   r10d, r10b
      +0x60  add     rdx, 0x10
      +0x64  or      r11d, ebx
      +0x67  mov     ebx, ebp
      +0x69  shr     ebp, 0xe
      +0x6c  or      ebp, r12d
      +0x6f  mov     r12d, eax
      +0x72  shr     eax, 0xc
      +0x75  movzx   r11d, r11b
      +0x79  shr     r12d, 0x4
      +0x7d  or      r13d, eax
      +0x80  mov     eax, ecx
      +0x82  movzx   ebp, bpl
      +0x86  shr     eax, 0x2
      +0x89  movzx   r13d, r13b
      +0x8d  movzx   r12d, r12b
      +0x91  shr     ebx, 0x6
      +0x94  movzx   eax, al
      +0x97  movzx   ebx, bl
      +0x9a  shr     ecx, 0xa
      +0x9d  shl     rax, 0x8
      +0xa1  mov     BYTE PTR [rsi+0x8], cl
      +0xa4  or      rax, r13
      +0xa7  shl     rax, 0x8
      +0xab  or      rax, r12
      +0xae  shl     rax, 0x8
      +0xb2  or      rax, rbp
      +0xb5  shl     rax, 0x8
      +0xb9  or      rax, rbx
      +0xbc  shl     rax, 0x8
      +0xc0  or      rax, r11
      +0xc3  shl     rax, 0x8
      +0xc7  or      rax, r10
      +0xca  shl     rax, 0x8
      +0xce  or      rax, r9
      +0xd1  add     rsi, 0x9
      +0xd5  mov     QWORD PTR [rsi-0x9], rax
     loop1_test:
      +0xd9  cmp     r8, rdx
     loop1_back:
      +0xdc  jne     loop1
     loop1_exit:
      +0xe2  pop     rbx
      +0xe3  pop     rbp
      +0xe4  pop     r12
      +0xe6  pop     r13
     ret:
      +0xe8  ret
 ***)

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_polyz_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The function saves R13, R12, RBP and RBX, which it uses, in  *)
(* the 32 bytes below the return address.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,576))
            [(word pc,libmldsa_size); (a,1024);
             (word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,libmldsa_size); (a,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyz_pack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !j. j < 576
                      ==> read(memory :> bytes8(word_add r (word j))) s =
                          mld_polyz_pack_17 x j)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,576);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs, the stack frame and the slot of the return address,   *)
(* and the writes within the outputs and the stack frame.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,576))
            [(word pc,libmldsa_size); (a,1024);
             (word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,libmldsa_size); (a,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyz_pack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!j. j < 576
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyz_pack_17 x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc (word_sub stackpointer (word 32))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [a,1024; r,576; word_sub stackpointer (word 32),32;
                        stackpointer,8]
                       [r,576; word_sub stackpointer (word 32),32]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,576);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,576))
            [(word pc,libmldsa_size); (a,1024);
             (word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,libmldsa_size); (a,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyz_pack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc (word_sub stackpointer (word 32))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [a,1024; r,576; word_sub stackpointer (word 32),32;
                        stackpointer,8]
                       [r,576; word_sub stackpointer (word 32),32]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,576);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
