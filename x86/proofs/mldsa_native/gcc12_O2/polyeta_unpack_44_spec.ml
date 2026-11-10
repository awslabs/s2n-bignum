(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 3 bits per coefficient, of 2 - a: the      *)
(* statement. This is the code for mldsa44_polyeta_unpack                    *)
(* (mld_polyeta_unpack in poly_kl.c with MLDSA_ETA = 2, for ML-DSA-44) from  *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mldsa_native/README.md), which reads 3 bytes for each 8 coefficients,     *)
(* stores the masked fields and then 2 - a over them, one coefficient at a   *)
(* time. It is verified in the whole image (see libmldsa.ml) against         *)
(* mld_polyeta_unpack_2 of common/mldsa_native_packing.ml. It is also shown  *)
(* to be constant time and memory safe.                                      *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_packing.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyeta_unpack:
       +0x0  push    r13
       +0x2  mov     rax, rdi
       +0x5  lea     r11, [rdi+0x400]
       +0xc  mov     rdx, rsi
       +0xf  push    r12
      +0x11  mov     edi, 0x2
      +0x16  push    rbp
      +0x17  push    rbx
      +0x18  nop     DWORD PTR [rax+rax*1+0x0]
     loop1:
      +0x20  movzx   r10d, BYTE PTR [rdx]
      +0x24  mov     r13d, edi
      +0x27  add     rax, 0x20
      +0x2b  add     rdx, 0x3
      +0x2f  and     r10d, 0x7
      +0x33  mov     DWORD PTR [rax-0x20], r10d
      +0x37  movzx   r9d, BYTE PTR [rdx-0x3]
      +0x3c  sub     r13d, r10d
      +0x3f  mov     r10d, edi
      +0x42  shr     r9b, 0x3
      +0x46  and     r9d, 0x7
      +0x4a  mov     DWORD PTR [rax-0x1c], r9d
      +0x4e  movzx   esi, BYTE PTR [rdx-0x3]
      +0x52  sub     r10d, r9d
      +0x55  mov     r9d, edi
      +0x58  movzx   ecx, BYTE PTR [rdx-0x2]
      +0x5c  shr     sil, 0x6
      +0x60  shl     ecx, 0x2
      +0x63  movzx   esi, sil
      +0x67  or      esi, ecx
      +0x69  and     esi, 0x7
      +0x6c  mov     DWORD PTR [rax-0x18], esi
      +0x6f  movzx   ebp, BYTE PTR [rdx-0x2]
      +0x73  sub     r9d, esi
      +0x76  mov     esi, edi
      +0x78  shr     bpl, 1
      +0x7b  and     ebp, 0x7
      +0x7e  mov     DWORD PTR [rax-0x14], ebp
      +0x81  movzx   ebx, BYTE PTR [rdx-0x2]
      +0x85  sub     esi, ebp
      +0x87  shr     bl, 0x4
      +0x8a  and     ebx, 0x7
      +0x8d  mov     DWORD PTR [rax-0x10], ebx
      +0x90  movzx   ecx, BYTE PTR [rdx-0x2]
      +0x94  movzx   r8d, BYTE PTR [rdx-0x1]
      +0x99  shr     cl, 0x7
      +0x9c  add     r8d, r8d
      +0x9f  movzx   ecx, cl
      +0xa2  or      ecx, r8d
      +0xa5  and     ecx, 0x7
      +0xa8  mov     DWORD PTR [rax-0xc], ecx
      +0xab  movzx   r8d, BYTE PTR [rdx-0x1]
      +0xb0  shr     r8b, 0x2
      +0xb4  and     r8d, 0x7
      +0xb8  mov     DWORD PTR [rax-0x8], r8d
      +0xbc  movzx   r12d, BYTE PTR [rdx-0x1]
      +0xc1  mov     DWORD PTR [rax-0x14], esi
      +0xc4  mov     esi, edi
      +0xc6  sub     esi, ebx
      +0xc8  shr     r12b, 0x5
      +0xcc  mov     DWORD PTR [rax-0x20], r13d
      +0xd0  mov     DWORD PTR [rax-0x10], esi
      +0xd3  mov     esi, edi
      +0xd5  movzx   r12d, r12b
      +0xd9  sub     esi, ecx
      +0xdb  mov     ecx, edi
      +0xdd  mov     DWORD PTR [rax-0x1c], r10d
      +0xe1  sub     ecx, r8d
      +0xe4  mov     DWORD PTR [rax-0x18], r9d
      +0xe8  mov     DWORD PTR [rax-0x8], ecx
      +0xeb  mov     ecx, edi
      +0xed  sub     ecx, r12d
      +0xf0  mov     DWORD PTR [rax-0xc], esi
      +0xf3  mov     DWORD PTR [rax-0x4], ecx
     loop1_test:
      +0xf6  cmp     r11, rax
     loop1_back:
      +0xf9  jne     loop1
     loop1_exit:
      +0xff  pop     rbx
     +0x100  pop     rbp
     +0x101  pop     r12
     +0x103  pop     r13
     ret:
     +0x105  ret
 ***)

let MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_polyeta_unpack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The function saves R13, R12, RBP and RBX, which it uses, in  *)
(* the 32 bytes below the return address.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,96);
             (word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,libmldsa_size); (a,96)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyeta_unpack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 96
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add r (word(4 * i))))
                            s = mld_polyeta_unpack_2 b i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,1024);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs, the stack frame and the slot of the return address,   *)
(* and the writes within the outputs and the stack frame.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,96);
             (word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,libmldsa_size); (a,96)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyeta_unpack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 96
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i))))
                             s = mld_polyeta_unpack_2 b i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc (word_sub stackpointer (word 32))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [a,96; r,1024; word_sub stackpointer (word 32),32;
                        stackpointer,8]
                       [r,1024; word_sub stackpointer (word 32),32]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,1024);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,96);
             (word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,libmldsa_size); (a,96)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyeta_unpack) /\
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
                       [a,96; r,1024; word_sub stackpointer (word 32),32;
                        stackpointer,8]
                       [r,1024; word_sub stackpointer (word 32),32]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,1024);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYETA_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
