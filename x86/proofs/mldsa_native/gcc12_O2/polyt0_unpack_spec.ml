(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 13 bits per coefficient, of 2^12 - a: the  *)
(* statement. This is the code for mldsa_polyt0_unpack (mld_polyt0_unpack in *)
(* poly.c) from mldsa-native's portable C implementation compiled by gcc 12  *)
(* with -O2 (see mldsa_native/README.md), which reads 13 bytes for each 8    *)
(* coefficients and, as the C code does, stores the partial results before   *)
(* the final ones. It is verified in the whole image (see libmldsa.ml)       *)
(* against mld_polyt0_unpack of common/mldsa_native_packing.ml. It is also   *)
(* shown to be constant time and memory safe.                                *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_packing.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_polyt0_unpack:
       +0x0  push    r13
       +0x2  mov     rdx, rsi
       +0x5  mov     rax, rdi
       +0x8  push    r12
       +0xa  lea     r12, [rsi+0x1a0]
      +0x11  push    rbp
      +0x12  push    rbx
      +0x13  mov     ebx, 0x1000
      +0x18  nop     DWORD PTR [rax+rax*1+0x0]
     loop1:
      +0x20  movzx   ecx, BYTE PTR [rdx]
      +0x23  mov     DWORD PTR [rax], ecx
      +0x25  movzx   r11d, BYTE PTR [rdx+0x1]
      +0x2a  shl     r11d, 0x8
      +0x2e  or      r11d, ecx
      +0x31  and     r11d, 0x1fff
      +0x38  mov     DWORD PTR [rax], r11d
      +0x3b  movzx   esi, BYTE PTR [rdx+0x1]
      +0x3f  shr     sil, 0x5
      +0x43  movzx   esi, sil
      +0x47  mov     DWORD PTR [rax+0x4], esi
      +0x4a  movzx   ecx, BYTE PTR [rdx+0x2]
      +0x4e  shl     ecx, 0x3
      +0x51  or      ecx, esi
      +0x53  mov     DWORD PTR [rax+0x4], ecx
      +0x56  movzx   r10d, BYTE PTR [rdx+0x3]
      +0x5b  shl     r10d, 0xb
      +0x5f  or      r10d, ecx
      +0x62  and     r10d, 0x1fff
      +0x69  mov     DWORD PTR [rax+0x4], r10d
      +0x6d  movzx   ecx, BYTE PTR [rdx+0x3]
      +0x71  shr     cl, 0x2
      +0x74  movzx   ecx, cl
      +0x77  mov     DWORD PTR [rax+0x8], ecx
      +0x7a  movzx   r9d, BYTE PTR [rdx+0x4]
      +0x7f  shl     r9d, 0x6
      +0x83  or      r9d, ecx
      +0x86  and     r9d, 0x1fff
      +0x8d  mov     DWORD PTR [rax+0x8], r9d
      +0x91  movzx   esi, BYTE PTR [rdx+0x4]
      +0x95  shr     sil, 0x7
      +0x99  movzx   esi, sil
      +0x9d  mov     DWORD PTR [rax+0xc], esi
      +0xa0  movzx   ecx, BYTE PTR [rdx+0x5]
      +0xa4  add     ecx, ecx
      +0xa6  or      ecx, esi
      +0xa8  mov     DWORD PTR [rax+0xc], ecx
      +0xab  movzx   r8d, BYTE PTR [rdx+0x6]
      +0xb0  shl     r8d, 0x9
      +0xb4  or      r8d, ecx
      +0xb7  and     r8d, 0x1fff
      +0xbe  mov     DWORD PTR [rax+0xc], r8d
      +0xc2  movzx   esi, BYTE PTR [rdx+0x6]
      +0xc6  shr     sil, 0x4
      +0xca  movzx   esi, sil
      +0xce  mov     DWORD PTR [rax+0x10], esi
      +0xd1  movzx   ecx, BYTE PTR [rdx+0x7]
      +0xd5  shl     ecx, 0x4
      +0xd8  or      ecx, esi
      +0xda  mov     DWORD PTR [rax+0x10], ecx
      +0xdd  movzx   edi, BYTE PTR [rdx+0x8]
      +0xe1  shl     edi, 0xc
      +0xe4  or      edi, ecx
      +0xe6  and     edi, 0x1fff
      +0xec  mov     DWORD PTR [rax+0x10], edi
      +0xef  movzx   ecx, BYTE PTR [rdx+0x8]
      +0xf3  shr     cl, 1
      +0xf5  movzx   ecx, cl
      +0xf8  mov     DWORD PTR [rax+0x14], ecx
      +0xfb  movzx   esi, BYTE PTR [rdx+0x9]
      +0xff  shl     esi, 0x7
     +0x102  or      esi, ecx
     +0x104  and     esi, 0x1fff
     +0x10a  mov     DWORD PTR [rax+0x14], esi
     +0x10d  movzx   ecx, BYTE PTR [rdx+0x9]
     +0x111  shr     cl, 0x6
     +0x114  movzx   ecx, cl
     +0x117  mov     DWORD PTR [rax+0x18], ecx
     +0x11a  movzx   ebp, BYTE PTR [rdx+0xa]
     +0x11e  shl     ebp, 0x2
     +0x121  or      ebp, ecx
     +0x123  mov     DWORD PTR [rax+0x18], ebp
     +0x126  movzx   ecx, BYTE PTR [rdx+0xb]
     +0x12a  shl     ecx, 0xa
     +0x12d  add     rdx, 0xd
     +0x131  add     rax, 0x20
     +0x135  or      ecx, ebp
     +0x137  and     ecx, 0x1fff
     +0x13d  mov     DWORD PTR [rax-0x8], ecx
     +0x140  movzx   ebp, BYTE PTR [rdx-0x2]
     +0x144  shr     bpl, 0x3
     +0x148  movzx   ebp, bpl
     +0x14c  mov     DWORD PTR [rax-0x4], ebp
     +0x14f  movzx   r13d, BYTE PTR [rdx-0x1]
     +0x154  shl     r13d, 0x5
     +0x158  or      ebp, r13d
     +0x15b  mov     r13d, ebx
     +0x15e  sub     r13d, r11d
     +0x161  mov     r11d, ebx
     +0x164  sub     r11d, r10d
     +0x167  mov     r10d, ebx
     +0x16a  mov     DWORD PTR [rax-0x20], r13d
     +0x16e  sub     r10d, r9d
     +0x171  mov     r9d, ebx
     +0x174  mov     DWORD PTR [rax-0x1c], r11d
     +0x178  sub     r9d, r8d
     +0x17b  mov     r8d, ebx
     +0x17e  mov     DWORD PTR [rax-0x18], r10d
     +0x182  sub     r8d, edi
     +0x185  mov     edi, ebx
     +0x187  mov     DWORD PTR [rax-0x14], r9d
     +0x18b  sub     edi, esi
     +0x18d  mov     esi, ebx
     +0x18f  mov     DWORD PTR [rax-0x10], r8d
     +0x193  sub     esi, ecx
     +0x195  mov     ecx, ebx
     +0x197  mov     DWORD PTR [rax-0xc], edi
     +0x19a  sub     ecx, ebp
     +0x19c  mov     DWORD PTR [rax-0x8], esi
     +0x19f  mov     DWORD PTR [rax-0x4], ecx
     loop1_test:
     +0x1a2  cmp     r12, rdx
     loop1_back:
     +0x1a5  jne     loop1
     loop1_exit:
     +0x1ab  pop     rbx
     +0x1ac  pop     rbp
     +0x1ad  pop     r12
     +0x1af  pop     r13
     ret:
     +0x1b1  ret
 ***)

let MLDSA_NATIVE_POLYT0_UNPACK_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_polyt0_unpack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The function saves R13, R12, RBP and RBX, which it uses, in  *)
(* the 32 bytes below the return address.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,416);
             (word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,libmldsa_size); (a,416)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyt0_unpack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 416
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add r (word(4 * i))))
                            s = mld_polyt0_unpack b i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,1024);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYT0_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYT0_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs, the stack frame and the slot of the return address,   *)
(* and the writes within the outputs and the stack frame.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,416);
             (word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,libmldsa_size); (a,416)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyt0_unpack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 416
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i))))
                             s = mld_polyt0_unpack b i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc (word_sub stackpointer (word 32))
                                   returnaddress /\
                     memaccess_inbounds e2
                       [a,416; r,1024; word_sub stackpointer (word 32),32;
                        stackpointer,8]
                       [r,1024; word_sub stackpointer (word 32),32]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,1024);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYT0_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYT0_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,416);
             (word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 32),32))
            [(word pc,libmldsa_size); (a,416)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_polyt0_unpack) /\
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
                       [a,416; r,1024; word_sub stackpointer (word 32),32;
                        stackpointer,8]
                       [r,1024; word_sub stackpointer (word 32),32]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,1024);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYT0_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYT0_UNPACK_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
