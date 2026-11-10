(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 18 bits per coefficient, of 2^17 - a: the  *)
(* statement. This is the code for mldsa44_polyz_unpack (mld_polyz_unpack_c  *)
(* in poly_kl.c with MLDSA_GAMMA1 = 2^17, for ML-DSA-44, which the build     *)
(* calls as mld_polyz_unpack) from mldsa-native's portable C implementation  *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), which reads 9   *)
(* bytes for each 4 coefficients and, as the C code does, stores the partial *)
(* results before the final ones. It is verified in the whole image (see     *)
(* libmldsa.ml) against mld_polyz_unpack_17 of                               *)
(* common/mldsa_native_packing.ml. It is also shown to be constant time and  *)
(* memory safe.                                                              *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_packing.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyz_unpack:
       +0x0  mov     rdx, rsi
       +0x3  mov     rax, rdi
       +0x6  lea     r11, [rdi+0x400]
       +0xd  mov     r10d, 0x20000
      +0x13  nop     DWORD PTR [rax+rax*1+0x0]
     loop1:
      +0x18  movzx   esi, BYTE PTR [rdx]
      +0x1b  add     rax, 0x10
      +0x1f  add     rdx, 0x9
      +0x23  mov     DWORD PTR [rax-0x10], esi
      +0x26  movzx   ecx, BYTE PTR [rdx-0x8]
      +0x2a  shl     ecx, 0x8
      +0x2d  or      ecx, esi
      +0x2f  mov     DWORD PTR [rax-0x10], ecx
      +0x32  movzx   edi, BYTE PTR [rdx-0x7]
      +0x36  shl     edi, 0x10
      +0x39  or      edi, ecx
      +0x3b  and     edi, 0x3ffff
      +0x41  mov     DWORD PTR [rax-0x10], edi
      +0x44  movzx   esi, BYTE PTR [rdx-0x7]
      +0x48  shr     sil, 0x2
      +0x4c  movzx   esi, sil
      +0x50  mov     DWORD PTR [rax-0xc], esi
      +0x53  movzx   ecx, BYTE PTR [rdx-0x6]
      +0x57  shl     ecx, 0x6
      +0x5a  or      ecx, esi
      +0x5c  mov     DWORD PTR [rax-0xc], ecx
      +0x5f  movzx   esi, BYTE PTR [rdx-0x5]
      +0x63  shl     esi, 0xe
      +0x66  or      esi, ecx
      +0x68  and     esi, 0x3ffff
      +0x6e  mov     DWORD PTR [rax-0xc], esi
      +0x71  movzx   ecx, BYTE PTR [rdx-0x5]
      +0x75  shr     cl, 0x4
      +0x78  movzx   ecx, cl
      +0x7b  mov     DWORD PTR [rax-0x8], ecx
      +0x7e  movzx   r8d, BYTE PTR [rdx-0x4]
      +0x83  shl     r8d, 0x4
      +0x87  or      r8d, ecx
      +0x8a  mov     DWORD PTR [rax-0x8], r8d
      +0x8e  movzx   ecx, BYTE PTR [rdx-0x3]
      +0x92  shl     ecx, 0xc
      +0x95  or      ecx, r8d
      +0x98  and     ecx, 0x3ffff
      +0x9e  mov     DWORD PTR [rax-0x8], ecx
      +0xa1  movzx   r9d, BYTE PTR [rdx-0x3]
      +0xa6  shr     r9b, 0x6
      +0xaa  movzx   r9d, r9b
      +0xae  mov     DWORD PTR [rax-0x4], r9d
      +0xb2  movzx   r8d, BYTE PTR [rdx-0x2]
      +0xb7  shl     r8d, 0x2
      +0xbb  or      r8d, r9d
      +0xbe  mov     DWORD PTR [rax-0x4], r8d
      +0xc2  movzx   r9d, BYTE PTR [rdx-0x1]
      +0xc7  shl     r9d, 0xa
      +0xcb  or      r8d, r9d
      +0xce  mov     r9d, r10d
      +0xd1  sub     r9d, edi
      +0xd4  mov     edi, r10d
      +0xd7  sub     edi, esi
      +0xd9  mov     esi, r10d
      +0xdc  mov     DWORD PTR [rax-0x10], r9d
      +0xe0  sub     esi, ecx
      +0xe2  mov     ecx, r10d
      +0xe5  mov     DWORD PTR [rax-0xc], edi
      +0xe8  sub     ecx, r8d
      +0xeb  mov     DWORD PTR [rax-0x8], esi
      +0xee  mov     DWORD PTR [rax-0x4], ecx
     loop1_test:
      +0xf1  cmp     rax, r11
     loop1_back:
      +0xf4  jne     loop1
     loop1_exit: ret:
      +0xfa  ret
 ***)

let MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_polyz_unpack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,576); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyz_unpack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 576
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add r (word(4 * i))))
                            s = mld_polyz_unpack_17 b i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the slot of the return address, and the writes     *)
(* within the outputs.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,576); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyz_unpack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 576
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i))))
                             s = mld_polyz_unpack_17 b i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [a,576; r,1024; stackpointer,8] [r,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,576); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyz_unpack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [a,576; r,1024; stackpointer,8] [r,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
