(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 20 bits per coefficient, of 2^19 - a: the  *)
(* statement. This is the code for mldsa65_polyz_unpack (mld_polyz_unpack_c  *)
(* in poly_kl.c with MLDSA_GAMMA1 = 2^19, for ML-DSA-65, which the build     *)
(* calls as mld_polyz_unpack) from mldsa-native's portable C implementation  *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), which reads 5   *)
(* bytes for each 2 coefficients and, as the C code does, stores the partial *)
(* results before the final ones. It is verified in the whole image (see     *)
(* libmldsa.ml) against mld_polyz_unpack_19 of                               *)
(* common/mldsa_native_packing.ml. It is also shown to be constant time and  *)
(* memory safe.                                                              *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_packing.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_polyz_unpack:
       +0x0  mov     rax, rsi
       +0x3  mov     rdx, rdi
       +0x6  lea     r9, [rsi+0x280]
       +0xd  mov     r8d, 0x80000
      +0x13  nop     DWORD PTR [rax+rax*1+0x0]
     loop1:
      +0x18  movzx   ecx, BYTE PTR [rax]
      +0x1b  add     rax, 0x5
      +0x1f  add     rdx, 0x8
      +0x23  mov     DWORD PTR [rdx-0x8], ecx
      +0x26  movzx   esi, BYTE PTR [rax-0x4]
      +0x2a  shl     esi, 0x8
      +0x2d  or      esi, ecx
      +0x2f  mov     DWORD PTR [rdx-0x8], esi
      +0x32  movzx   ecx, BYTE PTR [rax-0x3]
      +0x36  shl     ecx, 0x10
      +0x39  or      ecx, esi
      +0x3b  and     ecx, 0xfffff
      +0x41  mov     DWORD PTR [rdx-0x8], ecx
      +0x44  movzx   edi, BYTE PTR [rax-0x3]
      +0x48  shr     dil, 0x4
      +0x4c  movzx   edi, dil
      +0x50  mov     DWORD PTR [rdx-0x4], edi
      +0x53  movzx   esi, BYTE PTR [rax-0x2]
      +0x57  shl     esi, 0x4
      +0x5a  or      esi, edi
      +0x5c  mov     DWORD PTR [rdx-0x4], esi
      +0x5f  movzx   edi, BYTE PTR [rax-0x1]
      +0x63  shl     edi, 0xc
      +0x66  or      esi, edi
      +0x68  mov     edi, r8d
      +0x6b  sub     edi, ecx
      +0x6d  mov     ecx, r8d
      +0x70  sub     ecx, esi
      +0x72  mov     DWORD PTR [rdx-0x8], edi
      +0x75  mov     DWORD PTR [rdx-0x4], ecx
     loop1_test:
      +0x78  cmp     r9, rax
     loop1_back:
      +0x7b  jne     loop1
     loop1_exit: ret:
      +0x7d  ret
 ***)

let MLDSA_NATIVE_POLYZ_UNPACK_65_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_polyz_unpack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,640); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_polyz_unpack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 640
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add r (word(4 * i))))
                            s = mld_polyz_unpack_19 b i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYZ_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYZ_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the slot of the return address, and the writes     *)
(* within the outputs.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,640); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_polyz_unpack) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 640
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i))))
                             s = mld_polyz_unpack_19 b i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [a,640; r,1024; stackpointer,8] [r,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYZ_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYZ_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (a,640); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_polyz_unpack) /\
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
                       [a,640; r,1024; stackpointer,8] [r,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYZ_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYZ_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
