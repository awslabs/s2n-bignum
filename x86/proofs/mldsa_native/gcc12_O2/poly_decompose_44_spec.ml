(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decomposition of the coefficients of a polynomial into high and low       *)
(* parts: the statement. This is the code for mldsa44_poly_decompose         *)
(* (mld_poly_decompose_c in poly_kl.c, with mld_decompose of rounding.h for  *)
(* gamma2 = (q - 1) / 88, for ML-DSA-44) from mldsa-native's portable C      *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which replaces each coefficient a of a0 by its low part and writes the    *)
(* high part to a1. It is verified in the whole image (see libmldsa.ml)      *)
(* against mld_poly_decompose_hi_88 and mld_poly_decompose_lo_88 of          *)
(* common/mldsa_native_rounding.ml. It is also shown to be constant time and *)
(* memory safe.                                                              *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_rounding.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_poly_decompose:
       +0x0  xor     ecx, ecx
       +0x2  mov     r9d, 0x2b
       +0x8  mov     r8d, 0x3ff000
       +0xe  xchg    ax, ax
     loop1:
      +0x10  mov     r10d, DWORD PTR [rsi+rcx*1]
      +0x14  mov     eax, r9d
      +0x17  lea     edx, [r10+0x7f]
      +0x1b  sar     edx, 0x7
      +0x1e  imul    edx, edx, 0x2c0b
      +0x24  add     edx, 0x800000
      +0x2a  sar     edx, 0x18
      +0x2d  sub     eax, edx
      +0x2f  cdqe
      +0x31  sar     rax, 0x1f
      +0x35  not     eax
      +0x37  and     eax, edx
      +0x39  mov     edx, r8d
      +0x3c  mov     DWORD PTR [rdi+rcx*1], eax
      +0x3f  imul    eax, eax, 0xfffd1800
      +0x45  add     eax, r10d
      +0x48  sub     edx, eax
      +0x4a  movsxd  rdx, edx
      +0x4d  sar     rdx, 0x1f
      +0x51  lea     r10d, [rax-0x7fe001]
      +0x58  xor     r10d, eax
      +0x5b  and     edx, r10d
      +0x5e  xor     eax, edx
      +0x60  mov     DWORD PTR [rsi+rcx*1], eax
      +0x63  add     rcx, 0x4
     loop1_test:
      +0x67  cmp     rcx, 0x400
     loop1_back:
      +0x6e  jne     loop1
     loop1_exit: ret:
      +0x70  ret
 ***)

let MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_poly_decompose"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a1 a0 x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (word pc,libmldsa_size)] /\
        ALL (nonoverlapping (stackpointer,8)) [(a1,1024); (a0,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_poly_decompose) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a1; a0] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a0 (word(4 * i))))
                             s = x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a1 (word(4 * i))))
                             s = mld_poly_decompose_hi_88 x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a0 (word(4 * i))))
                             s = mld_poly_decompose_lo_88 x i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a1,1024);
                         memory :> bytes(a0,1024)])`;;

let MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the slot of the return address, and the writes     *)
(* within the outputs.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a1 a0 x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (word pc,libmldsa_size)] /\
        ALL (nonoverlapping (stackpointer,8)) [(a1,1024); (a0,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_poly_decompose) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a1; a0] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a0 (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a1 (word(4 * i))))
                             s = mld_poly_decompose_hi_88 x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a0 (word(4 * i))))
                             s = mld_poly_decompose_lo_88 x i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a1 a0 pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                      [a0,1024; a1,1024; stackpointer,8]
                      [a1,1024; a0,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a1,1024);
                         memory :> bytes(a0,1024)])`;;

let MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a1 a0 pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (word pc,libmldsa_size)] /\
        ALL (nonoverlapping (stackpointer,8)) [(a1,1024); (a0,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_poly_decompose) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a1; a0] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a1 a0 pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                      [a0,1024; a1,1024; stackpointer,8]
                      [a1,1024; a0,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a1,1024);
                         memory :> bytes(a0,1024)])`;;

let MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
