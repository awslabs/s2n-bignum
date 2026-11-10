(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decomposition of the coefficients of a polynomial into high and low       *)
(* parts: the statement. This is the code for mldsa87_poly_decompose         *)
(* (mld_poly_decompose_c in poly_kl.c, with mld_decompose of rounding.h for  *)
(* gamma2 = (q - 1) / 32, for ML-DSA-87) from mldsa-native's portable C      *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which replaces each coefficient a of a0 by its low part and writes the    *)
(* high part to a1. It is verified in the whole image (see libmldsa.ml)      *)
(* against mld_poly_decompose_hi_32 and mld_poly_decompose_lo_32 of          *)
(* common/mldsa_native_rounding.ml. It is also shown to be constant time and *)
(* memory safe.                                                              *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_rounding.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa87_poly_decompose:
       +0x0  xor     ecx, ecx
       +0x2  mov     r8d, 0x3ff000
       +0x8  nop     DWORD PTR [rax+rax*1+0x0]
     loop1:
      +0x10  mov     edx, DWORD PTR [rsi+rcx*1]
      +0x13  lea     eax, [rdx+0x7f]
      +0x16  sar     eax, 0x7
      +0x19  mov     r9d, eax
      +0x1c  shl     r9d, 0xa
      +0x20  lea     eax, [rax+r9*1+0x200000]
      +0x28  sar     eax, 0x16
      +0x2b  and     eax, 0xf
      +0x2e  mov     r9d, eax
      +0x31  mov     DWORD PTR [rdi+rcx*1], eax
      +0x34  shl     r9d, 0xa
      +0x38  sub     eax, r9d
      +0x3b  shl     eax, 0x9
      +0x3e  add     eax, edx
      +0x40  mov     edx, r8d
      +0x43  sub     edx, eax
      +0x45  movsxd  rdx, edx
      +0x48  sar     rdx, 0x1f
      +0x4c  lea     r9d, [rax-0x7fe001]
      +0x53  xor     r9d, eax
      +0x56  and     edx, r9d
      +0x59  xor     eax, edx
      +0x5b  mov     DWORD PTR [rsi+rcx*1], eax
      +0x5e  add     rcx, 0x4
     loop1_test:
      +0x62  cmp     rcx, 0x400
     loop1_back:
      +0x69  jne     loop1
     loop1_exit: ret:
      +0x6b  ret
 ***)

let MLDSA_NATIVE_POLY_DECOMPOSE_87_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_poly_decompose"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_DECOMPOSE_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a1 a0 x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (word pc,libmldsa_size)] /\
        ALL (nonoverlapping (stackpointer,8)) [(a1,1024); (a0,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa87_poly_decompose) /\
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
                             s = mld_poly_decompose_hi_32 x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a0 (word(4 * i))))
                             s = mld_poly_decompose_lo_32 x i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a1,1024);
                         memory :> bytes(a0,1024)])`;;

let MLDSA_NATIVE_POLY_DECOMPOSE_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_DECOMPOSE_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the slot of the return address, and the writes     *)
(* within the outputs.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_DECOMPOSE_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a1 a0 x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (word pc,libmldsa_size)] /\
        ALL (nonoverlapping (stackpointer,8)) [(a1,1024); (a0,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa87_poly_decompose) /\
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
                             s = mld_poly_decompose_hi_32 x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a0 (word(4 * i))))
                             s = mld_poly_decompose_lo_32 x i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a1 a0 pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                      [a0,1024; a1,1024; stackpointer,8]
                      [a1,1024; a0,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a1,1024);
                         memory :> bytes(a0,1024)])`;;

let MLDSA_NATIVE_POLY_DECOMPOSE_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_DECOMPOSE_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_DECOMPOSE_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a1 a0 pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (word pc,libmldsa_size)] /\
        ALL (nonoverlapping (stackpointer,8)) [(a1,1024); (a0,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa87_poly_decompose) /\
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

let MLDSA_NATIVE_POLY_DECOMPOSE_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_DECOMPOSE_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
