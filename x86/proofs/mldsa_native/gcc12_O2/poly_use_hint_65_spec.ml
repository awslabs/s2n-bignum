(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Correction of the high parts of the coefficients of a polynomial by       *)
(* hints: the statement. This is the code for mldsa65_poly_use_hint          *)
(* (mld_poly_use_hint_c in poly_kl.c, with mld_use_hint of rounding.h for    *)
(* gamma2 = (q - 1) / 32, for ML-DSA-65) from mldsa-native's portable C      *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which replaces each coefficient of a by its corrected high part,          *)
(* branching on each hint. It is verified in the whole image (see            *)
(* libmldsa.ml) against mld_poly_use_hint_32 of                              *)
(* common/mldsa_native_rounding.ml. It is also shown to be memory safe and   *)
(* constant time apart from the branches on the hint and the low part, which *)
(* the C code also has.                                                      *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_rounding.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_poly_use_hint:
       +0x0  mov     r8, rsi
       +0x3  mov     r9d, 0x3ff000
       +0x9  xor     esi, esi
       +0xb  jmp     loop1
       +0xd  nop     DWORD PTR [rax]
     join1: loop1_exit1:
      +0x10  add     edx, 0x1
      +0x13  and     edx, 0xf
     join2: loop1_exit2:
      +0x16  mov     DWORD PTR [rdi+rsi*1], edx
      +0x19  add     rsi, 0x4
      +0x1d  cmp     rsi, 0x400
      +0x24  je      join3
     loop1:
      +0x26  mov     r10d, DWORD PTR [rdi+rsi*1]
      +0x2a  lea     eax, [r10+0x7f]
      +0x2e  sar     eax, 0x7
      +0x31  mov     edx, eax
      +0x33  shl     edx, 0xa
      +0x36  lea     edx, [rax+rdx*1+0x200000]
      +0x3d  sar     edx, 0x16
      +0x40  and     edx, 0xf
      +0x43  mov     eax, edx
      +0x45  mov     ecx, edx
      +0x47  shl     eax, 0xa
      +0x4a  sub     ecx, eax
      +0x4c  mov     eax, r9d
      +0x4f  shl     ecx, 0x9
      +0x52  add     ecx, r10d
      +0x55  sub     eax, ecx
      +0x57  cdqe
      +0x59  sar     rax, 0x1f
      +0x5d  mov     r10d, DWORD PTR [r8+rsi*1]
     loop1_test1:
      +0x61  test    r10d, r10d
      +0x64  je      join2
     loop1_next1:
      +0x66  lea     r10d, [rcx-0x7fe001]
      +0x6d  xor     r10d, ecx
      +0x70  and     eax, r10d
     loop1_test2:
      +0x73  xor     eax, ecx
      +0x75  jg      join1
     loop1_next2:
      +0x77  sub     edx, 0x1
      +0x7a  and     edx, 0xf
      +0x7d  mov     DWORD PTR [rdi+rsi*1], edx
      +0x80  add     rsi, 0x4
     loop1_test3:
      +0x84  cmp     rsi, 0x400
     loop1_back:
      +0x8b  jne     loop1
     join3: loop1_exit3: ret:
      +0x8d  ret
 ***)

let MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_poly_use_hint"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a h x y pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping [(a,1024); (h,1024); (word pc,libmldsa_size)] /\
        nonoverlapping (a,1024) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_poly_use_hint) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; h] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add h (word(4 * i))))
                             s = y i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i))))
                            s = mld_poly_use_hint_32 x y i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`;;

let MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, of the hints y and of the         *)
(* polynomial x, on whose low parts the code also branches (as the C code    *)
(* does; both are public where mld_poly_use_hint is called, in the           *)
(* verification), with all accesses within the inputs and outputs and the    *)
(* slot of the return address, and the writes within the outputs.            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a h x y pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping [(a,1024); (h,1024); (word pc,libmldsa_size)] /\
        nonoverlapping (a,1024) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_poly_use_hint) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; h] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add h (word(4 * i))))
                             s = y i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = mld_poly_use_hint_32 x y i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a h x y pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [a,1024; h,1024; stackpointer,8] [a,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`;;

let MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the polynomial and the hints  *)
(* as data that the events may depend on.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a h x y pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping [(a,1024); (h,1024); (word pc,libmldsa_size)] /\
        nonoverlapping (a,1024) (stackpointer,8)
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_poly_use_hint) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; h] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add h (word(4 * i))))
                             s = y i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a h x y pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [a,1024; h,1024; stackpointer,8] [a,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`;;

let MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
