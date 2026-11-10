(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Correction of the high parts of the coefficients of a polynomial by       *)
(* hints: the statement. This is the code for mldsa44_poly_use_hint          *)
(* (mld_poly_use_hint_c in poly_kl.c, with mld_use_hint of rounding.h for    *)
(* gamma2 = (q - 1) / 88, for ML-DSA-44) from mldsa-native's portable C      *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which replaces each coefficient of a by its corrected high part,          *)
(* branching on each hint. It is verified in the whole image (see            *)
(* libmldsa.ml) against mld_poly_use_hint_88 of                              *)
(* common/mldsa_native_rounding.ml. It is also shown to be memory safe and   *)
(* constant time apart from the branches on the hint and the low part, which *)
(* the C code also has.                                                      *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_rounding.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_poly_use_hint:
       +0x0  mov     r8, rsi
       +0x3  push    rbx
       +0x4  xor     ecx, ecx
       +0x6  mov     esi, 0x2b
       +0xb  mov     r9d, 0x3ff000
      +0x11  xor     r10d, r10d
      +0x14  jmp     loop1
      +0x16  cs nop  WORD PTR [rax+rax*1+0x0]
     join1: loop1_exit1:
      +0x20  lea     edx, [rax+0x1]
      +0x23  cmp     eax, 0x2b
      +0x26  mov     eax, edx
      +0x28  cmove   eax, r10d
     join2: loop1_exit2:
      +0x2c  mov     DWORD PTR [rdi+rcx*1], eax
      +0x2f  add     rcx, 0x4
      +0x33  cmp     rcx, 0x400
      +0x3a  je      join3
     loop1:
      +0x3c  mov     r11d, DWORD PTR [rdi+rcx*1]
      +0x40  mov     eax, esi
      +0x42  lea     edx, [r11+0x7f]
      +0x46  sar     edx, 0x7
      +0x49  imul    edx, edx, 0x2c0b
      +0x4f  add     edx, 0x800000
      +0x55  sar     edx, 0x18
      +0x58  sub     eax, edx
      +0x5a  cdqe
      +0x5c  sar     rax, 0x1f
      +0x60  not     eax
      +0x62  and     eax, edx
      +0x64  imul    edx, eax, 0xfffd1800
      +0x6a  add     r11d, edx
      +0x6d  mov     edx, r9d
      +0x70  sub     edx, r11d
      +0x73  movsxd  rdx, edx
      +0x76  sar     rdx, 0x1f
      +0x7a  mov     ebx, DWORD PTR [r8+rcx*1]
     loop1_test1:
      +0x7e  test    ebx, ebx
      +0x80  je      join2
     loop1_next1:
      +0x82  lea     ebx, [r11-0x7fe001]
      +0x89  xor     ebx, r11d
      +0x8c  and     edx, ebx
     loop1_test2:
      +0x8e  xor     edx, r11d
      +0x91  jg      join1
     loop1_next2:
      +0x93  sub     eax, 0x1
      +0x96  cmovb   eax, esi
      +0x99  mov     DWORD PTR [rdi+rcx*1], eax
      +0x9c  add     rcx, 0x4
     loop1_test3:
      +0xa0  cmp     rcx, 0x400
     loop1_back:
      +0xa7  jne     loop1
     join3: loop1_exit3:
      +0xa9  pop     rbx
     ret:
      +0xaa  ret
 ***)

let MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_poly_use_hint"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The function saves RBX below the return address.             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a h x y pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping [(a,1024); (h,1024); (word pc,libmldsa_size)] /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 8),8); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 8),8))
            [(h,1024); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_poly_use_hint) /\
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
                            s = mld_poly_use_hint_88 x y i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024);
                         memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, of the hints y and of the         *)
(* polynomial x, on whose low parts the code also branches (as the C code    *)
(* does; both are public where mld_poly_use_hint is called, in the           *)
(* verification), with all accesses within the inputs and outputs, the stack *)
(* frame and the slot of the return address, and the writes within the       *)
(* outputs and the stack frame.                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a h x y pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping [(a,1024); (h,1024); (word pc,libmldsa_size)] /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 8),8); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 8),8))
            [(h,1024); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_poly_use_hint) /\
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
                             s = mld_poly_use_hint_88 x y i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a h x y pc (word_sub stackpointer (word 8))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; h,1024; word_sub stackpointer (word 8),8;
                       stackpointer,8]
                      [a,1024; word_sub stackpointer (word 8),8]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024);
                         memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the polynomial and the hints  *)
(* as data that the events may depend on.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a h x y pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping [(a,1024); (h,1024); (word pc,libmldsa_size)] /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 8),8); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 8),8))
            [(h,1024); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_poly_use_hint) /\
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
                     e2 = f_events a h x y pc (word_sub stackpointer (word 8))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; h,1024; word_sub stackpointer (word 8),8;
                       stackpointer,8]
                      [a,1024; word_sub stackpointer (word 8),8]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024);
                         memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
