(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Correction of the high parts of the coefficients of a polynomial by       *)
(* hints: the statement. This is the code for mldsa65_poly_use_hint          *)
(* (mld_poly_use_hint_c in poly_kl.c, with mld_use_hint of rounding.h for    *)
(* gamma2 = (q - 1) / 32, for ML-DSA-65) from mldsa-native's portable C      *)
(* implementation compiled by gcc 12 with -Os (see mldsa_native/README.md),  *)
(* which replaces each coefficient of a by its corrected high part, by a     *)
(* call of mld_decompose65 for each coefficient (a function of its own at    *)
(* -Os, see decompose_65_spec.ml) and a branch on its hint. The stack frame  *)
(* of 32 bytes holds the return address, the two outputs of the call and the *)
(* stack protector value, which the code reads from the guard whose address  *)
(* is in the GOT and compares with the guard at the end. It is verified in   *)
(* the whole image (see libmldsa.ml) against mld_poly_use_hint_32 of         *)
(* common/mldsa_native_rounding.ml. It is also shown to be memory safe and   *)
(* constant time apart from the branches on the hint, which the C code also  *)
(* has.                                                                      *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_rounding.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/decompose_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa65_poly_use_hint:
       +0x0: mov     x5, x0
       +0x4: str     x30, [sp, #-32]!
       +0x8: adrp    x0, <page>
       +0xc: ldr     x0, [x0, #4088]
      +0x10: mov     x6, x1
      +0x14: add     x7, sp, #0x14
      +0x18: mov     x4, #0x0
      +0x1c: ldr     x1, [x0]
      +0x20: str     x1, [sp, #24]
      +0x24: mov     x1, #0x0
      +0x28: add     x0, sp, #0x10
      +0x2c: ldr     w2, [x5, x4]
      +0x30: mov     x1, x7
      +0x34: ldr     w8, [x6, x4]
      +0x38: bl      <mld_decompose65>
      +0x3c: ldr     w2, [sp, #20]
      +0x40: cbz     w8, <mldsa65_poly_use_hint+0x60>
      +0x44: ldr     w1, [sp, #16]
      +0x48: add     w3, w2, #0x1
      +0x4c: sub     w2, w2, #0x1
      +0x50: and     w3, w3, #0xf
      +0x54: and     w2, w2, #0xf
      +0x58: cmp     w1, #0x0
      +0x5c: csel    w2, w2, w3, le
      +0x60: str     w2, [x5, x4]
      +0x64: add     x4, x4, #0x4
      +0x68: cmp     x4, #0x400
      +0x6c: b.ne    <mldsa65_poly_use_hint+0x2c>
      +0x70: adrp    x0, <page>
      +0x74: ldr     x0, [x0, #4088]
      +0x78: ldr     x2, [sp, #24]
      +0x7c: ldr     x1, [x0]
      +0x80: subs    x2, x2, x1
      +0x84: mov     x1, #0x0
      +0x88: b.eq    <mldsa65_poly_use_hint+0x90>
      +0x8c: bl      <stack_chk_fail>
      +0x90: ldr     x30, [sp], #32
      +0x94: ret
 ***)

let MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa65_poly_use_hint"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a h x y guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(a,1024); (h,1024); (word_sub stackpointer (word 32),32);
          (word pc,libmldsa_size)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 32),32)]
         [(word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa65_poly_use_hint) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; h] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add h (word(4 * i))))
                             s = y i))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i))))
                            s = mld_poly_use_hint_32 x y i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024);
                         memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and of the hints y, on which the   *)
(* code branches (as the C code does; the hints are part of a signature, so  *)
(* public), with all accesses within the inputs and outputs and the writes   *)
(* within the outputs.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a h x y guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(a,1024); (h,1024); (word_sub stackpointer (word 32),32);
          (word pc,libmldsa_size)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 32),32)]
         [(word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa65_poly_use_hint) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; h] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add h (word(4 * i))))
                             s = y i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = mld_poly_use_hint_32 x y i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a h y guard pc
                            (word_sub stackpointer (word 32)) returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; h,1024; word_sub stackpointer (word 32),32;
                       word(pc + got_stack_chk_guard),8; guard,8]
                      [a,1024; word_sub stackpointer (word 32),32]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024);
                         memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the hints as data that the    *)
(* events may depend on.                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a h y guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(a,1024); (h,1024); (word_sub stackpointer (word 32),32);
          (word pc,libmldsa_size)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 32),32)]
         [(word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa65_poly_use_hint) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; h] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add h (word(4 * i))))
                             s = y i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a h y guard pc
                            (word_sub stackpointer (word 32)) returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; h,1024; word_sub stackpointer (word 32),32;
                       word(pc + got_stack_chk_guard),8; guard,8]
                      [a,1024; word_sub stackpointer (word 32),32]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024);
                         memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
