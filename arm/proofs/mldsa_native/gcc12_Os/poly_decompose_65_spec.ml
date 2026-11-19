(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decomposition of the coefficients of a polynomial into high and low       *)
(* parts: the statement. This is the code for mldsa65_poly_decompose         *)
(* (mld_poly_decompose_c in poly_kl.c, with mld_decompose of rounding.h for  *)
(* gamma2 = (q - 1) / 32, for ML-DSA-65) from mldsa-native's portable C      *)
(* implementation compiled by gcc 12 with -Os (see mldsa_native/README.md),  *)
(* which replaces each coefficient a of a0 by its low part and writes the    *)
(* high part to a1, by a call of mld_decompose65 for each coefficient (a     *)
(* function of its own at -Os, see decompose_65_spec.ml). The frame of 16    *)
(* bytes at the stack pointer holds the return address. It is verified in    *)
(* the whole image (see libmldsa.ml) against mld_poly_decompose_hi_32 and    *)
(* mld_poly_decompose_lo_32 of common/mldsa_native_rounding.ml. It is also   *)
(* shown to be constant time and memory safe.                                *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_rounding.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/decompose_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa65_poly_decompose:
       +0x0: mov     x6, x0
       +0x4: mov     x5, x1
       +0x8: mov     x4, #0x0
       +0xc: str     x30, [sp, #-16]!
      +0x10: ldr     w2, [x5, x4]
      +0x14: add     x1, x6, x4
      +0x18: add     x0, x5, x4
      +0x1c: add     x4, x4, #0x4
      +0x20: bl      <mld_decompose65>
      +0x24: cmp     x4, #0x400
      +0x28: b.ne    <mldsa65_poly_decompose+0x10>
      +0x2c: ldr     x30, [sp], #16
      +0x30: ret
 ***)

let MLDSA_NATIVE_POLY_DECOMPOSE_65_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa65_poly_decompose"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_DECOMPOSE_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a1 a0 x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (word_sub stackpointer (word 16),16);
          (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa65_poly_decompose) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a1; a0] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a0 (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a1 (word(4 * i))))
                             s = mld_poly_decompose_hi_32 x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a0 (word(4 * i))))
                             s = mld_poly_decompose_lo_32 x i))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a1,1024);
                         memory :> bytes(a0,1024);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_POLY_DECOMPOSE_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_DECOMPOSE_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the writes within the outputs.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_DECOMPOSE_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a1 a0 x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (word_sub stackpointer (word 16),16);
          (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa65_poly_decompose) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a1; a0] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a0 (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a1 (word(4 * i))))
                             s = mld_poly_decompose_hi_32 x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a0 (word(4 * i))))
                             s = mld_poly_decompose_lo_32 x i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a1 a0 pc (word_sub stackpointer (word 16))
                            returnaddress /\
                     memaccess_inbounds e2
                      [a0,1024; a1,1024; word_sub stackpointer (word 16),16]
                      [a1,1024; a0,1024; word_sub stackpointer (word 16),16]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a1,1024);
                         memory :> bytes(a0,1024);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_POLY_DECOMPOSE_65_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_DECOMPOSE_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_DECOMPOSE_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a1 a0 pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (word_sub stackpointer (word 16),16);
          (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa65_poly_decompose) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a1; a0] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a1 a0 pc (word_sub stackpointer (word 16))
                            returnaddress /\
                     memaccess_inbounds e2
                      [a0,1024; a1,1024; word_sub stackpointer (word 16),16]
                      [a1,1024; a0,1024; word_sub stackpointer (word 16),16]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a1,1024);
                         memory :> bytes(a0,1024);
                         memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_POLY_DECOMPOSE_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_DECOMPOSE_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
