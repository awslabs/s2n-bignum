(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Splitting of the coefficients of a polynomial at 2^13: the statement.     *)
(* This is the code for mldsa_poly_power2round (mld_poly_power2round in      *)
(* poly.c, with mld_power2round of rounding.h) from mldsa-native's portable  *)
(* C implementation compiled by gcc 12 with -Os (see                         *)
(* mldsa_native/README.md), as a loop of 256 scalar splits. It is verified   *)
(* in the whole image (see libmldsa.ml) against mld_poly_power2round_hi and  *)
(* mld_poly_power2round_lo of common/mldsa_native_poly.ml, and shown to be   *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_poly.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_power2round:
       +0x0: mov     x3, #0x0
       +0x4: ldr     w4, [x2, x3]
       +0x8: add     w5, w4, #0xfff
       +0xc: asr     w6, w5, #13
      +0x10: and     w5, w5, #0xffffe000
      +0x14: str     w6, [x0, x3]
      +0x18: sub     w4, w4, w5
      +0x1c: str     w4, [x1, x3]
      +0x20: add     x3, x3, #0x4
      +0x24: cmp     x3, #0x400
      +0x28: b.ne    <mldsa_poly_power2round+0x4>
      +0x2c: ret
 ***)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa_poly_power2round"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. For the polynomial x at a, the high parts are written to a1  *)
(* and the low parts to a0, three regions of 1024 bytes that may not         *)
(* overlap.                                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a1 a0 a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (a,1024); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_poly_power2round) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a1; a0; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a1 (word(4 * i))))
                             s = mld_poly_power2round_hi x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a0 (word(4 * i))))
                             s = mld_poly_power2round_lo x i))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a1,1024); memory :> bytes(a0,1024)])`;;

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the writes within the outputs.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a1 a0 a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (a,1024); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_poly_power2round) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a1; a0; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a1 (word(4 * i))))
                             s = mld_poly_power2round_hi x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a0 (word(4 * i))))
                             s = mld_poly_power2round_lo x i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a1 a0 a pc returnaddress /\
                     memaccess_inbounds e2 [a,1024] [a1,1024; a0,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a1,1024); memory :> bytes(a0,1024)])`;;

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a1 a0 a pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (a,1024); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_poly_power2round) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a1; a0; a] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a1 a0 a pc returnaddress /\
                     memaccess_inbounds e2 [a,1024] [a1,1024; a0,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a1,1024); memory :> bytes(a0,1024)])`;;

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same in place, with the low part written over the input (a0 = a), as  *)
(* mld_compute_pack_t0_t1 calls it: each iteration loads its four input      *)
(* coefficients before it stores the results.                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_FULL_INPLACE_STMT =
 `exists f_events.
     forall e a1 a0 x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_poly_power2round) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a1; a0; a0] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a0 (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a1 (word(4 * i))))
                             s = mld_poly_power2round_hi x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a0 (word(4 * i))))
                             s = mld_poly_power2round_lo x i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a1 a0 pc returnaddress /\
                     memaccess_inbounds e2 [a0,1024] [a1,1024; a0,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a1,1024); memory :> bytes(a0,1024)])`;;

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_FULL_INPLACE =
  assume_spec
   MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_OS_IMAGE_SUBROUTINE_FULL_INPLACE_STMT;;
