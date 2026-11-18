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

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_rounding.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa87_poly_decompose:
       +0x0: mov     x5, #0x0
       +0x4: mov     w7, #0x3ff000
       +0x8: mov     w6, #0xff801fff
       +0xc: nop
      +0x10: ldr     w3, [x1, x5]
      +0x14: add     w2, w3, #0x7f
      +0x18: asr     w2, w2, #7
      +0x1c: add     w2, w2, w2, lsl #10
      +0x20: add     w2, w2, #0x200, lsl #12
      +0x24: ubfx    x2, x2, #22, #4
      +0x28: str     w2, [x0, x5]
      +0x2c: sub     w2, w2, w2, lsl #10
      +0x30: add     w2, w3, w2, lsl #9
      +0x34: sub     w3, w7, w2
      +0x38: sxtw    x3, w3
      +0x3c: asr     x3, x3, #31
      +0x40: add     w4, w2, w6
      +0x44: eor     w4, w4, w2
      +0x48: and     w3, w4, w3
      +0x4c: eor     w2, w3, w2
      +0x50: str     w2, [x1, x5]
      +0x54: add     x5, x5, #0x4
      +0x58: cmp     x5, #0x400
      +0x5c: b.ne    <mldsa87_poly_decompose+0x10>
      +0x60: ret
 ***)

let MLDSA_NATIVE_POLY_DECOMPOSE_87_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_poly_decompose"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_DECOMPOSE_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a1 a0 x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa87_poly_decompose) /\
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
                         memory :> bytes(a0,1024)])`;;

let MLDSA_NATIVE_POLY_DECOMPOSE_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_DECOMPOSE_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the writes within the outputs.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_DECOMPOSE_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a1 a0 x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa87_poly_decompose) /\
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
                     e2 = f_events a1 a0 pc returnaddress /\
                     memaccess_inbounds e2
                      [a0,1024; a1,1024]
                      [a1,1024; a0,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a1,1024);
                         memory :> bytes(a0,1024)])`;;

let MLDSA_NATIVE_POLY_DECOMPOSE_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_DECOMPOSE_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_DECOMPOSE_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a1 a0 pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa87_poly_decompose) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a1; a0] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a1 a0 pc returnaddress /\
                     memaccess_inbounds e2
                      [a0,1024; a1,1024]
                      [a1,1024; a0,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a1,1024);
                         memory :> bytes(a0,1024)])`;;

let MLDSA_NATIVE_POLY_DECOMPOSE_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_DECOMPOSE_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
