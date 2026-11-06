(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Splitting of the coefficients of a polynomial at 2^13: the statement.     *)
(* This is the code for mldsa_poly_power2round (mld_poly_power2round in      *)
(* poly.c, with mld_power2round of rounding.h) from mldsa-native's portable  *)
(* C implementation compiled by gcc 12 with -O2 (see                         *)
(* mldsa_native/README.md), which the compiler has vectorized. It is         *)
(* verified in the whole image (see libmldsa.ml) against                     *)
(* mld_poly_power2round_hi and mld_poly_power2round_lo of                    *)
(* common/mldsa_native_poly.ml.                                              *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_poly.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_power2round:
       +0x0: movi    v4.4s, #0xf, msl #8
       +0x4: mov     x3, #0x0
       +0x8: mvni    v3.4s, #0x1f, msl #8
       +0xc: nop
      +0x10: ldr     q0, [x2, x3]
      +0x14: add     v1.4s, v0.4s, v4.4s
      +0x18: and     v2.16b, v1.16b, v3.16b
      +0x1c: sshr    v1.4s, v1.4s, #13
      +0x20: sub     v0.4s, v0.4s, v2.4s
      +0x24: str     q1, [x0, x3]
      +0x28: str     q0, [x1, x3]
      +0x2c: add     x3, x3, #0x10
      +0x30: cmp     x3, #0x400
      +0x34: b.ne    <mldsa_poly_power2round+0x10>
      +0x38: ret
 ***)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_poly_power2round"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. For the polynomial x at a, the high parts are written to a1  *)
(* and the low parts to a0, three regions of 1024 bytes that may not         *)
(* overlap.                                                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a1 a0 a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (a,1024); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
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

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
