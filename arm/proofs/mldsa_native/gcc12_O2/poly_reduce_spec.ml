(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction of the coefficients of a polynomial with mld_reduce32: the      *)
(* statement. This is the code for mldsa_poly_reduce (mld_poly_reduce in     *)
(* poly.c) from mldsa-native's portable C implementation compiled by gcc 12  *)
(* with -O2 (see mldsa_native/README.md), which the compiler has vectorized, *)
(* with a vector of -q from the read-only data. It is verified in the whole  *)
(* image (see libmldsa.ml) against mld_poly_reduce of                        *)
(* common/mldsa_native_poly.ml.                                              *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_poly.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_reduce:
       +0x0: adrp    x2, <page>
       +0x4: add     x1, x0, #0x400
       +0x8: movi    v3.4s, #0x40, lsl #16
       +0xc: ldr     q2, [x2, #3536]
      +0x10: ldr     q0, [x0]
      +0x14: add     v1.4s, v0.4s, v3.4s
      +0x18: sshr    v1.4s, v1.4s, #23
      +0x1c: mla     v0.4s, v1.4s, v2.4s
      +0x20: str     q0, [x0], #16
      +0x24: cmp     x1, x0
      +0x28: b.ne    <mldsa_poly_reduce+0x10>
      +0x2c: ret
 ***)

let MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_poly_reduce"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomial x at a, 256 coefficients of 32 bits each,     *)
(* becomes mld_poly_reduce x.                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        nonoverlapping (a,1024) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_poly_reduce) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i))))
                            s = mld_poly_reduce x i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`;;

let MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
