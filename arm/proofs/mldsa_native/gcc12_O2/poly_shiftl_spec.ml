(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Multiplication of the coefficients of a polynomial by 2^13: the           *)
(* statement. This is the code for mldsa_poly_shiftl (mld_poly_shiftl in     *)
(* poly.c) from mldsa-native's portable C implementation compiled by gcc 12  *)
(* with -O2 (see mldsa_native/README.md), which the compiler has vectorized  *)
(* and does as a shift. It is verified in the whole image (see libmldsa.ml)  *)
(* against mld_poly_shiftl of common/mldsa_native_poly.ml.                   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_poly.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_shiftl:
       +0x0: add     x1, x0, #0x400
       +0x4: nop
       +0x8: ldr     q0, [x0]
       +0xc: shl     v0.4s, v0.4s, #13
      +0x10: str     q0, [x0], #16
      +0x14: cmp     x0, x1
      +0x18: b.ne    <mldsa_poly_shiftl+0x8>
      +0x1c: ret
 ***)

let MLDSA_NATIVE_POLY_SHIFTL_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_poly_shiftl"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomial x at a, 256 coefficients of 32 bits each,     *)
(* becomes mld_poly_shiftl x.                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_SHIFTL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        nonoverlapping (a,1024) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_poly_shiftl) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i))))
                            s = mld_poly_shiftl x i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`;;

let MLDSA_NATIVE_POLY_SHIFTL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_SHIFTL_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
