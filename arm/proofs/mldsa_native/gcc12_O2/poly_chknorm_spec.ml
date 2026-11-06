(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Check of the norm of a polynomial against a bound B: the statement. This  *)
(* is the code for mldsa_poly_chknorm (mld_poly_chknorm in poly.c, which     *)
(* calls mld_poly_chknorm_c) from mldsa-native's portable C implementation   *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md). It is verified  *)
(* in the whole image (see libmldsa.ml) against mld_poly_chknorm of          *)
(* common/mldsa_native_poly.ml: the result is all ones if some coefficient a *)
(* has B - 1 - |a| < 0, and zero otherwise.                                  *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_poly.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_chknorm:
       +0x0: sub     w5, w1, #0x1
       +0x4: mov     x4, x0
       +0x8: add     x6, x0, #0x400
       +0xc: mov     w0, #0x0
      +0x10: ldr     w3, [x4], #4
      +0x14: sxtw    x2, w3
      +0x18: asr     x2, x2, #31
      +0x1c: neg     w1, w3
      +0x20: eor     w1, w1, w3
      +0x24: and     w1, w1, w2
      +0x28: eor     w1, w1, w3
      +0x2c: sub     w1, w5, w1
      +0x30: sxtw    x1, w1
      +0x34: asr     x1, x1, #31
      +0x38: orr     w0, w0, w1
      +0x3c: cmp     x4, x6
      +0x40: b.ne    <mldsa_poly_chknorm+0x10>
      +0x44: ret
 ***)

let MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_poly_chknorm"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomial x is at a and the bound B is the low 32 bits  *)
(* of the second argument; the result is a 32-bit value, zero-extended.      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a x bnd pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_poly_chknorm) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; bnd] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  C_RETURN s = word_zx(mld_poly_chknorm x (word_zx bnd)))
             MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI`;;

let MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
