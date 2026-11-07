(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decomposition of the coefficients of a polynomial into high and low       *)
(* parts: the statement. This is the code for mldsa44_poly_decompose         *)
(* (mld_poly_decompose_c in poly_kl.c, with mld_decompose of rounding.h for  *)
(* gamma2 = (q - 1) / 88, for ML-DSA-44) from mldsa-native's portable C      *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which replaces each coefficient a of a0 by its low part and writes the    *)
(* high part to a1. It is verified in the whole image (see libmldsa.ml)      *)
(* against mld_poly_decompose_hi_88 and mld_poly_decompose_lo_88 of          *)
(* common/mldsa_native_rounding.ml.                                          *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_rounding.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_poly_decompose:
       +0x0: mov     w8, #0x1800
       +0x4: mov     x5, #0x0
       +0x8: mov     w10, #0x2c0b
       +0xc: mov     w9, #0x2b
      +0x10: movk    w8, #0xfffd, lsl #16
      +0x14: mov     w7, #0x3ff000
      +0x18: mov     w6, #0xff801fff
      +0x1c: nop
      +0x20: ldr     w4, [x1, x5]
      +0x24: add     w3, w4, #0x7f
      +0x28: asr     w3, w3, #7
      +0x2c: mul     w3, w3, w10
      +0x30: add     w3, w3, #0x800, lsl #12
      +0x34: asr     w3, w3, #24
      +0x38: sub     w2, w9, w3
      +0x3c: sxtw    x2, w2
      +0x40: asr     x2, x2, #31
      +0x44: bic     w2, w3, w2
      +0x48: str     w2, [x0, x5]
      +0x4c: madd    w2, w2, w8, w4
      +0x50: sub     w3, w7, w2
      +0x54: sxtw    x3, w3
      +0x58: asr     x3, x3, #31
      +0x5c: add     w4, w2, w6
      +0x60: eor     w4, w4, w2
      +0x64: and     w3, w4, w3
      +0x68: eor     w2, w3, w2
      +0x6c: str     w2, [x1, x5]
      +0x70: add     x5, x5, #0x4
      +0x74: cmp     x5, #0x400
      +0x78: b.ne    <mldsa44_poly_decompose+0x20>
      +0x7c: ret
 ***)

let MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_poly_decompose"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a1 a0 x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_poly_decompose) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a1; a0] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a0 (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a1 (word(4 * i))))
                             s = mld_poly_decompose_hi_88 x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a0 (word(4 * i))))
                             s = mld_poly_decompose_lo_88 x i))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a1,1024);
                         memory :> bytes(a0,1024)])`;;

let MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_DECOMPOSE_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
