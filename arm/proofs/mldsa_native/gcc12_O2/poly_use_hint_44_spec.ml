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
(* common/mldsa_native_rounding.ml.                                          *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_rounding.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_poly_use_hint:
       +0x0: mov     w10, #0x1800
       +0x4: mov     x6, #0x0
       +0x8: mov     w11, #0x2c0b
       +0xc: mov     w7, #0x2b
      +0x10: movk    w10, #0xfffd, lsl #16
      +0x14: mov     w9, #0x3ff000
      +0x18: mov     w8, #0xff801fff
      +0x1c: b       <mldsa44_poly_use_hint+0x38>
      +0x20: cmp     w2, #0x2b
      +0x24: csinc   w2, wzr, w2, eq
      +0x28: str     w2, [x0, x6]
      +0x2c: add     x6, x6, #0x4
      +0x30: cmp     x6, #0x400
      +0x34: b.eq    <mldsa44_poly_use_hint+0xac>
      +0x38: ldr     w4, [x0, x6]
      +0x3c: add     w3, w4, #0x7f
      +0x40: asr     w3, w3, #7
      +0x44: mul     w3, w3, w11
      +0x48: add     w3, w3, #0x800, lsl #12
      +0x4c: asr     w3, w3, #24
      +0x50: sub     w2, w7, w3
      +0x54: sxtw    x2, w2
      +0x58: asr     x2, x2, #31
      +0x5c: bic     w2, w3, w2
      +0x60: madd    w4, w2, w10, w4
      +0x64: sub     w3, w9, w4
      +0x68: sxtw    x3, w3
      +0x6c: asr     x3, x3, #31
      +0x70: ldr     w12, [x1, x6]
      +0x74: add     w5, w4, w8
      +0x78: eor     w5, w5, w4
      +0x7c: and     w3, w5, w3
      +0x80: eor     w3, w3, w4
      +0x84: cbz     w12, <mldsa44_poly_use_hint+0x28>
      +0x88: sub     w4, w2, #0x1
      +0x8c: cmp     w3, #0x0
      +0x90: b.gt    <mldsa44_poly_use_hint+0x20>
      +0x94: cmp     w2, #0x0
      +0x98: csel    w2, w4, w7, ne
      +0x9c: str     w2, [x0, x6]
      +0xa0: add     x6, x6, #0x4
      +0xa4: cmp     x6, #0x400
      +0xa8: b.ne    <mldsa44_poly_use_hint+0x38>
      +0xac: ret
 ***)

let MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_poly_use_hint"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a h x y pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping [(a,1024); (h,1024); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_poly_use_hint) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; h] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add h (word(4 * i))))
                             s = y i))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i))))
                            s = mld_poly_use_hint_88 x y i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`;;

let MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_USE_HINT_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
