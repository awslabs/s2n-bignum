(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Correction of the high parts of the coefficients of a polynomial by       *)
(* hints: the statement. This is the code for mldsa65_poly_use_hint          *)
(* (mld_poly_use_hint_c in poly_kl.c, with mld_use_hint of rounding.h for    *)
(* gamma2 = (q - 1) / 32, for ML-DSA-65) from mldsa-native's portable C      *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which replaces each coefficient of a by its corrected high part,          *)
(* branching on each hint. It is verified in the whole image (see            *)
(* libmldsa.ml) against mld_poly_use_hint_32 of                              *)
(* common/mldsa_native_rounding.ml.                                          *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_rounding.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_poly_use_hint:
       +0x0: mov     x6, #0x0
       +0x4: mov     w10, #0x3ff000
       +0x8: mov     w9, #0xff801fff
       +0xc: ldr     w3, [x0, x6]
      +0x10: add     w2, w3, #0x7f
      +0x14: asr     w2, w2, #7
      +0x18: add     w2, w2, w2, lsl #10
      +0x1c: add     w2, w2, #0x200, lsl #12
      +0x20: ubfx    x2, x2, #22, #4
      +0x24: sub     w5, w2, w2, lsl #10
      +0x28: add     w5, w3, w5, lsl #9
      +0x2c: sub     w3, w10, w5
      +0x30: sxtw    x3, w3
      +0x34: asr     x3, x3, #31
      +0x38: add     w4, w5, w9
      +0x3c: add     w7, w2, #0x1
      +0x40: eor     w4, w4, w5
      +0x44: sub     w8, w2, #0x1
      +0x48: and     w3, w4, w3
      +0x4c: ldr     w4, [x1, x6]
      +0x50: eor     w3, w3, w5
      +0x54: and     w7, w7, #0xf
      +0x58: cmp     w3, #0x0
      +0x5c: and     w8, w8, #0xf
      +0x60: cbz     w4, <mldsa65_poly_use_hint+0x68>
      +0x64: csel    w2, w8, w7, le
      +0x68: str     w2, [x0, x6]
      +0x6c: add     x6, x6, #0x4
      +0x70: cmp     x6, #0x400
      +0x74: b.ne    <mldsa65_poly_use_hint+0xc>
      +0x78: ret
 ***)

let MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_poly_use_hint"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a h x y pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping [(a,1024); (h,1024); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa65_poly_use_hint) /\
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
                            s = mld_poly_use_hint_32 x y i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`;;

let MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_USE_HINT_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
