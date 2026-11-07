(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 18 bits per coefficient, of 2^17 - a: the  *)
(* statement. This is the code for mldsa44_polyz_unpack (mld_polyz_unpack_c  *)
(* in poly_kl.c with MLDSA_GAMMA1 = 2^17, for ML-DSA-44, which the build     *)
(* calls as mld_polyz_unpack) from mldsa-native's portable C implementation  *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), which reads 9   *)
(* bytes for each 4 coefficients and, as the C code does, stores the partial *)
(* results before the final ones. It is verified in the whole image (see     *)
(* libmldsa.ml) against mld_polyz_unpack_17 of                               *)
(* common/mldsa_native_packing.ml.                                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyz_unpack:
       +0x0: add     x8, x1, #0x240
       +0x4: mov     w7, #0x20000
       +0x8: ldrb    w2, [x1]
       +0xc: add     x1, x1, #0x9
      +0x10: str     w2, [x0]
      +0x14: ldurb   w3, [x1, #-8]
      +0x18: orr     w3, w2, w3, lsl #8
      +0x1c: str     w3, [x0]
      +0x20: ldurb   w2, [x1, #-7]
      +0x24: orr     w2, w3, w2, lsl #16
      +0x28: and     w2, w2, #0x3ffff
      +0x2c: str     w2, [x0]
      +0x30: sub     w4, w7, w2
      +0x34: ldurb   w2, [x1, #-7]
      +0x38: lsr     w2, w2, #2
      +0x3c: str     w2, [x0, #4]
      +0x40: ldurb   w3, [x1, #-6]
      +0x44: orr     w3, w2, w3, lsl #6
      +0x48: str     w3, [x0, #4]
      +0x4c: ldurb   w2, [x1, #-5]
      +0x50: orr     w2, w3, w2, lsl #14
      +0x54: and     w2, w2, #0x3ffff
      +0x58: str     w2, [x0, #4]
      +0x5c: sub     w3, w7, w2
      +0x60: ldurb   w2, [x1, #-5]
      +0x64: lsr     w2, w2, #4
      +0x68: str     w2, [x0, #8]
      +0x6c: ldurb   w5, [x1, #-4]
      +0x70: orr     w5, w2, w5, lsl #4
      +0x74: str     w5, [x0, #8]
      +0x78: ldurb   w2, [x1, #-3]
      +0x7c: orr     w2, w5, w2, lsl #12
      +0x80: and     w2, w2, #0x3ffff
      +0x84: str     w2, [x0, #8]
      +0x88: sub     w2, w7, w2
      +0x8c: ldurb   w5, [x1, #-3]
      +0x90: lsr     w5, w5, #6
      +0x94: str     w5, [x0, #12]
      +0x98: ldurb   w6, [x1, #-2]
      +0x9c: orr     w6, w5, w6, lsl #2
      +0xa0: str     w6, [x0, #12]
      +0xa4: ldurb   w5, [x1, #-1]
      +0xa8: stp     w4, w3, [x0]
      +0xac: add     x0, x0, #0x10
      +0xb0: stur    w2, [x0, #-8]
      +0xb4: orr     w3, w6, w5, lsl #10
      +0xb8: sub     w2, w7, w3
      +0xbc: stur    w2, [x0, #-4]
      +0xc0: cmp     x8, x1
      +0xc4: b.ne    <mldsa44_polyz_unpack+0x8>
      +0xc8: ret
 ***)

let MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_polyz_unpack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (a,576)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_polyz_unpack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 576
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add r (word(4 * i))))
                            s = mld_polyz_unpack_17 b i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYZ_UNPACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
