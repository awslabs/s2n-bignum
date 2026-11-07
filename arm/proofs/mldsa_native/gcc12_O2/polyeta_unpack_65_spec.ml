(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 4 bits per coefficient, of 4 - a: the      *)
(* statement. This is the code for mldsa65_polyeta_unpack                    *)
(* (mld_polyeta_unpack in poly_kl.c with MLDSA_ETA = 4, for ML-DSA-65) from  *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mldsa_native/README.md), which reads a byte for each 2 coefficients. It   *)
(* is verified in the whole image (see libmldsa.ml) against                  *)
(* mld_polyeta_unpack_4 of common/mldsa_native_packing.ml.                   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_polyeta_unpack:
       +0x0: add     x5, x0, #0x400
       +0x4: mov     w4, #0x4
       +0x8: ldrb    w2, [x1]
       +0xc: add     x0, x0, #0x8
      +0x10: and     w2, w2, #0xf
      +0x14: stur    w2, [x0, #-8]
      +0x18: sub     w2, w4, w2
      +0x1c: ldrb    w3, [x1], #1
      +0x20: stur    w2, [x0, #-8]
      +0x24: sub     w2, w4, w3, lsr #4
      +0x28: stur    w2, [x0, #-4]
      +0x2c: cmp     x0, x5
      +0x30: b.ne    <mldsa65_polyeta_unpack+0x8>
      +0x34: ret
 ***)

let MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_polyeta_unpack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (a,128)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa65_polyeta_unpack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 128
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add r (word(4 * i))))
                            s = mld_polyeta_unpack_4 b i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYETA_UNPACK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
