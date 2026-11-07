(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 4 bits per coefficient: the statement.     *)
(* This is the code for mldsa_polyw1_unpack_32 (mld_polyw1_unpack_32 in      *)
(* poly.c, for ML-DSA-65 and ML-DSA-87) from mldsa-native's portable C       *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which reads a byte for each 2 coefficients. It is verified in the whole   *)
(* image (see libmldsa.ml) against mld_polyw1_unpack_32 of                   *)
(* common/mldsa_native_packing.ml.                                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_polyw1_unpack_32:
       +0x0: add     x3, x0, #0x400
       +0x4: ldrb    w2, [x1]
       +0x8: add     x0, x0, #0x8
       +0xc: and     w2, w2, #0xf
      +0x10: stur    w2, [x0, #-8]
      +0x14: ldrb    w2, [x1], #1
      +0x18: lsr     w2, w2, #4
      +0x1c: stur    w2, [x0, #-4]
      +0x20: cmp     x0, x3
      +0x24: b.ne    <mldsa_polyw1_unpack_32+0x4>
      +0x28: ret
 ***)

let MLDSA_NATIVE_POLYW1_UNPACK_32_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_polyw1_unpack_32"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYW1_UNPACK_32_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (a,128)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_polyw1_unpack_32) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 128
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add r (word(4 * i))))
                            s = mld_polyw1_unpack_32 b i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYW1_UNPACK_32_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYW1_UNPACK_32_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
