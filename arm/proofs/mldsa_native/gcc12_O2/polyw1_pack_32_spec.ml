(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 4 bits per coefficient: the statement. This  *)
(* is the code for mldsa_polyw1_pack_32 (mld_polyw1_pack_32 in poly.c, for   *)
(* ML-DSA-65 and ML-DSA-87) from mldsa-native's portable C implementation    *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), which writes a  *)
(* byte for each 2 coefficients. It is verified in the whole image (see      *)
(* libmldsa.ml) against mld_polyw1_pack_32 of                                *)
(* common/mldsa_native_packing.ml, byte by byte.                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_polyw1_pack_32:
       +0x0: add     x4, x1, #0x400
       +0x4: nop
       +0x8: ldr     w2, [x1, #4]
       +0xc: ldr     w3, [x1], #8
      +0x10: orr     w2, w3, w2, lsl #4
      +0x14: strb    w2, [x0], #1
      +0x18: cmp     x4, x1
      +0x1c: b.ne    <mldsa_polyw1_pack_32+0x8>
      +0x20: ret
 ***)

let MLDSA_NATIVE_POLYW1_PACK_32_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_polyw1_pack_32"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYW1_PACK_32_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,128)) [(word pc,libmldsa_size); (a,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_polyw1_pack_32) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  !j. j < 128
                      ==> read(memory :> bytes8(word_add r (word j))) s =
                          mld_polyw1_pack_32 x j)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,128)])`;;

let MLDSA_NATIVE_POLYW1_PACK_32_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYW1_PACK_32_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
