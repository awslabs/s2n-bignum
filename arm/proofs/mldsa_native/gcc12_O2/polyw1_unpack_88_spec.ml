(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a polynomial with 6 bits per coefficient: the statement.     *)
(* This is the code for mldsa_polyw1_unpack_88 (mld_polyw1_unpack_88 in      *)
(* poly.c, for ML-DSA-44) from mldsa-native's portable C implementation      *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), which reads 3   *)
(* bytes for each 4 coefficients. It is verified in the whole image (see     *)
(* libmldsa.ml) against mld_polyw1_unpack_88 of                              *)
(* common/mldsa_native_packing.ml.                                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_polyw1_unpack_88:
       +0x0: add     x4, x1, #0xc0
       +0x4: ldrb    w2, [x1]
       +0x8: add     x1, x1, #0x3
       +0xc: add     x0, x0, #0x10
      +0x10: and     w2, w2, #0x3f
      +0x14: stur    w2, [x0, #-16]
      +0x18: ldurb   w3, [x1, #-2]
      +0x1c: ldurb   w2, [x1, #-3]
      +0x20: lsl     w3, w3, #2
      +0x24: orr     w2, w3, w2, lsr #6
      +0x28: and     w2, w2, #0x3f
      +0x2c: stur    w2, [x0, #-12]
      +0x30: ldurb   w3, [x1, #-1]
      +0x34: ldurb   w2, [x1, #-2]
      +0x38: lsl     w3, w3, #4
      +0x3c: orr     w2, w3, w2, lsr #4
      +0x40: and     w2, w2, #0x3f
      +0x44: stur    w2, [x0, #-8]
      +0x48: ldurb   w2, [x1, #-1]
      +0x4c: lsr     w2, w2, #2
      +0x50: stur    w2, [x0, #-4]
      +0x54: cmp     x1, x4
      +0x58: b.ne    <mldsa_polyw1_unpack_88+0x4>
      +0x5c: ret
 ***)

let MLDSA_NATIVE_POLYW1_UNPACK_88_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_polyw1_unpack_88"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYW1_UNPACK_88_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (a,192)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_polyw1_unpack_88) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!j. j < 192
                       ==> read(memory :> bytes8(word_add a (word j))) s =
                           b j))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add r (word(4 * i))))
                            s = mld_polyw1_unpack_88 b i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLYW1_UNPACK_88_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYW1_UNPACK_88_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
