(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 20 bits per coefficient, of 2^19 - a: the    *)
(* statement. This is the code for mldsa87_polyz_pack (mld_polyz_pack in     *)
(* poly_kl.c with MLDSA_GAMMA1 = 2^19, for ML-DSA-87) from mldsa-native's    *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mldsa_native/README.md), which writes 5 bytes for each 2 coefficients. It *)
(* is verified in the whole image (see libmldsa.ml) against                  *)
(* mld_polyz_pack_19 of common/mldsa_native_packing.ml, byte by byte.        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa87_polyz_pack:
       +0x0: add     x7, x0, #0x280
       +0x4: mov     w5, #0x80000
       +0x8: nop
       +0xc: ldp     w3, w2, [x1]
      +0x10: add     x0, x0, #0x5
      +0x14: add     x1, x1, #0x8
      +0x18: sub     w2, w5, w2
      +0x1c: sub     w3, w5, w3
      +0x20: sturb   w3, [x0, #-5]
      +0x24: ubfiz   w4, w2, #4, #4
      +0x28: lsr     w6, w2, #4
      +0x2c: orr     w4, w4, w3, lsr #16
      +0x30: lsr     w2, w2, #12
      +0x34: lsr     w3, w3, #8
      +0x38: sturb   w3, [x0, #-4]
      +0x3c: sturb   w4, [x0, #-3]
      +0x40: sturb   w6, [x0, #-2]
      +0x44: sturb   w2, [x0, #-1]
      +0x48: cmp     x7, x0
      +0x4c: b.ne    <mldsa87_polyz_pack+0xc>
      +0x50: ret
 ***)

let MLDSA_NATIVE_POLYZ_PACK_87_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_polyz_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,640)) [(word pc,libmldsa_size); (a,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa87_polyz_pack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  !j. j < 640
                      ==> read(memory :> bytes8(word_add r (word j))) s =
                          mld_polyz_pack_19 x j)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,640)])`;;

let MLDSA_NATIVE_POLYZ_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYZ_PACK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
