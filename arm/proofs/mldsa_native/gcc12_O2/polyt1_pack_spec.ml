(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 10 bits per coefficient: the statement. This *)
(* is the code for mldsa_polyt1_pack (mld_polyt1_pack in poly.c) from        *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mldsa_native/README.md), which writes 5 bytes for each 4 coefficients. It *)
(* is verified in the whole image (see libmldsa.ml) against mld_polyt1_pack  *)
(* of common/mldsa_native_packing.ml, byte by byte.                          *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_polyt1_pack:
       +0x0: add     x4, x0, #0x140
       +0x4: ldr     w2, [x1]
       +0x8: add     x0, x0, #0x5
       +0xc: sturb   w2, [x0, #-5]
      +0x10: ldp     w2, w3, [x1]
      +0x14: lsl     w3, w3, #2
      +0x18: orr     w2, w3, w2, asr #8
      +0x1c: sturb   w2, [x0, #-4]
      +0x20: ldp     w2, w3, [x1, #4]
      +0x24: lsl     w3, w3, #4
      +0x28: orr     w2, w3, w2, asr #6
      +0x2c: sturb   w2, [x0, #-3]
      +0x30: ldp     w2, w3, [x1, #8]
      +0x34: add     x1, x1, #0x10
      +0x38: lsl     w3, w3, #6
      +0x3c: orr     w2, w3, w2, asr #4
      +0x40: sturb   w2, [x0, #-2]
      +0x44: ldur    w2, [x1, #-4]
      +0x48: asr     w2, w2, #2
      +0x4c: sturb   w2, [x0, #-1]
      +0x50: cmp     x0, x4
      +0x54: b.ne    <mldsa_polyt1_pack+0x4>
      +0x58: ret
 ***)

let MLDSA_NATIVE_POLYT1_PACK_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_polyt1_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT1_PACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,320)) [(word pc,libmldsa_size); (a,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_polyt1_pack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  !j. j < 320
                      ==> read(memory :> bytes8(word_add r (word j))) s =
                          mld_polyt1_pack x j)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,320)])`;;

let MLDSA_NATIVE_POLYT1_PACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYT1_PACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
