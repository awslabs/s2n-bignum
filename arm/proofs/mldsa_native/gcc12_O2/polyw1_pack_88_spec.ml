(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 6 bits per coefficient: the statement. This  *)
(* is the code for mldsa_polyw1_pack_88 (mld_polyw1_pack_88 in poly.c, for   *)
(* ML-DSA-44) from mldsa-native's portable C implementation compiled by gcc  *)
(* 12 with -O2 (see mldsa_native/README.md), which writes 3 bytes for each 4 *)
(* coefficients, as the C code does first the low part of each byte and then *)
(* the whole byte. It is verified in the whole image (see libmldsa.ml)       *)
(* against mld_polyw1_pack_88 of common/mldsa_native_packing.ml, byte by     *)
(* byte.                                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_polyw1_pack_88:
       +0x0: add     x4, x0, #0xc0
       +0x4: nop
       +0x8: ldrb    w3, [x1]
       +0xc: add     x0, x0, #0x3
      +0x10: sturb   w3, [x0, #-3]
      +0x14: add     x1, x1, #0x10
      +0x18: ldur    w2, [x1, #-12]
      +0x1c: orr     w2, w3, w2, lsl #6
      +0x20: sturb   w2, [x0, #-3]
      +0x24: ldur    w2, [x1, #-12]
      +0x28: ubfx    x2, x2, #2, #8
      +0x2c: sturb   w2, [x0, #-2]
      +0x30: ldur    w3, [x1, #-8]
      +0x34: orr     w2, w2, w3, lsl #4
      +0x38: sturb   w2, [x0, #-2]
      +0x3c: ldur    w2, [x1, #-8]
      +0x40: ubfx    x2, x2, #4, #8
      +0x44: sturb   w2, [x0, #-1]
      +0x48: ldur    w3, [x1, #-4]
      +0x4c: orr     w2, w2, w3, lsl #2
      +0x50: sturb   w2, [x0, #-1]
      +0x54: cmp     x0, x4
      +0x58: b.ne    <mldsa_polyw1_pack_88+0x8>
      +0x5c: ret
 ***)

let MLDSA_NATIVE_POLYW1_PACK_88_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_polyw1_pack_88"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYW1_PACK_88_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,192)) [(word pc,libmldsa_size); (a,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_polyw1_pack_88) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  !j. j < 192
                      ==> read(memory :> bytes8(word_add r (word j))) s =
                          mld_polyw1_pack_88 x j)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,192)])`;;

let MLDSA_NATIVE_POLYW1_PACK_88_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYW1_PACK_88_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
