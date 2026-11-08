(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 3 bits per coefficient, of 2 - a: the        *)
(* statement. This is the code for mldsa44_polyeta_pack (mld_polyeta_pack in *)
(* poly_kl.c with MLDSA_ETA = 2, for ML-DSA-44) from mldsa-native's portable *)
(* C implementation compiled by gcc 12 with -O2 (see                         *)
(* mldsa_native/README.md), which writes 3 bytes for each 8 coefficients. It *)
(* is verified in the whole image (see libmldsa.ml) against                  *)
(* mld_polyeta_pack_2 of common/mldsa_native_packing.ml, byte by byte. It is *)
(* also shown to be constant time and memory safe.                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyeta_pack:
       +0x0: add     x10, x1, #0x400
       +0x4: mov     w5, #0x2
       +0x8: ldp     w4, w2, [x1, #4]
       +0xc: add     x0, x0, #0x3
      +0x10: ldp     w6, w9, [x1, #12]
      +0x14: sub     w2, w5, w2
      +0x18: ldp     w7, w3, [x1, #20]
      +0x1c: sub     w4, w5, w4
      +0x20: ldr     w8, [x1, #28]
      +0x24: sub     w6, w5, w6
      +0x28: sub     w7, w5, w7
      +0x2c: sub     w9, w5, w9
      +0x30: sub     w3, w5, w3
      +0x34: sub     w8, w5, w8
      +0x38: ldr     w11, [x1], #32
      +0x3c: ubfiz   w13, w2, #6, #8
      +0x40: ubfiz   w8, w8, #5, #8
      +0x44: ubfiz   w12, w7, #7, #8
      +0x48: ubfx    x2, x2, #2, #6
      +0x4c: ubfiz   w4, w4, #3, #8
      +0x50: ubfiz   w6, w6, #1, #8
      +0x54: ubfiz   w9, w9, #4, #8
      +0x58: ubfiz   w3, w3, #2, #8
      +0x5c: orr     w4, w4, w13
      +0x60: orr     w3, w3, w8
      +0x64: orr     w6, w6, w9
      +0x68: sub     w8, w5, w11
      +0x6c: orr     w2, w2, w12
      +0x70: ubfx    x7, x7, #1, #7
      +0x74: orr     w4, w4, w8
      +0x78: orr     w2, w2, w6
      +0x7c: orr     w3, w3, w7
      +0x80: sturb   w4, [x0, #-3]
      +0x84: sturb   w2, [x0, #-2]
      +0x88: sturb   w3, [x0, #-1]
      +0x8c: cmp     x10, x1
      +0x90: b.ne    <mldsa44_polyeta_pack+0x8>
      +0x94: ret
 ***)

let MLDSA_NATIVE_POLYETA_PACK_44_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_polyeta_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,96)) [(word pc,libmldsa_size); (a,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_polyeta_pack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  !j. j < 96
                      ==> read(memory :> bytes8(word_add r (word j))) s =
                          mld_polyeta_pack_2 x j)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,96)])`;;

let MLDSA_NATIVE_POLYETA_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYETA_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the writes within the outputs.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,96)) [(word pc,libmldsa_size); (a,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_polyeta_pack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!j. j < 96
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyeta_pack_2 x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc returnaddress /\
                     memaccess_inbounds e2 [a,1024; r,96] [r,96]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,96)])`;;

let MLDSA_NATIVE_POLYETA_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYETA_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,96)) [(word pc,libmldsa_size); (a,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_polyeta_pack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc returnaddress /\
                     memaccess_inbounds e2 [a,1024; r,96] [r,96]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,96)])`;;

let MLDSA_NATIVE_POLYETA_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYETA_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
