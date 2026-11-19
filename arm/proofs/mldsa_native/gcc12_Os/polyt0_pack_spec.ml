(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 13 bits per coefficient, of 2^12 - a: the    *)
(* statement. This is the code for mldsa_polyt0_pack (mld_polyt0_pack in     *)
(* poly.c) from mldsa-native's portable C implementation compiled by gcc 12  *)
(* with -Os (see mldsa_native/README.md), which writes 13 bytes for each 8   *)
(* coefficients, one byte at a time. It is verified in the whole image (see  *)
(* libmldsa.ml) against mld_polyt0_pack of common/mldsa_native_packing.ml,   *)
(* byte by byte. It is also shown to be constant time and memory safe.       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa_polyt0_pack:
       +0x0: add     x11, x0, #0x1a0
       +0x4: mov     w2, #0x1000
       +0x8: ldp     w10, w6, [x1]
       +0xc: add     x0, x0, #0xd
      +0x10: ldp     w9, w5, [x1, #8]
      +0x14: sub     w6, w2, w6
      +0x18: sub     w10, w2, w10
      +0x1c: ubfiz   w12, w6, #5, #3
      +0x20: sub     w9, w2, w9
      +0x24: ldp     w4, w8, [x1, #16]
      +0x28: sub     w5, w2, w5
      +0x2c: ldp     w3, w7, [x1, #24]
      +0x30: sturb   w10, [x0, #-13]
      +0x34: orr     w10, w12, w10, lsr #8
      +0x38: sturb   w10, [x0, #-12]
      +0x3c: lsr     w10, w6, #3
      +0x40: sturb   w10, [x0, #-11]
      +0x44: ubfiz   w10, w9, #2, #6
      +0x48: sub     w4, w2, w4
      +0x4c: orr     w6, w10, w6, lsr #11
      +0x50: sturb   w6, [x0, #-10]
      +0x54: ubfiz   w6, w5, #7, #1
      +0x58: sub     w8, w2, w8
      +0x5c: orr     w9, w6, w9, lsr #6
      +0x60: lsr     w6, w5, #1
      +0x64: sturb   w6, [x0, #-8]
      +0x68: ubfiz   w6, w4, #4, #4
      +0x6c: orr     w5, w6, w5, lsr #9
      +0x70: sturb   w5, [x0, #-7]
      +0x74: lsr     w5, w4, #4
      +0x78: sub     w3, w2, w3
      +0x7c: sturb   w5, [x0, #-6]
      +0x80: ubfiz   w5, w8, #1, #7
      +0x84: orr     w4, w5, w4, lsr #12
      +0x88: sub     w7, w2, w7
      +0x8c: sturb   w4, [x0, #-5]
      +0x90: ubfiz   w4, w3, #6, #2
      +0x94: orr     w8, w4, w8, lsr #7
      +0x98: lsr     w4, w3, #2
      +0x9c: sturb   w4, [x0, #-3]
      +0xa0: ubfiz   w4, w7, #3, #5
      +0xa4: orr     w3, w4, w3, lsr #10
      +0xa8: lsr     w7, w7, #5
      +0xac: sturb   w9, [x0, #-9]
      +0xb0: add     x1, x1, #0x20
      +0xb4: sturb   w8, [x0, #-4]
      +0xb8: sturb   w3, [x0, #-2]
      +0xbc: sturb   w7, [x0, #-1]
      +0xc0: cmp     x11, x0
      +0xc4: b.ne    <mldsa_polyt0_pack+0x8>
      +0xc8: ret
 ***)

let MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa_polyt0_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,416)) [(word pc,libmldsa_size); (a,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_polyt0_pack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  !j. j < 416
                      ==> read(memory :> bytes8(word_add r (word j))) s =
                          mld_polyt0_pack x j)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,416)])`;;

let MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the writes within the outputs.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,416)) [(word pc,libmldsa_size); (a,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_polyt0_pack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!j. j < 416
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyt0_pack x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc returnaddress /\
                     memaccess_inbounds e2 [a,1024; r,416] [r,416]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,416)])`;;

let MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,416)) [(word pc,libmldsa_size); (a,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_polyt0_pack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc returnaddress /\
                     memaccess_inbounds e2 [a,1024; r,416] [r,416]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,416)])`;;

let MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYT0_PACK_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
