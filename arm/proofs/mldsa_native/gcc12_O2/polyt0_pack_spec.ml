(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 13 bits per coefficient, of 2^12 - a: the    *)
(* statement. This is the code for mldsa_polyt0_pack (mld_polyt0_pack in     *)
(* poly.c) from mldsa-native's portable C implementation compiled by gcc 12  *)
(* with -O2 (see mldsa_native/README.md), which writes 13 bytes for each 8   *)
(* coefficients, 8 of them as one 64-bit word assembled in a vector          *)
(* register. It is verified in the whole image (see libmldsa.ml) against     *)
(* mld_polyt0_pack of common/mldsa_native_packing.ml, byte by byte. It is    *)
(* also shown to be constant time and memory safe.                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_polyt0_pack:
       +0x0: add     x10, x0, #0x1a0
       +0x4: mov     w3, #0x1000
       +0x8: nop
       +0xc: ldp     w9, w6, [x1]
      +0x10: add     x0, x0, #0xd
      +0x14: ldp     w7, w4, [x1, #8]
      +0x18: sub     w6, w3, w6
      +0x1c: sub     w9, w3, w9
      +0x20: fmov    s0, w6
      +0x24: ubfiz   w2, w6, #5, #3
      +0x28: sub     w7, w3, w7
      +0x2c: ushr    v1.2s, v0.2s, #3
      +0x30: orr     w2, w2, w9, lsr #8
      +0x34: fmov    d0, x9
      +0x38: ubfiz   w11, w7, #2, #6
      +0x3c: orr     w6, w11, w6, lsr #11
      +0x40: sub     w4, w3, w4
      +0x44: mov     v0.b[1], w2
      +0x48: fmov    s2, w4
      +0x4c: ubfiz   w2, w4, #7, #1
      +0x50: orr     w9, w2, w7, lsr #6
      +0x54: ushr    v2.2s, v2.2s, #1
      +0x58: ldp     w5, w8, [x1, #16]
      +0x5c: mov     v0.b[2], v1.b[0]
      +0x60: sub     w5, w3, w5
      +0x64: fmov    s1, w5
      +0x68: sub     w8, w3, w8
      +0x6c: mov     v0.b[3], w6
      +0x70: ubfiz   w7, w5, #4, #4
      +0x74: orr     w4, w7, w4, lsr #9
      +0x78: ushr    v1.2s, v1.2s, #4
      +0x7c: ldp     w2, w7, [x1, #24]
      +0x80: ubfiz   w12, w8, #1, #7
      +0x84: mov     v0.b[4], w9
      +0x88: orr     w5, w12, w5, lsr #12
      +0x8c: sub     w2, w3, w2
      +0x90: sub     w6, w3, w7
      +0x94: sturb   w5, [x0, #-5]
      +0x98: add     x1, x1, #0x20
      +0x9c: ubfiz   w11, w2, #6, #2
      +0xa0: ubfiz   w7, w6, #3, #5
      +0xa4: mov     v0.b[5], v2.b[0]
      +0xa8: orr     w7, w7, w2, lsr #10
      +0xac: orr     w8, w11, w8, lsr #7
      +0xb0: lsr     w2, w2, #2
      +0xb4: lsr     w6, w6, #5
      +0xb8: sturb   w8, [x0, #-4]
      +0xbc: sturb   w2, [x0, #-3]
      +0xc0: mov     v0.b[6], w4
      +0xc4: sturb   w7, [x0, #-2]
      +0xc8: sturb   w6, [x0, #-1]
      +0xcc: mov     v0.b[7], v1.b[0]
      +0xd0: stur    d0, [x0, #-13]
      +0xd4: cmp     x0, x10
      +0xd8: b.ne    <mldsa_polyt0_pack+0xc>
      +0xdc: ret
 ***)

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_polyt0_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,416)) [(word pc,libmldsa_size); (a,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
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

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the writes within the outputs.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,416)) [(word pc,libmldsa_size); (a,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
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

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,416)) [(word pc,libmldsa_size); (a,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
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

let MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYT0_PACK_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
