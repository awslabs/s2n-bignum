(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 18 bits per coefficient, of 2^17 - a: the    *)
(* statement. This is the code for mldsa44_polyz_pack (mld_polyz_pack in     *)
(* poly_kl.c with MLDSA_GAMMA1 = 2^17, for ML-DSA-44) from mldsa-native's    *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mldsa_native/README.md), which writes 9 bytes for each 4 coefficients, 8  *)
(* of them as one 64-bit word assembled in a vector register. It is verified *)
(* in the whole image (see libmldsa.ml) against mld_polyz_pack_17 of         *)
(* common/mldsa_native_packing.ml, byte by byte. It is also shown to be      *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyz_pack:
       +0x0: add     x9, x1, #0x400
       +0x4: mov     w6, #0x20000
       +0x8: nop
       +0xc: ldp     w2, w4, [x1]
      +0x10: add     x0, x0, #0x9
      +0x14: ldp     w3, w5, [x1, #8]
      +0x18: sub     w2, w6, w2
      +0x1c: fmov    s0, w2
      +0x20: sub     w4, w6, w4
      +0x24: sub     w3, w6, w3
      +0x28: add     x1, x1, #0x10
      +0x2c: ushr    v1.2s, v0.2s, #8
      +0x30: fmov    s0, w4
      +0x34: ubfiz   w7, w4, #2, #6
      +0x38: ubfiz   w8, w3, #4, #4
      +0x3c: ushr    v3.2s, v0.2s, #6
      +0x40: fmov    d0, x2
      +0x44: orr     w7, w7, w2, lsr #16
      +0x48: orr     w4, w8, w4, lsr #14
      +0x4c: mov     v0.b[1], v1.b[0]
      +0x50: fmov    s1, w3
      +0x54: sub     w2, w6, w5
      +0x58: ushr    v2.2s, v1.2s, #4
      +0x5c: fmov    s1, w2
      +0x60: ubfiz   w5, w2, #6, #2
      +0x64: lsr     w2, w2, #10
      +0x68: mov     v0.b[2], w7
      +0x6c: orr     w3, w5, w3, lsr #12
      +0x70: ushr    v1.2s, v1.2s, #2
      +0x74: sturb   w2, [x0, #-1]
      +0x78: mov     v0.b[3], v3.b[0]
      +0x7c: mov     v0.b[4], w4
      +0x80: mov     v0.b[5], v2.b[0]
      +0x84: mov     v0.b[6], w3
      +0x88: mov     v0.b[7], v1.b[0]
      +0x8c: stur    d0, [x0, #-9]
      +0x90: cmp     x9, x1
      +0x94: b.ne    <mldsa44_polyz_pack+0xc>
      +0x98: ret
 ***)

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_polyz_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,576)) [(word pc,libmldsa_size); (a,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_polyz_pack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  !j. j < 576
                      ==> read(memory :> bytes8(word_add r (word j))) s =
                          mld_polyz_pack_17 x j)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,576)])`;;

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the writes within the outputs.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,576)) [(word pc,libmldsa_size); (a,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_polyz_pack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!j. j < 576
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyz_pack_17 x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc returnaddress /\
                     memaccess_inbounds e2 [a,1024; r,576] [r,576]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,576)])`;;

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,576)) [(word pc,libmldsa_size); (a,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_polyz_pack) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a pc returnaddress /\
                     memaccess_inbounds e2 [a,1024; r,576] [r,576]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,576)])`;;

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
