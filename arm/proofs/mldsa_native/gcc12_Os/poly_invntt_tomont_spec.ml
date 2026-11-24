(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse number-theoretic transform with the factor mont / 256: the        *)
(* statement. This is the code for mldsa_poly_invntt_tomont                  *)
(* (mld_poly_invntt_tomont in poly.c, which calls the _c version) from       *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -Os      *)
(* (see mldsa_native/README.md): three nested loops over the 8 layers, their *)
(* blocks and the butterflies of a block, with the table mld_zetas from the  *)
(* read-only data, then a loop over the coefficients that scales each. It    *)
(* is verified in the whole image (see libmldsa.ml) against                  *)
(* mld_poly_invntt_tomont of common/mldsa_native_poly.ml. It is also shown   *)
(* to be constant time and memory safe.                                      *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_ntt.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_invntt_tomont:
       +0x0: adrp    x9, <page>
       +0x4: mov     w14, #0x2001
       +0x8: add     x9, x9, #0xe78
       +0xc: mov     w3, #0x8
      +0x10: mov     w12, #0x100
      +0x14: mov     w13, #0x1
      +0x18: movk    w14, #0x380, lsl #16
      +0x1c: mov     w15, #0xff801fff
      +0x20: lsr     w2, w12, w3
      +0x24: mov     w4, #0x0
      +0x28: lsl     w5, w13, w3
      +0x2c: lsl     w11, w2, #1
      +0x30: sub     w5, w5, #0x1
      +0x34: mov     w1, w5
      +0x38: sub     w5, w5, #0x1
      +0x3c: ldr     w10, [x9, w1, uxtw #2]
      +0x40: neg     w10, w10
      +0x44: cmp     w4, w2
      +0x48: b.cs    <mldsa_poly_invntt_tomont+0x8c>
      +0x4c: mov     w6, w4
      +0x50: add     x8, x0, w2, uxtw #2
      +0x54: ldr     w1, [x0, x6, lsl #2]
      +0x58: ldr     w7, [x8]
      +0x5c: add     w7, w7, w1
      +0x60: str     w7, [x0, x6, lsl #2]
      +0x64: add     x6, x6, #0x1
      +0x68: ldr     w7, [x8]
      +0x6c: sub     w1, w1, w7
      +0x70: smull   x1, w1, w10
      +0x74: mul     w7, w1, w14
      +0x78: smaddl  x1, w7, w15, x1
      +0x7c: asr     x1, x1, #32
      +0x80: str     w1, [x8], #4
      +0x84: cmp     w2, w6
      +0x88: b.hi    <mldsa_poly_invntt_tomont+0x54>
      +0x8c: add     w4, w4, w11
      +0x90: add     w2, w2, w11
      +0x94: cmp     w4, #0xff
      +0x98: b.ls    <mldsa_poly_invntt_tomont+0x34>
      +0x9c: subs    w3, w3, #0x1
      +0xa0: b.ne    <mldsa_poly_invntt_tomont+0x20>
      +0xa4: mov     w5, #0x2001
      +0xa8: mov     x1, #0x0
      +0xac: mov     w6, #0xa3fa
      +0xb0: movk    w5, #0x380, lsl #16
      +0xb4: mov     w4, #0xff801fff
      +0xb8: ldr     w3, [x0, x1, lsl #2]
      +0xbc: smull   x3, w3, w6
      +0xc0: mul     w2, w3, w5
      +0xc4: smaddl  x2, w2, w4, x3
      +0xc8: asr     x2, x2, #32
      +0xcc: str     w2, [x0, x1, lsl #2]
      +0xd0: add     x1, x1, #0x1
      +0xd4: cmp     x1, #0x100
      +0xd8: b.ne    <mldsa_poly_invntt_tomont+0xb8>
      +0xdc: ret
 ***)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa_poly_invntt_tomont"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomial x at a, 256 coefficients of 32 bits each,     *)
(* becomes mld_poly_invntt_tomont x.                                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        nonoverlapping (a,1024) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_poly_invntt_tomont) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i))))
                            s = mld_poly_invntt_tomont x i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`;;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* polynomial and the table of zetas in the image, and the writes within     *)
(* the polynomial.                                                           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        nonoverlapping (a,1024) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_poly_invntt_tomont) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = mld_poly_invntt_tomont x i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; word(pc + rodata_mld_zetas),1024] [a,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`;;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        nonoverlapping (a,1024) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_poly_invntt_tomont) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; word(pc + rodata_mld_zetas),1024] [a,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`;;

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
