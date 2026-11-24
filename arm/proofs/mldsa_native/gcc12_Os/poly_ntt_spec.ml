(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number-theoretic transform: the statement. This is the code for   *)
(* mldsa_poly_ntt (mld_poly_ntt in poly.c, which calls mld_poly_ntt_c) from  *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -Os      *)
(* (see mldsa_native/README.md): three nested loops over the 8 layers, the   *)
(* blocks of a layer and the butterflies of a block, with the table          *)
(* mld_zetas from the read-only data. It is verified in the whole image (see *)
(* libmldsa.ml) against mld_poly_ntt of common/mldsa_native_poly.ml. It is   *)
(* also shown to be constant time and memory safe.                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_ntt.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_ntt:
       +0x0: mov     w1, #0x1
       +0x4: adrp    x8, <page>
       +0x8: mov     w13, #0x2001
       +0xc: mov     w11, w1
      +0x10: add     x8, x8, #0xe78
      +0x14: mov     w12, #0x100
      +0x18: movk    w13, #0x380, lsl #16
      +0x1c: mov     w14, #0xff801fff
      +0x20: sub     w6, w1, #0x1
      +0x24: lsr     w2, w12, w1
      +0x28: lsl     w10, w2, #1
      +0x2c: mov     w5, #0x0
      +0x30: lsl     w6, w11, w6
      +0x34: mov     w3, w6
      +0x38: add     w6, w6, #0x1
      +0x3c: ldr     w15, [x8, w3, uxtw #2]
      +0x40: cmp     w5, w2
      +0x44: b.cs    <mldsa_poly_ntt+0x88>
      +0x48: mov     w3, w5
      +0x4c: add     x9, x0, w2, uxtw #2
      +0x50: ldr     w7, [x9]
      +0x54: smull   x7, w15, w7
      +0x58: mul     w4, w7, w13
      +0x5c: smaddl  x4, w4, w14, x7
      +0x60: ldr     w7, [x0, x3, lsl #2]
      +0x64: asr     x4, x4, #32
      +0x68: sub     w7, w7, w4
      +0x6c: str     w7, [x9], #4
      +0x70: ldr     w7, [x0, x3, lsl #2]
      +0x74: add     w4, w7, w4
      +0x78: str     w4, [x0, x3, lsl #2]
      +0x7c: add     x3, x3, #0x1
      +0x80: cmp     w2, w3
      +0x84: b.hi    <mldsa_poly_ntt+0x50>
      +0x88: add     w5, w5, w10
      +0x8c: add     w2, w2, w10
      +0x90: cmp     w5, #0xff
      +0x94: b.ls    <mldsa_poly_ntt+0x34>
      +0x98: add     w1, w1, #0x1
      +0x9c: cmp     w1, #0x9
      +0xa0: b.ne    <mldsa_poly_ntt+0x20>
      +0xa4: ret
 ***)

let MLDSA_NATIVE_POLY_NTT_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa_poly_ntt"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomial x at a, 256 coefficients of 32 bits each,     *)
(* becomes mld_poly_ntt x.                                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        nonoverlapping (a,1024) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_poly_ntt) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i))))
                            s = mld_poly_ntt x i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`;;

let MLDSA_NATIVE_POLY_NTT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_NTT_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* polynomial and the table of zetas in the image, and the writes within the *)
(* polynomial.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        nonoverlapping (a,1024) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_poly_ntt) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = mld_poly_ntt x i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; word(pc + rodata_mld_zetas),1024]
                      [a,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`;;

let MLDSA_NATIVE_POLY_NTT_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_NTT_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        nonoverlapping (a,1024) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_poly_ntt) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; word(pc + rodata_mld_zetas),1024]
                      [a,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`;;

let MLDSA_NATIVE_POLY_NTT_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_NTT_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
