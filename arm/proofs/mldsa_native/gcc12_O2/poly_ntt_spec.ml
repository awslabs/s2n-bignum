(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Forward number-theoretic transform: the statement. This is the code for   *)
(* mldsa_poly_ntt (mld_poly_ntt in poly.c, which calls mld_poly_ntt_c) from  *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2      *)
(* (see mldsa_native/README.md): three nested loops over the 8 layers, the   *)
(* blocks of a layer and the butterflies of a block, with the table          *)
(* mld_zetas from the read-only data. It is verified in the whole image (see *)
(* libmldsa.ml) against mld_poly_ntt of common/mldsa_native_poly.ml. It is   *)
(* also shown to be constant time and memory safe.                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_ntt.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_ntt:
       +0x0: adrp    x9, <page>
       +0x4: mov     w15, #0x2001
       +0x8: mov     x6, x0
       +0xc: add     x9, x9, #0xe00
      +0x10: mov     w3, #0x0
      +0x14: mov     w8, #0x64f7
      +0x18: mov     w13, #0x1
      +0x1c: mov     w16, #0x100
      +0x20: movk    w15, #0x380, lsl #16
      +0x24: mov     w14, #0xff801fff
      +0x28: add     w12, w3, #0x1
      +0x2c: mov     w0, #0x0
      +0x30: lsl     w3, w13, w3
      +0x34: lsr     w2, w16, w12
      +0x38: lsl     w5, w2, #1
      +0x3c: nop
      +0x40: add     w3, w3, #0x1
      +0x44: cmp     w0, w2
      +0x48: b.cs    <mldsa_poly_ntt+0x98>
      +0x4c: mov     w4, w0
      +0x50: neg     x1, x4, lsl #2
      +0x54: add     x1, x1, w2, uxtw #2
      +0x58: add     x1, x6, x1
      +0x5c: nop
      +0x60: ldr     w10, [x1, x4, lsl #2]
      +0x64: ldr     w11, [x6, x4, lsl #2]
      +0x68: smull   x10, w8, w10
      +0x6c: mul     w7, w10, w15
      +0x70: smaddl  x7, w7, w14, x10
      +0x74: asr     x7, x7, #32
      +0x78: sub     w10, w11, w7
      +0x7c: str     w10, [x1, x4, lsl #2]
      +0x80: ldr     w10, [x6, x4, lsl #2]
      +0x84: add     w7, w10, w7
      +0x88: str     w7, [x6, x4, lsl #2]
      +0x8c: add     x4, x4, #0x1
      +0x90: cmp     w2, w4
      +0x94: b.hi    <mldsa_poly_ntt+0x60>
      +0x98: add     w0, w0, w5
      +0x9c: add     w2, w2, w5
      +0xa0: cmp     w0, #0xff
      +0xa4: b.hi    <mldsa_poly_ntt+0xb0>
      +0xa8: ldr     w8, [x9, w3, uxtw #2]
      +0xac: b       <mldsa_poly_ntt+0x40>
      +0xb0: cmp     w12, #0x8
      +0xb4: b.eq    <mldsa_poly_ntt+0xc8>
      +0xb8: lsl     w0, w13, w12
      +0xbc: mov     w3, w12
      +0xc0: ldr     w8, [x9, x0, lsl #2]
      +0xc4: b       <mldsa_poly_ntt+0x28>
      +0xc8: ret
 ***)

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_poly_ntt"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomial x at a, 256 coefficients of 32 bits each,     *)
(* becomes mld_poly_ntt x.                                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        nonoverlapping (a,1024) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
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

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* polynomial and the table of zetas in the image, and the writes within the *)
(* polynomial.                                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        nonoverlapping (a,1024) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
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

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        nonoverlapping (a,1024) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
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

let MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_NTT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
