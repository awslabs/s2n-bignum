(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Inverse number-theoretic transform with the factor mont / 256: the        *)
(* statement. This is the code for mldsa_poly_invntt_tomont                  *)
(* (mld_poly_invntt_tomont in poly.c, which calls the _c version) from       *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2      *)
(* (see mldsa_native/README.md): three nested loops over the 8 layers, their *)
(* blocks and the butterflies of a block, with the table mld_zetas from the  *)
(* read-only data, then a vectorized loop that scales the coefficients. It   *)
(* is verified in the whole image (see libmldsa.ml) against                  *)
(* mld_poly_invntt_tomont of common/mldsa_native_poly.ml.                    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_ntt.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_invntt_tomont:
      +0x0: adrp    x10, <page>
      +0x4: mov     w14, #0x2001
      +0x8: mov     x7, x0
      +0xc: add     x10, x10, #0xe00
     +0x10: add     x11, x0, #0x4
     +0x14: mov     w12, #0x8
     +0x18: mov     w16, #0x100
     +0x1c: mov     w15, #0x1
     +0x20: movk    w14, #0x380, lsl #16
     +0x24: mov     w13, #0xff801fff
     +0x28: lsr     w1, w16, w12
     +0x2c: mov     w2, #0x0
     +0x30: lsl     w5, w15, w12
     +0x34: lsl     w8, w1, #1
     +0x38: sub     w5, w5, #0x1
     +0x3c: nop
     +0x40: mov     w0, w5
     +0x44: sub     w5, w5, #0x1
     +0x48: ldr     w3, [x10, w0, uxtw #2]
     +0x4c: neg     w6, w3
     +0x50: cmp     w1, w2
     +0x54: b.ls    <mldsa_poly_invntt_tomont+0xac>
     +0x58: sub     w0, w1, w2
     +0x5c: mov     w4, w1
     +0x60: sub     w0, w0, #0x1
     +0x64: mov     w3, w2
     +0x68: add     x0, x0, x4
     +0x6c: sub     x3, x3, x4
     +0x70: add     x4, x7, w1, uxtw #2
     +0x74: add     x0, x11, x0, lsl #2
     +0x78: ldr     w9, [x4, x3, lsl #2]
     +0x7c: ldr     w17, [x4]
     +0x80: add     w17, w17, w9
     +0x84: str     w17, [x4, x3, lsl #2]
     +0x88: ldr     w17, [x4]
     +0x8c: sub     w9, w9, w17
     +0x90: smull   x9, w9, w6
     +0x94: mul     w17, w9, w14
     +0x98: smaddl  x9, w17, w13, x9
     +0x9c: asr     x9, x9, #32
     +0xa0: str     w9, [x4], #4
     +0xa4: cmp     x4, x0
     +0xa8: b.ne    <mldsa_poly_invntt_tomont+0x78>
     +0xac: add     w2, w2, w8
     +0xb0: add     w1, w1, w8
     +0xb4: cmp     w2, #0xff
     +0xb8: b.ls    <mldsa_poly_invntt_tomont+0x40>
     +0xbc: subs    w12, w12, #0x1
     +0xc0: b.ne    <mldsa_poly_invntt_tomont+0x28>
     +0xc4: adrp    x2, <page>
     +0xc8: adrp    x1, <page>
     +0xcc: mov     x0, x7
     +0xd0: ldr     q5, [x2, #3568]
     +0xd4: adrp    x2, <page>
     +0xd8: ldr     q4, [x1, #3552]
     +0xdc: add     x1, x7, #0x400
     +0xe0: ldr     q3, [x2, #3536]
     +0xe4: nop
     +0xe8: ldr     q0, [x0]
     +0xec: smull   v1.2d, v0.2s, v4.2s
     +0xf0: smull2  v0.2d, v0.4s, v4.4s
     +0xf4: uzp1    v2.4s, v1.4s, v0.4s
     +0xf8: mul     v2.4s, v2.4s, v5.4s
     +0xfc: smlal   v1.2d, v2.2s, v3.2s
    +0x100: smlal2  v0.2d, v2.4s, v3.4s
    +0x104: uzp2    v1.4s, v1.4s, v0.4s
    +0x108: str     q1, [x0], #16
    +0x10c: cmp     x1, x0
    +0x110: b.ne    <mldsa_poly_invntt_tomont+0xe8>
    +0x114: ret
 ***)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_poly_invntt_tomont"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomial x at a, 256 coefficients of 32 bits each,     *)
(* becomes mld_poly_invntt_tomont x.                                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        nonoverlapping (a,1024) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
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

let MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
