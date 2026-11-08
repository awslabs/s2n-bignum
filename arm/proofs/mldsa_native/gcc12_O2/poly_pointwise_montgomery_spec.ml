(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise Montgomery multiplication of polynomials: the statement. This  *)
(* is the code for mldsa_poly_pointwise_montgomery                           *)
(* (mld_poly_pointwise_montgomery in poly.c, which calls the _c version)     *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -O2 *)
(* (see mldsa_native/README.md), which the compiler has vectorized, with     *)
(* vectors of q^-1 mod 2^32 and -q from the read-only data. It is verified   *)
(* in the whole image (see libmldsa.ml) against                              *)
(* mld_poly_pointwise_montgomery of common/mldsa_native_poly.ml, and shown   *)
(* to be constant time and memory safe.                                      *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_poly.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_pointwise_montgomery:
       +0x0: adrp    x2, <page>
       +0x4: ldr     q4, [x2, #3568]
       +0x8: adrp    x2, <page>
       +0xc: ldr     q3, [x2, #3536]
      +0x10: mov     x2, #0x0
      +0x14: nop
      +0x18: ldr     q2, [x0, x2]
      +0x1c: ldr     q0, [x1, x2]
      +0x20: smull   v1.2d, v0.2s, v2.2s
      +0x24: smull2  v0.2d, v0.4s, v2.4s
      +0x28: uzp1    v2.4s, v1.4s, v0.4s
      +0x2c: mul     v2.4s, v2.4s, v4.4s
      +0x30: smlal   v1.2d, v2.2s, v3.2s
      +0x34: smlal2  v0.2d, v2.4s, v3.4s
      +0x38: uzp2    v1.4s, v1.4s, v0.4s
      +0x3c: str     q1, [x0, x2]
      +0x40: add     x2, x2, #0x10
      +0x44: cmp     x2, #0x400
      +0x48: b.ne    <mldsa_poly_pointwise_montgomery+0x18>
      +0x4c: ret
 ***)

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_poly_pointwise_montgomery"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomials x at r and y at b, 256 coefficients of 32    *)
(* bits each, may not overlap; r becomes                                    *)
(* mld_poly_pointwise_montgomery x y.                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r b x y pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (b,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_poly_pointwise_montgomery) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; b] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i))))
                             s = x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add b (word(4 * i))))
                             s = y i))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add r (word(4 * i))))
                            s = mld_poly_pointwise_montgomery x y i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the writes within the outputs.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r b x y pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (b,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_poly_pointwise_montgomery) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; b] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i))))
                             s = x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add b (word(4 * i))))
                             s = y i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i))))
                             s = mld_poly_pointwise_montgomery x y i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r b pc returnaddress /\
                     memaccess_inbounds e2
                      [r,1024; b,1024;
                       word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                       word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                      [r,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (b,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_poly_pointwise_montgomery) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; b] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r b pc returnaddress /\
                     memaccess_inbounds e2
                      [r,1024; b,1024;
                       word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                       word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                      [r,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
