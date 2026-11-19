(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise Montgomery multiplication of polynomials: the statement. This   *)
(* is the code for mldsa_poly_pointwise_montgomery                           *)
(* (mld_poly_pointwise_montgomery in poly.c, which calls the _c version)     *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -Os *)
(* (see mldsa_native/README.md), as a loop of 256 scalar multiplications.    *)
(* It is verified in the whole image (see libmldsa.ml) against               *)
(* mld_poly_pointwise_montgomery of common/mldsa_native_poly.ml, and shown   *)
(* to be constant time and memory safe.                                      *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_poly.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_pointwise_montgomery:
       +0x0: mov     w6, #0x2001
       +0x4: mov     x2, #0x0
       +0x8: movk    w6, #0x380, lsl #16
       +0xc: mov     w5, #0xff801fff
      +0x10: ldr     w3, [x1, x2]
      +0x14: ldr     w4, [x0, x2]
      +0x18: smull   x4, w4, w3
      +0x1c: mul     w3, w4, w6
      +0x20: smaddl  x3, w3, w5, x4
      +0x24: asr     x3, x3, #32
      +0x28: str     w3, [x0, x2]
      +0x2c: add     x2, x2, #0x4
      +0x30: cmp     x2, #0x400
      +0x34: b.ne    <mldsa_poly_pointwise_montgomery+0x10>
      +0x38: ret
 ***)

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa_poly_pointwise_montgomery"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomials x at r and y at b, 256 coefficients of 32    *)
(* bits each, may not overlap; r becomes                                     *)
(* mld_poly_pointwise_montgomery x y.                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r b x y pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (b,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
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

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the writes within the outputs.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r b x y pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (b,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
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
                     memaccess_inbounds e2 [r,1024; b,1024] [r,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (b,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_poly_pointwise_montgomery) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; b] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r b pc returnaddress /\
                     memaccess_inbounds e2 [r,1024; b,1024] [r,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
