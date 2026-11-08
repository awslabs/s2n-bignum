(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Subtraction of polynomials, coefficientwise with wraparound: the          *)
(* statement.                                                                *)
(* This is the code for mldsa_poly_sub (mld_poly_sub in poly.c) from         *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2      *)
(* (see mldsa_native/README.md), which the compiler has vectorized. It is    *)
(* verified in the whole image (see libmldsa.ml) against mld_poly_sub of     *)
(* common/mldsa_native_poly.ml, and shown to be constant time and memory     *)
(* safe.                                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_poly.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_sub:
       +0x0: mov     x2, #0x0
       +0x4: nop
       +0x8: ldr     q0, [x0, x2]
       +0xc: ldr     q1, [x1, x2]
      +0x10: sub     v0.4s, v0.4s, v1.4s
      +0x14: str     q0, [x0, x2]
      +0x18: add     x2, x2, #0x10
      +0x1c: cmp     x2, #0x400
      +0x20: b.ne    <mldsa_poly_sub+0x8>
      +0x24: ret
 ***)

let MLDSA_NATIVE_POLY_SUB_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_poly_sub"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomials x at r and y at b, 256 coefficients of 32    *)
(* bits each, may not overlap; r becomes mld_poly_sub x y.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_SUB_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r b x y pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (b,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_poly_sub) /\
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
                            s = mld_poly_sub x y i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLY_SUB_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_SUB_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* two polynomials and the writes within r.                                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_SUB_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r b x y pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (b,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_poly_sub) /\
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
                             s = mld_poly_sub x y i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r b pc returnaddress /\
                     memaccess_inbounds e2 [r,1024; b,1024] [r,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLY_SUB_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_SUB_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_SUB_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024)) [(word pc,libmldsa_size); (b,1024)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_poly_sub) /\
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

let MLDSA_NATIVE_POLY_SUB_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_SUB_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
