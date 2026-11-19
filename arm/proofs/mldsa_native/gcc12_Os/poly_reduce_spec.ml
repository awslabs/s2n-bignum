(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction of the coefficients of a polynomial with mld_reduce32: the      *)
(* statement. This is the code for mldsa_poly_reduce (mld_poly_reduce in     *)
(* poly.c) from mldsa-native's portable C implementation compiled by gcc 12  *)
(* with -Os (see mldsa_native/README.md), as a loop of 256 scalar            *)
(* reductions. It is verified in the whole image (see libmldsa.ml) against   *)
(* mld_poly_reduce of common/mldsa_native_poly.ml, and shown to be constant  *)
(* time and memory safe.                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_poly.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_reduce:
       +0x0: mov     x1, #0x0
       +0x4: mov     w4, #0xff801fff
       +0x8: ldr     w3, [x0, x1, lsl #2]
       +0xc: add     w2, w3, #0x400, lsl #12
      +0x10: asr     w2, w2, #23
      +0x14: madd    w2, w2, w4, w3
      +0x18: str     w2, [x0, x1, lsl #2]
      +0x1c: add     x1, x1, #0x1
      +0x20: cmp     x1, #0x100
      +0x24: b.ne    <mldsa_poly_reduce+0x8>
      +0x28: ret
 ***)

let MLDSA_NATIVE_POLY_REDUCE_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa_poly_reduce"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomial x at a, 256 coefficients of 32 bits each,     *)
(* becomes mld_poly_reduce x.                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_REDUCE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        nonoverlapping (a,1024) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_poly_reduce) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i))))
                            s = mld_poly_reduce x i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`;;

let MLDSA_NATIVE_POLY_REDUCE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_REDUCE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the writes within the outputs.                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_REDUCE_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a x pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        nonoverlapping (a,1024) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_poly_reduce) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = mld_poly_reduce x i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc returnaddress /\
                     memaccess_inbounds e2 [a,1024] [a,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`;;

let MLDSA_NATIVE_POLY_REDUCE_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_REDUCE_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_REDUCE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        nonoverlapping (a,1024) (word pc,libmldsa_size)
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa_poly_reduce) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc returnaddress /\
                     memaccess_inbounds e2 [a,1024] [a,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`;;

let MLDSA_NATIVE_POLY_REDUCE_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_REDUCE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
