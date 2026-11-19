(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise products of two vectors of 5 polynomials, accumulated and       *)
(* reduced: the statement. This is the code for                              *)
(* mldsa65_polyvecl_pointwise_acc_montgomery                                 *)
(* (mld_polyvecl_pointwise_acc_montgomery in polyvec.c, which calls the _c   *)
(* version) from mldsa-native's portable C implementation compiled by gcc 12 *)
(* with -Os (see mldsa_native/README.md), as a loop over the 256             *)
(* coefficients: for each coefficient, a loop over the 5 polynomials         *)
(* accumulates the 64-bit products, which are then reduced. It is verified   *)
(* in the whole image (see libmldsa.ml) against                              *)
(* mld_polyvec_pointwise_acc_montgomery 5 of common/mldsa_native_polyvec.ml, *)
(* and shown to be constant time and memory safe.                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa65_polyvecl_pointwise_acc_montgomery:
       +0x0: mov     w7, #0x2001
       +0x4: mov     x3, #0x0
       +0x8: movk    w7, #0x380, lsl #16
       +0xc: mov     w8, #0xff801fff
      +0x10: mov     x4, x3
      +0x14: mov     x5, #0x0
      +0x18: mov     w6, #0x0
      +0x1c: ldr     w10, [x1, x4]
      +0x20: add     w6, w6, #0x1
      +0x24: ldr     w9, [x2, x4]
      +0x28: add     x4, x4, #0x400
      +0x2c: smaddl  x5, w10, w9, x5
      +0x30: cmp     w6, #0x5
      +0x34: b.ne    <mldsa65_polyvecl_pointwise_acc_montgomery+0x1c>
      +0x38: mul     w4, w5, w7
      +0x3c: smaddl  x4, w4, w8, x5
      +0x40: asr     x4, x4, #32
      +0x44: str     w4, [x0, x3]
      +0x48: add     x3, x3, #0x4
      +0x4c: cmp     x3, #0x400
      +0x50: b.ne    <mldsa65_polyvecl_pointwise_acc_montgomery+0x10>
      +0x54: ret
 ***)

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa65_polyvecl_pointwise_acc_montgomery"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The vectors x at u and y at v, 5 polynomials of 256          *)
(* coefficients of 32 bits each (see common/mldsa_native_polyvec.ml), may    *)
(* overlap each other but not the polynomial at w, which becomes             *)
(* mld_polyvec_pointwise_acc_montgomery 5 x y.                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!w u v x y pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (w,1024))
            [(word pc,libmldsa_size); (u,5120); (v,5120)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s =
                    word (pc + mldsa65_polyvecl_pointwise_acc_montgomery) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [w; u; v] s /\
                  (!i. i < 1280
                       ==> read(memory :> bytes32(word_add u (word(4 * i))))
                             s = x i) /\
                  (!i. i < 1280
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = y i))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add w (word(4 * i))))
                            s = mld_polyvec_pointwise_acc_montgomery 5 x y i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(w,1024)])`;;

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with the reads within the    *)
(* two vectors and the writes within the polynomial at w.                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e w u v x y pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (w,1024))
            [(word pc,libmldsa_size); (u,5120); (v,5120)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s =
                    word (pc + mldsa65_polyvecl_pointwise_acc_montgomery) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [w; u; v] s /\
                  (!i. i < 1280
                       ==> read(memory :> bytes32(word_add u (word(4 * i))))
                             s = x i) /\
                  (!i. i < 1280
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = y i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add w (word(4 * i))))
                             s =
                           mld_polyvec_pointwise_acc_montgomery 5 x y i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events w u v pc returnaddress /\
                     memaccess_inbounds e2 [u,5120; v,5120] [w,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(w,1024)])`;;

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e w u v pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (w,1024))
            [(word pc,libmldsa_size); (u,5120); (v,5120)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s =
                    word (pc + mldsa65_polyvecl_pointwise_acc_montgomery) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [w; u; v] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events w u v pc returnaddress /\
                     memaccess_inbounds e2 [u,5120; v,5120] [w,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(w,1024)])`;;

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
