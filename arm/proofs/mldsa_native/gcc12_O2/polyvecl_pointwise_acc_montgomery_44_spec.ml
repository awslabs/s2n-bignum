(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise products of two vectors of 4 polynomials, accumulated and       *)
(* reduced: the statement. This is the code for                              *)
(* mldsa44_polyvecl_pointwise_acc_montgomery                                 *)
(* (mld_polyvecl_pointwise_acc_montgomery in polyvec.c, which calls the _c   *)
(* version) from mldsa-native's portable C implementation compiled by gcc 12 *)
(* with -O2 (see mldsa_native/README.md), which the compiler has             *)
(* vectorized: for each group of 4 coefficients, a loop over the 4           *)
(* polynomials accumulates the 64-bit products, which are then reduced with  *)
(* vectors of q^-1 mod 2^32 and -q from the read-only data. It is verified   *)
(* in the whole image (see libmldsa.ml) against                              *)
(* mld_polyvec_pointwise_acc_montgomery 4 of common/mldsa_native_polyvec.ml, *)
(* and shown to be constant time and memory safe.                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyvecl_pointwise_acc_montgomery:
       +0x0: mov     x6, x0
       +0x4: adrp    x0, <page>
       +0x8: mov     x4, x2
       +0xc: mov     x5, x1
      +0x10: ldr     q5, [x0, #3568]
      +0x14: adrp    x0, <page>
      +0x18: mov     x1, #0x0
      +0x1c: ldr     q4, [x0, #3536]
      +0x20: add     x3, x4, x1
      +0x24: movi    v1.4s, #0x0
      +0x28: add     x2, x5, x1
      +0x2c: mov     x0, #0x0
      +0x30: mov     v0.16b, v1.16b
      +0x34: ldr     q2, [x2, x0]
      +0x38: ldr     q3, [x3, x0]
      +0x3c: add     x0, x0, #0x400
      +0x40: smlal   v0.2d, v3.2s, v2.2s
      +0x44: smlal2  v1.2d, v3.4s, v2.4s
      +0x48: cmp     x0, #0x1, lsl #12
      +0x4c: b.ne    <mldsa44_polyvecl_pointwise_acc_montgomery+0x34>
      +0x50: uzp1    v2.4s, v0.4s, v1.4s
      +0x54: mul     v2.4s, v2.4s, v5.4s
      +0x58: smlal   v0.2d, v2.2s, v4.2s
      +0x5c: smlal2  v1.2d, v2.4s, v4.4s
      +0x60: uzp2    v0.4s, v0.4s, v1.4s
      +0x64: str     q0, [x6, x1]
      +0x68: add     x1, x1, #0x10
      +0x6c: cmp     x1, #0x400
      +0x70: b.ne    <mldsa44_polyvecl_pointwise_acc_montgomery+0x20>
      +0x74: ret
 ***)

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_44_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_polyvecl_pointwise_acc_montgomery"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The vectors x at u and y at v, 4 polynomials of 256          *)
(* coefficients of 32 bits each (see common/mldsa_native_polyvec.ml), may    *)
(* overlap each other but not the polynomial at w, which becomes             *)
(* mld_polyvec_pointwise_acc_montgomery 4 x y.                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!w u v x y pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (w,1024))
            [(word pc,libmldsa_size); (u,4096); (v,4096)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s =
                    word (pc + mldsa44_polyvecl_pointwise_acc_montgomery) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [w; u; v] s /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add u (word(4 * i))))
                             s = x i) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = y i))
             (\s. read PC s = returnaddress /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add w (word(4 * i))))
                            s = mld_polyvec_pointwise_acc_montgomery 4 x y i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(w,1024)])`;;

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with the reads within the    *)
(* two vectors and the two vectors of constants in the image, and the writes *)
(* within the polynomial at w.                                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e w u v x y pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (w,1024))
            [(word pc,libmldsa_size); (u,4096); (v,4096)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s =
                    word (pc + mldsa44_polyvecl_pointwise_acc_montgomery) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [w; u; v] s /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add u (word(4 * i))))
                             s = x i) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = y i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add w (word(4 * i))))
                             s =
                           mld_polyvec_pointwise_acc_montgomery 4 x y i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events w u v pc returnaddress /\
                     memaccess_inbounds e2
                      [u,4096; v,4096;
                       word(pc +
                         mldsa44_polyvecl_pointwise_acc_montgomery_const1),16;
                       word(pc +
                         mldsa44_polyvecl_pointwise_acc_montgomery_const2),16]
                      [w,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(w,1024)])`;;

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e w u v pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (w,1024))
            [(word pc,libmldsa_size); (u,4096); (v,4096)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s =
                    word (pc + mldsa44_polyvecl_pointwise_acc_montgomery) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [w; u; v] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events w u v pc returnaddress /\
                     memaccess_inbounds e2
                      [u,4096; v,4096;
                       word(pc +
                         mldsa44_polyvecl_pointwise_acc_montgomery_const1),16;
                       word(pc +
                         mldsa44_polyvecl_pointwise_acc_montgomery_const2),16]
                      [w,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(w,1024)])`;;

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
