(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Product of a row of the matrix with a vector, in the NTT domain: the      *)
(* statement. This is the code for                                           *)
(* mldsa65_polyvec_matrix_pointwise_montgomery_row_eager                     *)
(* (mld_polyvec_matrix_pointwise_montgomery_row_eager in polyvec_lazy.c)     *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -O2 *)
(* (see mldsa_native/README.md), which computes the address of row i of the  *)
(* matrix and calls mldsa65_polyvecl_pointwise_acc_montgomery as a tail      *)
(* call. It is verified in the whole image (see libmldsa.ml), using the      *)
(* theorems for the callee, and shown to be constant time and memory safe.   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_pointwise_acc_montgomery_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_polyvec_matrix_pointwise_montgomery_row_eager:
       +0x0: mov     w4, #0x1400
       +0x4: umaddl  x1, w3, w4, x1
       +0x8: b       <mldsa65_polyvecl_pointwise_acc_montgomery>
 ***)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_65_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_polyvec_matrix_pointwise_montgomery_row_eager"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The matrix A at mat, 6 rows of 5 polynomials of 256          *)
(* coefficients of 32 bits each, row i being the vector \j. A(1280 * i + j)  *)
(* (see common/mldsa_native_polyvec.ml), and the vector y at v, 5            *)
(* polynomials: the polynomial at t becomes the pointwise product of row i   *)
(* and y, mld_polyvec_pointwise_acc_montgomery 5 (\j. A(1280 * i + j)) y.    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!t mat v A y i pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        i < 6 /\
        ALL (nonoverlapping (t,1024))
            [(word pc,libmldsa_size); (mat,30720); (v,5120)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s =
                  word(pc +
                   mldsa65_polyvec_matrix_pointwise_montgomery_row_eager) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [t; mat; v; word i] s /\
                  (!j. j < 7680
                       ==> read(memory :> bytes32(word_add mat (word(4 * j))))
                             s = A j) /\
                  (!j. j < 1280
                       ==> read(memory :> bytes32(word_add v (word(4 * j))))
                             s = y j))
             (\s. read PC s = returnaddress /\
                  !k. k < 256
                      ==> read(memory :> bytes32(word_add t (word(4 * k))))
                            s =
                          mld_polyvec_pointwise_acc_montgomery 5
                           (\j. A(1280 * i + j)) y k)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(t,1024)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the row index only, with all   *)
(* accesses within the matrix, the vector, the polynomial and the constants  *)
(* of the callee, and the writes within the polynomial.                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e t mat v A y i pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        i < 6 /\
        ALL (nonoverlapping (t,1024))
            [(word pc,libmldsa_size); (mat,30720); (v,5120)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s =
                  word(pc +
                   mldsa65_polyvec_matrix_pointwise_montgomery_row_eager) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [t; mat; v; word i] s /\
                  (!j. j < 7680
                       ==> read(memory :> bytes32(word_add mat (word(4 * j))))
                             s = A j) /\
                  (!j. j < 1280
                       ==> read(memory :> bytes32(word_add v (word(4 * j))))
                             s = y j) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!k. k < 256
                       ==> read(memory :> bytes32(word_add t (word(4 * k))))
                             s =
                           mld_polyvec_pointwise_acc_montgomery 5
                            (\j. A(1280 * i + j)) y k) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events t mat v i pc returnaddress /\
                     memaccess_inbounds e2
                      [mat,30720; v,5120;
                       word(pc +
                         mldsa65_polyvecl_pointwise_acc_montgomery_const1),16;
                       word(pc +
                         mldsa65_polyvecl_pointwise_acc_montgomery_const2),16]
                      [t,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(t,1024)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e t mat v i pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        i < 6 /\
        ALL (nonoverlapping (t,1024))
            [(word pc,libmldsa_size); (mat,30720); (v,5120)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s =
                  word(pc +
                   mldsa65_polyvec_matrix_pointwise_montgomery_row_eager) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [t; mat; v; word i] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events t mat v i pc returnaddress /\
                     memaccess_inbounds e2
                      [mat,30720; v,5120;
                       word(pc +
                         mldsa65_polyvecl_pointwise_acc_montgomery_const1),16;
                       word(pc +
                         mldsa65_polyvecl_pointwise_acc_montgomery_const2),16]
                      [t,1024]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(t,1024)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
