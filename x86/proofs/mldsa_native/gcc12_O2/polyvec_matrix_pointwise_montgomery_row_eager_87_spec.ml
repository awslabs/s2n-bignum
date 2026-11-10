(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Product of a row of the matrix with a vector, in the NTT domain: the      *)
(* statement. This is the code for                                           *)
(* mldsa87_polyvec_matrix_pointwise_montgomery_row_eager                     *)
(* (mld_polyvec_matrix_pointwise_montgomery_row_eager in polyvec_lazy.c)     *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -O2 *)
(* (see mldsa_native/README.md), which computes the address of row i of the  *)
(* matrix and calls mldsa87_polyvecl_pointwise_acc_montgomery as a tail      *)
(* call. It is verified in the whole image (see libmldsa.ml), using the      *)
(* theorems for the callee, and shown to be constant time and memory safe.   *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_pointwise_acc_montgomery_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa87_polyvec_matrix_pointwise_montgomery_row_eager:
       +0x0  mov     ecx, ecx
       +0x2  lea     rax, [rcx*8+0x0]
       +0xa  sub     rax, rcx
       +0xd  shl     rax, 0xa
      +0x11  add     rsi, rax
      +0x14  jmp     mldsa87_polyvecl_pointwise_acc_montgomery
 ***)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_polyvec_matrix_pointwise_montgomery_row_eager"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The matrix A at mat, 8 rows of 7 polynomials of 256          *)
(* coefficients of 32 bits each, row i being the vector \j. A(1792 * i + j)  *)
(* (see common/mldsa_native_polyvec.ml), and the vector y at v, 7            *)
(* polynomials: the polynomial at t becomes the pointwise product of row i   *)
(* and y, mld_polyvec_pointwise_acc_montgomery 7 (\j. A(1792 * i + j)) y.    *)
(* The stack is that of the callee: the slot of the return address, and the  *)
(* 8 bytes below it where mldsa87_polyvecl_pointwise_acc_montgomery saves    *)
(* RBX.                                                                      *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!t mat v A y i pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        i < 8 /\
        ALL (nonoverlapping (t,1024))
            [(word pc,libmldsa_size); (mat,57344); (v,7168);
             (word_sub stackpointer (word 8),8); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 8),8))
            [(word pc,libmldsa_size); (mat,57344); (v,7168)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                  word(pc +
                   mldsa87_polyvec_matrix_pointwise_montgomery_row_eager) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [t; mat; v; word i] s /\
                  (!j. j < 14336
                       ==> read(memory :> bytes32(word_add mat (word(4 * j))))
                             s = A j) /\
                  (!j. j < 1792
                       ==> read(memory :> bytes32(word_add v (word(4 * j))))
                             s = y j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!k. k < 256
                       ==> read(memory :> bytes32(word_add t (word(4 * k))))
                             s =
                           mld_polyvec_pointwise_acc_montgomery 7
                            (\j. A(1792 * i + j)) y k))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(t,1024);
                memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the row index only, with all   *)
(* accesses within the matrix, the vector, the stack of the callee and the   *)
(* slot of the return address, and the writes within the polynomial and the  *)
(* stack of the callee.                                                      *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e t mat v A y i pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        i < 8 /\
        ALL (nonoverlapping (t,1024))
            [(word pc,libmldsa_size); (mat,57344); (v,7168);
             (word_sub stackpointer (word 8),8); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 8),8))
            [(word pc,libmldsa_size); (mat,57344); (v,7168)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                  word(pc +
                   mldsa87_polyvec_matrix_pointwise_montgomery_row_eager) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [t; mat; v; word i] s /\
                  (!j. j < 14336
                       ==> read(memory :> bytes32(word_add mat (word(4 * j))))
                             s = A j) /\
                  (!j. j < 1792
                       ==> read(memory :> bytes32(word_add v (word(4 * j))))
                             s = y j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!k. k < 256
                       ==> read(memory :> bytes32(word_add t (word(4 * k))))
                             s =
                           mld_polyvec_pointwise_acc_montgomery 7
                            (\j. A(1792 * i + j)) y k) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events t mat v i pc (word_sub stackpointer (word 8))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [mat,57344; v,7168; word_sub stackpointer (word 8),8;
                       stackpointer,8]
                      [t,1024; word_sub stackpointer (word 8),8]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(t,1024);
                memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e t mat v i pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        i < 8 /\
        ALL (nonoverlapping (t,1024))
            [(word pc,libmldsa_size); (mat,57344); (v,7168);
             (word_sub stackpointer (word 8),8); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 8),8))
            [(word pc,libmldsa_size); (mat,57344); (v,7168)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                  word(pc +
                   mldsa87_polyvec_matrix_pointwise_montgomery_row_eager) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [t; mat; v; word i] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events t mat v i pc (word_sub stackpointer (word 8))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [mat,57344; v,7168; word_sub stackpointer (word 8),8;
                       stackpointer,8]
                      [t,1024; word_sub stackpointer (word 8),8]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(t,1024);
                memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
