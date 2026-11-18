(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Expansion of the matrix A from rho, lazily: the statement. This is the    *)
(* code for mldsa44_polyvec_matrix_expand_lazy                               *)
(* (mld_polyvec_matrix_expand_lazy in polyvec_lazy.c) from mldsa-native's    *)
(* portable C implementation compiled by gcc 12 with -O2 and                 *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md). With                  *)
(* MLD_CONFIG_REDUCE_RAM the matrix is not stored: the structure             *)
(* mld_polymat_lazy at mat has a polynomial cur (1024 bytes) for one entry   *)
(* at a time, and the 32 bytes of rho at offset 1024, from which             *)
(* mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy and                  *)
(* mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy sample the entries  *)
(* when they need them. The code copies rho there with two 128-bit loads and *)
(* stores. It is verified in the whole image (see libmldsa.ml) and shown to  *)
(* be constant time and memory safe.                                         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyvec_matrix_expand_lazy:
       +0x0: ldp     q0, q1, [x1]
       +0x4: add     x0, x0, #0x400
       +0x8: stp     q0, q1, [x0]
       +0xc: ret
 ***)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa44_polyvec_matrix_expand_lazy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The 32 bytes b of rho at rho, which may not overlap the 32   *)
(* bytes at mat + 1024, are copied there.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mat rho b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (word_add mat (word 1024),32))
            [(word pc,libmldsa_size); (rho,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read PC s = word (pc + mldsa44_polyvec_matrix_expand_lazy) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [mat; rho] s /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add rho (word j))) s =
                           b j))
             (\s. read PC s = returnaddress /\
                  (!j. j < 32
                       ==> read(memory :> bytes8
                                 (word_add mat (word(1024 + j)))) s =
                           b j))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_add mat (word 1024),32)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within rho *)
(* and the copy, and the writes within the copy.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e mat rho b pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (word_add mat (word 1024),32))
            [(word pc,libmldsa_size); (rho,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read PC s = word (pc + mldsa44_polyvec_matrix_expand_lazy) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [mat; rho] s /\
                  (!j. j < 32
                       ==> read(memory :> bytes8(word_add rho (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!j. j < 32
                       ==> read(memory :> bytes8
                                 (word_add mat (word(1024 + j)))) s =
                           b j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events mat rho pc returnaddress /\
                     memaccess_inbounds e2
                      [rho,32; word_add mat (word 1024),32]
                      [word_add mat (word 1024),32]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_add mat (word 1024),32)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e mat rho pc returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (word_add mat (word 1024),32))
            [(word pc,libmldsa_size); (rho,32)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read PC s = word (pc + mldsa44_polyvec_matrix_expand_lazy) /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [mat; rho] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events mat rho pc returnaddress /\
                     memaccess_inbounds e2
                      [rho,32; word_add mat (word 1024),32]
                      [word_add mat (word 1024),32]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_add mat (word 1024),32)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
