(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a vector of 4 polynomials with coefficients in [-2,2]: the   *)
(* statement. This is the code for mldsa44_polyveck_unpack_eta               *)
(* (mld_polyveck_unpack_eta in polyvec.c) from mldsa-native's portable C     *)
(* implementation compiled by gcc 12 with -Os (see mldsa_native/README.md),  *)
(* which is a tail call of mldsa44_polyvecl_unpack_eta: with 4 rows and 4    *)
(* columns the two vectors have the same type. It is verified in the whole   *)
(* image (see libmldsa.ml) against mld_polyvec_unpack 96                     *)
(* mld_polyeta_unpack_2 of common/mldsa_native_polyvec.ml, using the         *)
(* theorems for mldsa44_polyvecl_unpack_eta, and shown to be constant time   *)
(* and memory safe.                                                          *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_unpack_eta_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyveck_unpack_eta:
       +0x0: b       <mldsa44_polyvecl_unpack_eta>
 ***)

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_44_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa44_polyveck_unpack_eta"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The 4 packed polynomials of 96 bytes each at r, given byte   *)
(* by byte by b, are unpacked to the vector mld_polyvec_unpack 96            *)
(* mld_polyeta_unpack_2 b at p, 4 polynomials of 256 coefficients of 32 bits *)
(* each (see common/mldsa_native_polyvec.ml).                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!p r b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (p,4096) (word_sub stackpointer (word 32),32) /\
        ALLPAIRS nonoverlapping
         [(p,4096); (word_sub stackpointer (word 32),32)]
         [(word pc,libmldsa_size); (r,384)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa44_polyveck_unpack_eta) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p; r] s /\
                  (!j. j < 384
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           b j))
             (\s. read PC s = returnaddress /\
                  !i. i < 1024
                      ==> read(memory :> bytes32(word_add p (word(4 * i))))
                            s =
                          mld_polyvec_unpack 96 mld_polyeta_unpack_2 b i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(p,4096);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLYVECK_UNPACK_ETA_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* packed polynomials, the vector and the stack frame, and the writes within *)
(* the vector and the stack frame.                                           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e p r b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (p,4096) (word_sub stackpointer (word 32),32) /\
        ALLPAIRS nonoverlapping
         [(p,4096); (word_sub stackpointer (word 32),32)]
         [(word pc,libmldsa_size); (r,384)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa44_polyveck_unpack_eta) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p; r] s /\
                  (!j. j < 384
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add p (word(4 * i))))
                             s =
                           mld_polyvec_unpack 96 mld_polyeta_unpack_2 b i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events p r pc (word_sub stackpointer (word 32))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [r,384; p,4096; word_sub stackpointer (word 32),32]
                      [p,4096; word_sub stackpointer (word 32),32]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(p,4096);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_44_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYVECK_UNPACK_ETA_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e p r pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (p,4096) (word_sub stackpointer (word 32),32) /\
        ALLPAIRS nonoverlapping
         [(p,4096); (word_sub stackpointer (word 32),32)]
         [(word pc,libmldsa_size); (r,384)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mldsa44_polyveck_unpack_eta) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p; r] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events p r pc (word_sub stackpointer (word 32))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [r,384; p,4096; word_sub stackpointer (word 32),32]
                      [p,4096; word_sub stackpointer (word 32),32]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(p,4096);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYVECK_UNPACK_ETA_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
