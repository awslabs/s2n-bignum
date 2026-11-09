(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking of a vector of 5 polynomials with coefficients in (-2^19,2^19]: *)
(* the statement. This is the code for mldsa65_polyvecl_unpack_z             *)
(* (mld_polyvecl_unpack_z in polyvec.c) from mldsa-native's portable C       *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which calls mldsa65_polyz_unpack for each polynomial in a loop. It is     *)
(* verified in the whole image (see libmldsa.ml) against mld_polyvec_unpack  *)
(* 640 mld_polyz_unpack_19 of common/mldsa_native_polyvec.ml, using the      *)
(* theorems for mldsa65_polyz_unpack, and shown to be constant time and      *)
(* memory safe.                                                              *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyz_unpack_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_polyvecl_unpack_z:
       +0x0: stp     x19, x20, [sp, #-32]!
       +0x4: mov     x19, x1
       +0x8: mov     x20, x0
       +0xc: stp     x21, x30, [sp, #16]
      +0x10: add     x21, x1, #0xc80
      +0x14: nop
      +0x18: mov     x1, x19
      +0x1c: mov     x0, x20
      +0x20: add     x19, x19, #0x280
      +0x24: bl      <mldsa65_polyz_unpack>
      +0x28: add     x20, x20, #0x400
      +0x2c: cmp     x19, x21
      +0x30: b.ne    <mldsa65_polyvecl_unpack_z+0x18>
      +0x34: ldp     x21, x30, [sp, #16]
      +0x38: ldp     x19, x20, [sp], #32
      +0x3c: ret
 ***)

let MLDSA_NATIVE_POLYVECL_UNPACK_Z_65_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_polyvecl_unpack_z"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The 5 packed polynomials of 640 bytes each at r, given byte  *)
(* by byte by b, are unpacked to the vector mld_polyvec_unpack 640           *)
(* mld_polyz_unpack_19 b at p, 5 polynomials of 256 coefficients of 32 bits  *)
(* each (see common/mldsa_native_polyvec.ml).                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_UNPACK_Z_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!p r b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (p,5120) (word_sub stackpointer (word 32),32) /\
        ALLPAIRS nonoverlapping
         [(p,5120); (word_sub stackpointer (word 32),32)]
         [(word pc,libmldsa_size); (r,3200)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa65_polyvecl_unpack_z) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p; r] s /\
                  (!j. j < 3200
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           b j))
             (\s. read PC s = returnaddress /\
                  !i. i < 1280
                      ==> read(memory :> bytes32(word_add p (word(4 * i))))
                            s =
                          mld_polyvec_unpack 640 mld_polyz_unpack_19 b i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(p,5120);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYVECL_UNPACK_Z_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLYVECL_UNPACK_Z_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* packed polynomials, the vector and the stack frame, and the writes within *)
(* the vector and the stack frame.                                           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_UNPACK_Z_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e p r b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (p,5120) (word_sub stackpointer (word 32),32) /\
        ALLPAIRS nonoverlapping
         [(p,5120); (word_sub stackpointer (word 32),32)]
         [(word pc,libmldsa_size); (r,3200)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa65_polyvecl_unpack_z) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [p; r] s /\
                  (!j. j < 3200
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 1280
                       ==> read(memory :> bytes32(word_add p (word(4 * i))))
                             s =
                           mld_polyvec_unpack 640 mld_polyz_unpack_19 b i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events p r pc (word_sub stackpointer (word 32))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [r,3200; p,5120; word_sub stackpointer (word 32),32]
                      [p,5120; word_sub stackpointer (word 32),32]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(p,5120);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYVECL_UNPACK_Z_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYVECL_UNPACK_Z_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_UNPACK_Z_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e p r pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (p,5120) (word_sub stackpointer (word 32),32) /\
        ALLPAIRS nonoverlapping
         [(p,5120); (word_sub stackpointer (word 32),32)]
         [(word pc,libmldsa_size); (r,3200)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa65_polyvecl_unpack_z) /\
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
                      [r,3200; p,5120; word_sub stackpointer (word 32),32]
                      [p,5120; word_sub stackpointer (word 32),32]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(p,5120);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYVECL_UNPACK_Z_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYVECL_UNPACK_Z_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
