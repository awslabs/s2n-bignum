(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Unpacking and norm check of a vector of 6 polynomials with coefficients   *)
(* in [-4,4]: the statement. This is the code for                            *)
(* mldsa65_polyveck_unpack_eta_chknorm (mld_polyveck_unpack_eta_chknorm in   *)
(* polyvec.c) from mldsa-native's portable C implementation compiled by gcc  *)
(* 12 with -O2 (see mldsa_native/README.md), which, for each polynomial in a *)
(* loop, unpacks it to the scratch polynomial with mldsa65_polyeta_unpack    *)
(* and ORs the result of mldsa_poly_chknorm for it. It is verified in the    *)
(* whole image (see libmldsa.ml) against mld_polyvec_chknorm and             *)
(* mld_polyvec_unpack of common/mldsa_native_polyvec.ml, using the theorems  *)
(* for mldsa65_polyeta_unpack and mldsa_poly_chknorm, and shown to be        *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyeta_unpack_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_chknorm_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_polyveck_unpack_eta_chknorm:
       +0x0: stp     x19, x20, [sp, #-48]!
       +0x4: mov     x19, x0
       +0x8: mov     x20, x2
       +0xc: stp     x21, x22, [sp, #16]
      +0x10: mov     w22, w1
      +0x14: mov     w21, #0x0
      +0x18: stp     x23, x30, [sp, #32]
      +0x1c: add     x23, x0, #0x300
      +0x20: mov     x1, x19
      +0x24: mov     x0, x20
      +0x28: bl      <mldsa65_polyeta_unpack>
      +0x2c: mov     w1, w22
      +0x30: mov     x0, x20
      +0x34: add     x19, x19, #0x80
      +0x38: bl      <mldsa_poly_chknorm>
      +0x3c: orr     w21, w21, w0
      +0x40: cmp     x19, x23
      +0x44: b.ne    <mldsa65_polyveck_unpack_eta_chknorm+0x20>
      +0x48: ldp     x23, x30, [sp, #32]
      +0x4c: mov     w0, w21
      +0x50: ldp     x21, x22, [sp, #16]
      +0x54: ldp     x19, x20, [sp], #48
      +0x58: ret
 ***)

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_polyveck_unpack_eta_chknorm"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. For the 6 packed polynomials of 128 bytes each at r, given   *)
(* byte by byte by b, and the bound in the low 32 bits of bnd, the result is *)
(* the norm check mld_polyvec_chknorm 6 of their unpacked forms              *)
(* mld_polyvec_unpack 128 mld_polyeta_unpack_4 b (see                        *)
(* common/mldsa_native_polyvec.ml). The scratch polynomial at scratch is     *)
(* overwritten.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r b bnd scratch pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (scratch,1024) (word_sub stackpointer (word 48),48) /\
        ALLPAIRS nonoverlapping
         [(scratch,1024); (word_sub stackpointer (word 48),48)]
         [(word pc,libmldsa_size); (r,768)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa65_polyveck_unpack_eta_chknorm) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; bnd; scratch] s /\
                  (!j. j < 768
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           b j))
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                    word_zx(mld_polyvec_chknorm 6
                             (mld_polyvec_unpack 128 mld_polyeta_unpack_4 b)
                             (word_zx bnd)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the bound only, with all       *)
(* accesses within the packed polynomials, the scratch polynomial and the    *)
(* stack frame, and the writes within the scratch polynomial and the stack   *)
(* frame.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r b bnd scratch pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (scratch,1024) (word_sub stackpointer (word 48),48) /\
        ALLPAIRS nonoverlapping
         [(scratch,1024); (word_sub stackpointer (word 48),48)]
         [(word pc,libmldsa_size); (r,768)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa65_polyveck_unpack_eta_chknorm) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; bnd; scratch] s /\
                  (!j. j < 768
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           b j) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  C_RETURN s =
                    word_zx(mld_polyvec_chknorm 6
                             (mld_polyvec_unpack 128 mld_polyeta_unpack_4 b)
                             (word_zx bnd)) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r bnd scratch pc
                            (word_sub stackpointer (word 48)) returnaddress /\
                     memaccess_inbounds e2
                      [r,768; scratch,1024;
                       word_sub stackpointer (word 48),48]
                      [scratch,1024; word_sub stackpointer (word 48),48]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r bnd scratch pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (scratch,1024) (word_sub stackpointer (word 48),48) /\
        ALLPAIRS nonoverlapping
         [(scratch,1024); (word_sub stackpointer (word 48),48)]
         [(word pc,libmldsa_size); (r,768)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa65_polyveck_unpack_eta_chknorm) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; bnd; scratch] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r bnd scratch pc
                            (word_sub stackpointer (word 48)) returnaddress /\
                     memaccess_inbounds e2
                      [r,768; scratch,1024;
                       word_sub stackpointer (word 48),48]
                      [scratch,1024; word_sub stackpointer (word 48),48]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYVECK_UNPACK_ETA_CHKNORM_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
