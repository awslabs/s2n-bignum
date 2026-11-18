(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decomposition of a vector of 6 polynomials with the packing of the high   *)
(* parts: the statement. This is the code for                                *)
(* mldsa65_polyveck_decompose_pack_w1 (mld_polyveck_decompose_pack_w1 in     *)
(* polyvec.c) from mldsa-native's portable C implementation compiled by gcc  *)
(* 12 with -O2 (see mldsa_native/README.md), which, for each polynomial in a *)
(* loop, decomposes it with mldsa65_poly_decompose, the low part in place    *)
(* and the high part in the scratch polynomial, and packs the high part with *)
(* mldsa_polyw1_pack_32. It is verified in the whole image (see libmldsa.ml) *)
(* against mld_polyvec_map and mld_polyvec_pack of                           *)
(* common/mldsa_native_polyvec.ml, using the theorems for                    *)
(* mldsa65_poly_decompose and mldsa_polyw1_pack_32, and shown to be constant *)
(* time and memory safe.                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_decompose_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyw1_pack_32_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_polyveck_decompose_pack_w1:
       +0x0: stp     x19, x20, [sp, #-48]!
       +0x4: mov     x20, x0
       +0x8: mov     x19, x1
       +0xc: mov     x0, #0x1800
      +0x10: stp     x21, x22, [sp, #16]
      +0x14: mov     x21, x2
      +0x18: add     x22, x1, x0
      +0x1c: str     x30, [sp, #32]
      +0x20: mov     x1, x19
      +0x24: mov     x0, x21
      +0x28: bl      <mldsa65_poly_decompose>
      +0x2c: add     x19, x19, #0x400
      +0x30: mov     x0, x20
      +0x34: mov     x1, x21
      +0x38: bl      <mldsa_polyw1_pack_32>
      +0x3c: add     x20, x20, #0x80
      +0x40: cmp     x19, x22
      +0x44: b.ne    <mldsa65_polyveck_decompose_pack_w1+0x20>
      +0x48: ldp     x21, x22, [sp, #16]
      +0x4c: ldr     x30, [sp, #32]
      +0x50: ldp     x19, x20, [sp], #48
      +0x54: ret
 ***)

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_polyveck_decompose_pack_w1"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The vector x at v, 6 polynomials of 256 coefficients of 32   *)
(* bits each (see common/mldsa_native_polyvec.ml), becomes mld_polyvec_map   *)
(* mld_poly_decompose_lo_32 x, the low parts, and the 6 packed high parts of *)
(* 128 bytes each at r are given byte by byte by mld_polyvec_pack 128        *)
(* (mld_polyw1_pack_32 o mld_poly_decompose_hi_32) x. The scratch polynomial *)
(* at scratch is overwritten.                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r v x scratch pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,768); (v,6144); (scratch,1024);
          (word_sub stackpointer (word 48),48); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa65_polyveck_decompose_pack_w1) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; v; scratch] s /\
                  (!i. i < 1536
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  (!i. i < 1536
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_decompose_lo_32 x i) /\
                  (!j. j < 768
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyvec_pack 128
                             (mld_polyw1_pack_32 o
                              mld_poly_decompose_hi_32) x j))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,768);
                memory :> bytes(v,6144);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses and writes *)
(* within the vector, the packed polynomials, the scratch polynomial and the *)
(* stack frame.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r v x scratch pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,768); (v,6144); (scratch,1024);
          (word_sub stackpointer (word 48),48); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa65_polyveck_decompose_pack_w1) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; v; scratch] s /\
                  (!i. i < 1536
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 1536
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_decompose_lo_32 x i) /\
                  (!j. j < 768
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyvec_pack 128
                             (mld_polyw1_pack_32 o
                              mld_poly_decompose_hi_32) x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r v scratch pc
                            (word_sub stackpointer (word 48)) returnaddress /\
                     memaccess_inbounds e2
                      [v,6144; r,768; scratch,1024;
                       word_sub stackpointer (word 48),48]
                      [v,6144; r,768; scratch,1024;
                       word_sub stackpointer (word 48),48]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,768);
                memory :> bytes(v,6144);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r v scratch pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,768); (v,6144); (scratch,1024);
          (word_sub stackpointer (word 48),48); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa65_polyveck_decompose_pack_w1) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; v; scratch] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r v scratch pc
                            (word_sub stackpointer (word 48)) returnaddress /\
                     memaccess_inbounds e2
                      [v,6144; r,768; scratch,1024;
                       word_sub stackpointer (word 48),48]
                      [v,6144; r,768; scratch,1024;
                       word_sub stackpointer (word 48),48]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,768);
                memory :> bytes(v,6144);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
