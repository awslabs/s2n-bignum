(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Decomposition of a vector of 4 polynomials with the packing of the high   *)
(* parts: the statement. This is the code for                                *)
(* mldsa44_polyveck_decompose_pack_w1 (mld_polyveck_decompose_pack_w1 in     *)
(* polyvec.c) from mldsa-native's portable C implementation compiled by gcc  *)
(* 12 with -O2 (see mldsa_native/README.md), which, for each polynomial in a *)
(* loop, decomposes it with mldsa44_poly_decompose, the low part in place    *)
(* and the high part in the scratch polynomial, and packs the high part with *)
(* mldsa_polyw1_pack_88. It is verified in the whole image (see libmldsa.ml) *)
(* against mld_polyvec_map and mld_polyvec_pack of                           *)
(* common/mldsa_native_polyvec.ml, using the theorems for                    *)
(* mldsa44_poly_decompose and mldsa_polyw1_pack_88, and shown to be constant *)
(* time and memory safe.                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_decompose_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyw1_pack_88_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyveck_decompose_pack_w1:
       +0x0: stp     x19, x20, [sp, #-48]!
       +0x4: mov     x19, x0
       +0x8: mov     x20, x1
       +0xc: stp     x21, x22, [sp, #16]
      +0x10: mov     x21, x2
      +0x14: add     x22, x0, #0x300
      +0x18: str     x30, [sp, #32]
      +0x1c: mov     x1, x20
      +0x20: mov     x0, x21
      +0x24: bl      <mldsa44_poly_decompose>
      +0x28: add     x20, x20, #0x400
      +0x2c: mov     x0, x19
      +0x30: mov     x1, x21
      +0x34: add     x19, x19, #0xc0
      +0x38: bl      <mldsa_polyw1_pack_88>
      +0x3c: cmp     x19, x22
      +0x40: b.ne    <mldsa44_polyveck_decompose_pack_w1+0x1c>
      +0x44: ldp     x21, x22, [sp, #16]
      +0x48: ldr     x30, [sp, #32]
      +0x4c: ldp     x19, x20, [sp], #48
      +0x50: ret
 ***)

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_polyveck_decompose_pack_w1"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The vector x at v, 4 polynomials of 256 coefficients of 32   *)
(* bits each (see common/mldsa_native_polyvec.ml), becomes mld_polyvec_map   *)
(* mld_poly_decompose_lo_88 x, the low parts, and the 4 packed high parts of *)
(* 192 bytes each at r are given byte by byte by mld_polyvec_pack 192        *)
(* (mld_polyw1_pack_88 o mld_poly_decompose_hi_88) x. The scratch polynomial *)
(* at scratch is overwritten.                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r v x scratch pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,768); (v,4096); (scratch,1024);
          (word_sub stackpointer (word 48),48); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_polyveck_decompose_pack_w1) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; v; scratch] s /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_decompose_lo_88 x i) /\
                  (!j. j < 768
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyvec_pack 192
                             (mld_polyw1_pack_88 o
                              mld_poly_decompose_hi_88) x j))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,768);
                memory :> bytes(v,4096);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses and writes *)
(* within the vector, the packed polynomials, the scratch polynomial and the *)
(* stack frame.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r v x scratch pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,768); (v,4096); (scratch,1024);
          (word_sub stackpointer (word 48),48); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_polyveck_decompose_pack_w1) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; v; scratch] s /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_decompose_lo_88 x i) /\
                  (!j. j < 768
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyvec_pack 192
                             (mld_polyw1_pack_88 o
                              mld_poly_decompose_hi_88) x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r v scratch pc
                            (word_sub stackpointer (word 48)) returnaddress /\
                     memaccess_inbounds e2
                      [v,4096; r,768; scratch,1024;
                       word_sub stackpointer (word 48),48]
                      [v,4096; r,768; scratch,1024;
                       word_sub stackpointer (word 48),48]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,768);
                memory :> bytes(v,4096);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r v scratch pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,768); (v,4096); (scratch,1024);
          (word_sub stackpointer (word 48),48); (word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa44_polyveck_decompose_pack_w1) /\
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
                      [v,4096; r,768; scratch,1024;
                       word_sub stackpointer (word 48),48]
                      [v,4096; r,768; scratch,1024;
                       word_sub stackpointer (word 48),48]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,768);
                memory :> bytes(v,4096);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYVECK_DECOMPOSE_PACK_W1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
