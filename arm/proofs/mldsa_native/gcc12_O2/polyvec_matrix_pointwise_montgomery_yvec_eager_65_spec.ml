(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Product of the matrix with a vector, out of the NTT domain: the           *)
(* statement. This is the code for                                           *)
(* mldsa65_polyvec_matrix_pointwise_montgomery_yvec_eager                    *)
(* (mld_polyvec_matrix_pointwise_montgomery_yvec_eager in polyvec_lazy.c)    *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -O2 *)
(* (see mldsa_native/README.md), which copies the vector y to the scratch    *)
(* vector with memcpy, transforms it with mldsa65_polyvecl_ntt, computes     *)
(* each polynomial of the product with                                       *)
(* mldsa65_polyvec_matrix_pointwise_montgomery_row_eager in a loop, and      *)
(* transforms the product back with mldsa65_polyveck_invntt_tomont as a tail *)
(* call. It is verified in the whole image (see libmldsa.ml) against         *)
(* mld_polyvec_matrix_pointwise_montgomery of                                *)
(* common/mldsa_native_polyvec.ml, using the theorems for the callees and    *)
(* the contract memcpy_full_contract of utils/mldsa_native_libc.ml for       *)
(* memcpy, and shown to be constant time and memory safe.                    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_ntt_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvec_matrix_pointwise_montgomery_row_eager_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyveck_invntt_tomont_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memcpy:

    mldsa65_polyvec_matrix_pointwise_montgomery_yvec_eager:
       +0x0: stp     x19, x20, [sp, #-48]!
       +0x4: mov     x20, x0
       +0x8: mov     w19, #0x0
       +0xc: stp     x21, x22, [sp, #16]
      +0x10: mov     x22, x1
      +0x14: mov     x1, x2
      +0x18: mov     x2, #0x1400
      +0x1c: mov     x21, x3
      +0x20: stp     x23, x30, [sp, #32]
      +0x24: mov     x23, x0
      +0x28: mov     x0, x3
      +0x2c: bl      <memcpy@plt>
      +0x30: mov     x0, x21
      +0x34: bl      <mldsa65_polyvecl_ntt>
      +0x38: mov     w3, w19
      +0x3c: mov     x0, x20
      +0x40: mov     x2, x21
      +0x44: mov     x1, x22
      +0x48: add     w19, w19, #0x1
      +0x4c: bl      <mldsa65_polyvec_matrix_pointwise_montgomery_row_eager>
      +0x50: add     x20, x20, #0x400
      +0x54: cmp     w19, #0x6
      +0x58: b.ne    <+0x38>
      +0x5c: ldp     x21, x22, [sp, #16]
      +0x60: mov     x0, x23
      +0x64: ldp     x23, x30, [sp, #32]
      +0x68: ldp     x19, x20, [sp], #48
      +0x6c: b       <mldsa65_polyveck_invntt_tomont>

    memcpy@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4048]
       +0x8: add     x16, x16, #0xfd0
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_polyvec_matrix_pointwise_montgomery_yvec_eager";
    layout_range "plt_memcpy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memcpy. The matrix A at mat, 6     *)
(* rows of 5 polynomials of 256 coefficients of 32 bits each, and the vector *)
(* z at y, 5 polynomials (see common/mldsa_native_polyvec.ml): the vector at *)
(* w becomes the inverse NTT of the product of A with the NTT of z,          *)
(* mld_polyvec_map mld_poly_invntt_tomont                                    *)
(* (mld_polyvec_matrix_pointwise_montgomery 5 A (mld_polyvec_map             *)
(* mld_poly_ntt z)). The scratch vector at scratch is overwritten. The stack *)
(* is the 48 bytes of the function and the 32 below them of                  *)
(* mldsa65_polyvecl_ntt.                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mc ea el ev.
     memcpy_full_contract mc ea el ev
     ==> !w mat y scratch A z pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(w,6144); (scratch,5120); (word_sub stackpointer (word 80),80)] /\
          ALLPAIRS nonoverlapping
           [(w,6144); (scratch,5120); (word_sub stackpointer (word 80),80)]
           [(word pc,libmldsa_size); (mat,30720); (y,5120);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word(pc +
                     mldsa65_polyvec_matrix_pointwise_montgomery_yvec_eager) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [w; mat; y; scratch] s /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 7680
                         ==> read(memory :> bytes32
                                   (word_add mat (word(4 * j)))) s =
                             A j) /\
                    (!j. j < 1280
                         ==> read(memory :> bytes32
                                   (word_add y (word(4 * j)))) s =
                             z j))
               (\s. read PC s = returnaddress /\
                    !i. i < 1536
                        ==> read(memory :> bytes32
                                  (word_add w (word(4 * i)))) s =
                            mld_polyvec_map mld_poly_invntt_tomont
                             (mld_polyvec_matrix_pointwise_montgomery 5 A
                               (mld_polyvec_map mld_poly_ntt z)) i)
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(w,6144); memory :> bytes(scratch,5120);
                  memory :> bytes(word_sub stackpointer (word 80),80)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* arguments, the stack, the GOT entry of memcpy, the region (ea,el) that    *)
(* memcpy may read, and the tables of the callees, and the writes within the *)
(* outputs and the stack.                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mc ea el ev.
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
         forall e w mat y scratch A z pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(w,6144); (scratch,5120); (word_sub stackpointer (word 80),80)] /\
          ALLPAIRS nonoverlapping
           [(w,6144); (scratch,5120); (word_sub stackpointer (word 80),80)]
           [(word pc,libmldsa_size); (mat,30720); (y,5120);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word(pc +
                     mldsa65_polyvec_matrix_pointwise_montgomery_yvec_eager) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [w; mat; y; scratch] s /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 7680
                         ==> read(memory :> bytes32
                                   (word_add mat (word(4 * j)))) s =
                             A j) /\
                    (!j. j < 1280
                         ==> read(memory :> bytes32
                                   (word_add y (word(4 * j)))) s =
                             z j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!i. i < 1536
                         ==> read(memory :> bytes32
                                   (word_add w (word(4 * i)))) s =
                             mld_polyvec_map mld_poly_invntt_tomont
                              (mld_polyvec_matrix_pointwise_montgomery 5 A
                                (mld_polyvec_map mld_poly_ntt z)) i) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events w mat y scratch mc pc
                              (word_sub stackpointer (word 80)) returnaddress /\
                       memaccess_inbounds e2
                        [w,6144; mat,30720; y,5120; scratch,5120;
                         word_sub stackpointer (word 80),80;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const2),16]
                        [w,6144; scratch,5120;
                         word_sub stackpointer (word 80),80]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(w,6144); memory :> bytes(scratch,5120);
                  memory :> bytes(word_sub stackpointer (word 80),80)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mc ea el ev.
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
         forall e w mat y scratch pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(w,6144); (scratch,5120); (word_sub stackpointer (word 80),80)] /\
          ALLPAIRS nonoverlapping
           [(w,6144); (scratch,5120); (word_sub stackpointer (word 80),80)]
           [(word pc,libmldsa_size); (mat,30720); (y,5120);
            (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s =
                    word(pc +
                     mldsa65_polyvec_matrix_pointwise_montgomery_yvec_eager) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [w; mat; y; scratch] s /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events w mat y scratch mc pc
                              (word_sub stackpointer (word 80)) returnaddress /\
                       memaccess_inbounds e2
                        [w,6144; mat,30720; y,5120; scratch,5120;
                         word_sub stackpointer (word 80),80;
                         word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const2),16]
                        [w,6144; scratch,5120;
                         word_sub stackpointer (word 80),80]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(w,6144); memory :> bytes(scratch,5120);
                  memory :> bytes(word_sub stackpointer (word 80),80)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
