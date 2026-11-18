(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Row i of the product of the matrix A with a vector in the NTT domain,     *)
(* with A sampled on demand: the statement. This is the code for             *)
(* mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy                      *)
(* (mld_polyvec_matrix_pointwise_montgomery_row_lazy in polyvec_lazy.c) from *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 and  *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md). The structure         *)
(* mld_polymat_lazy at mat has the polynomial cur and then rho (see          *)
(* polyvec_matrix_expand_lazy_65_spec.ml). The code copies rho to a buffer   *)
(* of 64 bytes on the stack, aligned to 32 bytes, with the indices j and i   *)
(* of an entry after it, samples entry (i,0) of A into the polynomial at t   *)
(* with mldsa_poly_uniform and multiplies it with polynomial 0 of the vector *)
(* with mldsa_poly_pointwise_montgomery, then for each j from 1 to 4 samples *)
(* entry (i,j) into cur, multiplies it with polynomial j and adds it to the  *)
(* result with mldsa_poly_add, and finally reduces the result with           *)
(* mldsa_poly_reduce and zeroes the buffer. The stack is the 160 bytes of    *)
(* the frame and the 1392 of mldsa_poly_uniform. It is verified in the whole *)
(* image (see libmldsa.ml) against mld_polyvec_matrix_row_lazy of            *)
(* common/mldsa_native_lazy.ml, using the theorems for the callees and the   *)
(* contract memset_full_contract of utils/mlkem_native_libc_full.ml for the  *)
(* memset of mldsa_poly_uniform, assuming that the sampling of the entries   *)
(* terminates (mld_matrix_terminates), and shown to be constant time and     *)
(* memory safe, with the events depending on rho, which is public.           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_lazy.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_uniform_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_pointwise_montgomery_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_add_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_reduce_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy:
       +0x0: stp     x19, x20, [sp, #-160]!
       +0x4: mov     x20, x1
       +0x8: stp     x21, x22, [sp, #16]
       +0xc: add     x22, x2, #0x400
      +0x10: add     x19, sp, #0x5f
      +0x14: stp     x23, x24, [sp, #32]
      +0x18: and     x19, x19, #0xffffffffffffffe0
      +0x1c: and     w24, w3, #0xff
      +0x20: stp     x25, x30, [sp, #48]
      +0x24: mov     x25, x2
      +0x28: mov     x1, x19
      +0x2c: adrp    x2, <page>
      +0x30: ldr     x2, [x2, #4088]
      +0x34: mov     x23, x0
      +0x38: ldr     q0, [x20, #1024]
      +0x3c: ldr     x3, [x2]
      +0x40: str     x3, [sp, #152]
      +0x44: mov     x3, #0x0
      +0x48: ldr     q1, [x20, #1040]
      +0x4c: strb    wzr, [x19, #32]
      +0x50: strb    w24, [x19, #33]
      +0x54: mov     w21, #0x1
      +0x58: stp     q0, q1, [x19]
      +0x5c: bl      <mldsa_poly_uniform>
      +0x60: mov     x1, x25
      +0x64: mov     x0, x23
      +0x68: bl      <mldsa_poly_pointwise_montgomery>
      +0x6c: mov     x1, x19
      +0x70: mov     x0, x20
      +0x74: strb    w21, [x19, #32]
      +0x78: add     w21, w21, #0x1
      +0x7c: strb    w24, [x19, #33]
      +0x80: bl      <mldsa_poly_uniform>
      +0x84: mov     x1, x22
      +0x88: mov     x0, x20
      +0x8c: bl      <mldsa_poly_pointwise_montgomery>
      +0x90: add     x22, x22, #0x400
      +0x94: mov     x1, x20
      +0x98: mov     x0, x23
      +0x9c: bl      <mldsa_poly_add>
      +0xa0: cmp     w21, #0x5
      +0xa4: b.ne    <mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy+0x6c>
      +0xa8: mov     x0, x23
      +0xac: bl      <mldsa_poly_reduce>
      +0xb0: movi    v0.4s, #0x0
      +0xb4: stp     q0, q0, [x19]
      +0xb8: stp     q0, q0, [x19, #32]
      +0xbc: adrp    x0, <page>
      +0xc0: ldr     x0, [x0, #4088]
      +0xc4: ldr     x2, [sp, #152]
      +0xc8: ldr     x1, [x0]
      +0xcc: subs    x2, x2, x1
      +0xd0: mov     x1, #0x0
      +0xd4: b.ne    <mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy+0xec>
      +0xd8: ldp     x21, x22, [sp, #16]
      +0xdc: ldp     x23, x24, [sp, #32]
      +0xe0: ldp     x25, x30, [sp, #48]
      +0xe4: ldp     x19, x20, [sp], #160
      +0xe8: ret
      +0xec: bl      <__stack_chk_fail@plt>
 ***)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The structure at mat has   *)
(* the 32 bytes of rho, as the number r, at offset 1024, and the vector x at *)
(* v is 5 polynomials of 256 coefficients of 32 bits each (see               *)
(* common/mldsa_native_polyvec.ml): the polynomial at t becomes              *)
(* mld_polyvec_matrix_row_lazy 5 r x i. The polynomial cur at mat and the    *)
(* stack are scratch space.                                                  *)
(* ------------------------------------------------------------------------- *)
let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !t mat v r x i guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 r /\ i < 6 /\
          PAIRWISE nonoverlapping
           [(t,1024); (mat,1024); (word_sub stackpointer (word 1552),1552)] /\
          ALLPAIRS nonoverlapping
           [(t,1024); (mat,1024); (word_sub stackpointer (word 1552),1552)]
           [(word_add mat (word 1024),32); (v,5120); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                    read PC s = word (pc + mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [t; mat; v; word i] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(word_add mat (word 1024),32)) s = r /\
                    (!j. j < 1280
                         ==> read(memory :> bytes32(word_add v (word(4 * j))))
                               s = x j))
               (\s. read PC s = returnaddress /\
                    (!m. m < 256
                         ==> read(memory :> bytes32(word_add t (word(4 * m)))) s =
                             mld_polyvec_matrix_row_lazy 5 r x i m))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(t,1024); memory :> bytes(mat,1024);
                  memory :> bytes(word_sub stackpointer (word 1552),1552)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;


(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, i, rho and the addresses of the   *)
(* stack guard and memset, with all accesses within the arguments, the       *)
(* stack, the GOT entries and the stack guard, the region (ea,el) that       *)
(* memset may read and the constants of the callees, and the writes within   *)
(* t, cur and the stack.                                                     *)
(* ------------------------------------------------------------------------- *)
let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e t mat v r x i guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 r /\ i < 6 /\
          PAIRWISE nonoverlapping
           [(t,1024); (mat,1024); (word_sub stackpointer (word 1552),1552)] /\
          ALLPAIRS nonoverlapping
           [(t,1024); (mat,1024); (word_sub stackpointer (word 1552),1552)]
           [(word_add mat (word 1024),32); (v,5120); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                    read PC s = word (pc + mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [t; mat; v; word i] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(word_add mat (word 1024),32)) s = r /\
                    (!j. j < 1280
                         ==> read(memory :> bytes32(word_add v (word(4 * j))))
                               s = x j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!m. m < 256
                         ==> read(memory :> bytes32(word_add t (word(4 * m)))) s =
                             mld_polyvec_matrix_row_lazy 5 r x i m) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events t mat v i r guard mf pc
                              (word_sub stackpointer (word 1552))
                              returnaddress /\
                       memaccess_inbounds e2
                        [word_add mat (word 1024),32; v,5120; t,1024; mat,1024;
                         word_sub stackpointer (word 1552),1552;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16;
                         word(pc + mldsa_poly_reduce_consts),16]
                        [t,1024; mat,1024;
                         word_sub stackpointer (word 1552),1552]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(t,1024); memory :> bytes(mat,1024);
                  memory :> bytes(word_sub stackpointer (word 1552),1552)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;


(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)
let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e t mat v r i guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 r /\ i < 6 /\
          PAIRWISE nonoverlapping
           [(t,1024); (mat,1024); (word_sub stackpointer (word 1552),1552)] /\
          ALLPAIRS nonoverlapping
           [(t,1024); (mat,1024); (word_sub stackpointer (word 1552),1552)]
           [(word_add mat (word 1024),32); (v,5120); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                    read PC s = word (pc + mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [t; mat; v; word i] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(word_add mat (word 1024),32)) s = r /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events t mat v i r guard mf pc
                              (word_sub stackpointer (word 1552))
                              returnaddress /\
                       memaccess_inbounds e2
                        [word_add mat (word 1024),32; v,5120; t,1024; mat,1024;
                         word_sub stackpointer (word 1552),1552;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16;
                         word(pc + mldsa_poly_reduce_consts),16]
                        [t,1024; mat,1024;
                         word_sub stackpointer (word 1552),1552]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(t,1024); memory :> bytes(mat,1024);
                  memory :> bytes(word_sub stackpointer (word 1552),1552)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
