(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The product w = A y of signing, with A sampled on demand and the vector y *)
(* sampled polynomial by polynomial: the statement. This is the code for     *)
(* mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy                     *)
(* (mld_polyvec_matrix_pointwise_montgomery_yvec_lazy in polyvec_lazy.c)     *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -O2 *)
(* and MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md). The structure     *)
(* mld_polymat_lazy at mat has the polynomial cur and then rho (see          *)
(* polyvec_matrix_expand_lazy_87_spec.ml), and the structure mld_yvec_lazy   *)
(* at y the address of rho'' and the 16-bit counter kappa. The code copies   *)
(* rho to a buffer of 64 bytes on the stack, aligned to 32 bytes, and for    *)
(* each column j samples polynomial j of y into the polynomial at scratch    *)
(* with mldsa87_poly_uniform_gamma1 (nonce kappa + j) and transforms it with *)
(* mldsa_poly_ntt, and for each row i samples entry (i,j) of A with          *)
(* mldsa_poly_uniform, into polynomial i of w for j = 0 and into cur         *)
(* otherwise, multiplies it with the polynomial at scratch with              *)
(* mldsa_poly_pointwise_montgomery and, for j > 0, adds it to polynomial i   *)
(* of w with mldsa_poly_add. It then zeroes the buffer, reduces w with       *)
(* mldsa87_polyveck_reduce and transforms it back with                       *)
(* mldsa87_polyveck_invntt_tomont. The stack is the 176 bytes of the frame   *)
(* and the 1392 of mldsa_poly_uniform. It is verified in the whole image     *)
(* (see libmldsa.ml) against mld_polyvec_matrix_yvec_lazy of                 *)
(* common/mldsa_native_lazy.ml and mld_sign_y of                             *)
(* common/mldsa_native_sign.ml, using the theorems for the callees and the   *)
(* contract memset_full_contract of utils/mlkem_native_libc_full.ml for the  *)
(* memsets of the samplers, assuming that the sampling of the entries        *)
(* terminates (mld_matrix_terminates), and shown to be constant time and     *)
(* memory safe, with the events depending on rho, which is public.           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_lazy.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_uniform_gamma1_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_uniform_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_pointwise_montgomery_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_add_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyveck_reduce_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyveck_invntt_tomont_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy:
       +0x0: stp     x19, x20, [sp, #-176]!
       +0x4: stp     x23, x24, [sp, #32]
       +0x8: mov     x23, x1
       +0xc: mov     x24, x3
      +0x10: stp     x21, x22, [sp, #16]
      +0x14: add     x21, sp, #0x6f
      +0x18: and     x21, x21, #0xffffffffffffffe0
      +0x1c: stp     x25, x26, [sp, #48]
      +0x20: mov     x26, x0
      +0x24: mov     x25, x2
      +0x28: str     x30, [sp, #64]
      +0x2c: mov     w22, #0x0
      +0x30: adrp    x0, <page>
      +0x34: ldr     x0, [x0, #4088]
      +0x38: ldr     q0, [x23, #1024]
      +0x3c: ldr     x1, [x0]
      +0x40: str     x1, [sp, #168]
      +0x44: mov     x1, #0x0
      +0x48: ldr     q1, [x23, #1040]
      +0x4c: stp     q0, q1, [x21]
      +0x50: nop
      +0x54: ldrh    w2, [x25, #8]
      +0x58: ldr     x1, [x25]
      +0x5c: add     w2, w22, w2
      +0x60: mov     x0, x24
      +0x64: mov     x20, x26
      +0x68: mov     w19, #0x0
      +0x6c: bl      <mldsa87_poly_uniform_gamma1>
      +0x70: mov     x0, x24
      +0x74: bl      <mldsa_poly_ntt>
      +0x78: b       <mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy+0xb4>
      +0x7c: mov     x0, x23
      +0x80: strb    w22, [x21, #32]
      +0x84: strb    w19, [x21, #33]
      +0x88: bl      <mldsa_poly_uniform>
      +0x8c: mov     x1, x24
      +0x90: mov     x0, x23
      +0x94: bl      <mldsa_poly_pointwise_montgomery>
      +0x98: add     w19, w19, #0x1
      +0x9c: mov     x0, x20
      +0xa0: mov     x1, x23
      +0xa4: bl      <mldsa_poly_add>
      +0xa8: add     x20, x20, #0x400
      +0xac: cmp     w19, #0x8
      +0xb0: b.eq    <mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy+0xe8>
      +0xb4: mov     x1, x21
      +0xb8: cbnz    w22, <mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy+0x7c>
      +0xbc: mov     x0, x20
      +0xc0: strb    wzr, [x21, #32]
      +0xc4: strb    w19, [x21, #33]
      +0xc8: bl      <mldsa_poly_uniform>
      +0xcc: mov     x0, x20
      +0xd0: mov     x1, x24
      +0xd4: add     w19, w19, #0x1
      +0xd8: bl      <mldsa_poly_pointwise_montgomery>
      +0xdc: add     x20, x20, #0x400
      +0xe0: cmp     w19, #0x8
      +0xe4: b.ne    <mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy+0xb4>
      +0xe8: add     w22, w22, #0x1
      +0xec: cmp     w22, #0x7
      +0xf0: b.ne    <mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy+0x54>
      +0xf4: movi    v0.4s, #0x0
      +0xf8: stp     q0, q0, [x21]
      +0xfc: stp     q0, q0, [x21, #32]
     +0x100: mov     x0, x26
     +0x104: bl      <mldsa87_polyveck_reduce>
     +0x108: mov     x0, x26
     +0x10c: bl      <mldsa87_polyveck_invntt_tomont>
     +0x110: adrp    x0, <page>
     +0x114: ldr     x0, [x0, #4088]
     +0x118: ldr     x2, [sp, #168]
     +0x11c: ldr     x1, [x0]
     +0x120: subs    x2, x2, x1
     +0x124: mov     x1, #0x0
     +0x128: b.ne    <mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy+0x144>
     +0x12c: ldp     x21, x22, [sp, #16]
     +0x130: ldp     x23, x24, [sp, #32]
     +0x134: ldp     x25, x26, [sp, #48]
     +0x138: ldr     x30, [sp, #64]
     +0x13c: ldp     x19, x20, [sp], #176
     +0x140: ret
     +0x144: bl      <__stack_chk_fail@plt>
 ***)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The structure at mat has   *)
(* the 32 bytes of rho, as the number r, at offset 1024, and the structure   *)
(* at y the address rp of the 64 bytes RP of rho'' and kappa: the vector at  *)
(* w becomes mld_polyvec_matrix_yvec_lazy 7 r y for the vector y sampled     *)
(* from RP and kappa (mld_sign_y). The polynomials cur at mat and at scratch *)
(* and the stack are scratch space.                                          *)
(* ------------------------------------------------------------------------- *)
let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !w mat y scratch r rp RP kappa guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 r /\
          PAIRWISE nonoverlapping
           [(w,8192); (mat,1024); (scratch,1024);
            (word_sub stackpointer (word 1568),1568)] /\
          ALLPAIRS nonoverlapping
           [(w,8192); (mat,1024); (scratch,1024);
            (word_sub stackpointer (word 1568),1568)]
           [(word_add mat (word 1024),32); (y,16); (rp,64);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                    read PC s = word (pc + mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [w; mat; y; scratch] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(word_add mat (word 1024),32)) s = r /\
                    read (memory :> bytes64 y) s = rp /\
                    read (memory :> bytes16(word_add y (word 8))) s = kappa /\
                    read (memory :> bytes(rp,64)) s = RP)
               (\s. read PC s = returnaddress /\
                    (!m. m < 2048
                         ==> read(memory :> bytes32(word_add w (word(4 * m)))) s =
                             mld_polyvec_matrix_yvec_lazy 7 r
                              (mld_sign_y mld_poly_uniform_gamma1_19 RP (val kappa))
                              m))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(w,8192); memory :> bytes(mat,1024);
                  memory :> bytes(scratch,1024);
                  memory :> bytes(word_sub stackpointer (word 1568),1568)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;


(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, rp and the addresses of the  *)
(* stack guard and memset, with all accesses within the arguments, rho'',    *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset may read and the constants of the callees, and the writes within   *)
(* w, cur, scratch and the stack.                                            *)
(* ------------------------------------------------------------------------- *)
let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e w mat y scratch r rp RP kappa guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 r /\
          PAIRWISE nonoverlapping
           [(w,8192); (mat,1024); (scratch,1024);
            (word_sub stackpointer (word 1568),1568)] /\
          ALLPAIRS nonoverlapping
           [(w,8192); (mat,1024); (scratch,1024);
            (word_sub stackpointer (word 1568),1568)]
           [(word_add mat (word 1024),32); (y,16); (rp,64);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                    read PC s = word (pc + mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [w; mat; y; scratch] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(word_add mat (word 1024),32)) s = r /\
                    read (memory :> bytes64 y) s = rp /\
                    read (memory :> bytes16(word_add y (word 8))) s = kappa /\
                    read (memory :> bytes(rp,64)) s = RP /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!m. m < 2048
                         ==> read(memory :> bytes32(word_add w (word(4 * m)))) s =
                             mld_polyvec_matrix_yvec_lazy 7 r
                              (mld_sign_y mld_poly_uniform_gamma1_19 RP (val kappa))
                              m) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events w mat y scratch r rp guard mf pc
                              (word_sub stackpointer (word 1568))
                              returnaddress /\
                       memaccess_inbounds e2
                        [word_add mat (word 1024),32; y,16; rp,64; w,8192;
                         mat,1024; scratch,1024;
                         word_sub stackpointer (word 1568),1568;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16;
                         word(pc + mldsa_poly_reduce_consts),16]
                        [w,8192; mat,1024; scratch,1024;
                         word_sub stackpointer (word 1568),1568]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(w,8192); memory :> bytes(mat,1024);
                  memory :> bytes(scratch,1024);
                  memory :> bytes(word_sub stackpointer (word 1568),1568)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;


(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)
let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e w mat y scratch r rp guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 r /\
          PAIRWISE nonoverlapping
           [(w,8192); (mat,1024); (scratch,1024);
            (word_sub stackpointer (word 1568),1568)] /\
          ALLPAIRS nonoverlapping
           [(w,8192); (mat,1024); (scratch,1024);
            (word_sub stackpointer (word 1568),1568)]
           [(word_add mat (word 1024),32); (y,16); (rp,64);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                    read PC s = word (pc + mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [w; mat; y; scratch] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(word_add mat (word 1024),32)) s = r /\
                    read (memory :> bytes64 y) s = rp /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events w mat y scratch r rp guard mf pc
                              (word_sub stackpointer (word 1568))
                              returnaddress /\
                       memaccess_inbounds e2
                        [word_add mat (word 1024),32; y,16; rp,64; w,8192;
                         mat,1024; scratch,1024;
                         word_sub stackpointer (word 1568),1568;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16;
                         word(pc + mldsa_poly_reduce_consts),16]
                        [w,8192; mat,1024; scratch,1024;
                         word_sub stackpointer (word 1568),1568]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(w,8192); memory :> bytes(mat,1024);
                  memory :> bytes(scratch,1024);
                  memory :> bytes(word_sub stackpointer (word 1568),1568)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
