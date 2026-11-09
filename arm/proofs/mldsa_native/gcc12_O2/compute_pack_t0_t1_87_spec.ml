(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The vector t of key generation, split and packed: the statement. This is  *)
(* the code for mld_compute_pack_t0_t187 (mld_compute_pack_t0_t1 in sign.c)  *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -O2 *)
(* (see mldsa_native/README.md), which expands the matrix from rho into a    *)
(* buffer on the stack with mldsa87_polyvec_matrix_expand_eager, and for     *)
(* each row k computes polynomial k of t = A * s1 + s2 with                  *)
(* mldsa87_polyvec_matrix_pointwise_montgomery_row_eager,                    *)
(* mldsa_poly_invntt_tomont, mldsa87_polyeta_unpack (for s2), mldsa_poly_add,*)
(* mldsa_poly_reduce and mldsa_poly_caddq, splits it with                    *)
(* mldsa_poly_power2round and packs t1 and t0 with mldsa_polyt1_pack and     *)
(* mldsa_polyt0_pack, before zeroing the buffers with memset. It is verified *)
(* in the whole image (see libmldsa.ml) against mld_compute_t of             *)
(* common/mldsa_native_sign.ml, using the theorems for the callees and the   *)
(* contract memset_full_contract of utils/mlkem_native_libc_full.ml for      *)
(* memset, assuming that the expansion of the matrix terminates              *)
(* (mld_matrix_terminates), and shown to be constant time and memory safe,   *)
(* with the events depending on rho, which is public.                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvec_matrix_expand_eager_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvec_matrix_pointwise_montgomery_row_eager_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyeta_unpack_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_add_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_reduce_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_caddq_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_power2round_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyt1_pack_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyt0_pack_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mld_compute_pack_t0_t187:
       +0x0: mov     x12, #0xe870
       +0x4: sub     sp, sp, x12
       +0x8: stp     x21, x22, [sp, #16]
       +0xc: mov     x22, x3
      +0x10: mov     w21, #0x0
      +0x14: adrp    x3, <page>
      +0x18: ldr     x3, [x3, #4088]
      +0x1c: stp     x19, x20, [sp]
      +0x20: stp     x23, x24, [sp, #32]
      +0x24: mov     x24, x1
      +0x28: mov     x1, x4
      +0x2c: stp     x25, x26, [sp, #48]
      +0x30: add     x4, sp, #0xc, lsl #12
      +0x34: mov     x23, x2
      +0x38: str     x30, [sp, #64]
      +0x3c: add     x26, sp, #0x6f
      +0x40: and     x26, x26, #0xffffffffffffffe0
      +0x44: mov     x25, x0
      +0x48: ldr     x2, [x3]
      +0x4c: str     x2, [x4, #10344]
      +0x50: mov     x2, #0x0
      +0x54: mov     x0, #0xe400
      +0x58: add     x20, x26, #0xe, lsl #12
      +0x5c: add     x19, x26, x0
      +0x60: mov     x0, x26
      +0x64: bl      <mldsa87_polyvec_matrix_expand_eager>
      +0x68: mov     w3, w21
      +0x6c: mov     x2, x23
      +0x70: mov     x1, x26
      +0x74: mov     x0, x19
      +0x78: bl      <mldsa87_polyvec_matrix_pointwise_montgomery_row_eager>
      +0x7c: add     w21, w21, #0x1
      +0x80: mov     x0, x19
      +0x84: bl      <mldsa_poly_invntt_tomont>
      +0x88: mov     x1, x22
      +0x8c: mov     x0, x20
      +0x90: bl      <mldsa87_polyeta_unpack>
      +0x94: add     x22, x22, #0x60
      +0x98: mov     x1, x20
      +0x9c: mov     x0, x19
      +0xa0: bl      <mldsa_poly_add>
      +0xa4: mov     x0, x19
      +0xa8: bl      <mldsa_poly_reduce>
      +0xac: mov     x0, x19
      +0xb0: bl      <mldsa_poly_caddq>
      +0xb4: mov     x2, x19
      +0xb8: mov     x1, x19
      +0xbc: mov     x0, x20
      +0xc0: bl      <mldsa_poly_power2round>
      +0xc4: mov     x0, x25
      +0xc8: mov     x1, x20
      +0xcc: bl      <mldsa_polyt1_pack>
      +0xd0: add     x25, x25, #0x140
      +0xd4: mov     x0, x24
      +0xd8: mov     x1, x19
      +0xdc: bl      <mldsa_polyt0_pack>
      +0xe0: add     x24, x24, #0x1a0
      +0xe4: cmp     w21, #0x8
      +0xe8: b.ne    <+0x68>
      +0xec: mov     x0, x20
      +0xf0: mov     x2, #0x400
      +0xf4: mov     w1, #0x0
      +0xf8: bl      <memset@plt>
      +0xfc: mov     x2, #0x400
     +0x100: mov     x0, x19
     +0x104: mov     w1, #0x0
     +0x108: bl      <memset@plt>
     +0x10c: mov     x2, #0xe000
     +0x110: mov     x0, x26
     +0x114: mov     w1, #0x0
     +0x118: bl      <memset@plt>
     +0x11c: adrp    x0, <page>
     +0x120: ldr     x0, [x0, #4088]
     +0x124: add     x2, sp, #0xc, lsl #12
     +0x128: ldr     x3, [x2, #10344]
     +0x12c: ldr     x1, [x0]
     +0x130: subs    x3, x3, x1
     +0x134: mov     x1, #0x0
     +0x138: b.ne    <+0x160>
     +0x13c: ldp     x19, x20, [sp]
     +0x140: mov     w0, #0x0
     +0x144: ldp     x21, x22, [sp, #16]
     +0x148: mov     x12, #0xe870
     +0x14c: ldp     x23, x24, [sp, #32]
     +0x150: ldp     x25, x26, [sp, #48]
     +0x154: ldr     x30, [sp, #64]
     +0x158: add     sp, sp, x12
     +0x15c: ret
     +0x160: bl      <__stack_chk_fail@plt>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mld_compute_pack_t0_t187"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The vector s1hat (s1 in    *)
(* the NTT domain) of 7 polynomials sh at s1hat, the 8 polynomials of s2     *)
(* packed in 96 bytes each, s2b at s2, and rho, the 32 bytes r at rho: the   *)
(* 8 polynomials of t1 packed in 320 bytes each are written at pkt1 and the  *)
(* 8 of t0 packed in 416 bytes each at t0, with t = mld_compute_t, if the    *)
(* expansion of the matrix terminates, and the result is 0. The stack is the *)
(* 59504 bytes of the function and the 5056 of the callees below them.       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pkt1 t0 s1hat s2 rho sh s2b r guard pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 r /\
          PAIRWISE nonoverlapping
           [(pkt1,2560); (t0,3328);
            (word_sub stackpointer (word 64560),64560)] /\
          ALLPAIRS nonoverlapping
           [(pkt1,2560); (t0,3328);
            (word_sub stackpointer (word 64560),64560)]
           [(s1hat,7168); (s2,768); (rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mld_compute_pack_t0_t187) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 1792
                         ==> read(memory :> bytes32
                                   (word_add s1hat (word(4 * j)))) s =
                             sh j) /\
                    (!j. j < 768
                         ==> read(memory :> bytes8(word_add s2 (word j))) s =
                             s2b j) /\
                    read (memory :> bytes(rho,32)) s = r)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add pkt1 (word j))) s =
                             mld_polyvec_pack 320 mld_polyt1_pack
                              (mld_polyvec_map mld_poly_power2round_hi
                                (mld_compute_t 7 mld_polyeta_unpack_2 96 r
                                   sh s2b)) j) /\
                    (!j. j < 3328
                         ==> read(memory :> bytes8(word_add t0 (word j))) s =
                             mld_polyvec_pack 416 mld_polyt0_pack
                              (mld_polyvec_map mld_poly_power2round_lo
                                (mld_compute_t 7 mld_polyeta_unpack_2 96 r
                                   sh s2b)) j))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pkt1,2560); memory :> bytes(t0,3328);
                  memory :> bytes(word_sub stackpointer (word 64560),64560)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the address of memset and    *)
(* the stack, with all accesses within the arguments, the stack, the GOT     *)
(* entries and the stack guard, the region (ea,el) that memset may read and  *)
(* the constants of the callees, and the writes within the outputs and the   *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pkt1 t0 s1hat s2 rho sh s2b r guard pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 r /\
          PAIRWISE nonoverlapping
           [(pkt1,2560); (t0,3328);
            (word_sub stackpointer (word 64560),64560)] /\
          ALLPAIRS nonoverlapping
           [(pkt1,2560); (t0,3328);
            (word_sub stackpointer (word 64560),64560)]
           [(s1hat,7168); (s2,768); (rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mld_compute_pack_t0_t187) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 1792
                         ==> read(memory :> bytes32
                                   (word_add s1hat (word(4 * j)))) s =
                             sh j) /\
                    (!j. j < 768
                         ==> read(memory :> bytes8(word_add s2 (word j))) s =
                             s2b j) /\
                    read (memory :> bytes(rho,32)) s = r /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add pkt1 (word j))) s =
                             mld_polyvec_pack 320 mld_polyt1_pack
                              (mld_polyvec_map mld_poly_power2round_hi
                                (mld_compute_t 7 mld_polyeta_unpack_2 96 r
                                   sh s2b)) j) /\
                    (!j. j < 3328
                         ==> read(memory :> bytes8(word_add t0 (word j))) s =
                             mld_polyvec_pack 416 mld_polyt0_pack
                              (mld_polyvec_map mld_poly_power2round_lo
                                (mld_compute_t 7 mld_polyeta_unpack_2 96 r
                                   sh s2b)) j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pkt1 t0 s1hat s2 rho r guard mf pc
                              (word_sub stackpointer (word 64560))
                              returnaddress /\
                       memaccess_inbounds e2
                        [s1hat,7168; s2,768; rho,32; pkt1,2560; t0,3328;
                         word_sub stackpointer (word 64560),64560;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const2),16]
                        [pkt1,2560; t0,3328;
                         word_sub stackpointer (word 64560),64560]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pkt1,2560); memory :> bytes(t0,3328);
                  memory :> bytes(word_sub stackpointer (word 64560),64560)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pkt1 t0 s1hat s2 rho sh s2b r guard pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 r /\
          PAIRWISE nonoverlapping
           [(pkt1,2560); (t0,3328);
            (word_sub stackpointer (word 64560),64560)] /\
          ALLPAIRS nonoverlapping
           [(pkt1,2560); (t0,3328);
            (word_sub stackpointer (word 64560),64560)]
           [(s1hat,7168); (s2,768); (rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mld_compute_pack_t0_t187) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 1792
                         ==> read(memory :> bytes32
                                   (word_add s1hat (word(4 * j)))) s =
                             sh j) /\
                    (!j. j < 768
                         ==> read(memory :> bytes8(word_add s2 (word j))) s =
                             s2b j) /\
                    read (memory :> bytes(rho,32)) s = r /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pkt1 t0 s1hat s2 rho r guard mf pc
                              (word_sub stackpointer (word 64560))
                              returnaddress /\
                       memaccess_inbounds e2
                        [s1hat,7168; s2,768; rho,32; pkt1,2560; t0,3328;
                         word_sub stackpointer (word 64560),64560;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const2),16]
                        [pkt1,2560; t0,3328;
                         word_sub stackpointer (word 64560),64560]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pkt1,2560); memory :> bytes(t0,3328);
                  memory :> bytes(word_sub stackpointer (word 64560),64560)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_COMPUTE_PACK_T0_T1_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
