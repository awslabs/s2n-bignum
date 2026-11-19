(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The vector t of key generation, split and packed: the statement. This is  *)
(* the code for mld_compute_pack_t0_t144 (mld_compute_pack_t0_t1 in sign.c)  *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -Os *)
(* (see mldsa_native/README.md), which expands the matrix from rho into a    *)
(* buffer on the stack with mldsa44_polyvec_matrix_expand_eager, and for     *)
(* each row k computes polynomial k of t = A * s1 + s2 with                  *)
(* mldsa44_polyvec_matrix_pointwise_montgomery_row_eager,                    *)
(* mldsa_poly_invntt_tomont, mldsa44_polyeta_unpack (for s2), mldsa_poly_add,*)
(* mldsa_poly_reduce and mldsa_poly_caddq, splits it with                    *)
(* mldsa_poly_power2round and packs t1 and t0 with mldsa_polyt1_pack and     *)
(* mldsa_polyt0_pack, before zeroing the buffers with mld_zeroize_2 (a call  *)
(* of memset). It is verified in the whole image (see libmldsa.ml) against   *)
(* mld_compute_t of common/mldsa_native_sign.ml, using the theorems for the  *)
(* callees and the contract memset_full_contract of                          *)
(* utils/mlkem_native_libc_full.ml for memset, assuming that the expansion   *)
(* of the matrix terminates (mld_matrix_terminates), and shown to be         *)
(* constant time and memory safe, with the events depending on rho, which is *)
(* public.                                                                   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvec_matrix_expand_eager_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvec_matrix_pointwise_montgomery_row_eager_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyeta_unpack_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_add_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_reduce_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_caddq_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_power2round_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyt1_pack_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyt0_pack_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/zeroize_2_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mld_compute_pack_t0_t144:
       +0x0: mov     x12, #0x4890
       +0x4: sub     sp, sp, x12
       +0x8: stp     x23, x24, [sp, #32]
       +0xc: mov     x23, x0
      +0x10: mov     x24, x3
      +0x14: adrp    x0, <page>
      +0x18: ldr     x0, [x0, #4088]
      +0x1c: stp     x19, x20, [sp]
      +0x20: mov     x3, #0x4400
      +0x24: stp     x21, x22, [sp, #16]
      +0x28: add     x20, sp, #0x8f
      +0x2c: and     x20, x20, #0xffffffffffffffe0
      +0x30: stp     x25, x26, [sp, #48]
      +0x34: mov     x22, x1
      +0x38: add     x19, x20, x3
      +0x3c: stp     x27, x28, [sp, #64]
      +0x40: mov     x1, x4
      +0x44: add     x21, x20, #0x4, lsl #12
      +0x48: str     x30, [sp, #80]
      +0x4c: mov     x25, #0x0
      +0x50: str     x2, [sp, #104]
      +0x54: mov     x28, #0x60
      +0x58: mov     x27, #0x140
      +0x5c: mov     x26, #0x1a0
      +0x60: ldr     x2, [x0]
      +0x64: str     x2, [sp, #18568]
      +0x68: mov     x2, #0x0
      +0x6c: mov     x0, x20
      +0x70: bl      <mldsa44_polyvec_matrix_expand_eager>
      +0x74: ldr     x2, [sp, #104]
      +0x78: mov     w3, w25
      +0x7c: mov     x1, x20
      +0x80: mov     x0, x19
      +0x84: bl      <mldsa44_polyvec_matrix_pointwise_montgomery_row_eager>
      +0x88: mov     x0, x19
      +0x8c: bl      <mldsa_poly_invntt_tomont>
      +0x90: madd    x1, x25, x28, x24
      +0x94: mov     x0, x21
      +0x98: bl      <mldsa44_polyeta_unpack>
      +0x9c: mov     x1, x21
      +0xa0: mov     x0, x19
      +0xa4: bl      <mldsa_poly_add>
      +0xa8: mov     x0, x19
      +0xac: bl      <mldsa_poly_reduce>
      +0xb0: mov     x0, x19
      +0xb4: bl      <mldsa_poly_caddq>
      +0xb8: mov     x2, x19
      +0xbc: mov     x1, x19
      +0xc0: mov     x0, x21
      +0xc4: bl      <mldsa_poly_power2round>
      +0xc8: madd    x0, x25, x27, x23
      +0xcc: mov     x1, x21
      +0xd0: bl      <mldsa_polyt1_pack>
      +0xd4: madd    x0, x25, x26, x22
      +0xd8: mov     x1, x19
      +0xdc: add     x25, x25, #0x1
      +0xe0: bl      <mldsa_polyt0_pack>
      +0xe4: cmp     x25, #0x4
      +0xe8: b.ne    <mld_compute_pack_t0_t144+0x74>
      +0xec: mov     x0, x21
      +0xf0: mov     x1, #0x400
      +0xf4: bl      <mld_zeroize_2>
      +0xf8: mov     x0, x19
      +0xfc: mov     x1, #0x400
     +0x100: bl      <mld_zeroize_2>
     +0x104: mov     x0, x20
     +0x108: mov     x1, #0x4000
     +0x10c: bl      <mld_zeroize_2>
     +0x110: adrp    x0, <page>
     +0x114: ldr     x0, [x0, #4088]
     +0x118: ldr     x2, [sp, #18568]
     +0x11c: ldr     x1, [x0]
     +0x120: subs    x2, x2, x1
     +0x124: mov     x1, #0x0
     +0x128: b.eq    <mld_compute_pack_t0_t144+0x130>
     +0x12c: bl      <stack_chk_fail>
     +0x130: ldp     x19, x20, [sp]
     +0x134: mov     w0, #0x0
     +0x138: ldp     x21, x22, [sp, #16]
     +0x13c: mov     x12, #0x4890
     +0x140: ldp     x23, x24, [sp, #32]
     +0x144: ldp     x25, x26, [sp, #48]
     +0x148: ldp     x27, x28, [sp, #64]
     +0x14c: ldr     x30, [sp, #80]
     +0x150: add     sp, sp, x12
     +0x154: ret
 ***)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mld_compute_pack_t0_t144"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The vector s1hat (s1 in    *)
(* the NTT domain) of 4 polynomials sh at s1hat, the 4 polynomials of s2     *)
(* packed in 96 bytes each, s2b at s2, and rho, the 32 bytes r at rho: the   *)
(* 4 polynomials of t1 packed in 320 bytes each are written at pkt1 and the  *)
(* 4 of t0 packed in 416 bytes each at t0, with t = mld_compute_t, if the    *)
(* expansion of the matrix terminates, and the result is 0. The stack is the *)
(* 18576 bytes of the function and the 5104 of the callees below them.       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pkt1 t0 s1hat s2 rho sh s2b r guard pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 4 4 r /\
          PAIRWISE nonoverlapping
           [(pkt1,1280); (t0,1664);
            (word_sub stackpointer (word 23680),23680)] /\
          ALLPAIRS nonoverlapping
           [(pkt1,1280); (t0,1664);
            (word_sub stackpointer (word 23680),23680)]
           [(s1hat,4096); (s2,384); (rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mld_compute_pack_t0_t144) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 1024
                         ==> read(memory :> bytes32
                                   (word_add s1hat (word(4 * j)))) s =
                             sh j) /\
                    (!j. j < 384
                         ==> read(memory :> bytes8(word_add s2 (word j))) s =
                             s2b j) /\
                    read (memory :> bytes(rho,32)) s = r)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    (!j. j < 1280
                         ==> read(memory :> bytes8(word_add pkt1 (word j))) s =
                             mld_polyvec_pack 320 mld_polyt1_pack
                              (mld_polyvec_map mld_poly_power2round_hi
                                (mld_compute_t 4 mld_polyeta_unpack_2 96 r
                                   sh s2b)) j) /\
                    (!j. j < 1664
                         ==> read(memory :> bytes8(word_add t0 (word j))) s =
                             mld_polyvec_pack 416 mld_polyt0_pack
                              (mld_polyvec_map mld_poly_power2round_lo
                                (mld_compute_t 4 mld_polyeta_unpack_2 96 r
                                   sh s2b)) j))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pkt1,1280); memory :> bytes(t0,1664);
                  memory :> bytes(word_sub stackpointer (word 23680),23680)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the address of memset and    *)
(* the stack, with all accesses within the arguments, the stack, the GOT     *)
(* entries and the stack guard, the region (ea,el) that memset may read and  *)
(* the constants of the callees, and the writes within the outputs and the   *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pkt1 t0 s1hat s2 rho sh s2b r guard pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 4 4 r /\
          PAIRWISE nonoverlapping
           [(pkt1,1280); (t0,1664);
            (word_sub stackpointer (word 23680),23680)] /\
          ALLPAIRS nonoverlapping
           [(pkt1,1280); (t0,1664);
            (word_sub stackpointer (word 23680),23680)]
           [(s1hat,4096); (s2,384); (rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mld_compute_pack_t0_t144) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 1024
                         ==> read(memory :> bytes32
                                   (word_add s1hat (word(4 * j)))) s =
                             sh j) /\
                    (!j. j < 384
                         ==> read(memory :> bytes8(word_add s2 (word j))) s =
                             s2b j) /\
                    read (memory :> bytes(rho,32)) s = r /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    (!j. j < 1280
                         ==> read(memory :> bytes8(word_add pkt1 (word j))) s =
                             mld_polyvec_pack 320 mld_polyt1_pack
                              (mld_polyvec_map mld_poly_power2round_hi
                                (mld_compute_t 4 mld_polyeta_unpack_2 96 r
                                   sh s2b)) j) /\
                    (!j. j < 1664
                         ==> read(memory :> bytes8(word_add t0 (word j))) s =
                             mld_polyvec_pack 416 mld_polyt0_pack
                              (mld_polyvec_map mld_poly_power2round_lo
                                (mld_compute_t 4 mld_polyeta_unpack_2 96 r
                                   sh s2b)) j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pkt1 t0 s1hat s2 rho r guard mf pc
                              (word_sub stackpointer (word 23680))
                              returnaddress /\
                       memaccess_inbounds e2
                        [s1hat,4096; s2,384; rho,32; pkt1,1280; t0,1664;
                         word_sub stackpointer (word 23680),23680;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024]
                        [pkt1,1280; t0,1664;
                         word_sub stackpointer (word 23680),23680]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pkt1,1280); memory :> bytes(t0,1664);
                  memory :> bytes(word_sub stackpointer (word 23680),23680)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pkt1 t0 s1hat s2 rho sh s2b r guard pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 4 4 r /\
          PAIRWISE nonoverlapping
           [(pkt1,1280); (t0,1664);
            (word_sub stackpointer (word 23680),23680)] /\
          ALLPAIRS nonoverlapping
           [(pkt1,1280); (t0,1664);
            (word_sub stackpointer (word 23680),23680)]
           [(s1hat,4096); (s2,384); (rho,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mld_compute_pack_t0_t144) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pkt1; t0; s1hat; s2; rho] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 1024
                         ==> read(memory :> bytes32
                                   (word_add s1hat (word(4 * j)))) s =
                             sh j) /\
                    (!j. j < 384
                         ==> read(memory :> bytes8(word_add s2 (word j))) s =
                             s2b j) /\
                    read (memory :> bytes(rho,32)) s = r /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pkt1 t0 s1hat s2 rho r guard mf pc
                              (word_sub stackpointer (word 23680))
                              returnaddress /\
                       memaccess_inbounds e2
                        [s1hat,4096; s2,384; rho,32; pkt1,1280; t0,1664;
                         word_sub stackpointer (word 23680),23680;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024]
                        [pkt1,1280; t0,1664;
                         word_sub stackpointer (word 23680),23680]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pkt1,1280); memory :> bytes(t0,1664);
                  memory :> bytes(word_sub stackpointer (word 23680),23680)])`;;

let MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_COMPUTE_PACK_T0_T1_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
