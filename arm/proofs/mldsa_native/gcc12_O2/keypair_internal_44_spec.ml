(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation: the statement. This is the code for                       *)
(* mldsa44_keypair_internal (mld_sign_keypair_internal in sign.c, with       *)
(* mld_sample_pack_s1_s2 inlined) from mldsa-native's portable C             *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which expands the seed with mldsa_shake256 into rho, rho' and the key,    *)
(* samples s1 and s2 from rho' with two calls of                             *)
(* mldsa44_poly_uniform_eta_4x, for s2 and then s1, packing each polynomial  *)
(* into the secret key with mldsa44_polyeta_pack, transforms s1 to the NTT   *)
(* domain with mldsa44_polyvecl_ntt, copies rho into the public key,         *)
(* computes t and packs t1 into the public key and t0 into the secret key    *)
(* with mld_compute_pack_t0_t144, hashes the public key into tr with         *)
(* mldsa_shake256, packs rho, the key and tr into the secret key with        *)
(* mldsa44_pack_sk_rho_key_tr, and zeroes its buffers. It is verified in the *)
(* whole image (see libmldsa.ml) against mld_keypair_pk_44 and               *)
(* mld_keypair_sk_44 of common/mldsa_native_sign.ml, using the theorems for  *)
(* the callees and the contract memset_full_contract of                      *)
(* utils/mlkem_native_libc_full.ml for memset, assuming that the expansion   *)
(* of the matrix and the sampling of each polynomial terminate, and shown to *)
(* be constant time and memory safe, with the events depending only on the   *)
(* addresses and the values that the C code declassifies (rho and            *)
(* mld_keypair_declass_44).                                                  *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_uniform_eta_4x_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyeta_pack_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_ntt_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/compute_pack_t0_t1_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/pack_sk_rho_key_tr_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa44_keypair_internal:
       +0x0: mov     x12, #0x1180
       +0x4: sub     sp, sp, x12
       +0x8: mov     x3, #0x10c0
       +0xc: mov     w4, #0x404
      +0x10: stp     x19, x20, [sp, #16]
      +0x14: add     x19, sp, #0x8f
      +0x18: and     x19, x19, #0xffffffffffffffe0
      +0x1c: stp     x21, x22, [sp, #32]
      +0x20: add     x22, x19, x3
      +0x24: add     x20, x19, #0x1, lsl #12
      +0x28: stp     x23, x24, [sp, #48]
      +0x2c: mov     x23, x0
      +0x30: mov     x21, x1
      +0x34: stp     x25, x26, [sp, #64]
      +0x38: add     x24, x19, #0xc00
      +0x3c: add     x25, x19, #0x800
      +0x40: stp     x27, x28, [sp, #80]
      +0x44: mov     x3, #0x22
      +0x48: add     x28, x20, #0x20
      +0x4c: str     x30, [sp, #96]
      +0x50: mov     x1, #0x80
      +0x54: add     x26, x19, #0x400
      +0x58: add     x27, x21, #0x200
      +0x5c: ldp     q0, q1, [x2]
      +0x60: adrp    x2, <page>
      +0x64: ldr     x2, [x2, #4088]
      +0x68: ldr     x0, [x2]
      +0x6c: str     x0, [sp, #4472]
      +0x70: mov     x0, #0x0
      +0x74: stp     q0, q1, [x22]
      +0x78: mov     x2, x22
      +0x7c: mov     x0, x20
      +0x80: strh    w4, [x19, #4320]
      +0x84: bl      <mldsa_shake256>
      +0x88: mov     x3, x24
      +0x8c: mov     x2, x25
      +0x90: mov     x4, x28
      +0x94: mov     w0, #0x7
      +0x98: strb    w0, [sp]
      +0x9c: mov     w7, #0x6
      +0xa0: mov     w6, #0x5
      +0xa4: mov     w5, #0x4
      +0xa8: mov     x1, x26
      +0xac: mov     x0, x19
      +0xb0: bl      <mldsa44_poly_uniform_eta_4x>
      +0xb4: mov     x1, x19
      +0xb8: mov     x0, x27
      +0xbc: bl      <mldsa44_polyeta_pack>
      +0xc0: mov     x1, x26
      +0xc4: add     x0, x21, #0x260
      +0xc8: bl      <mldsa44_polyeta_pack>
      +0xcc: mov     x1, x25
      +0xd0: add     x0, x21, #0x2c0
      +0xd4: bl      <mldsa44_polyeta_pack>
      +0xd8: mov     x1, x24
      +0xdc: add     x0, x21, #0x320
      +0xe0: bl      <mldsa44_polyeta_pack>
      +0xe4: mov     x3, x24
      +0xe8: mov     x2, x25
      +0xec: mov     x4, x28
      +0xf0: mov     w0, #0x3
      +0xf4: strb    w0, [sp]
      +0xf8: mov     w7, #0x2
      +0xfc: mov     w6, #0x1
     +0x100: mov     w5, #0x0
     +0x104: mov     x1, x26
     +0x108: mov     x0, x19
     +0x10c: bl      <mldsa44_poly_uniform_eta_4x>
     +0x110: mov     x1, x19
     +0x114: add     x0, x21, #0x80
     +0x118: bl      <mldsa44_polyeta_pack>
     +0x11c: mov     x1, x26
     +0x120: add     x0, x21, #0xe0
     +0x124: bl      <mldsa44_polyeta_pack>
     +0x128: mov     x1, x25
     +0x12c: add     x0, x21, #0x140
     +0x130: bl      <mldsa44_polyeta_pack>
     +0x134: mov     x1, x24
     +0x138: add     x0, x21, #0x1a0
     +0x13c: bl      <mldsa44_polyeta_pack>
     +0x140: mov     x0, x19
     +0x144: bl      <mldsa44_polyvecl_ntt>
     +0x148: ldp     q0, q1, [x20]
     +0x14c: mov     x4, x20
     +0x150: mov     x3, x27
     +0x154: mov     x2, x19
     +0x158: add     x1, x21, #0x380
     +0x15c: add     x0, x23, #0x20
     +0x160: stp     q0, q1, [x23]
     +0x164: bl      <mld_compute_pack_t0_t144>
     +0x168: mov     x4, #0x1080
     +0x16c: mov     w25, w0
     +0x170: add     x24, x19, x4
     +0x174: cbnz    w0, <+0x1a0>
     +0x178: mov     x0, x24
     +0x17c: mov     x2, x23
     +0x180: mov     x3, #0x520
     +0x184: mov     x1, #0x40
     +0x188: bl      <mldsa_shake256>
     +0x18c: mov     x2, x24
     +0x190: add     x3, x20, #0x60
     +0x194: mov     x1, x20
     +0x198: mov     x0, x21
     +0x19c: bl      <mldsa44_pack_sk_rho_key_tr>
     +0x1a0: mov     x0, x19
     +0x1a4: mov     x2, #0x1000
     +0x1a8: mov     w1, #0x0
     +0x1ac: bl      <memset@plt>
     +0x1b0: movi    v0.4s, #0x0
     +0x1b4: stp     q0, q0, [x24]
     +0x1b8: stp     q0, q0, [x24, #32]
     +0x1bc: stp     xzr, xzr, [x22]
     +0x1c0: stp     xzr, xzr, [x22, #16]
     +0x1c4: strh    wzr, [x22, #32]
     +0x1c8: stp     q0, q0, [x20]
     +0x1cc: stp     q0, q0, [x20, #32]
     +0x1d0: stp     q0, q0, [x20, #64]
     +0x1d4: stp     q0, q0, [x20, #96]
     +0x1d8: cbnz    w25, <+0x220>
     +0x1dc: adrp    x0, <page>
     +0x1e0: ldr     x0, [x0, #4088]
     +0x1e4: ldr     x2, [sp, #4472]
     +0x1e8: ldr     x1, [x0]
     +0x1ec: subs    x2, x2, x1
     +0x1f0: mov     x1, #0x0
     +0x1f4: b.ne    <+0x244>
     +0x1f8: ldp     x19, x20, [sp, #16]
     +0x1fc: mov     w0, w25
     +0x200: ldp     x21, x22, [sp, #32]
     +0x204: mov     x12, #0x1180
     +0x208: ldp     x23, x24, [sp, #48]
     +0x20c: ldp     x25, x26, [sp, #64]
     +0x210: ldp     x27, x28, [sp, #80]
     +0x214: ldr     x30, [sp, #96]
     +0x218: add     sp, sp, x12
     +0x21c: ret
     +0x220: mov     x0, x23
     +0x224: mov     x2, #0x520
     +0x228: mov     w1, #0x0
     +0x22c: bl      <memset@plt>
     +0x230: mov     x2, #0xa00
     +0x234: mov     x0, x21
     +0x238: mov     w1, #0x0
     +0x23c: bl      <memset@plt>
     +0x240: b       <+0x1dc>
     +0x244: bl      <__stack_chk_fail@plt>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_keypair_internal"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. From the seed SEED (32     *)
(* bytes at seed), the public key at pk (1312 bytes) becomes                 *)
(* mld_keypair_pk_44 SEED and the secret key at sk (2560 bytes)              *)
(* mld_keypair_sk_44 SEED, and the result is 0. The stack is the 4480 bytes  *)
(* of the function and those of the callees below them.                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pk sk seed SEED guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 4 4 (mld_keypair_rho 4 4 SEED) /\
          mld_keypair_terminates_44 SEED /\
          PAIRWISE nonoverlapping
           [(pk,1312); (sk,2560);
            (word_sub stackpointer (word 28096),28096)] /\
          ALLPAIRS nonoverlapping
           [(pk,1312); (sk,2560);
            (word_sub stackpointer (word 28096),28096)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa44_keypair_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,32)) s = SEED)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             mld_keypair_pk_44 SEED j) /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             mld_keypair_sk_44 SEED j))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1312); memory :> bytes(sk,2560);
                  memory :> bytes(word_sub stackpointer (word 28096),28096)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, whether each nibble read by  *)
(* the sampling of each polynomial is accepted (mld_keypair_declass_44), the *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset may read and the constants of the callees, and the writes within   *)
(* the keys and the stack.                                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk seed SEED guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 4 4 (mld_keypair_rho 4 4 SEED) /\
          mld_keypair_terminates_44 SEED /\
          PAIRWISE nonoverlapping
           [(pk,1312); (sk,2560);
            (word_sub stackpointer (word 28096),28096)] /\
          ALLPAIRS nonoverlapping
           [(pk,1312); (sk,2560);
            (word_sub stackpointer (word 28096),28096)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa44_keypair_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,32)) s = SEED /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s = word 0 /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             mld_keypair_pk_44 SEED j) /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             mld_keypair_sk_44 SEED j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk seed (mld_keypair_rho 4 4 SEED)
                             (mld_keypair_declass_44 SEED) guard mf pc
                             (word_sub stackpointer (word 28096))
                             returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; pk,1312; sk,2560;
                         word_sub stackpointer (word 28096),28096;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const2),16]
                        [pk,1312; sk,2560;
                         word_sub stackpointer (word 28096),28096]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1312); memory :> bytes(sk,2560);
                  memory :> bytes(word_sub stackpointer (word 28096),28096)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk seed SEED guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 4 4 (mld_keypair_rho 4 4 SEED) /\
          mld_keypair_terminates_44 SEED /\
          PAIRWISE nonoverlapping
           [(pk,1312); (sk,2560);
            (word_sub stackpointer (word 28096),28096)] /\
          ALLPAIRS nonoverlapping
           [(pk,1312); (sk,2560);
            (word_sub stackpointer (word 28096),28096)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa44_keypair_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,32)) s = SEED /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk seed (mld_keypair_rho 4 4 SEED)
                             (mld_keypair_declass_44 SEED) guard mf pc
                             (word_sub stackpointer (word 28096))
                             returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; pk,1312; sk,2560;
                         word_sub stackpointer (word 28096),28096;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const2),16]
                        [pk,1312; sk,2560;
                         word_sub stackpointer (word 28096),28096]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1312); memory :> bytes(sk,2560);
                  memory :> bytes(word_sub stackpointer (word 28096),28096)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
