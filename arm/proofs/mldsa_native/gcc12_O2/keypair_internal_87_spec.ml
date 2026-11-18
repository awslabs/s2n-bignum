(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation: the statement. This is the code for                       *)
(* mldsa87_keypair_internal (mld_sign_keypair_internal in sign.c, with       *)
(* mld_sample_pack_s1_s2 inlined) from mldsa-native's portable C             *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which expands the seed with mldsa_shake256 into rho, rho' and the key,    *)
(* samples s1 and s2 from rho' with four calls of                            *)
(* mldsa87_poly_uniform_eta_4x, for the last four polynomials of s2, the     *)
(* first four, the last three of s1 and one with the irrelevant nonce 255,   *)
(* and the first four of s1, packing each polynomial into the secret key     *)
(* with mldsa87_polyeta_pack, transforms s1 to the NTT domain with           *)
(* mldsa87_polyvecl_ntt, copies rho into the public key, computes t and      *)
(* packs t1 into the public key and t0 into the secret key with              *)
(* mld_compute_pack_t0_t187, hashes the public key into tr with              *)
(* mldsa_shake256, packs rho, the key and tr into the secret key with        *)
(* mldsa87_pack_sk_rho_key_tr, and zeroes its buffers. It is verified in the *)
(* whole image (see libmldsa.ml) against mld_keypair_pk_87 and               *)
(* mld_keypair_sk_87 of common/mldsa_native_sign.ml, using the theorems for  *)
(* the callees and the contract memset_full_contract of                      *)
(* utils/mlkem_native_libc_full.ml for memset, assuming that the expansion   *)
(* of the matrix and the sampling of each polynomial terminate, and shown to *)
(* be constant time and memory safe, with the events depending only on the   *)
(* addresses and the values that the C code declassifies (rho and            *)
(* mld_keypair_declass_87).                                                  *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_uniform_eta_4x_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyeta_pack_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_ntt_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/compute_pack_t0_t1_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/pack_sk_rho_key_tr_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa87_keypair_internal:
       +0x0: mov     x12, #0x1da0
       +0x4: sub     sp, sp, x12
       +0x8: mov     x3, #0x1cc0
       +0xc: mov     x4, #0x1c00
      +0x10: stp     x19, x20, [sp, #16]
      +0x14: add     x19, sp, #0xaf
      +0x18: and     x19, x19, #0xffffffffffffffe0
      +0x1c: stp     x21, x22, [sp, #32]
      +0x20: add     x21, x19, x4
      +0x24: mov     w4, #0x708
      +0x28: stp     x23, x24, [sp, #48]
      +0x2c: mov     x22, x0
      +0x30: mov     x20, x1
      +0x34: stp     x25, x26, [sp, #64]
      +0x38: add     x23, x19, #0xc00
      +0x3c: add     x24, x19, #0x800
      +0x40: stp     x27, x28, [sp, #80]
      +0x44: add     x27, x19, x3
      +0x48: add     x26, x21, #0x20
      +0x4c: str     x30, [sp, #96]
      +0x50: mov     x3, #0x22
      +0x54: mov     x1, #0x80
      +0x58: add     x25, x19, #0x400
      +0x5c: ldp     q0, q1, [x2]
      +0x60: adrp    x2, <page>
      +0x64: ldr     x2, [x2, #4088]
      +0x68: ldr     x0, [x2]
      +0x6c: str     x0, [sp, #7576]
      +0x70: mov     x0, #0x0
      +0x74: stp     q0, q1, [x27]
      +0x78: mov     x2, x27
      +0x7c: mov     x0, x21
      +0x80: strh    w4, [x19, #7392]
      +0x84: bl      <mldsa_shake256>
      +0x88: mov     x3, x23
      +0x8c: mov     x2, x24
      +0x90: mov     x4, x26
      +0x94: mov     w0, #0xe
      +0x98: strb    w0, [sp]
      +0x9c: mov     w7, #0xd
      +0xa0: mov     w6, #0xc
      +0xa4: mov     w5, #0xb
      +0xa8: mov     x1, x25
      +0xac: mov     x0, x19
      +0xb0: bl      <mldsa87_poly_uniform_eta_4x>
      +0xb4: mov     x1, x19
      +0xb8: add     x0, x20, #0x4a0
      +0xbc: bl      <mldsa87_polyeta_pack>
      +0xc0: mov     x1, x25
      +0xc4: add     x0, x20, #0x500
      +0xc8: bl      <mldsa87_polyeta_pack>
      +0xcc: mov     x1, x24
      +0xd0: add     x0, x20, #0x560
      +0xd4: bl      <mldsa87_polyeta_pack>
      +0xd8: mov     x1, x23
      +0xdc: add     x0, x20, #0x5c0
      +0xe0: bl      <mldsa87_polyeta_pack>
      +0xe4: mov     x3, x23
      +0xe8: mov     x2, x24
      +0xec: mov     x4, x26
      +0xf0: mov     w0, #0xa
      +0xf4: strb    w0, [sp]
      +0xf8: mov     w7, #0x9
      +0xfc: mov     w6, #0x8
     +0x100: mov     w5, #0x7
     +0x104: add     x0, x20, #0x320
     +0x108: mov     x1, x25
     +0x10c: mov     x28, x0
     +0x110: mov     x0, x19
     +0x114: bl      <mldsa87_poly_uniform_eta_4x>
     +0x118: str     x28, [sp, #120]
     +0x11c: mov     x0, x28
     +0x120: mov     x1, x19
     +0x124: bl      <mldsa87_polyeta_pack>
     +0x128: mov     x1, x25
     +0x12c: add     x0, x20, #0x380
     +0x130: bl      <mldsa87_polyeta_pack>
     +0x134: mov     x1, x24
     +0x138: add     x0, x20, #0x3e0
     +0x13c: bl      <mldsa87_polyeta_pack>
     +0x140: mov     x5, #0x1800
     +0x144: mov     x1, x23
     +0x148: add     x28, x19, x5
     +0x14c: add     x0, x20, #0x440
     +0x150: bl      <mldsa87_polyeta_pack>
     +0x154: mov     x6, #0x1400
     +0x158: add     x9, x19, x6
     +0x15c: mov     w0, #0xffffffff
     +0x160: strb    w0, [sp]
     +0x164: mov     x4, x26
     +0x168: mov     x2, x28
     +0x16c: mov     x3, x19
     +0x170: mov     w7, #0x6
     +0x174: mov     w6, #0x5
     +0x178: mov     w5, #0x4
     +0x17c: mov     x1, x9
     +0x180: add     x0, x19, #0x1, lsl #12
     +0x184: stp     x0, x9, [sp, #128]
     +0x188: bl      <mldsa87_poly_uniform_eta_4x>
     +0x18c: ldr     x0, [sp, #128]
     +0x190: mov     x1, x0
     +0x194: add     x0, x20, #0x200
     +0x198: bl      <mldsa87_polyeta_pack>
     +0x19c: ldr     x9, [sp, #136]
     +0x1a0: add     x0, x20, #0x260
     +0x1a4: mov     x1, x9
     +0x1a8: bl      <mldsa87_polyeta_pack>
     +0x1ac: mov     x1, x28
     +0x1b0: add     x0, x20, #0x2c0
     +0x1b4: bl      <mldsa87_polyeta_pack>
     +0x1b8: mov     x3, x23
     +0x1bc: mov     x2, x24
     +0x1c0: mov     x4, x26
     +0x1c4: mov     w0, #0x3
     +0x1c8: strb    w0, [sp]
     +0x1cc: mov     w7, #0x2
     +0x1d0: mov     w6, #0x1
     +0x1d4: mov     w5, #0x0
     +0x1d8: mov     x1, x25
     +0x1dc: mov     x0, x19
     +0x1e0: bl      <mldsa87_poly_uniform_eta_4x>
     +0x1e4: mov     x1, x19
     +0x1e8: add     x0, x20, #0x80
     +0x1ec: bl      <mldsa87_polyeta_pack>
     +0x1f0: mov     x1, x25
     +0x1f4: add     x0, x20, #0xe0
     +0x1f8: bl      <mldsa87_polyeta_pack>
     +0x1fc: mov     x1, x24
     +0x200: add     x0, x20, #0x140
     +0x204: bl      <mldsa87_polyeta_pack>
     +0x208: mov     x1, x23
     +0x20c: add     x0, x20, #0x1a0
     +0x210: bl      <mldsa87_polyeta_pack>
     +0x214: mov     x0, x19
     +0x218: bl      <mldsa87_polyvecl_ntt>
     +0x21c: ldp     q0, q1, [x21]
     +0x220: mov     x7, #0x1c80
     +0x224: ldr     x3, [sp, #120]
     +0x228: mov     x4, x21
     +0x22c: mov     x2, x19
     +0x230: add     x1, x20, #0x620
     +0x234: add     x0, x22, #0x20
     +0x238: add     x23, x19, x7
     +0x23c: stp     q0, q1, [x22]
     +0x240: bl      <mld_compute_pack_t0_t187>
     +0x244: mov     w24, w0
     +0x248: cbnz    w0, <+0x274>
     +0x24c: mov     x0, x23
     +0x250: mov     x2, x22
     +0x254: mov     x3, #0xa20
     +0x258: mov     x1, #0x40
     +0x25c: bl      <mldsa_shake256>
     +0x260: mov     x2, x23
     +0x264: add     x3, x21, #0x60
     +0x268: mov     x1, x21
     +0x26c: mov     x0, x20
     +0x270: bl      <mldsa87_pack_sk_rho_key_tr>
     +0x274: mov     x0, x19
     +0x278: mov     x2, #0x1c00
     +0x27c: mov     w1, #0x0
     +0x280: bl      <memset@plt>
     +0x284: movi    v0.4s, #0x0
     +0x288: stp     q0, q0, [x23]
     +0x28c: stp     q0, q0, [x23, #32]
     +0x290: stp     xzr, xzr, [x27]
     +0x294: stp     xzr, xzr, [x27, #16]
     +0x298: strh    wzr, [x27, #32]
     +0x29c: stp     q0, q0, [x21]
     +0x2a0: stp     q0, q0, [x21, #32]
     +0x2a4: stp     q0, q0, [x21, #64]
     +0x2a8: stp     q0, q0, [x21, #96]
     +0x2ac: cbnz    w24, <+0x2f4>
     +0x2b0: adrp    x0, <page>
     +0x2b4: ldr     x0, [x0, #4088]
     +0x2b8: ldr     x2, [sp, #7576]
     +0x2bc: ldr     x1, [x0]
     +0x2c0: subs    x2, x2, x1
     +0x2c4: mov     x1, #0x0
     +0x2c8: b.ne    <+0x318>
     +0x2cc: ldp     x19, x20, [sp, #16]
     +0x2d0: mov     w0, w24
     +0x2d4: ldp     x21, x22, [sp, #32]
     +0x2d8: mov     x12, #0x1da0
     +0x2dc: ldp     x23, x24, [sp, #48]
     +0x2e0: ldp     x25, x26, [sp, #64]
     +0x2e4: ldp     x27, x28, [sp, #80]
     +0x2e8: ldr     x30, [sp, #96]
     +0x2ec: add     sp, sp, x12
     +0x2f0: ret
     +0x2f4: mov     x0, x22
     +0x2f8: mov     x2, #0xa20
     +0x2fc: mov     w1, #0x0
     +0x300: bl      <memset@plt>
     +0x304: mov     x2, #0x1320
     +0x308: mov     x0, x20
     +0x30c: mov     w1, #0x0
     +0x310: bl      <memset@plt>
     +0x314: b       <+0x2b0>
     +0x318: bl      <__stack_chk_fail@plt>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_keypair_internal"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. From the seed SEED (32     *)
(* bytes at seed), the public key at pk (2592 bytes) becomes                 *)
(* mld_keypair_pk_87 SEED and the secret key at sk (4896 bytes)              *)
(* mld_keypair_sk_87 SEED, and the result is 0. The stack is the 7584 bytes  *)
(* of the function and those of the callees below them.                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pk sk seed SEED guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 (mld_keypair_rho 8 7 SEED) /\
          mld_keypair_terminates_87 SEED /\
          PAIRWISE nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 72144),72144)] /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 72144),72144)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_keypair_internal) /\
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
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             mld_keypair_pk_87 SEED j) /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             mld_keypair_sk_87 SEED j))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592); memory :> bytes(sk,4896);
                  memory :> bytes(word_sub stackpointer (word 72144),72144)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, whether each nibble read by  *)
(* the sampling of each polynomial is accepted (mld_keypair_declass_87), the *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset may read and the constants of the callees, and the writes within   *)
(* the keys and the stack.                                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk seed SEED guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 (mld_keypair_rho 8 7 SEED) /\
          mld_keypair_terminates_87 SEED /\
          PAIRWISE nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 72144),72144)] /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 72144),72144)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_keypair_internal) /\
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
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             mld_keypair_pk_87 SEED j) /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             mld_keypair_sk_87 SEED j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk seed (mld_keypair_rho 8 7 SEED)
                             (mld_keypair_declass_87 SEED) guard mf pc
                             (word_sub stackpointer (word 72144))
                             returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; pk,2592; sk,4896;
                         word_sub stackpointer (word 72144),72144;
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
                        [pk,2592; sk,4896;
                         word_sub stackpointer (word 72144),72144]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592); memory :> bytes(sk,4896);
                  memory :> bytes(word_sub stackpointer (word 72144),72144)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk seed SEED guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 (mld_keypair_rho 8 7 SEED) /\
          mld_keypair_terminates_87 SEED /\
          PAIRWISE nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 72144),72144)] /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 72144),72144)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_keypair_internal) /\
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
                       e2 = f_events pk sk seed (mld_keypair_rho 8 7 SEED)
                             (mld_keypair_declass_87 SEED) guard mf pc
                             (word_sub stackpointer (word 72144))
                             returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; pk,2592; sk,4896;
                         word_sub stackpointer (word 72144),72144;
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
                        [pk,2592; sk,4896;
                         word_sub stackpointer (word 72144),72144]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592); memory :> bytes(sk,4896);
                  memory :> bytes(word_sub stackpointer (word 72144),72144)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
