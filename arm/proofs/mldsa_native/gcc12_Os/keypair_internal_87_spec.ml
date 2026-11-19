(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation: the statement. This is the code for                       *)
(* mldsa87_keypair_internal (mld_sign_keypair_internal in sign.c, with       *)
(* mld_sample_pack_s1_s2 inlined) from mldsa-native's portable C             *)
(* implementation compiled by gcc 12 with -Os (see mldsa_native/README.md),  *)
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
(* mldsa87_pack_sk_rho_key_tr, and zeroes its buffers with mld_zeroize_6 (a  *)
(* call of memset). It is verified in the whole image (see libmldsa.ml)      *)
(* against mld_keypair_pk_87 and mld_keypair_sk_87 of                        *)
(* common/mldsa_native_sign.ml, using the theorems for the callees and the   *)
(* contract memset_full_contract of utils/mlkem_native_libc_full.ml for      *)
(* memset, assuming that the expansion of the matrix and the sampling of     *)
(* each polynomial terminate, and shown to be constant time and memory safe, *)
(* with the events depending only on the addresses and the values that the C *)
(* code declassifies (rho and mld_keypair_declass_87).                       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_uniform_eta_4x_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyeta_pack_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_ntt_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/compute_pack_t0_t1_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/pack_sk_rho_key_tr_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/zeroize_6_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa87_keypair_internal:
       +0x0: mov     x12, #0x1da0
       +0x4: sub     sp, sp, x12
       +0x8: mov     x3, #0x1c00
       +0xc: stp     x19, x20, [sp, #16]
      +0x10: add     x19, sp, #0xaf
      +0x14: and     x19, x19, #0xffffffffffffffe0
      +0x18: stp     x21, x22, [sp, #32]
      +0x1c: mov     x20, x1
      +0x20: mov     x22, x0
      +0x24: stp     x23, x24, [sp, #48]
      +0x28: mov     x1, #0x1cc0
      +0x2c: add     x21, x19, x3
      +0x30: stp     x25, x26, [sp, #64]
      +0x34: add     x26, x19, x1
      +0x38: add     x23, x19, #0xc00
      +0x3c: stp     x27, x28, [sp, #80]
      +0x40: add     x24, x19, #0x800
      +0x44: add     x27, x21, #0x20
      +0x48: str     x30, [sp, #96]
      +0x4c: mov     x3, #0x22
      +0x50: adrp    x0, <page>
      +0x54: ldr     x0, [x0, #4088]
      +0x58: add     x25, x19, #0x400
      +0x5c: ldp     q0, q1, [x2]
      +0x60: ldr     x1, [x0]
      +0x64: str     x1, [sp, #7576]
      +0x68: mov     x1, #0x0
      +0x6c: mov     w0, #0x708
      +0x70: mov     x2, x26
      +0x74: mov     x1, #0x80
      +0x78: add     x28, x20, #0x320
      +0x7c: stp     q0, q1, [x26]
      +0x80: strh    w0, [x19, #7392]
      +0x84: mov     x0, x21
      +0x88: bl      <mldsa_shake256>
      +0x8c: mov     x3, x23
      +0x90: mov     x2, x24
      +0x94: mov     x4, x27
      +0x98: mov     w0, #0xe
      +0x9c: strb    w0, [sp]
      +0xa0: mov     w7, #0xd
      +0xa4: mov     w6, #0xc
      +0xa8: mov     w5, #0xb
      +0xac: mov     x1, x25
      +0xb0: mov     x0, x19
      +0xb4: bl      <mldsa87_poly_uniform_eta_4x>
      +0xb8: mov     x1, x19
      +0xbc: add     x0, x20, #0x4a0
      +0xc0: bl      <mldsa87_polyeta_pack>
      +0xc4: mov     x1, x25
      +0xc8: add     x0, x20, #0x500
      +0xcc: bl      <mldsa87_polyeta_pack>
      +0xd0: mov     x1, x24
      +0xd4: add     x0, x20, #0x560
      +0xd8: bl      <mldsa87_polyeta_pack>
      +0xdc: mov     x1, x23
      +0xe0: add     x0, x20, #0x5c0
      +0xe4: bl      <mldsa87_polyeta_pack>
      +0xe8: mov     x3, x23
      +0xec: mov     x2, x24
      +0xf0: mov     x4, x27
      +0xf4: mov     w0, #0xa
      +0xf8: strb    w0, [sp]
      +0xfc: mov     w7, #0x9
     +0x100: mov     w6, #0x8
     +0x104: mov     w5, #0x7
     +0x108: mov     x1, x25
     +0x10c: mov     x0, x19
     +0x110: bl      <mldsa87_poly_uniform_eta_4x>
     +0x114: mov     x1, x19
     +0x118: mov     x0, x28
     +0x11c: bl      <mldsa87_polyeta_pack>
     +0x120: mov     x1, x25
     +0x124: add     x0, x20, #0x380
     +0x128: bl      <mldsa87_polyeta_pack>
     +0x12c: mov     x1, x24
     +0x130: add     x0, x20, #0x3e0
     +0x134: bl      <mldsa87_polyeta_pack>
     +0x138: mov     x1, x23
     +0x13c: add     x0, x20, #0x440
     +0x140: bl      <mldsa87_polyeta_pack>
     +0x144: mov     x5, #0x1400
     +0x148: add     x8, x19, x5
     +0x14c: mov     w1, #0xffffffff
     +0x150: strb    w1, [sp]
     +0x154: mov     x4, #0x1800
     +0x158: mov     x3, x19
     +0x15c: add     x2, x19, x4
     +0x160: mov     w7, #0x6
     +0x164: mov     x4, x27
     +0x168: mov     w6, #0x5
     +0x16c: mov     w5, #0x4
     +0x170: mov     x1, x8
     +0x174: add     x0, x19, #0x1, lsl #12
     +0x178: stp     x0, x8, [sp, #120]
     +0x17c: str     x2, [sp, #136]
     +0x180: bl      <mldsa87_poly_uniform_eta_4x>
     +0x184: ldr     x0, [sp, #120]
     +0x188: mov     x1, x0
     +0x18c: add     x0, x20, #0x200
     +0x190: bl      <mldsa87_polyeta_pack>
     +0x194: ldr     x8, [sp, #128]
     +0x198: add     x0, x20, #0x260
     +0x19c: mov     x1, x8
     +0x1a0: bl      <mldsa87_polyeta_pack>
     +0x1a4: ldr     x2, [sp, #136]
     +0x1a8: add     x0, x20, #0x2c0
     +0x1ac: mov     x1, x2
     +0x1b0: bl      <mldsa87_polyeta_pack>
     +0x1b4: mov     x3, x23
     +0x1b8: mov     x2, x24
     +0x1bc: mov     x4, x27
     +0x1c0: mov     w0, #0x3
     +0x1c4: strb    w0, [sp]
     +0x1c8: mov     w6, #0x1
     +0x1cc: mov     w7, #0x2
     +0x1d0: mov     w5, #0x0
     +0x1d4: mov     x1, x25
     +0x1d8: mov     x0, x19
     +0x1dc: bl      <mldsa87_poly_uniform_eta_4x>
     +0x1e0: mov     x1, x19
     +0x1e4: add     x0, x20, #0x80
     +0x1e8: bl      <mldsa87_polyeta_pack>
     +0x1ec: mov     x1, x25
     +0x1f0: add     x0, x20, #0xe0
     +0x1f4: bl      <mldsa87_polyeta_pack>
     +0x1f8: mov     x1, x24
     +0x1fc: add     x0, x20, #0x140
     +0x200: bl      <mldsa87_polyeta_pack>
     +0x204: mov     x1, x23
     +0x208: add     x0, x20, #0x1a0
     +0x20c: bl      <mldsa87_polyeta_pack>
     +0x210: mov     x0, x19
     +0x214: bl      <mldsa87_polyvecl_ntt>
     +0x218: ldp     q0, q1, [x21]
     +0x21c: mov     x4, x21
     +0x220: mov     x3, x28
     +0x224: mov     x2, x19
     +0x228: add     x1, x20, #0x620
     +0x22c: add     x0, x22, #0x20
     +0x230: stp     q0, q1, [x22]
     +0x234: bl      <mld_compute_pack_t0_t187>
     +0x238: mov     x6, #0x1c80
     +0x23c: mov     w23, w0
     +0x240: add     x24, x19, x6
     +0x244: cbnz    w0, <mldsa87_keypair_internal+0x270>
     +0x248: mov     x2, x22
     +0x24c: mov     x0, x24
     +0x250: mov     x3, #0xa20
     +0x254: mov     x1, #0x40
     +0x258: bl      <mldsa_shake256>
     +0x25c: add     x3, x21, #0x60
     +0x260: mov     x2, x24
     +0x264: mov     x1, x21
     +0x268: mov     x0, x20
     +0x26c: bl      <mldsa87_pack_sk_rho_key_tr>
     +0x270: mov     x0, x19
     +0x274: mov     x1, #0x1c00
     +0x278: bl      <mld_zeroize_6>
     +0x27c: mov     x0, x24
     +0x280: mov     x1, #0x40
     +0x284: bl      <mld_zeroize_6>
     +0x288: mov     x0, x26
     +0x28c: mov     x1, #0x22
     +0x290: bl      <mld_zeroize_6>
     +0x294: mov     x0, x21
     +0x298: mov     x1, #0x80
     +0x29c: bl      <mld_zeroize_6>
     +0x2a0: cbz     w23, <mldsa87_keypair_internal+0x2bc>
     +0x2a4: mov     x0, x22
     +0x2a8: mov     x1, #0xa20
     +0x2ac: bl      <mld_zeroize_6>
     +0x2b0: mov     x0, x20
     +0x2b4: mov     x1, #0x1320
     +0x2b8: bl      <mld_zeroize_6>
     +0x2bc: adrp    x0, <page>
     +0x2c0: ldr     x0, [x0, #4088]
     +0x2c4: ldr     x2, [sp, #7576]
     +0x2c8: ldr     x1, [x0]
     +0x2cc: subs    x2, x2, x1
     +0x2d0: mov     x1, #0x0
     +0x2d4: b.eq    <mldsa87_keypair_internal+0x2dc>
     +0x2d8: bl      <stack_chk_fail>
     +0x2dc: ldp     x19, x20, [sp, #16]
     +0x2e0: mov     w0, w23
     +0x2e4: ldp     x21, x22, [sp, #32]
     +0x2e8: mov     x12, #0x1da0
     +0x2ec: ldp     x23, x24, [sp, #48]
     +0x2f0: ldp     x25, x26, [sp, #64]
     +0x2f4: ldp     x27, x28, [sp, #80]
     +0x2f8: ldr     x30, [sp, #96]
     +0x2fc: add     sp, sp, x12
     +0x300: ret
 ***)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa87_keypair_internal"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. From the seed SEED (32     *)
(* bytes at seed), the public key at pk (2592 bytes) becomes                 *)
(* mld_keypair_pk_87 SEED and the secret key at sk (4896 bytes)              *)
(* mld_keypair_sk_87 SEED, and the result is 0. The stack is the 7584 bytes  *)
(* of the function and those of the callees below them.                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pk sk seed SEED guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 (mld_keypair_rho 8 7 SEED) /\
          mld_keypair_terminates_87 SEED /\
          PAIRWISE nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 72208),72208)] /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 72208),72208)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                  memory :> bytes(word_sub stackpointer (word 72208),72208)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, whether each nibble read by  *)
(* the sampling of each polynomial is accepted (mld_keypair_declass_87), the *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset may read and the constants of the callees, and the writes within   *)
(* the keys and the stack.                                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
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
            (word_sub stackpointer (word 72208),72208)] /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 72208),72208)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                             (word_sub stackpointer (word 72208))
                             returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; pk,2592; sk,4896;
                         word_sub stackpointer (word 72208),72208;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024]
                        [pk,2592; sk,4896;
                         word_sub stackpointer (word 72208),72208]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592); memory :> bytes(sk,4896);
                  memory :> bytes(word_sub stackpointer (word 72208),72208)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
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
            (word_sub stackpointer (word 72208),72208)] /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (sk,4896);
            (word_sub stackpointer (word 72208),72208)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                             (word_sub stackpointer (word 72208))
                             returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; pk,2592; sk,4896;
                         word_sub stackpointer (word 72208),72208;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024]
                        [pk,2592; sk,4896;
                         word_sub stackpointer (word 72208),72208]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592); memory :> bytes(sk,4896);
                  memory :> bytes(word_sub stackpointer (word 72208),72208)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
