(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Key generation: the statement. This is the code for                       *)
(* mldsa65_keypair_internal (mld_sign_keypair_internal in sign.c, with       *)
(* mld_sample_pack_s1_s2 inlined) from mldsa-native's portable C             *)
(* implementation compiled by gcc 12 with -Os (see mldsa_native/README.md),  *)
(* which expands the seed with mldsa_shake256 into rho, rho' and the key,    *)
(* samples s1 and s2 from rho' with three calls of                           *)
(* mldsa65_poly_uniform_eta_4x, for the last four polynomials of s2, then    *)
(* the last of s1, the first two of s2 and one with the irrelevant nonce     *)
(* 255, and then the first four of s1, packing each polynomial into the      *)
(* secret key with mldsa65_polyeta_pack, transforms s1 to the NTT domain     *)
(* with mldsa65_polyvecl_ntt, copies rho into the public key, computes t and *)
(* packs t1 into the public key and t0 into the secret key with              *)
(* mld_compute_pack_t0_t165, hashes the public key into tr with              *)
(* mldsa_shake256, packs rho, the key and tr into the secret key with        *)
(* mldsa65_pack_sk_rho_key_tr, and zeroes its buffers with mld_zeroize_4 (a  *)
(* call of memset). It is verified in the whole image (see libmldsa.ml)      *)
(* against mld_keypair_pk_65 and mld_keypair_sk_65 of                        *)
(* common/mldsa_native_sign.ml, using the theorems for the callees and the   *)
(* contract memset_full_contract of utils/mlkem_native_libc_full.ml for      *)
(* memset, assuming that the expansion of the matrix and the sampling of     *)
(* each polynomial terminate, and shown to be constant time and memory safe, *)
(* with the events depending only on the addresses and the values that the C *)
(* code declassifies (rho and mld_keypair_declass_65).                       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_uniform_eta_4x_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyeta_pack_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_ntt_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/compute_pack_t0_t1_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/pack_sk_rho_key_tr_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/zeroize_4_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa65_keypair_internal:
       +0x0: mov     x12, #0x1590
       +0x4: sub     sp, sp, x12
       +0x8: mov     x3, #0x1400
       +0xc: stp     x19, x20, [sp, #16]
      +0x10: add     x19, sp, #0x9f
      +0x14: and     x19, x19, #0xffffffffffffffe0
      +0x18: stp     x21, x22, [sp, #32]
      +0x1c: mov     x20, x1
      +0x20: mov     x22, x0
      +0x24: stp     x23, x24, [sp, #48]
      +0x28: mov     x1, #0x14c0
      +0x2c: add     x21, x19, x3
      +0x30: stp     x25, x26, [sp, #64]
      +0x34: add     x25, x19, x1
      +0x38: add     x24, x19, #0x800
      +0x3c: stp     x27, x28, [sp, #80]
      +0x40: add     x26, x19, #0xc00
      +0x44: add     x27, x21, #0x20
      +0x48: str     x30, [sp, #96]
      +0x4c: mov     x3, #0x22
      +0x50: adrp    x0, <page>
      +0x54: ldr     x0, [x0, #4088]
      +0x58: add     x23, x19, #0x400
      +0x5c: ldp     q0, q1, [x2]
      +0x60: ldr     x1, [x0]
      +0x64: str     x1, [sp, #5512]
      +0x68: mov     x1, #0x0
      +0x6c: mov     w0, #0x506
      +0x70: mov     x2, x25
      +0x74: mov     x1, #0x80
      +0x78: add     x28, x20, #0x300
      +0x7c: stp     q0, q1, [x25]
      +0x80: strh    w0, [x19, #5344]
      +0x84: mov     x0, x21
      +0x88: bl      <mldsa_shake256>
      +0x8c: mov     x2, x24
      +0x90: mov     x4, x27
      +0x94: mov     x3, x26
      +0x98: mov     w0, #0xa
      +0x9c: strb    w0, [sp]
      +0xa0: mov     w7, #0x9
      +0xa4: mov     w6, #0x8
      +0xa8: mov     w5, #0x7
      +0xac: mov     x1, x23
      +0xb0: mov     x0, x19
      +0xb4: bl      <mldsa65_poly_uniform_eta_4x>
      +0xb8: mov     x1, x19
      +0xbc: add     x0, x20, #0x400
      +0xc0: bl      <mldsa65_polyeta_pack>
      +0xc4: mov     x1, x23
      +0xc8: add     x0, x20, #0x480
      +0xcc: bl      <mldsa65_polyeta_pack>
      +0xd0: mov     x1, x24
      +0xd4: add     x0, x20, #0x500
      +0xd8: bl      <mldsa65_polyeta_pack>
      +0xdc: mov     x1, x26
      +0xe0: add     x0, x20, #0x580
      +0xe4: bl      <mldsa65_polyeta_pack>
      +0xe8: mov     w1, #0xffffffff
      +0xec: strb    w1, [sp]
      +0xf0: mov     x3, x24
      +0xf4: mov     x2, x23
      +0xf8: mov     x4, x27
      +0xfc: mov     w7, #0x6
     +0x100: mov     w6, #0x5
     +0x104: mov     w5, #0x4
     +0x108: add     x0, x19, #0x1, lsl #12
     +0x10c: mov     x1, x19
     +0x110: str     x0, [sp, #120]
     +0x114: bl      <mldsa65_poly_uniform_eta_4x>
     +0x118: ldr     x0, [sp, #120]
     +0x11c: mov     x1, x0
     +0x120: add     x0, x20, #0x280
     +0x124: bl      <mldsa65_polyeta_pack>
     +0x128: mov     x1, x19
     +0x12c: mov     x0, x28
     +0x130: bl      <mldsa65_polyeta_pack>
     +0x134: mov     x1, x23
     +0x138: add     x0, x20, #0x380
     +0x13c: bl      <mldsa65_polyeta_pack>
     +0x140: mov     x2, x24
     +0x144: mov     x4, x27
     +0x148: mov     x3, x26
     +0x14c: mov     w0, #0x3
     +0x150: strb    w0, [sp]
     +0x154: mov     w7, #0x2
     +0x158: mov     w6, #0x1
     +0x15c: mov     w5, #0x0
     +0x160: mov     x1, x23
     +0x164: mov     x0, x19
     +0x168: bl      <mldsa65_poly_uniform_eta_4x>
     +0x16c: mov     x1, x19
     +0x170: add     x0, x20, #0x80
     +0x174: bl      <mldsa65_polyeta_pack>
     +0x178: mov     x1, x23
     +0x17c: add     x0, x20, #0x100
     +0x180: bl      <mldsa65_polyeta_pack>
     +0x184: mov     x1, x24
     +0x188: add     x0, x20, #0x180
     +0x18c: bl      <mldsa65_polyeta_pack>
     +0x190: mov     x1, x26
     +0x194: add     x0, x20, #0x200
     +0x198: bl      <mldsa65_polyeta_pack>
     +0x19c: mov     x0, x19
     +0x1a0: bl      <mldsa65_polyvecl_ntt>
     +0x1a4: ldp     q0, q1, [x21]
     +0x1a8: mov     x4, x21
     +0x1ac: mov     x3, x28
     +0x1b0: mov     x2, x19
     +0x1b4: add     x1, x20, #0x600
     +0x1b8: add     x0, x22, #0x20
     +0x1bc: stp     q0, q1, [x22]
     +0x1c0: bl      <mld_compute_pack_t0_t165>
     +0x1c4: mov     x4, #0x1480
     +0x1c8: mov     w23, w0
     +0x1cc: add     x24, x19, x4
     +0x1d0: cbnz    w0, <mldsa65_keypair_internal+0x1fc>
     +0x1d4: mov     x2, x22
     +0x1d8: mov     x0, x24
     +0x1dc: mov     x3, #0x7a0
     +0x1e0: mov     x1, #0x40
     +0x1e4: bl      <mldsa_shake256>
     +0x1e8: add     x3, x21, #0x60
     +0x1ec: mov     x2, x24
     +0x1f0: mov     x1, x21
     +0x1f4: mov     x0, x20
     +0x1f8: bl      <mldsa65_pack_sk_rho_key_tr>
     +0x1fc: mov     x0, x19
     +0x200: mov     x1, #0x1400
     +0x204: bl      <mld_zeroize_4>
     +0x208: mov     x0, x24
     +0x20c: mov     x1, #0x40
     +0x210: bl      <mld_zeroize_4>
     +0x214: mov     x0, x25
     +0x218: mov     x1, #0x22
     +0x21c: bl      <mld_zeroize_4>
     +0x220: mov     x0, x21
     +0x224: mov     x1, #0x80
     +0x228: bl      <mld_zeroize_4>
     +0x22c: cbz     w23, <mldsa65_keypair_internal+0x248>
     +0x230: mov     x0, x22
     +0x234: mov     x1, #0x7a0
     +0x238: bl      <mld_zeroize_4>
     +0x23c: mov     x0, x20
     +0x240: mov     x1, #0xfc0
     +0x244: bl      <mld_zeroize_4>
     +0x248: adrp    x0, <page>
     +0x24c: ldr     x0, [x0, #4088]
     +0x250: ldr     x2, [sp, #5512]
     +0x254: ldr     x1, [x0]
     +0x258: subs    x2, x2, x1
     +0x25c: mov     x1, #0x0
     +0x260: b.eq    <mldsa65_keypair_internal+0x268>
     +0x264: bl      <stack_chk_fail>
     +0x268: ldp     x19, x20, [sp, #16]
     +0x26c: mov     w0, w23
     +0x270: ldp     x21, x22, [sp, #32]
     +0x274: mov     x12, #0x1590
     +0x278: ldp     x23, x24, [sp, #48]
     +0x27c: ldp     x25, x26, [sp, #64]
     +0x280: ldp     x27, x28, [sp, #80]
     +0x284: ldr     x30, [sp, #96]
     +0x288: add     sp, sp, x12
     +0x28c: ret
 ***)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa65_keypair_internal"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. From the seed SEED (32     *)
(* bytes at seed), the public key at pk (1952 bytes) becomes                 *)
(* mld_keypair_pk_65 SEED and the secret key at sk (4032 bytes)              *)
(* mld_keypair_sk_65 SEED, and the result is 0. The stack is the 5520 bytes  *)
(* of the function and those of the callees below them.                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pk sk seed SEED guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 (mld_keypair_rho 6 5 SEED) /\
          mld_keypair_terminates_65 SEED /\
          PAIRWISE nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 43504),43504)] /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 43504),43504)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa65_keypair_internal) /\
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
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             mld_keypair_pk_65 SEED j) /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             mld_keypair_sk_65 SEED j))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952); memory :> bytes(sk,4032);
                  memory :> bytes(word_sub stackpointer (word 43504),43504)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, whether each nibble read by  *)
(* the sampling of each polynomial is accepted (mld_keypair_declass_65), the *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset may read and the constants of the callees, and the writes within   *)
(* the keys and the stack.                                                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk seed SEED guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 (mld_keypair_rho 6 5 SEED) /\
          mld_keypair_terminates_65 SEED /\
          PAIRWISE nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 43504),43504)] /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 43504),43504)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa65_keypair_internal) /\
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
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             mld_keypair_pk_65 SEED j) /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             mld_keypair_sk_65 SEED j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk seed (mld_keypair_rho 6 5 SEED)
                             (mld_keypair_declass_65 SEED) guard mf pc
                             (word_sub stackpointer (word 43504))
                             returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; pk,1952; sk,4032;
                         word_sub stackpointer (word 43504),43504;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024]
                        [pk,1952; sk,4032;
                         word_sub stackpointer (word 43504),43504]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952); memory :> bytes(sk,4032);
                  memory :> bytes(word_sub stackpointer (word 43504),43504)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk seed SEED guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 (mld_keypair_rho 6 5 SEED) /\
          mld_keypair_terminates_65 SEED /\
          PAIRWISE nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 43504),43504)] /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (sk,4032);
            (word_sub stackpointer (word 43504),43504)]
           [(seed,32); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa65_keypair_internal) /\
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
                       e2 = f_events pk sk seed (mld_keypair_rho 6 5 SEED)
                             (mld_keypair_declass_65 SEED) guard mf pc
                             (word_sub stackpointer (word 43504))
                             returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; pk,1952; sk,4032;
                         word_sub stackpointer (word 43504),43504;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024]
                        [pk,1952; sk,4032;
                         word_sub stackpointer (word 43504),43504]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952); memory :> bytes(sk,4032);
                  memory :> bytes(word_sub stackpointer (word 43504),43504)])`;;

let MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_KEYPAIR_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
