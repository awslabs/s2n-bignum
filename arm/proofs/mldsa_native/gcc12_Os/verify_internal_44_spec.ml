(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the statement. This is the code for          *)
(* mldsa44_verify_internal (mld_sign_verify_internal in sign.c) from mldsa-  *)
(* native's portable C implementation compiled by gcc 12 with -Os (see       *)
(* mldsa_native/README.md), which unpacks z and checks its norm, computes mu *)
(* with mld_H44 (or takes it from m if ext is nonzero), expands the matrix   *)
(* from rho, the challenge from c~, and for each row computes w1' =          *)
(* UseHint(h, A z - c t1 2^d), unpacking the hints of the row, and packs it, *)
(* and then compares c~ with the hash of mu and w1' (mld_H44 again) with     *)
(* mld_ct_memcmp_1. It zeroizes its buffers with mld_zeroize_2, a call of    *)
(* memset. It is verified in the whole image (see libmldsa.ml) against       *)
(* mld_verify_internal_ok of common/mldsa_native_sign.ml, using the theorems *)
(* for the callees and the contract memset_ret_full_contract of              *)
(* utils/mldsa_native_libc.ml for memset, assuming that the expansion of the *)
(* matrix and the sampling of the challenge terminate, and shown to be       *)
(* constant time and memory safe, with events depending on the signature,    *)
(* the message, the prefix and the public key, which are all public.         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sign.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_unpack_z_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_chknorm_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_ntt_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvec_matrix_expand_eager_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_challenge_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvec_matrix_pointwise_montgomery_row_eager_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/unpack_pk_t1_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_shiftl_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_pointwise_montgomery_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_sub_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_reduce_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_caddq_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/sig_unpack_hints_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_use_hint_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyw1_pack_88_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/H_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/zeroize_2_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/ct_memcmp_1_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa44_verify_internal:
       +0x0: mov     x12, #0x6030
       +0x4: sub     sp, sp, x12
       +0x8: mov     x11, #0x5c00
       +0xc: mov     x12, #0x5800
      +0x10: mov     x13, #0x5400
      +0x14: stp     x23, x24, [sp, #32]
      +0x18: mov     x24, x0
      +0x1c: stp     x19, x20, [sp]
      +0x20: add     x19, sp, #0xaf
      +0x24: and     x19, x19, #0xffffffffffffffe0
      +0x28: stp     x21, x22, [sp, #16]
      +0x2c: add     x23, x19, x11
      +0x30: add     x21, x19, x13
      +0x34: stp     x25, x26, [sp, #48]
      +0x38: add     x25, x19, #0x6, lsl #12
      +0x3c: add     x26, x19, #0x4, lsl #12
      +0x40: stp     x27, x28, [sp, #64]
      +0x44: mov     x28, x1
      +0x48: add     x27, x19, x12
      +0x4c: str     x30, [sp, #80]
      +0x50: add     x22, x19, #0x5, lsl #12
      +0x54: adrp    x0, <page>
      +0x58: ldr     x0, [x0, #4088]
      +0x5c: str     x5, [sp, #96]
      +0x60: ldp     q0, q1, [x24]
      +0x64: stp     x2, x3, [sp, #112]
      +0x68: str     x4, [sp, #128]
      +0x6c: str     w6, [sp, #140]
      +0x70: ldr     x1, [x0]
      +0x74: str     x1, [sp, #24616]
      +0x78: mov     x1, #0x0
      +0x7c: mov     x0, x26
      +0x80: add     x1, x24, #0x20
      +0x84: stp     q0, q1, [x25, #-160]
      +0x88: bl      <mldsa44_polyvecl_unpack_z>
      +0x8c: mov     w1, #0xffb2
      +0x90: mov     x0, x26
      +0x94: movk    w1, #0x1, lsl #16
      +0x98: bl      <mldsa44_polyvecl_chknorm>
      +0x9c: mov     x14, #0x5f60
      +0xa0: mov     w20, w0
      +0xa4: add     x0, x19, x14
      +0xa8: str     x0, [sp, #104]
      +0xac: cbnz    w20, <mldsa44_verify_internal+0x228>
      +0xb0: ldr     w6, [sp, #140]
      +0xb4: cbnz    w6, <mldsa44_verify_internal+0x2c0>
      +0xb8: ldr     x2, [sp, #96]
      +0xbc: mov     x0, x23
      +0xc0: mov     x7, #0x0
      +0xc4: mov     x6, #0x0
      +0xc8: mov     x5, #0x0
      +0xcc: mov     x4, #0x0
      +0xd0: mov     x3, #0x520
      +0xd4: mov     x1, #0x40
      +0xd8: bl      <mld_H44>
      +0xdc: ldp     x7, x4, [sp, #112]
      +0xe0: mov     x10, #0x5f00
      +0xe4: ldr     x5, [sp, #128]
      +0xe8: mov     x6, x28
      +0xec: mov     x2, x23
      +0xf0: mov     x3, #0x40
      +0xf4: add     x0, x19, x10
      +0xf8: mov     x1, x3
      +0xfc: bl      <mld_H44>
     +0x100: mov     x0, x23
     +0x104: mov     x1, #0x40
     +0x108: bl      <mld_zeroize_2>
     +0x10c: mov     x0, x26
     +0x110: bl      <mldsa44_polyvecl_ntt>
     +0x114: ldr     x1, [sp, #96]
     +0x118: mov     x0, x19
     +0x11c: mov     x28, x23
     +0x120: bl      <mldsa44_polyvec_matrix_expand_eager>
     +0x124: mov     x9, #0x5f60
     +0x128: add     x1, x19, x9
     +0x12c: mov     x0, x27
     +0x130: bl      <mldsa44_poly_challenge>
     +0x134: mov     x0, x27
     +0x138: bl      <mldsa_poly_ntt>
     +0x13c: mov     w3, w20
     +0x140: mov     x2, x26
     +0x144: mov     x1, x19
     +0x148: mov     x0, x21
     +0x14c: bl      <mldsa44_polyvec_matrix_pointwise_montgomery_row_eager>
     +0x150: ldr     x1, [sp, #96]
     +0x154: mov     w2, w20
     +0x158: mov     x0, x22
     +0x15c: bl      <mldsa44_unpack_pk_t1>
     +0x160: mov     x0, x22
     +0x164: bl      <mldsa_poly_shiftl>
     +0x168: mov     x0, x22
     +0x16c: bl      <mldsa_poly_ntt>
     +0x170: mov     x1, x27
     +0x174: mov     x0, x22
     +0x178: bl      <mldsa_poly_pointwise_montgomery>
     +0x17c: mov     x1, x22
     +0x180: mov     x0, x21
     +0x184: bl      <mldsa_poly_sub>
     +0x188: mov     x0, x21
     +0x18c: bl      <mldsa_poly_reduce>
     +0x190: mov     x0, x21
     +0x194: bl      <mldsa_poly_invntt_tomont>
     +0x198: mov     x0, x21
     +0x19c: bl      <mldsa_poly_caddq>
     +0x1a0: mov     w2, w20
     +0x1a4: mov     x1, x24
     +0x1a8: mov     x0, x22
     +0x1ac: bl      <mldsa44_sig_unpack_hints>
     +0x1b0: mov     w25, w0
     +0x1b4: cbnz    w0, <mldsa44_verify_internal+0x228>
     +0x1b8: mov     x1, x22
     +0x1bc: mov     x0, x21
     +0x1c0: bl      <mldsa44_poly_use_hint>
     +0x1c4: add     w20, w20, #0x1
     +0x1c8: mov     x0, x28
     +0x1cc: mov     x1, x21
     +0x1d0: bl      <mldsa_polyw1_pack_88>
     +0x1d4: add     x28, x28, #0xc0
     +0x1d8: cmp     w20, #0x4
     +0x1dc: b.ne    <mldsa44_verify_internal+0x13c>
     +0x1e0: mov     x8, #0x5f00
     +0x1e4: mov     x3, #0x5f40
     +0x1e8: add     x20, x19, x3
     +0x1ec: add     x2, x19, x8
     +0x1f0: mov     x0, x20
     +0x1f4: mov     x1, #0x20
     +0x1f8: mov     x4, x23
     +0x1fc: mov     x7, #0x0
     +0x200: mov     x6, #0x0
     +0x204: mov     x5, #0x300
     +0x208: mov     x3, #0x40
     +0x20c: bl      <mld_H44>
     +0x210: ldr     x0, [sp, #104]
     +0x214: mov     x1, x20
     +0x218: mov     x2, #0x20
     +0x21c: bl      <mld_ct_memcmp_1>
     +0x220: tst     w0, #0xff
     +0x224: b.eq    <mldsa44_verify_internal+0x22c>
     +0x228: mov     w25, #0xfffffffa
     +0x22c: mov     x0, x22
     +0x230: mov     x1, #0x400
     +0x234: bl      <mld_zeroize_2>
     +0x238: mov     x0, x21
     +0x23c: mov     x1, #0x400
     +0x240: bl      <mld_zeroize_2>
     +0x244: mov     x0, x19
     +0x248: mov     x1, #0x4000
     +0x24c: bl      <mld_zeroize_2>
     +0x250: mov     x0, x27
     +0x254: mov     x1, #0x400
     +0x258: bl      <mld_zeroize_2>
     +0x25c: mov     x0, x26
     +0x260: mov     x1, #0x1000
     +0x264: bl      <mld_zeroize_2>
     +0x268: mov     x1, #0x20
     +0x26c: mov     x0, #0x5f40
     +0x270: add     x0, x19, x0
     +0x274: bl      <mld_zeroize_2>
     +0x278: ldr     x0, [sp, #104]
     +0x27c: mov     x1, #0x20
     +0x280: bl      <mld_zeroize_2>
     +0x284: mov     x2, #0x5f00
     +0x288: mov     x1, #0x40
     +0x28c: add     x0, x19, x2
     +0x290: bl      <mld_zeroize_2>
     +0x294: mov     x0, x23
     +0x298: mov     x1, #0x300
     +0x29c: bl      <mld_zeroize_2>
     +0x2a0: adrp    x0, <page>
     +0x2a4: ldr     x0, [x0, #4088]
     +0x2a8: ldr     x2, [sp, #24616]
     +0x2ac: ldr     x1, [x0]
     +0x2b0: subs    x2, x2, x1
     +0x2b4: mov     x1, #0x0
     +0x2b8: b.eq    <mldsa44_verify_internal+0x2d8>
     +0x2bc: bl      <stack_chk_fail>
     +0x2c0: ldp     q0, q1, [x28]
     +0x2c4: sub     x0, x25, #0x100
     +0x2c8: stp     q0, q1, [x0]
     +0x2cc: ldp     q0, q1, [x28, #32]
     +0x2d0: stp     q0, q1, [x0, #32]
     +0x2d4: b       <mldsa44_verify_internal+0x10c>
     +0x2d8: ldp     x19, x20, [sp]
     +0x2dc: mov     w0, w25
     +0x2e0: ldp     x21, x22, [sp, #16]
     +0x2e4: mov     x12, #0x6030
     +0x2e8: ldp     x23, x24, [sp, #32]
     +0x2ec: ldp     x25, x26, [sp, #48]
     +0x2f0: ldp     x27, x28, [sp, #64]
     +0x2f4: ldr     x30, [sp, #80]
     +0x2f8: add     sp, sp, x12
     +0x2fc: ret
 ***)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa44_verify_internal"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The signature sigb at sig  *)
(* (2420 bytes), the message M of mlen bytes at m and the prefix PRE of      *)
(* prelen bytes at pre (or, if ext is nonzero as a 32-bit integer, mu in the *)
(* first 64 bytes at m), the public key pkb at pk (1312 bytes): the result   *)
(* is 0 if the signature is accepted, and -6 otherwise. The stack is the     *)
(* 24624 bytes of the function and those of the callees below them.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_ret_full_contract mf ea el ev
     ==> !sig m mlen pre prelen pk ext sigb pkb M PRE guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 4 4 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 39 32
           (num_of_bytelist(list_of_seq sigb 32)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 29728),29728))
              [(sig,2420); (m,mlen); (pre,prelen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_verify_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk;
                                 ext] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2420
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_verify_internal_ok 4 4 32
                           mld_polyz_unpack_17 576 130994
                           mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39
                           sigb pkb
                           (if word_zx ext = (word 0:int32)
                            then mld_verify_mu 1312 pkb prelen PRE mlen M
                            else M MOD 2 EXP 512)
                     then word 0 else word 4294967290))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 29728),29728)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the flag ext, the    *)
(* signature, the message, the prefix and the public key, all public, the    *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset may read and the constants of the callees, and the writes within   *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_ret_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen pk ext sigb pkb M PRE guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 4 4 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 39 32
           (num_of_bytelist(list_of_seq sigb 32)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 29728),29728))
              [(sig,2420); (m,mlen); (pre,prelen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_verify_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk;
                                 ext] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2420
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_verify_internal_ok 4 4 32
                           mld_polyz_unpack_17 576 130994
                           mld_poly_use_hint_88 mld_polyw1_pack_88 192 80 39
                           sigb pkb
                           (if word_zx ext = (word 0:int32)
                            then mld_verify_mu 1312 pkb prelen PRE mlen M
                            else M MOD 2 EXP 512)
                     then word 0 else word 4294967290) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen pk ext sigb pkb M PRE
                              guard mf pc (word_sub stackpointer (word 29728))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; pre,prelen; pk,1312;
                         word_sub stackpointer (word 29728),29728;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word 0,0;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024]
                        [word_sub stackpointer (word 29728),29728]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 29728),29728)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_ret_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen pk ext sigb pkb M PRE guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 4 4 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 39 32
           (num_of_bytelist(list_of_seq sigb 32)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 29728),29728))
              [(sig,2420); (m,mlen); (pre,prelen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_verify_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk;
                                 ext] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2420
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen pk ext sigb pkb M PRE
                              guard mf pc (word_sub stackpointer (word 29728))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; pre,prelen; pk,1312;
                         word_sub stackpointer (word 29728),29728;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word 0,0;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024]
                        [word_sub stackpointer (word 29728),29728]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 29728),29728)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
