(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the statement. This is the code for          *)
(* mldsa65_verify_internal (mld_sign_verify_internal in sign.c) from mldsa-  *)
(* native's portable C implementation compiled by gcc 12 with -Os (see       *)
(* mldsa_native/README.md), which unpacks z and checks its norm, computes mu *)
(* with mld_H65 (or takes it from m if ext is nonzero), expands the matrix   *)
(* from rho, the challenge from c~, and for each row computes w1' =          *)
(* UseHint(h, A z - c t1 2^d), unpacking the hints of the row, and packs it, *)
(* and then compares c~ with the hash of mu and w1' (mld_H65 again) with     *)
(* mld_ct_memcmp_2. It zeroizes its buffers with mld_zeroize_4, a call of    *)
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
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_unpack_z_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_chknorm_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_ntt_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvec_matrix_expand_eager_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_challenge_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvec_matrix_pointwise_montgomery_row_eager_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/unpack_pk_t1_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_shiftl_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_pointwise_montgomery_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_sub_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_reduce_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_caddq_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/sig_unpack_hints_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_use_hint_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyw1_pack_32_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/H_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/zeroize_4_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/ct_memcmp_2_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa65_verify_internal:
       +0x0: mov     x12, #0x9c60
       +0x4: sub     sp, sp, x12
       +0x8: mov     x11, #0x8030
       +0xc: mov     x12, #0x9c00
      +0x10: mov     x13, #0x7800
      +0x14: mov     x14, #0x9800
      +0x18: stp     x23, x24, [sp, #32]
      +0x1c: mov     x23, x0
      +0x20: mov     x15, #0x9400
      +0x24: adrp    x0, <page>
      +0x28: ldr     x0, [x0, #4088]
      +0x2c: stp     x19, x20, [sp]
      +0x30: add     x19, sp, #0xaf
      +0x34: stp     x21, x22, [sp, #16]
      +0x38: and     x19, x19, #0xffffffffffffffe0
      +0x3c: mov     x16, #0x8c00
      +0x40: stp     x25, x26, [sp, #48]
      +0x44: add     x25, x19, x12
      +0x48: add     x26, x19, x13
      +0x4c: stp     x27, x28, [sp, #64]
      +0x50: mov     x28, x1
      +0x54: add     x1, sp, x11
      +0x58: str     x30, [sp, #80]
      +0x5c: add     x24, x19, x14
      +0x60: str     x5, [sp, #96]
      +0x64: add     x27, x19, x15
      +0x68: stp     x2, x3, [sp, #112]
      +0x6c: add     x22, x19, x16
      +0x70: add     x21, x19, #0x9, lsl #12
      +0x74: str     x4, [sp, #128]
      +0x78: str     w6, [sp, #140]
      +0x7c: ldp     q0, q1, [x23]
      +0x80: ldr     x2, [x0]
      +0x84: str     x2, [x1, #7208]
      +0x88: mov     x2, #0x0
      +0x8c: sub     x0, x25, #0x80
      +0x90: add     x1, x23, #0x30
      +0x94: stp     q0, q1, [x0]
      +0x98: ldr     q0, [x23, #32]
      +0x9c: str     q0, [x0, #32]
      +0xa0: mov     x0, x26
      +0xa4: bl      <mldsa65_polyvecl_unpack_z>
      +0xa8: mov     w1, #0xff3c
      +0xac: mov     x0, x26
      +0xb0: movk    w1, #0x7, lsl #16
      +0xb4: bl      <mldsa65_polyvecl_chknorm>
      +0xb8: mov     x17, #0x9b80
      +0xbc: mov     w20, w0
      +0xc0: add     x0, x19, x17
      +0xc4: str     x0, [sp, #104]
      +0xc8: cbnz    w20, <mldsa65_verify_internal+0x244>
      +0xcc: ldr     w6, [sp, #140]
      +0xd0: cbnz    w6, <mldsa65_verify_internal+0x2e4>
      +0xd4: ldr     x2, [sp, #96]
      +0xd8: mov     x0, x24
      +0xdc: mov     x7, #0x0
      +0xe0: mov     x6, #0x0
      +0xe4: mov     x5, #0x0
      +0xe8: mov     x4, #0x0
      +0xec: mov     x3, #0x7a0
      +0xf0: mov     x1, #0x40
      +0xf4: bl      <mld_H65>
      +0xf8: ldp     x7, x4, [sp, #112]
      +0xfc: mov     x10, #0x9b00
     +0x100: ldr     x5, [sp, #128]
     +0x104: mov     x6, x28
     +0x108: mov     x2, x24
     +0x10c: mov     x3, #0x40
     +0x110: add     x0, x19, x10
     +0x114: mov     x1, x3
     +0x118: bl      <mld_H65>
     +0x11c: mov     x0, x24
     +0x120: mov     x1, #0x40
     +0x124: bl      <mld_zeroize_4>
     +0x128: mov     x0, x26
     +0x12c: bl      <mldsa65_polyvecl_ntt>
     +0x130: ldr     x1, [sp, #96]
     +0x134: mov     x0, x19
     +0x138: mov     x28, x24
     +0x13c: bl      <mldsa65_polyvec_matrix_expand_eager>
     +0x140: mov     x9, #0x9b80
     +0x144: add     x1, x19, x9
     +0x148: mov     x0, x27
     +0x14c: bl      <mldsa65_poly_challenge>
     +0x150: mov     x0, x27
     +0x154: bl      <mldsa_poly_ntt>
     +0x158: mov     w3, w20
     +0x15c: mov     x2, x26
     +0x160: mov     x1, x19
     +0x164: mov     x0, x21
     +0x168: bl      <mldsa65_polyvec_matrix_pointwise_montgomery_row_eager>
     +0x16c: ldr     x1, [sp, #96]
     +0x170: mov     w2, w20
     +0x174: mov     x0, x22
     +0x178: bl      <mldsa65_unpack_pk_t1>
     +0x17c: mov     x0, x22
     +0x180: bl      <mldsa_poly_shiftl>
     +0x184: mov     x0, x22
     +0x188: bl      <mldsa_poly_ntt>
     +0x18c: mov     x1, x27
     +0x190: mov     x0, x22
     +0x194: bl      <mldsa_poly_pointwise_montgomery>
     +0x198: mov     x1, x22
     +0x19c: mov     x0, x21
     +0x1a0: bl      <mldsa_poly_sub>
     +0x1a4: mov     x0, x21
     +0x1a8: bl      <mldsa_poly_reduce>
     +0x1ac: mov     x0, x21
     +0x1b0: bl      <mldsa_poly_invntt_tomont>
     +0x1b4: mov     x0, x21
     +0x1b8: bl      <mldsa_poly_caddq>
     +0x1bc: mov     w2, w20
     +0x1c0: mov     x1, x23
     +0x1c4: mov     x0, x22
     +0x1c8: bl      <mldsa65_sig_unpack_hints>
     +0x1cc: mov     w25, w0
     +0x1d0: cbnz    w0, <mldsa65_verify_internal+0x244>
     +0x1d4: mov     x1, x22
     +0x1d8: mov     x0, x21
     +0x1dc: bl      <mldsa65_poly_use_hint>
     +0x1e0: add     w20, w20, #0x1
     +0x1e4: mov     x0, x28
     +0x1e8: mov     x1, x21
     +0x1ec: bl      <mldsa_polyw1_pack_32>
     +0x1f0: add     x28, x28, #0x80
     +0x1f4: cmp     w20, #0x6
     +0x1f8: b.ne    <mldsa65_verify_internal+0x158>
     +0x1fc: mov     x8, #0x9b00
     +0x200: mov     x4, #0x9b40
     +0x204: add     x20, x19, x4
     +0x208: add     x2, x19, x8
     +0x20c: mov     x0, x20
     +0x210: mov     x1, #0x30
     +0x214: mov     x4, x24
     +0x218: mov     x7, #0x0
     +0x21c: mov     x6, #0x0
     +0x220: mov     x5, #0x300
     +0x224: mov     x3, #0x40
     +0x228: bl      <mld_H65>
     +0x22c: ldr     x0, [sp, #104]
     +0x230: mov     x1, x20
     +0x234: mov     x2, #0x30
     +0x238: bl      <mld_ct_memcmp_2>
     +0x23c: tst     w0, #0xff
     +0x240: b.eq    <mldsa65_verify_internal+0x248>
     +0x244: mov     w25, #0xfffffffa
     +0x248: mov     x0, x22
     +0x24c: mov     x1, #0x400
     +0x250: bl      <mld_zeroize_4>
     +0x254: mov     x0, x21
     +0x258: mov     x1, #0x400
     +0x25c: bl      <mld_zeroize_4>
     +0x260: mov     x0, x19
     +0x264: mov     x1, #0x7800
     +0x268: bl      <mld_zeroize_4>
     +0x26c: mov     x0, x27
     +0x270: mov     x1, #0x400
     +0x274: bl      <mld_zeroize_4>
     +0x278: mov     x0, x26
     +0x27c: mov     x1, #0x1400
     +0x280: bl      <mld_zeroize_4>
     +0x284: mov     x1, #0x30
     +0x288: mov     x0, #0x9b40
     +0x28c: add     x0, x19, x0
     +0x290: bl      <mld_zeroize_4>
     +0x294: ldr     x0, [sp, #104]
     +0x298: mov     x1, #0x30
     +0x29c: bl      <mld_zeroize_4>
     +0x2a0: mov     x2, #0x9b00
     +0x2a4: mov     x1, #0x40
     +0x2a8: add     x0, x19, x2
     +0x2ac: bl      <mld_zeroize_4>
     +0x2b0: mov     x0, x24
     +0x2b4: mov     x1, #0x300
     +0x2b8: bl      <mld_zeroize_4>
     +0x2bc: adrp    x0, <page>
     +0x2c0: ldr     x0, [x0, #4088]
     +0x2c4: mov     x3, #0x8030
     +0x2c8: add     x2, sp, x3
     +0x2cc: ldr     x3, [x2, #7208]
     +0x2d0: ldr     x1, [x0]
     +0x2d4: subs    x3, x3, x1
     +0x2d8: mov     x1, #0x0
     +0x2dc: b.eq    <mldsa65_verify_internal+0x2fc>
     +0x2e0: bl      <stack_chk_fail>
     +0x2e4: ldp     q0, q1, [x28]
     +0x2e8: sub     x0, x25, #0x100
     +0x2ec: stp     q0, q1, [x0]
     +0x2f0: ldp     q0, q1, [x28, #32]
     +0x2f4: stp     q0, q1, [x0, #32]
     +0x2f8: b       <mldsa65_verify_internal+0x128>
     +0x2fc: ldp     x19, x20, [sp]
     +0x300: mov     w0, w25
     +0x304: ldp     x21, x22, [sp, #16]
     +0x308: mov     x12, #0x9c60
     +0x30c: ldp     x23, x24, [sp, #32]
     +0x310: ldp     x25, x26, [sp, #48]
     +0x314: ldp     x27, x28, [sp, #64]
     +0x318: ldr     x30, [sp, #80]
     +0x31c: add     sp, sp, x12
     +0x320: ret
 ***)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa65_verify_internal"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The signature sigb at sig  *)
(* (3309 bytes), the message M of mlen bytes at m and the prefix PRE of      *)
(* prelen bytes at pre (or, if ext is nonzero as a 32-bit integer, mu in the *)
(* first 64 bytes at m), the public key pkb at pk (1952 bytes): the result   *)
(* is 0 if the signature is accepted, and -6 otherwise. The stack is the     *)
(* 40032 bytes of the function and those of the callees below them.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_ret_full_contract mf ea el ev
     ==> !sig m mlen pre prelen pk ext sigb pkb M PRE guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 6 5 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 49 48
           (num_of_bytelist(list_of_seq sigb 48)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 45120),45120))
              [(sig,3309); (m,mlen); (pre,prelen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa65_verify_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk;
                                 ext] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 3309
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_verify_internal_ok 6 5 48
                           mld_polyz_unpack_19 640 524092
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49
                           sigb pkb
                           (if word_zx ext = (word 0:int32)
                            then mld_verify_mu 1952 pkb prelen PRE mlen M
                            else M MOD 2 EXP 512)
                     then word 0 else word 4294967290))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 45120),45120)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the flag ext, the    *)
(* signature, the message, the prefix and the public key, all public, the    *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset may read and the constants of the callees, and the writes within   *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_ret_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen pk ext sigb pkb M PRE guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 6 5 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 49 48
           (num_of_bytelist(list_of_seq sigb 48)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 45120),45120))
              [(sig,3309); (m,mlen); (pre,prelen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa65_verify_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk;
                                 ext] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 3309
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_verify_internal_ok 6 5 48
                           mld_polyz_unpack_19 640 524092
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 55 49
                           sigb pkb
                           (if word_zx ext = (word 0:int32)
                            then mld_verify_mu 1952 pkb prelen PRE mlen M
                            else M MOD 2 EXP 512)
                     then word 0 else word 4294967290) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen pk ext sigb pkb M PRE
                              guard mf pc (word_sub stackpointer (word 45120))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; pre,prelen; pk,1952;
                         word_sub stackpointer (word 45120),45120;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word 0,0;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024]
                        [word_sub stackpointer (word 45120),45120]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 45120),45120)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_ret_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen pk ext sigb pkb M PRE guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 6 5 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 49 48
           (num_of_bytelist(list_of_seq sigb 48)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 45120),45120))
              [(sig,3309); (m,mlen); (pre,prelen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa65_verify_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk;
                                 ext] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 3309
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen pk ext sigb pkb M PRE
                              guard mf pc (word_sub stackpointer (word 45120))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; pre,prelen; pk,1952;
                         word_sub stackpointer (word 45120),45120;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word 0,0;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024]
                        [word_sub stackpointer (word 45120),45120]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 45120),45120)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
