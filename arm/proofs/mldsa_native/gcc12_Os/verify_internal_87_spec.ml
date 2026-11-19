(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the statement. This is the code for          *)
(* mldsa87_verify_internal (mld_sign_verify_internal in sign.c) from mldsa-  *)
(* native's portable C implementation compiled by gcc 12 with -Os (see       *)
(* mldsa_native/README.md), which unpacks z and checks its norm, computes mu *)
(* with mld_H87 (or takes it from m if ext is nonzero), expands the matrix   *)
(* from rho, the challenge from c~, and for each row computes w1' =          *)
(* UseHint(h, A z - c t1 2^d), unpacking the hints of the row, and packs it, *)
(* and then compares c~ with the hash of mu and w1' (mld_H87 again) with     *)
(* mld_ct_memcmp_3. It zeroizes its buffers with mld_zeroize_6, a call of    *)
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
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_unpack_z_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_chknorm_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_ntt_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvec_matrix_expand_eager_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_challenge_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvec_matrix_pointwise_montgomery_row_eager_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/unpack_pk_t1_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_shiftl_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_pointwise_montgomery_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_sub_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_reduce_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_caddq_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/sig_unpack_hints_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/poly_use_hint_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyw1_pack_32_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/H_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/zeroize_6_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/ct_memcmp_3_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa87_verify_internal:
       +0x0: sub     sp, sp, #0xd70
       +0x4: mov     x7, #0xfc00
       +0x8: sub     sp, sp, #0x10, lsl #12
       +0xc: stp     x19, x20, [sp]
      +0x10: add     x19, sp, #0xaf
      +0x14: and     x19, x19, #0xffffffffffffffe0
      +0x18: stp     x23, x24, [sp, #32]
      +0x1c: mov     x23, x0
      +0x20: add     x24, x19, #0x10, lsl #12
      +0x24: adrp    x0, <page>
      +0x28: ldr     x0, [x0, #4088]
      +0x2c: stp     x21, x22, [sp, #16]
      +0x30: add     x22, x19, x7
      +0x34: stp     x25, x26, [sp, #48]
      +0x38: mov     x25, x1
      +0x3c: add     x26, x19, #0x10, lsl #12
      +0x40: stp     x27, x28, [sp, #64]
      +0x44: add     x1, sp, #0x10, lsl #12
      +0x48: add     x1, x1, #0x30
      +0x4c: str     x30, [sp, #80]
      +0x50: add     x26, x26, #0xc00
      +0x54: stp     x2, x5, [sp, #96]
      +0x58: add     x27, x19, #0xe, lsl #12
      +0x5c: add     x28, x19, #0x10, lsl #12
      +0x60: stp     x3, x4, [sp, #120]
      +0x64: add     x24, x24, #0x800
      +0x68: add     x28, x28, #0x400
      +0x6c: str     w6, [sp, #140]
      +0x70: add     x21, x19, #0x10, lsl #12
      +0x74: ldp     q0, q1, [x23]
      +0x78: ldr     x2, [x0]
      +0x7c: str     x2, [x1, #3384]
      +0x80: mov     x2, #0x0
      +0x84: add     x0, x26, #0x40
      +0x88: add     x1, x23, #0x40
      +0x8c: stp     q0, q1, [x0]
      +0x90: ldp     q0, q1, [x23, #32]
      +0x94: stp     q0, q1, [x0, #32]
      +0x98: mov     x0, x27
      +0x9c: bl      <mldsa87_polyvecl_unpack_z>
      +0xa0: mov     w1, #0xff88
      +0xa4: mov     x0, x27
      +0xa8: movk    w1, #0x7, lsl #16
      +0xac: bl      <mldsa87_polyvecl_chknorm>
      +0xb0: mov     w20, w0
      +0xb4: add     x0, x19, #0x10, lsl #12
      +0xb8: add     x0, x0, #0xc40
      +0xbc: str     x0, [sp, #112]
      +0xc0: cbnz    w20, <mldsa87_verify_internal+0x230>
      +0xc4: ldr     w6, [sp, #140]
      +0xc8: cbnz    w6, <mldsa87_verify_internal+0x2cc>
      +0xcc: ldr     x1, [sp, #104]
      +0xd0: mov     x0, x24
      +0xd4: mov     x6, #0x0
      +0xd8: mov     x5, #0x0
      +0xdc: mov     x4, #0x0
      +0xe0: mov     x3, #0x0
      +0xe4: mov     x2, #0xa20
      +0xe8: bl      <mld_H87>
      +0xec: ldp     x3, x4, [sp, #120]
      +0xf0: mov     x5, x25
      +0xf4: ldr     x6, [sp, #96]
      +0xf8: add     x0, x19, #0x10, lsl #12
      +0xfc: mov     x2, #0x40
     +0x100: mov     x1, x24
     +0x104: add     x0, x0, #0xc80
     +0x108: bl      <mld_H87>
     +0x10c: mov     x0, x24
     +0x110: mov     x1, #0x40
     +0x114: bl      <mld_zeroize_6>
     +0x118: mov     x0, x27
     +0x11c: bl      <mldsa87_polyvecl_ntt>
     +0x120: ldr     x1, [sp, #104]
     +0x124: mov     x0, x19
     +0x128: bl      <mldsa87_polyvec_matrix_expand_eager>
     +0x12c: add     x1, x19, #0x10, lsl #12
     +0x130: mov     x0, x28
     +0x134: add     x1, x1, #0xc40
     +0x138: bl      <mldsa87_poly_challenge>
     +0x13c: mov     x0, x28
     +0x140: bl      <mldsa_poly_ntt>
     +0x144: str     x24, [sp, #96]
     +0x148: mov     w3, w20
     +0x14c: mov     x2, x27
     +0x150: mov     x1, x19
     +0x154: mov     x0, x21
     +0x158: bl      <mldsa87_polyvec_matrix_pointwise_montgomery_row_eager>
     +0x15c: ldr     x1, [sp, #104]
     +0x160: mov     w2, w20
     +0x164: mov     x0, x22
     +0x168: bl      <mldsa87_unpack_pk_t1>
     +0x16c: mov     x0, x22
     +0x170: bl      <mldsa_poly_shiftl>
     +0x174: mov     x0, x22
     +0x178: bl      <mldsa_poly_ntt>
     +0x17c: mov     x1, x28
     +0x180: mov     x0, x22
     +0x184: bl      <mldsa_poly_pointwise_montgomery>
     +0x188: mov     x1, x22
     +0x18c: mov     x0, x21
     +0x190: bl      <mldsa_poly_sub>
     +0x194: mov     x0, x21
     +0x198: bl      <mldsa_poly_reduce>
     +0x19c: mov     x0, x21
     +0x1a0: bl      <mldsa_poly_invntt_tomont>
     +0x1a4: mov     x0, x21
     +0x1a8: bl      <mldsa_poly_caddq>
     +0x1ac: mov     w2, w20
     +0x1b0: mov     x1, x23
     +0x1b4: mov     x0, x22
     +0x1b8: bl      <mldsa87_sig_unpack_hints>
     +0x1bc: mov     w25, w0
     +0x1c0: cbnz    w0, <mldsa87_verify_internal+0x230>
     +0x1c4: mov     x1, x22
     +0x1c8: mov     x0, x21
     +0x1cc: bl      <mldsa87_poly_use_hint>
     +0x1d0: add     w20, w20, #0x1
     +0x1d4: ldr     x0, [sp, #96]
     +0x1d8: mov     x1, x21
     +0x1dc: bl      <mldsa_polyw1_pack_32>
     +0x1e0: ldr     x0, [sp, #96]
     +0x1e4: add     x0, x0, #0x80
     +0x1e8: str     x0, [sp, #96]
     +0x1ec: cmp     w20, #0x8
     +0x1f0: b.ne    <mldsa87_verify_internal+0x148>
     +0x1f4: add     x1, x19, #0x10, lsl #12
     +0x1f8: mov     x0, x26
     +0x1fc: add     x1, x1, #0xc80
     +0x200: mov     x2, #0x40
     +0x204: mov     x3, x24
     +0x208: mov     x6, #0x0
     +0x20c: mov     x5, #0x0
     +0x210: mov     x4, #0x400
     +0x214: bl      <mld_H87>
     +0x218: ldr     x0, [sp, #112]
     +0x21c: mov     x1, x26
     +0x220: mov     x2, #0x40
     +0x224: bl      <mld_ct_memcmp_3>
     +0x228: tst     w0, #0xff
     +0x22c: b.eq    <mldsa87_verify_internal+0x234>
     +0x230: mov     w25, #0xfffffffa
     +0x234: mov     x0, x22
     +0x238: mov     x1, #0x400
     +0x23c: bl      <mld_zeroize_6>
     +0x240: mov     x0, x21
     +0x244: mov     x1, #0x400
     +0x248: bl      <mld_zeroize_6>
     +0x24c: mov     x0, x19
     +0x250: mov     x1, #0xe000
     +0x254: bl      <mld_zeroize_6>
     +0x258: mov     x0, x28
     +0x25c: mov     x1, #0x400
     +0x260: bl      <mld_zeroize_6>
     +0x264: mov     x0, x27
     +0x268: mov     x1, #0x1c00
     +0x26c: bl      <mld_zeroize_6>
     +0x270: mov     x0, x26
     +0x274: mov     x1, #0x40
     +0x278: bl      <mld_zeroize_6>
     +0x27c: ldr     x0, [sp, #112]
     +0x280: mov     x1, #0x40
     +0x284: bl      <mld_zeroize_6>
     +0x288: add     x0, x19, #0x10, lsl #12
     +0x28c: mov     x1, #0x40
     +0x290: add     x0, x0, #0xc80
     +0x294: bl      <mld_zeroize_6>
     +0x298: mov     x0, x24
     +0x29c: mov     x1, #0x400
     +0x2a0: bl      <mld_zeroize_6>
     +0x2a4: adrp    x0, <page>
     +0x2a8: ldr     x0, [x0, #4088]
     +0x2ac: add     x2, sp, #0x10, lsl #12
     +0x2b0: add     x2, x2, #0x30
     +0x2b4: ldr     x3, [x2, #3384]
     +0x2b8: ldr     x1, [x0]
     +0x2bc: subs    x3, x3, x1
     +0x2c0: mov     x1, #0x0
     +0x2c4: b.eq    <mldsa87_verify_internal+0x2e4>
     +0x2c8: bl      <stack_chk_fail>
     +0x2cc: ldp     q0, q1, [x25]
     +0x2d0: add     x0, x26, #0x80
     +0x2d4: stp     q0, q1, [x0]
     +0x2d8: ldp     q0, q1, [x25, #32]
     +0x2dc: stp     q0, q1, [x0, #32]
     +0x2e0: b       <mldsa87_verify_internal+0x118>
     +0x2e4: ldp     x19, x20, [sp]
     +0x2e8: mov     w0, w25
     +0x2ec: ldp     x21, x22, [sp, #16]
     +0x2f0: ldp     x23, x24, [sp, #32]
     +0x2f4: ldp     x25, x26, [sp, #48]
     +0x2f8: ldp     x27, x28, [sp, #64]
     +0x2fc: ldr     x30, [sp, #80]
     +0x300: add     sp, sp, #0xd70
     +0x304: add     sp, sp, #0x10, lsl #12
     +0x308: ret
 ***)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa87_verify_internal"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The signature sigb at sig  *)
(* (4627 bytes), the message M of mlen bytes at m and the prefix PRE of      *)
(* prelen bytes at pre (or, if ext is nonzero as a 32-bit integer, mu in the *)
(* first 64 bytes at m), the public key pkb at pk (2592 bytes): the result   *)
(* is 0 if the signature is accepted, and -6 otherwise. The stack is the     *)
(* 68976 bytes of the function and those of the callees below them.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_ret_full_contract mf ea el ev
     ==> !sig m mlen pre prelen pk ext sigb pkb M PRE guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 8 7 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 60 64
           (num_of_bytelist(list_of_seq sigb 64)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 74064),74064))
              [(sig,4627); (m,mlen); (pre,prelen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa87_verify_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk;
                                 ext] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4627
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_verify_internal_ok 8 7 64
                           mld_polyz_unpack_19 640 524168
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60
                           sigb pkb
                           (if word_zx ext = (word 0:int32)
                            then mld_verify_mu 2592 pkb prelen PRE mlen M
                            else M MOD 2 EXP 512)
                     then word 0 else word 4294967290))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74064),74064)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the flag ext, the    *)
(* signature, the message, the prefix and the public key, all public, the    *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset may read and the constants of the callees, and the writes within   *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_ret_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen pk ext sigb pkb M PRE guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 8 7 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 60 64
           (num_of_bytelist(list_of_seq sigb 64)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 74064),74064))
              [(sig,4627); (m,mlen); (pre,prelen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa87_verify_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk;
                                 ext] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4627
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_verify_internal_ok 8 7 64
                           mld_polyz_unpack_19 640 524168
                           mld_poly_use_hint_32 mld_polyw1_pack_32 128 75 60
                           sigb pkb
                           (if word_zx ext = (word 0:int32)
                            then mld_verify_mu 2592 pkb prelen PRE mlen M
                            else M MOD 2 EXP 512)
                     then word 0 else word 4294967290) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen pk ext sigb pkb M PRE
                              guard mf pc (word_sub stackpointer (word 74064))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; pre,prelen; pk,2592;
                         word_sub stackpointer (word 74064),74064;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word 0,0;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024]
                        [word_sub stackpointer (word 74064),74064]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74064),74064)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_ret_full_contract mf ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen pk ext sigb pkb M PRE guard pc
                 stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          mld_matrix_terminates 8 7 (num_of_bytelist(list_of_seq pkb 32)) /\
          mld_poly_challenge_terminates 60 64
           (num_of_bytelist(list_of_seq sigb 64)) /\
          ALL (nonoverlapping (word_sub stackpointer (word 74064),74064))
              [(sig,4627); (m,mlen); (pre,prelen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa87_verify_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; pk;
                                 ext] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4627
                         ==> read(memory :> bytes8(word_add sig (word j))) s =
                             sigb j) /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             pkb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen pk ext sigb pkb M PRE
                              guard mf pc (word_sub stackpointer (word 74064))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; pre,prelen; pk,2592;
                         word_sub stackpointer (word 74064),74064;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word 0,0;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024]
                        [word_sub stackpointer (word 74064),74064]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74064),74064)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
