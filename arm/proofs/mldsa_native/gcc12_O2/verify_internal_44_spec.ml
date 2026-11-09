(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the statement. This is the code for          *)
(* mldsa44_verify_internal (mld_sign_verify_internal in sign.c) from         *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mldsa_native/README.md), which unpacks z and checks its norm, computes mu *)
(* (or takes it from m if ext is nonzero), expands the matrix from rho, the  *)
(* challenge from c~, and for each row computes w1' = UseHint(h, A z - c t1  *)
(* 2^d), unpacking the hints of the row, and packs it, and then compares c~  *)
(* with the hash of mu and w1'. It is verified in the whole image (see       *)
(* libmldsa.ml) against mld_verify_internal_ok of                            *)
(* common/mldsa_native_sign.ml, using the theorems for the callees and the   *)
(* contract memset_ret_full_contract of utils/mldsa_native_libc.ml, assuming *)
(* that the expansion of the matrix and the sampling of the challenge        *)
(* terminate, and shown to be constant time and memory safe, with events     *)
(* depending on the signature, the message, the prefix and the public key,   *)
(* which are all public.                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_unpack_z_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_chknorm_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_ntt_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvec_matrix_expand_eager_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_challenge_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvec_matrix_pointwise_montgomery_row_eager_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/unpack_pk_t1_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_shiftl_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_pointwise_montgomery_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_sub_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_reduce_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_caddq_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/sig_unpack_hints_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_use_hint_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyw1_pack_88_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_absorb_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_finalize_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_squeeze_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/H_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa44_verify_internal:
       +0x0: mov     x12, #0x60f0
       +0x4: sub     sp, sp, x12
       +0x8: mov     x7, x0
       +0xc: stp     x19, x20, [sp]
      +0x10: mov     x19, x1
      +0x14: mov     x20, x4
      +0x18: stp     x21, x22, [sp, #16]
      +0x1c: add     x21, sp, #0x9f
      +0x20: and     x21, x21, #0xffffffffffffffe0
      +0x24: stp     x23, x24, [sp, #32]
      +0x28: add     x24, x21, #0x6, lsl #12
      +0x2c: mov     x23, x2
      +0x30: stp     x25, x26, [sp, #48]
      +0x34: add     x25, x21, #0x4, lsl #12
      +0x38: mov     w26, w6
      +0x3c: stp     x27, x28, [sp, #64]
      +0x40: str     x30, [sp, #80]
      +0x44: stp     x5, x0, [sp, #104]
      +0x48: ldp     q0, q1, [x7]
      +0x4c: str     x3, [sp, #120]
      +0x50: adrp    x0, <page>
      +0x54: ldr     x0, [x0, #4088]
      +0x58: ldr     x1, [x0]
      +0x5c: str     x1, [sp, #24808]
      +0x60: mov     x1, #0x0
      +0x64: mov     x0, x25
      +0x68: add     x1, x7, #0x20
      +0x6c: stp     q0, q1, [x24, #-160]
      +0x70: bl      <mldsa44_polyvecl_unpack_z>
      +0x74: mov     w1, #0xffb2
      +0x78: mov     x0, x25
      +0x7c: movk    w1, #0x1, lsl #16
      +0x80: bl      <mldsa44_polyvecl_chknorm>
      +0x84: cbnz    w0, <+0x414>
      +0x88: mov     w22, w0
      +0x8c: cbz     w26, <+0x360>
      +0x90: ldp     q2, q3, [x19]
      +0x94: sub     x24, x24, #0x100
      +0x98: ldp     q0, q1, [x19, #32]
      +0x9c: mov     x6, #0x5c00
      +0xa0: mov     x7, #0x5f00
      +0xa4: add     x28, x21, x6
      +0xa8: add     x27, x21, x7
      +0xac: stp     q2, q3, [x24]
      +0xb0: stp     q0, q1, [x24, #32]
      +0xb4: mov     x3, #0x5f60
      +0xb8: add     x1, x21, x3
      +0xbc: mov     x4, #0x5400
      +0xc0: mov     x5, #0x5800
      +0xc4: mov     x19, x1
      +0xc8: add     x26, x21, x5
      +0xcc: add     x20, x21, x4
      +0xd0: mov     x0, x25
      +0xd4: str     x1, [sp, #120]
      +0xd8: bl      <mldsa44_polyvecl_ntt>
      +0xdc: mov     x24, x28
      +0xe0: ldr     x1, [sp, #104]
      +0xe4: mov     x0, x21
      +0xe8: bl      <mldsa44_polyvec_matrix_expand_eager>
      +0xec: mov     x1, x19
      +0xf0: mov     x0, x26
      +0xf4: bl      <mldsa44_poly_challenge>
      +0xf8: add     x19, x21, #0x5, lsl #12
      +0xfc: mov     x0, x26
     +0x100: bl      <mldsa_poly_ntt>
     +0x104: mov     w3, w22
     +0x108: mov     x2, x25
     +0x10c: mov     x1, x21
     +0x110: mov     x0, x20
     +0x114: bl      <mldsa44_polyvec_matrix_pointwise_montgomery_row_eager>
     +0x118: ldr     x1, [sp, #104]
     +0x11c: mov     w2, w22
     +0x120: mov     x0, x19
     +0x124: bl      <mldsa44_unpack_pk_t1>
     +0x128: mov     x0, x19
     +0x12c: bl      <mldsa_poly_shiftl>
     +0x130: mov     x0, x19
     +0x134: bl      <mldsa_poly_ntt>
     +0x138: mov     x1, x26
     +0x13c: mov     x0, x19
     +0x140: bl      <mldsa_poly_pointwise_montgomery>
     +0x144: mov     x1, x19
     +0x148: mov     x0, x20
     +0x14c: bl      <mldsa_poly_sub>
     +0x150: mov     x0, x20
     +0x154: bl      <mldsa_poly_reduce>
     +0x158: mov     x0, x20
     +0x15c: bl      <mldsa_poly_invntt_tomont>
     +0x160: mov     x0, x20
     +0x164: bl      <mldsa_poly_caddq>
     +0x168: ldr     x1, [sp, #112]
     +0x16c: mov     w2, w22
     +0x170: mov     x0, x19
     +0x174: bl      <mldsa44_sig_unpack_hints>
     +0x178: mov     w23, w0
     +0x17c: cbnz    w0, <+0x404>
     +0x180: mov     x1, x19
     +0x184: mov     x0, x20
     +0x188: bl      <mldsa44_poly_use_hint>
     +0x18c: add     w22, w22, #0x1
     +0x190: mov     x0, x24
     +0x194: mov     x1, x20
     +0x198: bl      <mldsa_polyw1_pack_88>
     +0x19c: add     x24, x24, #0xc0
     +0x1a0: cmp     w22, #0x4
     +0x1a4: b.ne    <+0x104>
     +0x1a8: mov     x1, #0x5f40
     +0x1ac: mov     x0, #0x6018
     +0x1b0: add     x24, sp, x0
     +0x1b4: add     x22, x21, x1
     +0x1b8: mov     x0, x24
     +0x1bc: bl      <mldsa_shake256_init>
     +0x1c0: mov     x0, x24
     +0x1c4: mov     x1, x27
     +0x1c8: mov     x2, #0x40
     +0x1cc: bl      <mldsa_shake256_absorb>
     +0x1d0: mov     x1, x28
     +0x1d4: mov     x2, #0x300
     +0x1d8: mov     x0, x24
     +0x1dc: bl      <mldsa_shake256_absorb>
     +0x1e0: mov     x0, x24
     +0x1e4: bl      <mldsa_shake256_finalize>
     +0x1e8: mov     x2, x24
     +0x1ec: mov     x1, #0x20
     +0x1f0: mov     x0, x22
     +0x1f4: bl      <mldsa_shake256_squeeze>
     +0x1f8: mov     x0, x24
     +0x1fc: bl      <mldsa_shake256_release>
     +0x200: movi    v0.4s, #0x0
     +0x204: stp     q0, q0, [x24]
     +0x208: stp     q0, q0, [x24, #32]
     +0x20c: stp     q0, q0, [x24, #64]
     +0x210: stp     q0, q0, [x24, #96]
     +0x214: stp     q0, q0, [x24, #128]
     +0x218: stp     q0, q0, [x24, #160]
     +0x21c: str     q0, [x24, #192]
     +0x220: ldr     q4, [x21, #24384]
     +0x224: ldr     q3, [x21, #24400]
     +0x228: ldr     q1, [x21, #24416]
     +0x22c: ldr     q2, [x21, #24432]
     +0x230: eor     v1.16b, v1.16b, v4.16b
     +0x234: eor     v2.16b, v2.16b, v3.16b
     +0x238: orr     v4.16b, v1.16b, v2.16b
     +0x23c: eor     v1.16b, v1.16b, v2.16b
     +0x240: ext     v3.16b, v4.16b, v0.16b, #8
     +0x244: ext     v2.16b, v1.16b, v0.16b, #8
     +0x248: orr     v3.16b, v3.16b, v4.16b
     +0x24c: eor     v2.16b, v2.16b, v1.16b
     +0x250: ext     v4.16b, v3.16b, v0.16b, #4
     +0x254: ext     v1.16b, v2.16b, v0.16b, #4
     +0x258: orr     v4.16b, v4.16b, v3.16b
     +0x25c: eor     v1.16b, v1.16b, v2.16b
     +0x260: ext     v3.16b, v4.16b, v0.16b, #2
     +0x264: ext     v2.16b, v1.16b, v0.16b, #2
     +0x268: orr     v3.16b, v3.16b, v4.16b
     +0x26c: eor     v2.16b, v2.16b, v1.16b
     +0x270: ext     v1.16b, v3.16b, v0.16b, #1
     +0x274: ext     v0.16b, v2.16b, v0.16b, #1
     +0x278: orr     v1.16b, v1.16b, v3.16b
     +0x27c: eor     v0.16b, v0.16b, v2.16b
     +0x280: umov    w1, v1.b[0]
     +0x284: umov    w0, v0.b[0]
     +0x288: neg     x1, x1
     +0x28c: asr     x1, x1, #32
     +0x290: eor     w1, w0, w1
     +0x294: cmp     w0, w1, uxtb
     +0x298: b.ne    <+0x40c>
     +0x29c: mov     x0, x19
     +0x2a0: mov     x2, #0x400
     +0x2a4: mov     w1, #0x0
     +0x2a8: bl      <memset@plt>
     +0x2ac: mov     x2, #0x400
     +0x2b0: mov     x0, x20
     +0x2b4: mov     w1, #0x0
     +0x2b8: bl      <memset@plt>
     +0x2bc: mov     x2, #0x4000
     +0x2c0: mov     x0, x21
     +0x2c4: mov     w1, #0x0
     +0x2c8: bl      <memset@plt>
     +0x2cc: mov     x2, #0x400
     +0x2d0: mov     x0, x26
     +0x2d4: mov     w1, #0x0
     +0x2d8: bl      <memset@plt>
     +0x2dc: mov     x2, #0x1000
     +0x2e0: mov     x0, x25
     +0x2e4: mov     w1, #0x0
     +0x2e8: bl      <memset@plt>
     +0x2ec: stp     xzr, xzr, [x22]
     +0x2f0: stp     xzr, xzr, [x22, #16]
     +0x2f4: ldr     x0, [sp, #120]
     +0x2f8: stp     xzr, xzr, [x0]
     +0x2fc: stp     xzr, xzr, [x0, #16]
     +0x300: movi    v0.4s, #0x0
     +0x304: stp     q0, q0, [x27]
     +0x308: stp     q0, q0, [x27, #32]
     +0x30c: mov     x2, #0x300
     +0x310: mov     x0, x28
     +0x314: mov     w1, #0x0
     +0x318: bl      <memset@plt>
     +0x31c: adrp    x0, <page>
     +0x320: ldr     x0, [x0, #4088]
     +0x324: ldr     x2, [sp, #24808]
     +0x328: ldr     x1, [x0]
     +0x32c: subs    x2, x2, x1
     +0x330: mov     x1, #0x0
     +0x334: b.ne    <+0x454>
     +0x338: ldp     x19, x20, [sp]
     +0x33c: mov     w0, w23
     +0x340: ldp     x21, x22, [sp, #16]
     +0x344: mov     x12, #0x60f0
     +0x348: ldp     x23, x24, [sp, #32]
     +0x34c: ldp     x25, x26, [sp, #48]
     +0x350: ldp     x27, x28, [sp, #64]
     +0x354: ldr     x30, [sp, #80]
     +0x358: add     sp, sp, x12
     +0x35c: ret
     +0x360: mov     x8, #0x6018
     +0x364: mov     x9, #0x5c00
     +0x368: add     x24, sp, x8
     +0x36c: add     x28, x21, x9
     +0x370: mov     x0, x24
     +0x374: bl      <mldsa_shake256_init>
     +0x378: ldr     x1, [sp, #104]
     +0x37c: mov     x2, #0x520
     +0x380: mov     x0, x24
     +0x384: bl      <mldsa_shake256_absorb>
     +0x388: mov     x0, x24
     +0x38c: bl      <mldsa_shake256_finalize>
     +0x390: mov     x2, x24
     +0x394: mov     x1, #0x40
     +0x398: mov     x0, x28
     +0x39c: bl      <mldsa_shake256_squeeze>
     +0x3a0: mov     x0, x24
     +0x3a4: bl      <mldsa_shake256_release>
     +0x3a8: movi    v0.4s, #0x0
     +0x3ac: stp     q0, q0, [x24]
     +0x3b0: stp     q0, q0, [x24, #32]
     +0x3b4: stp     q0, q0, [x24, #64]
     +0x3b8: stp     q0, q0, [x24, #96]
     +0x3bc: stp     q0, q0, [x24, #128]
     +0x3c0: stp     q0, q0, [x24, #160]
     +0x3c4: str     q0, [x24, #192]
     +0x3c8: ldr     x4, [sp, #120]
     +0x3cc: mov     x10, #0x5f00
     +0x3d0: add     x27, x21, x10
     +0x3d4: mov     x3, #0x40
     +0x3d8: mov     x7, x23
     +0x3dc: mov     x6, x19
     +0x3e0: mov     x5, x20
     +0x3e4: mov     x0, x27
     +0x3e8: mov     x2, x28
     +0x3ec: mov     x1, x3
     +0x3f0: bl      <mld_H44>
     +0x3f4: movi    v0.4s, #0x0
     +0x3f8: stp     q0, q0, [x28]
     +0x3fc: stp     q0, q0, [x28, #32]
     +0x400: b       <+0xb4>
     +0x404: mov     x2, #0x5f40
     +0x408: add     x22, x21, x2
     +0x40c: mov     w23, #0xfffffffa
     +0x410: b       <+0x29c>
     +0x414: mov     x11, #0x5c00
     +0x418: mov     x12, #0x5f00
     +0x41c: mov     x13, #0x5f60
     +0x420: mov     x14, #0x5800
     +0x424: add     x0, x21, x13
     +0x428: mov     x15, #0x5400
     +0x42c: mov     x16, #0x5f40
     +0x430: add     x28, x21, x11
     +0x434: add     x27, x21, x12
     +0x438: add     x26, x21, x14
     +0x43c: add     x20, x21, x15
     +0x440: add     x19, x21, #0x5, lsl #12
     +0x444: add     x22, x21, x16
     +0x448: mov     w23, #0xfffffffa
     +0x44c: str     x0, [sp, #120]
     +0x450: b       <+0x29c>
     +0x454: bl      <__stack_chk_fail@plt>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_verify_internal"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The signature sigb at sig  *)
(* (2420 bytes), the message M of mlen bytes at m and the prefix PRE of      *)
(* prelen bytes at pre (or, if ext is nonzero as a 32-bit integer, mu in the *)
(* first 64 bytes at m), the public key pkb at pk (1312 bytes): the result   *)
(* is 0 if the signature is accepted, and -6 otherwise. The stack is the     *)
(* 24816 bytes of the function and those of the callees below them.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 29888),29888))
              [(sig,2420); (m,mlen); (pre,prelen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
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
                 [memory :> bytes(word_sub stackpointer (word 29888),29888)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the flag ext, the    *)
(* signature, the message, the prefix and the public key, all public, the    *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset may read and the constants of the callees, and the writes within   *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 29888),29888))
              [(sig,2420); (m,mlen); (pre,prelen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
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
                              guard mf pc (word_sub stackpointer (word 29888))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; pre,prelen; pk,1312;
                         word_sub stackpointer (word 29888),29888;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16;
                         word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const2),16]
                        [word_sub stackpointer (word 29888),29888]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 29888),29888)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 29888),29888))
              [(sig,2420); (m,mlen); (pre,prelen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
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
                              guard mf pc (word_sub stackpointer (word 29888))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; pre,prelen; pk,1312;
                         word_sub stackpointer (word 29888),29888;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16;
                         word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const2),16]
                        [word_sub stackpointer (word 29888),29888]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 29888),29888)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
