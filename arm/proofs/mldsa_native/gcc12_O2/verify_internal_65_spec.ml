(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the statement. This is the code for          *)
(* mldsa65_verify_internal (mld_sign_verify_internal in sign.c) from         *)
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
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_unpack_z_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_chknorm_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_ntt_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvec_matrix_expand_eager_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_challenge_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvec_matrix_pointwise_montgomery_row_eager_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/unpack_pk_t1_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_shiftl_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_pointwise_montgomery_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_sub_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_reduce_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_caddq_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/sig_unpack_hints_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_use_hint_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyw1_pack_32_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_absorb_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_finalize_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_squeeze_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/H_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa65_verify_internal:
       +0x0: mov     x12, #0x9d20
       +0x4: sub     sp, sp, x12
       +0x8: stp     x19, x20, [sp]
       +0xc: mov     x19, #0x9c00
      +0x10: mov     x20, #0x7800
      +0x14: stp     x21, x22, [sp, #16]
      +0x18: add     x22, sp, #0x9f
      +0x1c: and     x22, x22, #0xffffffffffffffe0
      +0x20: stp     x23, x24, [sp, #32]
      +0x24: add     x23, x22, x19
      +0x28: sub     x7, x23, #0x80
      +0x2c: stp     x25, x26, [sp, #48]
      +0x30: mov     x25, x0
      +0x34: mov     x26, #0x8020
      +0x38: stp     x27, x28, [sp, #64]
      +0x3c: mov     x28, x1
      +0x40: add     x1, sp, x26
      +0x44: str     x30, [sp, #80]
      +0x48: mov     x21, x2
      +0x4c: str     x5, [sp, #96]
      +0x50: add     x27, x22, x20
      +0x54: ldp     q1, q2, [x0]
      +0x58: mov     x19, x3
      +0x5c: ldr     q0, [x0, #32]
      +0x60: mov     x20, x4
      +0x64: adrp    x0, <page>
      +0x68: ldr     x0, [x0, #4088]
      +0x6c: mov     w24, w6
      +0x70: ldr     x2, [x0]
      +0x74: str     x2, [x1, #7416]
      +0x78: mov     x2, #0x0
      +0x7c: mov     x0, x27
      +0x80: add     x1, x25, #0x30
      +0x84: stp     q1, q2, [x7]
      +0x88: str     q0, [x7, #32]
      +0x8c: bl      <mldsa65_polyvecl_unpack_z>
      +0x90: mov     w1, #0xff3c
      +0x94: mov     x0, x27
      +0x98: movk    w1, #0x7, lsl #16
      +0x9c: bl      <mldsa65_polyvecl_chknorm>
      +0xa0: cbnz    w0, <+0x468>
      +0xa4: mov     w26, w0
      +0xa8: cbz     w24, <+0x3b0>
      +0xac: ldp     q2, q3, [x28]
      +0xb0: sub     x0, x23, #0x100
      +0xb4: ldp     q0, q1, [x28, #32]
      +0xb8: mov     x8, #0x9800
      +0xbc: add     x1, x22, x8
      +0xc0: mov     x9, #0x9b00
      +0xc4: str     x1, [sp, #104]
      +0xc8: add     x1, x22, x9
      +0xcc: str     x1, [sp, #112]
      +0xd0: stp     q2, q3, [x0]
      +0xd4: stp     q0, q1, [x0, #32]
      +0xd8: mov     x5, #0x9b80
      +0xdc: add     x1, x22, x5
      +0xe0: mov     x6, #0x9400
      +0xe4: mov     x19, x1
      +0xe8: add     x28, x22, x6
      +0xec: mov     x0, x27
      +0xf0: str     x1, [sp, #120]
      +0xf4: bl      <mldsa65_polyvecl_ntt>
      +0xf8: add     x20, x22, #0x9, lsl #12
      +0xfc: ldr     x1, [sp, #96]
     +0x100: mov     x0, x22
     +0x104: mov     w21, #0x0
     +0x108: bl      <mldsa65_polyvec_matrix_expand_eager>
     +0x10c: mov     x1, x19
     +0x110: mov     x7, #0x8c00
     +0x114: ldr     x24, [sp, #104]
     +0x118: mov     x0, x28
     +0x11c: add     x19, x22, x7
     +0x120: bl      <mldsa65_poly_challenge>
     +0x124: mov     x0, x28
     +0x128: bl      <mldsa_poly_ntt>
     +0x12c: mov     w3, w21
     +0x130: mov     x2, x27
     +0x134: mov     x1, x22
     +0x138: mov     x0, x20
     +0x13c: bl      <mldsa65_polyvec_matrix_pointwise_montgomery_row_eager>
     +0x140: ldr     x1, [sp, #96]
     +0x144: mov     w2, w21
     +0x148: mov     x0, x19
     +0x14c: bl      <mldsa65_unpack_pk_t1>
     +0x150: mov     x0, x19
     +0x154: bl      <mldsa_poly_shiftl>
     +0x158: mov     x0, x19
     +0x15c: bl      <mldsa_poly_ntt>
     +0x160: mov     x1, x28
     +0x164: mov     x0, x19
     +0x168: bl      <mldsa_poly_pointwise_montgomery>
     +0x16c: mov     x1, x19
     +0x170: mov     x0, x20
     +0x174: bl      <mldsa_poly_sub>
     +0x178: mov     x0, x20
     +0x17c: bl      <mldsa_poly_reduce>
     +0x180: mov     x0, x20
     +0x184: bl      <mldsa_poly_invntt_tomont>
     +0x188: mov     x0, x20
     +0x18c: bl      <mldsa_poly_caddq>
     +0x190: mov     w2, w21
     +0x194: mov     x1, x25
     +0x198: mov     x0, x19
     +0x19c: bl      <mldsa65_sig_unpack_hints>
     +0x1a0: mov     w23, w0
     +0x1a4: cbnz    w0, <+0x458>
     +0x1a8: mov     x1, x19
     +0x1ac: mov     x0, x20
     +0x1b0: bl      <mldsa65_poly_use_hint>
     +0x1b4: add     w21, w21, #0x1
     +0x1b8: mov     x0, x24
     +0x1bc: mov     x1, x20
     +0x1c0: bl      <mldsa_polyw1_pack_32>
     +0x1c4: add     x24, x24, #0x80
     +0x1c8: cmp     w21, #0x6
     +0x1cc: b.ne    <+0x12c>
     +0x1d0: mov     x3, #0x9b40
     +0x1d4: mov     x2, #0x9c48
     +0x1d8: add     x21, sp, x2
     +0x1dc: add     x24, x22, x3
     +0x1e0: mov     x0, x21
     +0x1e4: bl      <mldsa_shake256_init>
     +0x1e8: ldr     x1, [sp, #112]
     +0x1ec: mov     x0, x21
     +0x1f0: mov     x2, #0x40
     +0x1f4: bl      <mldsa_shake256_absorb>
     +0x1f8: ldr     x1, [sp, #104]
     +0x1fc: mov     x2, #0x300
     +0x200: mov     x0, x21
     +0x204: bl      <mldsa_shake256_absorb>
     +0x208: mov     x0, x21
     +0x20c: bl      <mldsa_shake256_finalize>
     +0x210: mov     x2, x21
     +0x214: mov     x1, #0x30
     +0x218: mov     x0, x24
     +0x21c: bl      <mldsa_shake256_squeeze>
     +0x220: mov     x0, x21
     +0x224: bl      <mldsa_shake256_release>
     +0x228: movi    v0.4s, #0x0
     +0x22c: stp     q0, q0, [x21]
     +0x230: stp     q0, q0, [x21, #32]
     +0x234: stp     q0, q0, [x21, #64]
     +0x238: stp     q0, q0, [x21, #96]
     +0x23c: stp     q0, q0, [x21, #128]
     +0x240: stp     q0, q0, [x21, #160]
     +0x244: str     q0, [x21, #192]
     +0x248: ldr     x0, [sp, #120]
     +0x24c: mov     x1, x24
     +0x250: mov     v2.16b, v0.16b
     +0x254: ldr     q1, [x0], #16
     +0x258: add     w26, w26, #0x1
     +0x25c: ldr     q3, [x1], #16
     +0x260: eor     v1.16b, v1.16b, v3.16b
     +0x264: orr     v2.16b, v2.16b, v1.16b
     +0x268: eor     v0.16b, v0.16b, v1.16b
     +0x26c: cmp     w26, #0x3
     +0x270: b.ne    <+0x254>
     +0x274: movi    v1.4s, #0x0
     +0x278: ext     v5.16b, v2.16b, v1.16b, #8
     +0x27c: ext     v3.16b, v0.16b, v1.16b, #8
     +0x280: orr     v5.16b, v5.16b, v2.16b
     +0x284: eor     v2.16b, v3.16b, v0.16b
     +0x288: ext     v4.16b, v5.16b, v1.16b, #4
     +0x28c: ext     v0.16b, v2.16b, v1.16b, #4
     +0x290: orr     v4.16b, v4.16b, v5.16b
     +0x294: eor     v0.16b, v0.16b, v2.16b
     +0x298: ext     v3.16b, v4.16b, v1.16b, #2
     +0x29c: ext     v2.16b, v0.16b, v1.16b, #2
     +0x2a0: orr     v3.16b, v3.16b, v4.16b
     +0x2a4: eor     v2.16b, v2.16b, v0.16b
     +0x2a8: ext     v0.16b, v3.16b, v1.16b, #1
     +0x2ac: ext     v1.16b, v2.16b, v1.16b, #1
     +0x2b0: orr     v0.16b, v0.16b, v3.16b
     +0x2b4: eor     v1.16b, v1.16b, v2.16b
     +0x2b8: umov    w0, v0.b[0]
     +0x2bc: umov    w1, v1.b[0]
     +0x2c0: neg     x0, x0
     +0x2c4: asr     x0, x0, #32
     +0x2c8: eor     w0, w1, w0
     +0x2cc: cmp     w1, w0, uxtb
     +0x2d0: b.ne    <+0x460>
     +0x2d4: mov     x0, x19
     +0x2d8: mov     x2, #0x400
     +0x2dc: mov     w1, #0x0
     +0x2e0: bl      <memset@plt>
     +0x2e4: mov     x2, #0x400
     +0x2e8: mov     x0, x20
     +0x2ec: mov     w1, #0x0
     +0x2f0: bl      <memset@plt>
     +0x2f4: mov     x2, #0x7800
     +0x2f8: mov     x0, x22
     +0x2fc: mov     w1, #0x0
     +0x300: bl      <memset@plt>
     +0x304: mov     x2, #0x400
     +0x308: mov     x0, x28
     +0x30c: mov     w1, #0x0
     +0x310: bl      <memset@plt>
     +0x314: mov     x2, #0x1400
     +0x318: mov     x0, x27
     +0x31c: mov     w1, #0x0
     +0x320: bl      <memset@plt>
     +0x324: stp     xzr, xzr, [x24]
     +0x328: stp     xzr, xzr, [x24, #16]
     +0x32c: stp     xzr, xzr, [x24, #32]
     +0x330: ldr     x0, [sp, #120]
     +0x334: stp     xzr, xzr, [x0]
     +0x338: stp     xzr, xzr, [x0, #16]
     +0x33c: stp     xzr, xzr, [x0, #32]
     +0x340: ldr     x0, [sp, #112]
     +0x344: movi    v0.4s, #0x0
     +0x348: stp     q0, q0, [x0]
     +0x34c: stp     q0, q0, [x0, #32]
     +0x350: ldr     x19, [sp, #104]
     +0x354: mov     x2, #0x300
     +0x358: mov     w1, #0x0
     +0x35c: mov     x0, x19
     +0x360: bl      <memset@plt>
     +0x364: adrp    x0, <page>
     +0x368: ldr     x0, [x0, #4088]
     +0x36c: mov     x1, #0x8020
     +0x370: add     x2, sp, x1
     +0x374: ldr     x3, [x2, #7416]
     +0x378: ldr     x1, [x0]
     +0x37c: subs    x3, x3, x1
     +0x380: mov     x1, #0x0
     +0x384: b.ne    <+0x4b0>
     +0x388: ldp     x19, x20, [sp]
     +0x38c: mov     w0, w23
     +0x390: ldp     x21, x22, [sp, #16]
     +0x394: mov     x12, #0x9d20
     +0x398: ldp     x23, x24, [sp, #32]
     +0x39c: ldp     x25, x26, [sp, #48]
     +0x3a0: ldp     x27, x28, [sp, #64]
     +0x3a4: ldr     x30, [sp, #80]
     +0x3a8: add     sp, sp, x12
     +0x3ac: ret
     +0x3b0: mov     x10, #0x9c48
     +0x3b4: mov     x11, #0x9800
     +0x3b8: add     x23, sp, x10
     +0x3bc: add     x24, x22, x11
     +0x3c0: mov     x0, x23
     +0x3c4: str     x24, [sp, #104]
     +0x3c8: bl      <mldsa_shake256_init>
     +0x3cc: ldr     x1, [sp, #96]
     +0x3d0: mov     x2, #0x7a0
     +0x3d4: mov     x0, x23
     +0x3d8: bl      <mldsa_shake256_absorb>
     +0x3dc: mov     x0, x23
     +0x3e0: bl      <mldsa_shake256_finalize>
     +0x3e4: mov     x2, x23
     +0x3e8: mov     x1, #0x40
     +0x3ec: mov     x0, x24
     +0x3f0: bl      <mldsa_shake256_squeeze>
     +0x3f4: mov     x0, x23
     +0x3f8: bl      <mldsa_shake256_release>
     +0x3fc: movi    v0.4s, #0x0
     +0x400: stp     q0, q0, [x23]
     +0x404: stp     q0, q0, [x23, #32]
     +0x408: stp     q0, q0, [x23, #64]
     +0x40c: stp     q0, q0, [x23, #96]
     +0x410: stp     q0, q0, [x23, #128]
     +0x414: stp     q0, q0, [x23, #160]
     +0x418: str     q0, [x23, #192]
     +0x41c: mov     x12, #0x9b00
     +0x420: mov     x3, #0x40
     +0x424: add     x0, x22, x12
     +0x428: mov     x7, x21
     +0x42c: mov     x6, x28
     +0x430: mov     x5, x20
     +0x434: mov     x4, x19
     +0x438: mov     x2, x24
     +0x43c: mov     x1, x3
     +0x440: str     x0, [sp, #112]
     +0x444: bl      <mld_H65>
     +0x448: movi    v0.4s, #0x0
     +0x44c: stp     q0, q0, [x24]
     +0x450: stp     q0, q0, [x24, #32]
     +0x454: b       <+0xd8>
     +0x458: mov     x4, #0x9b40
     +0x45c: add     x24, x22, x4
     +0x460: mov     w23, #0xfffffffa
     +0x464: b       <+0x2d4>
     +0x468: mov     x13, #0x9800
     +0x46c: add     x0, x22, x13
     +0x470: mov     x17, #0x9b00
     +0x474: str     x0, [sp, #104]
     +0x478: add     x0, x22, x17
     +0x47c: mov     x14, #0x9400
     +0x480: mov     x15, #0x8c00
     +0x484: mov     x16, #0x9b40
     +0x488: mov     x18, #0x9b80
     +0x48c: add     x28, x22, x14
     +0x490: add     x20, x22, #0x9, lsl #12
     +0x494: add     x19, x22, x15
     +0x498: add     x24, x22, x16
     +0x49c: mov     w23, #0xfffffffa
     +0x4a0: str     x0, [sp, #112]
     +0x4a4: add     x0, x22, x18
     +0x4a8: str     x0, [sp, #120]
     +0x4ac: b       <+0x2d4>
     +0x4b0: bl      <__stack_chk_fail@plt>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_verify_internal"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The signature sigb at sig  *)
(* (3309 bytes), the message M of mlen bytes at m and the prefix PRE of      *)
(* prelen bytes at pre (or, if ext is nonzero as a 32-bit integer, mu in the *)
(* first 64 bytes at m), the public key pkb at pk (1952 bytes): the result   *)
(* is 0 if the signature is accepted, and -6 otherwise. The stack is the     *)
(* 40224 bytes of the function and those of the callees below them.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 45280),45280))
              [(sig,3309); (m,mlen); (pre,prelen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
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
                 [memory :> bytes(word_sub stackpointer (word 45280),45280)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the flag ext, the    *)
(* signature, the message, the prefix and the public key, all public, the    *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset may read and the constants of the callees, and the writes within   *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 45280),45280))
              [(sig,3309); (m,mlen); (pre,prelen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
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
                              guard mf pc (word_sub stackpointer (word 45280))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; pre,prelen; pk,1952;
                         word_sub stackpointer (word 45280),45280;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16;
                         word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const2),16]
                        [word_sub stackpointer (word 45280),45280]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 45280),45280)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 45280),45280))
              [(sig,3309); (m,mlen); (pre,prelen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
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
                              guard mf pc (word_sub stackpointer (word 45280))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; pre,prelen; pk,1952;
                         word_sub stackpointer (word 45280),45280;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16;
                         word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const2),16]
                        [word_sub stackpointer (word 45280),45280]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 45280),45280)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
