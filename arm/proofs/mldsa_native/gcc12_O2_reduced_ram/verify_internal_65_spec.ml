(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the statement. This is the code for          *)
(* mldsa65_verify_internal (mld_sign_verify_internal in sign.c) from         *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 and  *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which unpacks z and   *)
(* checks its norm, computes mu (or takes it from m if ext is nonzero),      *)
(* expands the challenge from c~, and for each row computes w1' = UseHint(h, *)
(* A z - c t1 2^d), sampling the entries of the row of A from rho and        *)
(* unpacking the hints of the row, and packs it, and then compares c~ with   *)
(* the hash of mu and w1'. It is verified in the whole image (see            *)
(* libmldsa.ml) against mld_verify_internal_ok of                            *)
(* common/mldsa_native_sign.ml, using the theorems for the callees and the   *)
(* contract memset_ret_full_contract of utils/mldsa_native_libc.ml, assuming *)
(* that the sampling of the entries of the matrix and of the challenge       *)
(* terminate, and shown to be constant time and memory safe, with events     *)
(* depending on the signature, the message, the prefix and the public key,   *)
(* which are all public.                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvecl_unpack_z_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvecl_chknorm_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvecl_ntt_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_expand_lazy_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_challenge_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/unpack_pk_t1_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_shiftl_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_pointwise_montgomery_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_sub_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_reduce_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_caddq_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/sig_unpack_hints_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_use_hint_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyw1_pack_32_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_absorb_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_finalize_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_squeeze_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/H_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa65_verify_internal:
       +0x0: mov     x12, #0x2940
       +0x4: sub     sp, sp, x12
       +0x8: stp     x19, x20, [sp]
       +0xc: mov     x20, x3
      +0x10: stp     x21, x22, [sp, #16]
      +0x14: add     x22, sp, #0x9f
      +0x18: and     x22, x22, #0xffffffffffffffe0
      +0x1c: stp     x23, x24, [sp, #32]
      +0x20: mov     x24, #0x2800
      +0x24: add     x19, x22, x24
      +0x28: stp     x25, x26, [sp, #48]
      +0x2c: mov     x25, x0
      +0x30: sub     x7, x19, #0x60
      +0x34: stp     x27, x28, [sp, #64]
      +0x38: mov     x24, x1
      +0x3c: mov     x23, x2
      +0x40: str     x30, [sp, #80]
      +0x44: mov     x21, x4
      +0x48: str     x5, [sp, #96]
      +0x4c: mov     w27, w6
      +0x50: ldp     q1, q2, [x0]
      +0x54: ldr     q0, [x0, #32]
      +0x58: adrp    x0, <page>
      +0x5c: ldr     x0, [x0, #4088]
      +0x60: ldr     x1, [x0]
      +0x64: str     x1, [sp, #10552]
      +0x68: mov     x1, #0x0
      +0x6c: mov     x0, x22
      +0x70: add     x1, x25, #0x30
      +0x74: stp     q1, q2, [x7]
      +0x78: str     q0, [x7, #32]
      +0x7c: bl      <mldsa65_polyvecl_unpack_z>
      +0x80: mov     w1, #0xff3c
      +0x84: mov     x0, x22
      +0x88: movk    w1, #0x7, lsl #16
      +0x8c: bl      <mldsa65_polyvecl_chknorm>
      +0x90: cbnz    w0, <mldsa65_verify_internal+0x45c>
      +0x94: mov     w26, w0
      +0x98: cbz     w27, <mldsa65_verify_internal+0x3a4>
      +0x9c: ldp     q2, q3, [x24]
      +0xa0: sub     x0, x19, #0xe0
      +0xa4: ldp     q0, q1, [x24, #32]
      +0xa8: mov     x8, #0x2420
      +0xac: add     x1, x22, x8
      +0xb0: mov     x9, #0x2720
      +0xb4: str     x1, [sp, #104]
      +0xb8: add     x1, x22, x9
      +0xbc: str     x1, [sp, #112]
      +0xc0: stp     q2, q3, [x0]
      +0xc4: stp     q0, q1, [x0, #32]
      +0xc8: mov     x3, #0x1400
      +0xcc: mov     x0, x22
      +0xd0: add     x28, x22, x3
      +0xd4: bl      <mldsa65_polyvecl_ntt>
      +0xd8: mov     w21, #0x0
      +0xdc: ldr     x1, [sp, #96]
      +0xe0: mov     x4, #0x27a0
      +0xe4: add     x2, x22, x4
      +0xe8: mov     x5, #0x1c20
      +0xec: mov     x6, #0x2020
      +0xf0: mov     x19, x2
      +0xf4: add     x27, x22, x6
      +0xf8: mov     x0, x28
      +0xfc: add     x20, x22, x5
     +0x100: str     x2, [sp, #120]
     +0x104: bl      <mldsa65_polyvec_matrix_expand_lazy>
     +0x108: mov     x1, x19
     +0x10c: mov     x7, #0x1820
     +0x110: ldr     x24, [sp, #104]
     +0x114: mov     x0, x27
     +0x118: add     x19, x22, x7
     +0x11c: bl      <mldsa65_poly_challenge>
     +0x120: mov     x0, x27
     +0x124: bl      <mldsa_poly_ntt>
     +0x128: mov     w3, w21
     +0x12c: mov     x2, x22
     +0x130: mov     x1, x28
     +0x134: mov     x0, x20
     +0x138: bl      <mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy>
     +0x13c: ldr     x1, [sp, #96]
     +0x140: mov     w2, w21
     +0x144: mov     x0, x19
     +0x148: bl      <mldsa65_unpack_pk_t1>
     +0x14c: mov     x0, x19
     +0x150: bl      <mldsa_poly_shiftl>
     +0x154: mov     x0, x19
     +0x158: bl      <mldsa_poly_ntt>
     +0x15c: mov     x1, x27
     +0x160: mov     x0, x19
     +0x164: bl      <mldsa_poly_pointwise_montgomery>
     +0x168: mov     x1, x19
     +0x16c: mov     x0, x20
     +0x170: bl      <mldsa_poly_sub>
     +0x174: mov     x0, x20
     +0x178: bl      <mldsa_poly_reduce>
     +0x17c: mov     x0, x20
     +0x180: bl      <mldsa_poly_invntt_tomont>
     +0x184: mov     x0, x20
     +0x188: bl      <mldsa_poly_caddq>
     +0x18c: mov     w2, w21
     +0x190: mov     x1, x25
     +0x194: mov     x0, x19
     +0x198: bl      <mldsa65_sig_unpack_hints>
     +0x19c: mov     w23, w0
     +0x1a0: cbnz    w0, <mldsa65_verify_internal+0x44c>
     +0x1a4: mov     x1, x19
     +0x1a8: mov     x0, x20
     +0x1ac: bl      <mldsa65_poly_use_hint>
     +0x1b0: add     w21, w21, #0x1
     +0x1b4: mov     x0, x24
     +0x1b8: mov     x1, x20
     +0x1bc: bl      <mldsa_polyw1_pack_32>
     +0x1c0: add     x24, x24, #0x80
     +0x1c4: cmp     w21, #0x6
     +0x1c8: b.ne    <mldsa65_verify_internal+0x128>
     +0x1cc: mov     x1, #0x2760
     +0x1d0: mov     x0, #0x2868
     +0x1d4: add     x21, sp, x0
     +0x1d8: add     x24, x22, x1
     +0x1dc: mov     x0, x21
     +0x1e0: bl      <mldsa_shake256_init>
     +0x1e4: ldr     x1, [sp, #112]
     +0x1e8: mov     x0, x21
     +0x1ec: mov     x2, #0x40
     +0x1f0: bl      <mldsa_shake256_absorb>
     +0x1f4: ldr     x1, [sp, #104]
     +0x1f8: mov     x2, #0x300
     +0x1fc: mov     x0, x21
     +0x200: bl      <mldsa_shake256_absorb>
     +0x204: mov     x0, x21
     +0x208: bl      <mldsa_shake256_finalize>
     +0x20c: mov     x2, x21
     +0x210: mov     x1, #0x30
     +0x214: mov     x0, x24
     +0x218: bl      <mldsa_shake256_squeeze>
     +0x21c: mov     x0, x21
     +0x220: bl      <mldsa_shake256_release>
     +0x224: movi    v0.4s, #0x0
     +0x228: stp     q0, q0, [x21]
     +0x22c: stp     q0, q0, [x21, #32]
     +0x230: stp     q0, q0, [x21, #64]
     +0x234: stp     q0, q0, [x21, #96]
     +0x238: stp     q0, q0, [x21, #128]
     +0x23c: stp     q0, q0, [x21, #160]
     +0x240: str     q0, [x21, #192]
     +0x244: ldr     x0, [sp, #120]
     +0x248: mov     x1, x24
     +0x24c: mov     v2.16b, v0.16b
     +0x250: ldr     q1, [x0], #16
     +0x254: add     w26, w26, #0x1
     +0x258: ldr     q3, [x1], #16
     +0x25c: eor     v1.16b, v1.16b, v3.16b
     +0x260: orr     v2.16b, v2.16b, v1.16b
     +0x264: eor     v0.16b, v0.16b, v1.16b
     +0x268: cmp     w26, #0x3
     +0x26c: b.ne    <mldsa65_verify_internal+0x250>
     +0x270: movi    v1.4s, #0x0
     +0x274: ext     v5.16b, v2.16b, v1.16b, #8
     +0x278: ext     v3.16b, v0.16b, v1.16b, #8
     +0x27c: orr     v5.16b, v5.16b, v2.16b
     +0x280: eor     v2.16b, v3.16b, v0.16b
     +0x284: ext     v4.16b, v5.16b, v1.16b, #4
     +0x288: ext     v0.16b, v2.16b, v1.16b, #4
     +0x28c: orr     v4.16b, v4.16b, v5.16b
     +0x290: eor     v0.16b, v0.16b, v2.16b
     +0x294: ext     v3.16b, v4.16b, v1.16b, #2
     +0x298: ext     v2.16b, v0.16b, v1.16b, #2
     +0x29c: orr     v3.16b, v3.16b, v4.16b
     +0x2a0: eor     v2.16b, v2.16b, v0.16b
     +0x2a4: ext     v0.16b, v3.16b, v1.16b, #1
     +0x2a8: ext     v1.16b, v2.16b, v1.16b, #1
     +0x2ac: orr     v0.16b, v0.16b, v3.16b
     +0x2b0: eor     v1.16b, v1.16b, v2.16b
     +0x2b4: umov    w0, v0.b[0]
     +0x2b8: umov    w1, v1.b[0]
     +0x2bc: neg     x0, x0
     +0x2c0: asr     x0, x0, #32
     +0x2c4: eor     w0, w1, w0
     +0x2c8: cmp     w1, w0, uxtb
     +0x2cc: b.ne    <mldsa65_verify_internal+0x454>
     +0x2d0: mov     x0, x19
     +0x2d4: mov     x2, #0x400
     +0x2d8: mov     w1, #0x0
     +0x2dc: bl      <memset@plt>
     +0x2e0: mov     x2, #0x400
     +0x2e4: mov     x0, x20
     +0x2e8: mov     w1, #0x0
     +0x2ec: bl      <memset@plt>
     +0x2f0: mov     x2, #0x420
     +0x2f4: mov     x0, x28
     +0x2f8: mov     w1, #0x0
     +0x2fc: bl      <memset@plt>
     +0x300: mov     x2, #0x400
     +0x304: mov     x0, x27
     +0x308: mov     w1, #0x0
     +0x30c: bl      <memset@plt>
     +0x310: mov     x2, #0x1400
     +0x314: mov     x0, x22
     +0x318: mov     w1, #0x0
     +0x31c: bl      <memset@plt>
     +0x320: stp     xzr, xzr, [x24]
     +0x324: stp     xzr, xzr, [x24, #16]
     +0x328: stp     xzr, xzr, [x24, #32]
     +0x32c: ldr     x0, [sp, #120]
     +0x330: stp     xzr, xzr, [x0]
     +0x334: stp     xzr, xzr, [x0, #16]
     +0x338: stp     xzr, xzr, [x0, #32]
     +0x33c: ldr     x0, [sp, #112]
     +0x340: movi    v0.4s, #0x0
     +0x344: stp     q0, q0, [x0]
     +0x348: stp     q0, q0, [x0, #32]
     +0x34c: ldr     x19, [sp, #104]
     +0x350: mov     x2, #0x300
     +0x354: mov     w1, #0x0
     +0x358: mov     x0, x19
     +0x35c: bl      <memset@plt>
     +0x360: adrp    x0, <page>
     +0x364: ldr     x0, [x0, #4088]
     +0x368: ldr     x2, [sp, #10552]
     +0x36c: ldr     x1, [x0]
     +0x370: subs    x2, x2, x1
     +0x374: mov     x1, #0x0
     +0x378: b.ne    <mldsa65_verify_internal+0x4b0>
     +0x37c: ldp     x19, x20, [sp]
     +0x380: mov     w0, w23
     +0x384: ldp     x21, x22, [sp, #16]
     +0x388: mov     x12, #0x2940
     +0x38c: ldp     x23, x24, [sp, #32]
     +0x390: ldp     x25, x26, [sp, #48]
     +0x394: ldp     x27, x28, [sp, #64]
     +0x398: ldr     x30, [sp, #80]
     +0x39c: add     sp, sp, x12
     +0x3a0: ret
     +0x3a4: mov     x10, #0x2868
     +0x3a8: mov     x11, #0x2420
     +0x3ac: add     x19, sp, x10
     +0x3b0: add     x27, x22, x11
     +0x3b4: mov     x0, x19
     +0x3b8: str     x27, [sp, #104]
     +0x3bc: bl      <mldsa_shake256_init>
     +0x3c0: ldr     x1, [sp, #96]
     +0x3c4: mov     x2, #0x7a0
     +0x3c8: mov     x0, x19
     +0x3cc: bl      <mldsa_shake256_absorb>
     +0x3d0: mov     x0, x19
     +0x3d4: bl      <mldsa_shake256_finalize>
     +0x3d8: mov     x2, x19
     +0x3dc: mov     x1, #0x40
     +0x3e0: mov     x0, x27
     +0x3e4: bl      <mldsa_shake256_squeeze>
     +0x3e8: mov     x0, x19
     +0x3ec: bl      <mldsa_shake256_release>
     +0x3f0: movi    v0.4s, #0x0
     +0x3f4: stp     q0, q0, [x19]
     +0x3f8: stp     q0, q0, [x19, #32]
     +0x3fc: stp     q0, q0, [x19, #64]
     +0x400: stp     q0, q0, [x19, #96]
     +0x404: stp     q0, q0, [x19, #128]
     +0x408: stp     q0, q0, [x19, #160]
     +0x40c: str     q0, [x19, #192]
     +0x410: mov     x12, #0x2720
     +0x414: mov     x3, #0x40
     +0x418: add     x0, x22, x12
     +0x41c: mov     x7, x23
     +0x420: mov     x6, x24
     +0x424: mov     x5, x21
     +0x428: mov     x4, x20
     +0x42c: mov     x2, x27
     +0x430: mov     x1, x3
     +0x434: str     x0, [sp, #112]
     +0x438: bl      <mld_H65>
     +0x43c: movi    v0.4s, #0x0
     +0x440: stp     q0, q0, [x27]
     +0x444: stp     q0, q0, [x27, #32]
     +0x448: b       <mldsa65_verify_internal+0xc8>
     +0x44c: mov     x2, #0x2760
     +0x450: add     x24, x22, x2
     +0x454: mov     w23, #0xfffffffa
     +0x458: b       <mldsa65_verify_internal+0x2d0>
     +0x45c: mov     x13, #0x2420
     +0x460: add     x0, x22, x13
     +0x464: mov     x23, #0x27a0
     +0x468: mov     x21, #0x2720
     +0x46c: str     x0, [sp, #104]
     +0x470: add     x0, x22, x21
     +0x474: mov     x14, #0x1400
     +0x478: mov     x15, #0x2020
     +0x47c: mov     x16, #0x1c20
     +0x480: mov     x17, #0x1820
     +0x484: mov     x18, #0x2760
     +0x488: add     x28, x22, x14
     +0x48c: add     x27, x22, x15
     +0x490: add     x20, x22, x16
     +0x494: add     x19, x22, x17
     +0x498: add     x24, x22, x18
     +0x49c: str     x0, [sp, #112]
     +0x4a0: add     x0, x22, x23
     +0x4a4: mov     w23, #0xfffffffa
     +0x4a8: str     x0, [sp, #120]
     +0x4ac: b       <mldsa65_verify_internal+0x2d0>
     +0x4b0: bl      <__stack_chk_fail@plt>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa65_verify_internal"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The signature sigb at sig  *)
(* (3309 bytes), the message M of mlen bytes at m and the prefix PRE of      *)
(* prelen bytes at pre (or, if ext is nonzero as a 32-bit integer, mu in the *)
(* first 64 bytes at m), the public key pkb at pk (1952 bytes): the result   *)
(* is 0 if the signature is accepted, and -6 otherwise. The stack is the     *)
(* 40224 bytes of the function and those of the callees below them.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 12112),12112))
              [(sig,3309); (m,mlen); (pre,prelen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
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
                 [memory :> bytes(word_sub stackpointer (word 12112),12112)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the flag ext, the    *)
(* signature, the message, the prefix and the public key, all public, the    *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset may read and the constants of the callees, and the writes within   *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 12112),12112))
              [(sig,3309); (m,mlen); (pre,prelen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
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
                              guard mf pc (word_sub stackpointer (word 12112))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; pre,prelen; pk,1952;
                         word_sub stackpointer (word 12112),12112;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [word_sub stackpointer (word 12112),12112]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 12112),12112)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 12112),12112))
              [(sig,3309); (m,mlen); (pre,prelen); (pk,1952);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
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
                              guard mf pc (word_sub stackpointer (word 12112))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; pre,prelen; pk,1952;
                         word_sub stackpointer (word 12112),12112;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [word_sub stackpointer (word 12112),12112]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 12112),12112)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
