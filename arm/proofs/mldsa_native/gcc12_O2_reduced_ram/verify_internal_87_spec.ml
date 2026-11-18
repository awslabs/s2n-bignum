(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the statement. This is the code for          *)
(* mldsa87_verify_internal (mld_sign_verify_internal in sign.c) from         *)
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
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvecl_unpack_z_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvecl_chknorm_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvecl_ntt_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_expand_lazy_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_challenge_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/unpack_pk_t1_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_shiftl_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_pointwise_montgomery_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_sub_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_reduce_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_caddq_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/sig_unpack_hints_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_use_hint_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyw1_pack_32_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_absorb_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_finalize_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_squeeze_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/H_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa87_verify_internal:
       +0x0: mov     x12, #0x3250
       +0x4: sub     sp, sp, x12
       +0x8: stp     x19, x20, [sp]
       +0xc: mov     x20, x3
      +0x10: stp     x21, x22, [sp, #16]
      +0x14: add     x22, sp, #0x9f
      +0x18: and     x22, x22, #0xffffffffffffffe0
      +0x1c: stp     x23, x24, [sp, #32]
      +0x20: add     x19, x22, #0x3, lsl #12
      +0x24: add     x7, x19, #0x60
      +0x28: stp     x25, x26, [sp, #48]
      +0x2c: mov     x25, x0
      +0x30: mov     x26, x1
      +0x34: stp     x27, x28, [sp, #64]
      +0x38: mov     x24, x2
      +0x3c: mov     x23, x4
      +0x40: str     x30, [sp, #80]
      +0x44: mov     w27, w6
      +0x48: str     x5, [sp, #104]
      +0x4c: ldp     q2, q3, [x0]
      +0x50: ldp     q0, q1, [x0, #32]
      +0x54: adrp    x0, <page>
      +0x58: ldr     x0, [x0, #4088]
      +0x5c: ldr     x1, [x0]
      +0x60: str     x1, [sp, #12872]
      +0x64: mov     x1, #0x0
      +0x68: mov     x0, x22
      +0x6c: add     x1, x25, #0x40
      +0x70: stp     q2, q3, [x7]
      +0x74: stp     q0, q1, [x7, #32]
      +0x78: bl      <mldsa87_polyvecl_unpack_z>
      +0x7c: mov     w1, #0xff88
      +0x80: mov     x0, x22
      +0x84: movk    w1, #0x7, lsl #16
      +0x88: bl      <mldsa87_polyvecl_chknorm>
      +0x8c: cbnz    w0, <mldsa87_verify_internal+0x43c>
      +0x90: mov     w21, w0
      +0x94: cbz     w27, <mldsa87_verify_internal+0x388>
      +0x98: ldp     q2, q3, [x26]
      +0x9c: add     x0, x19, #0xa0
      +0xa0: ldp     q0, q1, [x26, #32]
      +0xa4: mov     x8, #0x2c20
      +0xa8: add     x1, x22, x8
      +0xac: mov     x9, #0x30a0
      +0xb0: str     x1, [sp, #112]
      +0xb4: add     x1, x22, x9
      +0xb8: str     x1, [sp, #120]
      +0xbc: stp     q2, q3, [x0]
      +0xc0: stp     q0, q1, [x0, #32]
      +0xc4: mov     x3, #0x1c00
      +0xc8: mov     x0, x22
      +0xcc: add     x27, x22, x3
      +0xd0: bl      <mldsa87_polyvecl_ntt>
      +0xd4: ldr     x1, [sp, #104]
      +0xd8: mov     x4, #0x3060
      +0xdc: mov     x5, #0x2420
      +0xe0: mov     x6, #0x2020
      +0xe4: mov     x7, #0x2820
      +0xe8: add     x28, x22, x4
      +0xec: add     x26, x22, x7
      +0xf0: mov     x0, x27
      +0xf4: add     x20, x22, x5
      +0xf8: add     x19, x22, x6
      +0xfc: bl      <mldsa87_polyvec_matrix_expand_lazy>
     +0x100: mov     x1, x28
     +0x104: mov     x0, x26
     +0x108: ldr     x24, [sp, #112]
     +0x10c: bl      <mldsa87_poly_challenge>
     +0x110: mov     x0, x26
     +0x114: bl      <mldsa_poly_ntt>
     +0x118: mov     w3, w21
     +0x11c: mov     x2, x22
     +0x120: mov     x1, x27
     +0x124: mov     x0, x20
     +0x128: bl      <mldsa87_polyvec_matrix_pointwise_montgomery_row_lazy>
     +0x12c: ldr     x1, [sp, #104]
     +0x130: mov     w2, w21
     +0x134: mov     x0, x19
     +0x138: bl      <mldsa87_unpack_pk_t1>
     +0x13c: mov     x0, x19
     +0x140: bl      <mldsa_poly_shiftl>
     +0x144: mov     x0, x19
     +0x148: bl      <mldsa_poly_ntt>
     +0x14c: mov     x1, x26
     +0x150: mov     x0, x19
     +0x154: bl      <mldsa_poly_pointwise_montgomery>
     +0x158: mov     x1, x19
     +0x15c: mov     x0, x20
     +0x160: bl      <mldsa_poly_sub>
     +0x164: mov     x0, x20
     +0x168: bl      <mldsa_poly_reduce>
     +0x16c: mov     x0, x20
     +0x170: bl      <mldsa_poly_invntt_tomont>
     +0x174: mov     x0, x20
     +0x178: bl      <mldsa_poly_caddq>
     +0x17c: mov     w2, w21
     +0x180: mov     x1, x25
     +0x184: mov     x0, x19
     +0x188: bl      <mldsa87_sig_unpack_hints>
     +0x18c: mov     w23, w0
     +0x190: cbnz    w0, <mldsa87_verify_internal+0x42c>
     +0x194: mov     x1, x19
     +0x198: mov     x0, x20
     +0x19c: bl      <mldsa87_poly_use_hint>
     +0x1a0: add     w21, w21, #0x1
     +0x1a4: mov     x0, x24
     +0x1a8: mov     x1, x20
     +0x1ac: bl      <mldsa_polyw1_pack_32>
     +0x1b0: add     x24, x24, #0x80
     +0x1b4: cmp     w21, #0x8
     +0x1b8: b.ne    <mldsa87_verify_internal+0x118>
     +0x1bc: mov     x1, #0x3020
     +0x1c0: mov     x0, #0x3178
     +0x1c4: add     x21, sp, x0
     +0x1c8: add     x24, x22, x1
     +0x1cc: mov     x0, x21
     +0x1d0: bl      <mldsa_shake256_init>
     +0x1d4: ldr     x1, [sp, #120]
     +0x1d8: mov     x0, x21
     +0x1dc: mov     x2, #0x40
     +0x1e0: bl      <mldsa_shake256_absorb>
     +0x1e4: ldr     x1, [sp, #112]
     +0x1e8: mov     x2, #0x400
     +0x1ec: mov     x0, x21
     +0x1f0: bl      <mldsa_shake256_absorb>
     +0x1f4: mov     x0, x21
     +0x1f8: bl      <mldsa_shake256_finalize>
     +0x1fc: mov     x2, x21
     +0x200: mov     x1, #0x40
     +0x204: mov     x0, x24
     +0x208: bl      <mldsa_shake256_squeeze>
     +0x20c: mov     x0, x21
     +0x210: bl      <mldsa_shake256_release>
     +0x214: movi    v0.4s, #0x0
     +0x218: stp     q0, q0, [x21]
     +0x21c: stp     q0, q0, [x21, #32]
     +0x220: stp     q0, q0, [x21, #64]
     +0x224: stp     q0, q0, [x21, #96]
     +0x228: stp     q0, q0, [x21, #128]
     +0x22c: stp     q0, q0, [x21, #160]
     +0x230: str     q0, [x21, #192]
     +0x234: mov     v2.16b, v0.16b
     +0x238: mov     x0, x24
     +0x23c: mov     x1, x28
     +0x240: add     x2, x24, #0x40
     +0x244: ldr     q1, [x1], #16
     +0x248: ldr     q3, [x0], #16
     +0x24c: eor     v1.16b, v1.16b, v3.16b
     +0x250: orr     v2.16b, v2.16b, v1.16b
     +0x254: eor     v0.16b, v0.16b, v1.16b
     +0x258: cmp     x2, x0
     +0x25c: b.ne    <mldsa87_verify_internal+0x244>
     +0x260: movi    v1.4s, #0x0
     +0x264: ext     v5.16b, v2.16b, v1.16b, #8
     +0x268: ext     v3.16b, v0.16b, v1.16b, #8
     +0x26c: orr     v5.16b, v5.16b, v2.16b
     +0x270: eor     v2.16b, v3.16b, v0.16b
     +0x274: ext     v4.16b, v5.16b, v1.16b, #4
     +0x278: ext     v0.16b, v2.16b, v1.16b, #4
     +0x27c: orr     v4.16b, v4.16b, v5.16b
     +0x280: eor     v0.16b, v0.16b, v2.16b
     +0x284: ext     v3.16b, v4.16b, v1.16b, #2
     +0x288: ext     v2.16b, v0.16b, v1.16b, #2
     +0x28c: orr     v3.16b, v3.16b, v4.16b
     +0x290: eor     v2.16b, v2.16b, v0.16b
     +0x294: ext     v0.16b, v3.16b, v1.16b, #1
     +0x298: ext     v1.16b, v2.16b, v1.16b, #1
     +0x29c: orr     v0.16b, v0.16b, v3.16b
     +0x2a0: eor     v1.16b, v1.16b, v2.16b
     +0x2a4: umov    w0, v0.b[0]
     +0x2a8: umov    w1, v1.b[0]
     +0x2ac: neg     x0, x0
     +0x2b0: asr     x0, x0, #32
     +0x2b4: eor     w0, w1, w0
     +0x2b8: cmp     w1, w0, uxtb
     +0x2bc: b.ne    <mldsa87_verify_internal+0x434>
     +0x2c0: mov     x0, x19
     +0x2c4: mov     x2, #0x400
     +0x2c8: mov     w1, #0x0
     +0x2cc: bl      <memset@plt>
     +0x2d0: mov     x2, #0x400
     +0x2d4: mov     x0, x20
     +0x2d8: mov     w1, #0x0
     +0x2dc: bl      <memset@plt>
     +0x2e0: mov     x2, #0x420
     +0x2e4: mov     x0, x27
     +0x2e8: mov     w1, #0x0
     +0x2ec: bl      <memset@plt>
     +0x2f0: mov     x2, #0x400
     +0x2f4: mov     x0, x26
     +0x2f8: mov     w1, #0x0
     +0x2fc: bl      <memset@plt>
     +0x300: mov     x2, #0x1c00
     +0x304: mov     x0, x22
     +0x308: mov     w1, #0x0
     +0x30c: bl      <memset@plt>
     +0x310: movi    v0.4s, #0x0
     +0x314: stp     q0, q0, [x24]
     +0x318: stp     q0, q0, [x24, #32]
     +0x31c: stp     q0, q0, [x28]
     +0x320: stp     q0, q0, [x28, #32]
     +0x324: ldr     x0, [sp, #120]
     +0x328: stp     q0, q0, [x0]
     +0x32c: stp     q0, q0, [x0, #32]
     +0x330: ldr     x19, [sp, #112]
     +0x334: mov     x2, #0x400
     +0x338: mov     w1, #0x0
     +0x33c: mov     x0, x19
     +0x340: bl      <memset@plt>
     +0x344: adrp    x0, <page>
     +0x348: ldr     x0, [x0, #4088]
     +0x34c: ldr     x2, [sp, #12872]
     +0x350: ldr     x1, [x0]
     +0x354: subs    x2, x2, x1
     +0x358: mov     x1, #0x0
     +0x35c: b.ne    <mldsa87_verify_internal+0x48c>
     +0x360: ldp     x19, x20, [sp]
     +0x364: mov     w0, w23
     +0x368: ldp     x21, x22, [sp, #16]
     +0x36c: mov     x12, #0x3250
     +0x370: ldp     x23, x24, [sp, #32]
     +0x374: ldp     x25, x26, [sp, #48]
     +0x378: ldp     x27, x28, [sp, #64]
     +0x37c: ldr     x30, [sp, #80]
     +0x380: add     sp, sp, x12
     +0x384: ret
     +0x388: mov     x10, #0x3178
     +0x38c: mov     x11, #0x2c20
     +0x390: add     x19, sp, x10
     +0x394: add     x27, x22, x11
     +0x398: mov     x0, x19
     +0x39c: str     x27, [sp, #112]
     +0x3a0: bl      <mldsa_shake256_init>
     +0x3a4: ldr     x1, [sp, #104]
     +0x3a8: mov     x2, #0xa20
     +0x3ac: mov     x0, x19
     +0x3b0: bl      <mldsa_shake256_absorb>
     +0x3b4: mov     x0, x19
     +0x3b8: bl      <mldsa_shake256_finalize>
     +0x3bc: mov     x2, x19
     +0x3c0: mov     x1, #0x40
     +0x3c4: mov     x0, x27
     +0x3c8: bl      <mldsa_shake256_squeeze>
     +0x3cc: mov     x0, x19
     +0x3d0: bl      <mldsa_shake256_release>
     +0x3d4: movi    v0.4s, #0x0
     +0x3d8: stp     q0, q0, [x19]
     +0x3dc: stp     q0, q0, [x19, #32]
     +0x3e0: stp     q0, q0, [x19, #64]
     +0x3e4: stp     q0, q0, [x19, #96]
     +0x3e8: stp     q0, q0, [x19, #128]
     +0x3ec: stp     q0, q0, [x19, #160]
     +0x3f0: str     q0, [x19, #192]
     +0x3f4: mov     x12, #0x30a0
     +0x3f8: mov     x6, x24
     +0x3fc: add     x0, x22, x12
     +0x400: mov     x5, x26
     +0x404: mov     x4, x23
     +0x408: mov     x3, x20
     +0x40c: mov     x1, x27
     +0x410: mov     x2, #0x40
     +0x414: str     x0, [sp, #120]
     +0x418: bl      <mld_H87.constprop.0>
     +0x41c: movi    v0.4s, #0x0
     +0x420: stp     q0, q0, [x27]
     +0x424: stp     q0, q0, [x27, #32]
     +0x428: b       <mldsa87_verify_internal+0xc4>
     +0x42c: mov     x2, #0x3020
     +0x430: add     x24, x22, x2
     +0x434: mov     w23, #0xfffffffa
     +0x438: b       <mldsa87_verify_internal+0x2c0>
     +0x43c: mov     x23, #0x30a0
     +0x440: mov     x13, #0x2c20
     +0x444: add     x0, x22, x13
     +0x448: mov     x14, #0x1c00
     +0x44c: mov     x15, #0x3060
     +0x450: mov     x16, #0x2820
     +0x454: mov     x17, #0x2420
     +0x458: mov     x18, #0x2020
     +0x45c: mov     x21, #0x3020
     +0x460: add     x27, x22, x14
     +0x464: add     x28, x22, x15
     +0x468: add     x26, x22, x16
     +0x46c: add     x20, x22, x17
     +0x470: add     x19, x22, x18
     +0x474: add     x24, x22, x21
     +0x478: str     x0, [sp, #112]
     +0x47c: add     x0, x22, x23
     +0x480: mov     w23, #0xfffffffa
     +0x484: str     x0, [sp, #120]
     +0x488: b       <mldsa87_verify_internal+0x2c0>
     +0x48c: bl      <__stack_chk_fail@plt>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa87_verify_internal"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The signature sigb at sig  *)
(* (4627 bytes), the message M of mlen bytes at m and the prefix PRE of      *)
(* prelen bytes at pre (or, if ext is nonzero as a 32-bit integer, mu in the *)
(* first 64 bytes at m), the public key pkb at pk (2592 bytes): the result   *)
(* is 0 if the signature is accepted, and -6 otherwise. The stack is the     *)
(* 69168 bytes of the function and those of the callees below them.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 14432),14432))
              [(sig,4627); (m,mlen); (pre,prelen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
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
                 [memory :> bytes(word_sub stackpointer (word 14432),14432)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the flag ext, the    *)
(* signature, the message, the prefix and the public key, all public, the    *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset may read and the constants of the callees, and the writes within   *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 14432),14432))
              [(sig,4627); (m,mlen); (pre,prelen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
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
                              guard mf pc (word_sub stackpointer (word 14432))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; pre,prelen; pk,2592;
                         word_sub stackpointer (word 14432),14432;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [word_sub stackpointer (word 14432),14432]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 14432),14432)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 14432),14432))
              [(sig,4627); (m,mlen); (pre,prelen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
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
                              guard mf pc (word_sub stackpointer (word 14432))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; pre,prelen; pk,2592;
                         word_sub stackpointer (word 14432),14432;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [word_sub stackpointer (word 14432),14432]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 14432),14432)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
