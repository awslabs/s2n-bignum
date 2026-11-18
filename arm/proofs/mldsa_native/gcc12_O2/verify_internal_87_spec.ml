(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the statement. This is the code for          *)
(* mldsa87_verify_internal (mld_sign_verify_internal in sign.c) from         *)
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
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_unpack_z_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_chknorm_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_ntt_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvec_matrix_expand_eager_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_challenge_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvec_matrix_pointwise_montgomery_row_eager_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/unpack_pk_t1_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_shiftl_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_pointwise_montgomery_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_sub_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_reduce_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_caddq_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/sig_unpack_hints_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_use_hint_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyw1_pack_32_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_absorb_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_finalize_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_squeeze_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/H_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa87_verify_internal:
       +0x0: sub     sp, sp, #0xe30
       +0x4: sub     sp, sp, #0x10, lsl #12
       +0x8: stp     x19, x20, [sp]
       +0xc: mov     x20, x2
      +0x10: mov     x19, x4
      +0x14: stp     x21, x22, [sp, #16]
      +0x18: mov     x22, x3
      +0x1c: stp     x23, x24, [sp, #32]
      +0x20: add     x23, sp, #0x9f
      +0x24: and     x23, x23, #0xffffffffffffffe0
      +0x28: stp     x25, x26, [sp, #48]
      +0x2c: mov     x25, x0
      +0x30: add     x26, x23, #0xe, lsl #12
      +0x34: stp     x27, x28, [sp, #64]
      +0x38: add     x28, x23, #0x10, lsl #12
      +0x3c: mov     x27, x1
      +0x40: str     x30, [sp, #80]
      +0x44: add     x1, sp, #0x10, lsl #12
      +0x48: str     x5, [sp, #96]
      +0x4c: add     x1, x1, #0x20
      +0x50: ldp     q2, q3, [x0]
      +0x54: add     x28, x28, #0xc00
      +0x58: ldp     q0, q1, [x0, #32]
      +0x5c: add     x7, x28, #0x40
      +0x60: adrp    x0, <page>
      +0x64: ldr     x0, [x0, #4088]
      +0x68: mov     w24, w6
      +0x6c: ldr     x2, [x0]
      +0x70: str     x2, [x1, #3592]
      +0x74: mov     x2, #0x0
      +0x78: mov     x0, x26
      +0x7c: add     x1, x25, #0x40
      +0x80: stp     q2, q3, [x7]
      +0x84: stp     q0, q1, [x7, #32]
      +0x88: bl      <mldsa87_polyvecl_unpack_z>
      +0x8c: mov     w1, #0xff88
      +0x90: mov     x0, x26
      +0x94: movk    w1, #0x7, lsl #16
      +0x98: bl      <mldsa87_polyvecl_chknorm>
      +0x9c: cbnz    w0, <+0x448>
      +0xa0: mov     w21, w0
      +0xa4: cbz     w24, <+0x39c>
      +0xa8: add     x1, x23, #0x10, lsl #12
      +0xac: add     x0, x28, #0x80
      +0xb0: ldp     q2, q3, [x27]
      +0xb4: add     x1, x1, #0x800
      +0xb8: ldp     q0, q1, [x27, #32]
      +0xbc: str     x1, [sp, #104]
      +0xc0: add     x1, x23, #0x10, lsl #12
      +0xc4: stp     q2, q3, [x0]
      +0xc8: add     x1, x1, #0xc80
      +0xcc: str     x1, [sp, #112]
      +0xd0: stp     q0, q1, [x0, #32]
      +0xd4: add     x1, x23, #0x10, lsl #12
      +0xd8: add     x1, x1, #0xc40
      +0xdc: mov     x0, x26
      +0xe0: mov     x19, x1
      +0xe4: str     x1, [sp, #120]
      +0xe8: add     x27, x23, #0x10, lsl #12
      +0xec: add     x20, x23, #0x10, lsl #12
      +0xf0: bl      <mldsa87_polyvecl_ntt>
      +0xf4: add     x27, x27, #0x400
      +0xf8: ldr     x1, [sp, #96]
      +0xfc: mov     x0, x23
     +0x100: bl      <mldsa87_polyvec_matrix_expand_eager>
     +0x104: mov     x1, x19
     +0x108: mov     x0, #0xfc00
     +0x10c: ldr     x24, [sp, #104]
     +0x110: add     x19, x23, x0
     +0x114: mov     x0, x27
     +0x118: bl      <mldsa87_poly_challenge>
     +0x11c: mov     x0, x27
     +0x120: bl      <mldsa_poly_ntt>
     +0x124: nop
     +0x128: mov     w3, w21
     +0x12c: mov     x2, x26
     +0x130: mov     x1, x23
     +0x134: mov     x0, x20
     +0x138: bl      <mldsa87_polyvec_matrix_pointwise_montgomery_row_eager>
     +0x13c: ldr     x1, [sp, #96]
     +0x140: mov     w2, w21
     +0x144: mov     x0, x19
     +0x148: bl      <mldsa87_unpack_pk_t1>
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
     +0x198: bl      <mldsa87_sig_unpack_hints>
     +0x19c: mov     w22, w0
     +0x1a0: cbnz    w0, <+0x480>
     +0x1a4: mov     x1, x19
     +0x1a8: mov     x0, x20
     +0x1ac: bl      <mldsa87_poly_use_hint>
     +0x1b0: add     w21, w21, #0x1
     +0x1b4: mov     x0, x24
     +0x1b8: mov     x1, x20
     +0x1bc: bl      <mldsa_polyw1_pack_32>
     +0x1c0: add     x24, x24, #0x80
     +0x1c4: cmp     w21, #0x8
     +0x1c8: b.ne    <+0x128>
     +0x1cc: add     x21, sp, #0x10, lsl #12
     +0x1d0: add     x21, x21, #0xd58
     +0x1d4: mov     x0, x21
     +0x1d8: bl      <mldsa_shake256_init>
     +0x1dc: ldr     x1, [sp, #112]
     +0x1e0: mov     x0, x21
     +0x1e4: mov     x2, #0x40
     +0x1e8: bl      <mldsa_shake256_absorb>
     +0x1ec: ldr     x1, [sp, #104]
     +0x1f0: mov     x2, #0x400
     +0x1f4: mov     x0, x21
     +0x1f8: bl      <mldsa_shake256_absorb>
     +0x1fc: mov     x0, x21
     +0x200: bl      <mldsa_shake256_finalize>
     +0x204: mov     x2, x21
     +0x208: mov     x1, #0x40
     +0x20c: mov     x0, x28
     +0x210: bl      <mldsa_shake256_squeeze>
     +0x214: mov     x0, x21
     +0x218: bl      <mldsa_shake256_release>
     +0x21c: movi    v0.4s, #0x0
     +0x220: stp     q0, q0, [x21]
     +0x224: stp     q0, q0, [x21, #32]
     +0x228: stp     q0, q0, [x21, #64]
     +0x22c: stp     q0, q0, [x21, #96]
     +0x230: stp     q0, q0, [x21, #128]
     +0x234: stp     q0, q0, [x21, #160]
     +0x238: str     q0, [x21, #192]
     +0x23c: ldr     x1, [sp, #120]
     +0x240: mov     x0, x28
     +0x244: mov     v2.16b, v0.16b
     +0x248: add     x2, x28, #0x40
     +0x24c: ldr     q1, [x1], #16
     +0x250: ldr     q3, [x0], #16
     +0x254: eor     v1.16b, v1.16b, v3.16b
     +0x258: orr     v2.16b, v2.16b, v1.16b
     +0x25c: eor     v0.16b, v0.16b, v1.16b
     +0x260: cmp     x2, x0
     +0x264: b.ne    <+0x24c>
     +0x268: movi    v1.4s, #0x0
     +0x26c: ext     v5.16b, v2.16b, v1.16b, #8
     +0x270: ext     v3.16b, v0.16b, v1.16b, #8
     +0x274: orr     v5.16b, v5.16b, v2.16b
     +0x278: eor     v2.16b, v3.16b, v0.16b
     +0x27c: ext     v4.16b, v5.16b, v1.16b, #4
     +0x280: ext     v0.16b, v2.16b, v1.16b, #4
     +0x284: orr     v4.16b, v4.16b, v5.16b
     +0x288: eor     v0.16b, v0.16b, v2.16b
     +0x28c: ext     v3.16b, v4.16b, v1.16b, #2
     +0x290: ext     v2.16b, v0.16b, v1.16b, #2
     +0x294: orr     v3.16b, v3.16b, v4.16b
     +0x298: eor     v2.16b, v2.16b, v0.16b
     +0x29c: ext     v0.16b, v3.16b, v1.16b, #1
     +0x2a0: ext     v1.16b, v2.16b, v1.16b, #1
     +0x2a4: orr     v0.16b, v0.16b, v3.16b
     +0x2a8: eor     v1.16b, v1.16b, v2.16b
     +0x2ac: umov    w0, v0.b[0]
     +0x2b0: umov    w1, v1.b[0]
     +0x2b4: neg     x0, x0
     +0x2b8: asr     x0, x0, #32
     +0x2bc: eor     w0, w1, w0
     +0x2c0: cmp     w1, w0, uxtb
     +0x2c4: b.ne    <+0x480>
     +0x2c8: mov     x0, x19
     +0x2cc: mov     x2, #0x400
     +0x2d0: mov     w1, #0x0
     +0x2d4: bl      <memset@plt>
     +0x2d8: mov     x2, #0x400
     +0x2dc: mov     x0, x20
     +0x2e0: mov     w1, #0x0
     +0x2e4: bl      <memset@plt>
     +0x2e8: mov     x2, #0xe000
     +0x2ec: mov     x0, x23
     +0x2f0: mov     w1, #0x0
     +0x2f4: bl      <memset@plt>
     +0x2f8: mov     x2, #0x400
     +0x2fc: mov     x0, x27
     +0x300: mov     w1, #0x0
     +0x304: bl      <memset@plt>
     +0x308: mov     x2, #0x1c00
     +0x30c: mov     x0, x26
     +0x310: mov     w1, #0x0
     +0x314: bl      <memset@plt>
     +0x318: movi    v0.4s, #0x0
     +0x31c: stp     q0, q0, [x28]
     +0x320: stp     q0, q0, [x28, #32]
     +0x324: ldr     x0, [sp, #120]
     +0x328: stp     q0, q0, [x0]
     +0x32c: stp     q0, q0, [x0, #32]
     +0x330: ldr     x0, [sp, #112]
     +0x334: stp     q0, q0, [x0]
     +0x338: stp     q0, q0, [x0, #32]
     +0x33c: ldr     x19, [sp, #104]
     +0x340: mov     x2, #0x400
     +0x344: mov     w1, #0x0
     +0x348: mov     x0, x19
     +0x34c: bl      <memset@plt>
     +0x350: adrp    x0, <page>
     +0x354: ldr     x0, [x0, #4088]
     +0x358: add     x2, sp, #0x10, lsl #12
     +0x35c: add     x2, x2, #0x20
     +0x360: ldr     x3, [x2, #3592]
     +0x364: ldr     x1, [x0]
     +0x368: subs    x3, x3, x1
     +0x36c: mov     x1, #0x0
     +0x370: b.ne    <+0x488>
     +0x374: ldp     x19, x20, [sp]
     +0x378: mov     w0, w22
     +0x37c: ldp     x21, x22, [sp, #16]
     +0x380: ldp     x23, x24, [sp, #32]
     +0x384: ldp     x25, x26, [sp, #48]
     +0x388: ldp     x27, x28, [sp, #64]
     +0x38c: ldr     x30, [sp, #80]
     +0x390: add     sp, sp, #0xe30
     +0x394: add     sp, sp, #0x10, lsl #12
     +0x398: ret
     +0x39c: add     x24, sp, #0x10, lsl #12
     +0x3a0: add     x0, x23, #0x10, lsl #12
     +0x3a4: add     x24, x24, #0xd58
     +0x3a8: add     x0, x0, #0x800
     +0x3ac: str     x0, [sp, #104]
     +0x3b0: mov     x0, x24
     +0x3b4: bl      <mldsa_shake256_init>
     +0x3b8: ldr     x1, [sp, #96]
     +0x3bc: mov     x2, #0xa20
     +0x3c0: mov     x0, x24
     +0x3c4: bl      <mldsa_shake256_absorb>
     +0x3c8: mov     x0, x24
     +0x3cc: bl      <mldsa_shake256_finalize>
     +0x3d0: ldr     x0, [sp, #104]
     +0x3d4: mov     x2, x24
     +0x3d8: mov     x1, #0x40
     +0x3dc: bl      <mldsa_shake256_squeeze>
     +0x3e0: mov     x0, x24
     +0x3e4: bl      <mldsa_shake256_release>
     +0x3e8: movi    v0.4s, #0x0
     +0x3ec: stp     q0, q0, [x24]
     +0x3f0: stp     q0, q0, [x24, #32]
     +0x3f4: stp     q0, q0, [x24, #64]
     +0x3f8: stp     q0, q0, [x24, #96]
     +0x3fc: stp     q0, q0, [x24, #128]
     +0x400: stp     q0, q0, [x24, #160]
     +0x404: str     q0, [x24, #192]
     +0x408: mov     x4, x19
     +0x40c: add     x1, x23, #0x10, lsl #12
     +0x410: ldr     x19, [sp, #104]
     +0x414: add     x1, x1, #0xc80
     +0x418: mov     x0, x1
     +0x41c: mov     x6, x20
     +0x420: mov     x5, x27
     +0x424: mov     x3, x22
     +0x428: mov     x2, #0x40
     +0x42c: str     x1, [sp, #112]
     +0x430: mov     x1, x19
     +0x434: bl      <mld_H87>
     +0x438: movi    v0.4s, #0x0
     +0x43c: stp     q0, q0, [x19]
     +0x440: stp     q0, q0, [x19, #32]
     +0x444: b       <+0xd4>
     +0x448: add     x0, x23, #0x10, lsl #12
     +0x44c: add     x27, x23, #0x10, lsl #12
     +0x450: add     x0, x0, #0x800
     +0x454: str     x0, [sp, #104]
     +0x458: add     x0, x23, #0x10, lsl #12
     +0x45c: mov     x1, #0xfc00
     +0x460: add     x0, x0, #0xc80
     +0x464: add     x27, x27, #0x400
     +0x468: add     x20, x23, #0x10, lsl #12
     +0x46c: add     x19, x23, x1
     +0x470: str     x0, [sp, #112]
     +0x474: add     x0, x23, #0x10, lsl #12
     +0x478: add     x0, x0, #0xc40
     +0x47c: str     x0, [sp, #120]
     +0x480: mov     w22, #0xfffffffa
     +0x484: b       <+0x2c8>
     +0x488: bl      <__stack_chk_fail@plt>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_verify_internal"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The signature sigb at sig  *)
(* (4627 bytes), the message M of mlen bytes at m and the prefix PRE of      *)
(* prelen bytes at pre (or, if ext is nonzero as a 32-bit integer, mu in the *)
(* first 64 bytes at m), the public key pkb at pk (2592 bytes): the result   *)
(* is 0 if the signature is accepted, and -6 otherwise. The stack is the     *)
(* 69168 bytes of the function and those of the callees below them.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 74224),74224))
              [(sig,4627); (m,mlen); (pre,prelen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
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
                 [memory :> bytes(word_sub stackpointer (word 74224),74224)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the flag ext, the    *)
(* signature, the message, the prefix and the public key, all public, the    *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset may read and the constants of the callees, and the writes within   *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 74224),74224))
              [(sig,4627); (m,mlen); (pre,prelen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
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
                              guard mf pc (word_sub stackpointer (word 74224))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; pre,prelen; pk,2592;
                         word_sub stackpointer (word 74224),74224;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const2),16]
                        [word_sub stackpointer (word 74224),74224]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74224),74224)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 74224),74224))
              [(sig,4627); (m,mlen); (pre,prelen); (pk,2592);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
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
                              guard mf pc (word_sub stackpointer (word 74224))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; pre,prelen; pk,2592;
                         word_sub stackpointer (word 74224),74224;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const2),16]
                        [word_sub stackpointer (word 74224),74224]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 74224),74224)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
