(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Verification of a signature: the statement. This is the code for          *)
(* mldsa44_verify_internal (mld_sign_verify_internal in sign.c) from         *)
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
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvecl_unpack_z_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvecl_chknorm_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvecl_ntt_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_expand_lazy_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_challenge_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_ntt_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyvec_matrix_pointwise_montgomery_row_lazy_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/unpack_pk_t1_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_shiftl_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_pointwise_montgomery_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_sub_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_reduce_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_invntt_tomont_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_caddq_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/sig_unpack_hints_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_use_hint_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/polyw1_pack_88_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_absorb_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_finalize_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_squeeze_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/shake256_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/H_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa44_verify_internal:
       +0x0: mov     x12, #0x2510
       +0x4: sub     sp, sp, x12
       +0x8: stp     x25, x26, [sp, #48]
       +0xc: mov     x25, x0
      +0x10: mov     x26, x1
      +0x14: stp     x19, x20, [sp]
      +0x18: add     x20, sp, #0x9f
      +0x1c: and     x20, x20, #0xffffffffffffffe0
      +0x20: stp     x21, x22, [sp, #16]
      +0x24: mov     x19, #0x2400
      +0x28: add     x19, x20, x19
      +0x2c: stp     x23, x24, [sp, #32]
      +0x30: mov     x21, x3
      +0x34: mov     x24, x2
      +0x38: stp     x27, x28, [sp, #64]
      +0x3c: mov     x23, x4
      +0x40: mov     w27, w6
      +0x44: str     x30, [sp, #80]
      +0x48: adrp    x0, <page>
      +0x4c: ldr     x0, [x0, #4088]
      +0x50: str     x5, [sp, #104]
      +0x54: ldp     q0, q1, [x25]
      +0x58: ldr     x1, [x0]
      +0x5c: str     x1, [sp, #9480]
      +0x60: mov     x1, #0x0
      +0x64: add     x1, x25, #0x20
      +0x68: mov     x0, x20
      +0x6c: stp     q0, q1, [x19, #-128]
      +0x70: bl      <mldsa44_polyvecl_unpack_z>
      +0x74: mov     w1, #0xffb2
      +0x78: mov     x0, x20
      +0x7c: movk    w1, #0x1, lsl #16
      +0x80: bl      <mldsa44_polyvecl_chknorm>
      +0x84: cbnz    w0, <mldsa44_verify_internal+0x428>
      +0x88: mov     w22, w0
      +0x8c: cbz     w27, <mldsa44_verify_internal+0x374>
      +0x90: ldp     q2, q3, [x26]
      +0x94: sub     x19, x19, #0xe0
      +0x98: ldp     q0, q1, [x26, #32]
      +0x9c: mov     x7, #0x2020
      +0xa0: mov     x8, #0x2320
      +0xa4: add     x28, x20, x7
      +0xa8: add     x27, x20, x8
      +0xac: stp     q2, q3, [x19]
      +0xb0: stp     q0, q1, [x19, #32]
      +0xb4: add     x1, x20, #0x1, lsl #12
      +0xb8: mov     x3, #0x1820
      +0xbc: mov     x4, #0x1c20
      +0xc0: mov     x19, x1
      +0xc4: add     x26, x20, x4
      +0xc8: add     x21, x20, x3
      +0xcc: mov     x0, x20
      +0xd0: str     x1, [sp, #112]
      +0xd4: bl      <mldsa44_polyvecl_ntt>
      +0xd8: ldr     x1, [sp, #104]
      +0xdc: mov     x5, #0x2380
      +0xe0: add     x2, x20, x5
      +0xe4: mov     x0, x19
      +0xe8: mov     x19, x2
      +0xec: str     x2, [sp, #120]
      +0xf0: mov     x24, x28
      +0xf4: bl      <mldsa44_polyvec_matrix_expand_lazy>
      +0xf8: mov     x1, x19
      +0xfc: mov     x6, #0x1420
     +0x100: mov     x0, x26
     +0x104: add     x19, x20, x6
     +0x108: bl      <mldsa44_poly_challenge>
     +0x10c: mov     x0, x26
     +0x110: bl      <mldsa_poly_ntt>
     +0x114: ldr     x1, [sp, #112]
     +0x118: mov     w3, w22
     +0x11c: mov     x2, x20
     +0x120: mov     x0, x21
     +0x124: bl      <mldsa44_polyvec_matrix_pointwise_montgomery_row_lazy>
     +0x128: ldr     x1, [sp, #104]
     +0x12c: mov     w2, w22
     +0x130: mov     x0, x19
     +0x134: bl      <mldsa44_unpack_pk_t1>
     +0x138: mov     x0, x19
     +0x13c: bl      <mldsa_poly_shiftl>
     +0x140: mov     x0, x19
     +0x144: bl      <mldsa_poly_ntt>
     +0x148: mov     x1, x26
     +0x14c: mov     x0, x19
     +0x150: bl      <mldsa_poly_pointwise_montgomery>
     +0x154: mov     x1, x19
     +0x158: mov     x0, x21
     +0x15c: bl      <mldsa_poly_sub>
     +0x160: mov     x0, x21
     +0x164: bl      <mldsa_poly_reduce>
     +0x168: mov     x0, x21
     +0x16c: bl      <mldsa_poly_invntt_tomont>
     +0x170: mov     x0, x21
     +0x174: bl      <mldsa_poly_caddq>
     +0x178: mov     w2, w22
     +0x17c: mov     x1, x25
     +0x180: mov     x0, x19
     +0x184: bl      <mldsa44_sig_unpack_hints>
     +0x188: mov     w23, w0
     +0x18c: cbnz    w0, <mldsa44_verify_internal+0x418>
     +0x190: mov     x1, x19
     +0x194: mov     x0, x21
     +0x198: bl      <mldsa44_poly_use_hint>
     +0x19c: add     w22, w22, #0x1
     +0x1a0: mov     x0, x24
     +0x1a4: mov     x1, x21
     +0x1a8: bl      <mldsa_polyw1_pack_88>
     +0x1ac: add     x24, x24, #0xc0
     +0x1b0: cmp     w22, #0x4
     +0x1b4: b.ne    <mldsa44_verify_internal+0x114>
     +0x1b8: mov     x1, #0x2360
     +0x1bc: mov     x0, #0x2438
     +0x1c0: add     x24, sp, x0
     +0x1c4: add     x22, x20, x1
     +0x1c8: mov     x0, x24
     +0x1cc: bl      <mldsa_shake256_init>
     +0x1d0: mov     x0, x24
     +0x1d4: mov     x1, x27
     +0x1d8: mov     x2, #0x40
     +0x1dc: bl      <mldsa_shake256_absorb>
     +0x1e0: mov     x1, x28
     +0x1e4: mov     x2, #0x300
     +0x1e8: mov     x0, x24
     +0x1ec: bl      <mldsa_shake256_absorb>
     +0x1f0: mov     x0, x24
     +0x1f4: bl      <mldsa_shake256_finalize>
     +0x1f8: mov     x2, x24
     +0x1fc: mov     x1, #0x20
     +0x200: mov     x0, x22
     +0x204: bl      <mldsa_shake256_squeeze>
     +0x208: mov     x0, x24
     +0x20c: bl      <mldsa_shake256_release>
     +0x210: movi    v0.4s, #0x0
     +0x214: stp     q0, q0, [x24]
     +0x218: stp     q0, q0, [x24, #32]
     +0x21c: stp     q0, q0, [x24, #64]
     +0x220: stp     q0, q0, [x24, #96]
     +0x224: stp     q0, q0, [x24, #128]
     +0x228: stp     q0, q0, [x24, #160]
     +0x22c: str     q0, [x24, #192]
     +0x230: ldr     q4, [x20, #9056]
     +0x234: ldr     q3, [x20, #9072]
     +0x238: ldr     q1, [x20, #9088]
     +0x23c: ldr     q2, [x20, #9104]
     +0x240: eor     v1.16b, v1.16b, v4.16b
     +0x244: eor     v2.16b, v2.16b, v3.16b
     +0x248: orr     v4.16b, v1.16b, v2.16b
     +0x24c: eor     v1.16b, v1.16b, v2.16b
     +0x250: ext     v3.16b, v4.16b, v0.16b, #8
     +0x254: ext     v2.16b, v1.16b, v0.16b, #8
     +0x258: orr     v3.16b, v3.16b, v4.16b
     +0x25c: eor     v2.16b, v2.16b, v1.16b
     +0x260: ext     v4.16b, v3.16b, v0.16b, #4
     +0x264: ext     v1.16b, v2.16b, v0.16b, #4
     +0x268: orr     v4.16b, v4.16b, v3.16b
     +0x26c: eor     v1.16b, v1.16b, v2.16b
     +0x270: ext     v3.16b, v4.16b, v0.16b, #2
     +0x274: ext     v2.16b, v1.16b, v0.16b, #2
     +0x278: orr     v3.16b, v3.16b, v4.16b
     +0x27c: eor     v2.16b, v2.16b, v1.16b
     +0x280: ext     v1.16b, v3.16b, v0.16b, #1
     +0x284: ext     v0.16b, v2.16b, v0.16b, #1
     +0x288: orr     v1.16b, v1.16b, v3.16b
     +0x28c: eor     v0.16b, v0.16b, v2.16b
     +0x290: umov    w1, v1.b[0]
     +0x294: umov    w0, v0.b[0]
     +0x298: neg     x1, x1
     +0x29c: asr     x1, x1, #32
     +0x2a0: eor     w1, w0, w1
     +0x2a4: cmp     w0, w1, uxtb
     +0x2a8: b.ne    <mldsa44_verify_internal+0x420>
     +0x2ac: mov     x0, x19
     +0x2b0: mov     x2, #0x400
     +0x2b4: mov     w1, #0x0
     +0x2b8: bl      <memset@plt>
     +0x2bc: mov     x2, #0x400
     +0x2c0: mov     x0, x21
     +0x2c4: mov     w1, #0x0
     +0x2c8: bl      <memset@plt>
     +0x2cc: ldr     x19, [sp, #112]
     +0x2d0: mov     x2, #0x420
     +0x2d4: mov     w1, #0x0
     +0x2d8: mov     x0, x19
     +0x2dc: bl      <memset@plt>
     +0x2e0: mov     x2, #0x400
     +0x2e4: mov     x0, x26
     +0x2e8: mov     w1, #0x0
     +0x2ec: bl      <memset@plt>
     +0x2f0: mov     x2, #0x1000
     +0x2f4: mov     x0, x20
     +0x2f8: mov     w1, #0x0
     +0x2fc: bl      <memset@plt>
     +0x300: stp     xzr, xzr, [x22]
     +0x304: stp     xzr, xzr, [x22, #16]
     +0x308: ldr     x0, [sp, #120]
     +0x30c: stp     xzr, xzr, [x0]
     +0x310: stp     xzr, xzr, [x0, #16]
     +0x314: movi    v0.4s, #0x0
     +0x318: stp     q0, q0, [x27]
     +0x31c: stp     q0, q0, [x27, #32]
     +0x320: mov     x2, #0x300
     +0x324: mov     x0, x28
     +0x328: mov     w1, #0x0
     +0x32c: bl      <memset@plt>
     +0x330: adrp    x0, <page>
     +0x334: ldr     x0, [x0, #4088]
     +0x338: ldr     x2, [sp, #9480]
     +0x33c: ldr     x1, [x0]
     +0x340: subs    x2, x2, x1
     +0x344: mov     x1, #0x0
     +0x348: b.ne    <mldsa44_verify_internal+0x474>
     +0x34c: ldp     x19, x20, [sp]
     +0x350: mov     w0, w23
     +0x354: ldp     x21, x22, [sp, #16]
     +0x358: mov     x12, #0x2510
     +0x35c: ldp     x23, x24, [sp, #32]
     +0x360: ldp     x25, x26, [sp, #48]
     +0x364: ldp     x27, x28, [sp, #64]
     +0x368: ldr     x30, [sp, #80]
     +0x36c: add     sp, sp, x12
     +0x370: ret
     +0x374: mov     x9, #0x2438
     +0x378: mov     x10, #0x2020
     +0x37c: add     x19, sp, x9
     +0x380: add     x28, x20, x10
     +0x384: mov     x0, x19
     +0x388: bl      <mldsa_shake256_init>
     +0x38c: ldr     x1, [sp, #104]
     +0x390: mov     x2, #0x520
     +0x394: mov     x0, x19
     +0x398: bl      <mldsa_shake256_absorb>
     +0x39c: mov     x0, x19
     +0x3a0: bl      <mldsa_shake256_finalize>
     +0x3a4: mov     x2, x19
     +0x3a8: mov     x1, #0x40
     +0x3ac: mov     x0, x28
     +0x3b0: bl      <mldsa_shake256_squeeze>
     +0x3b4: mov     x0, x19
     +0x3b8: bl      <mldsa_shake256_release>
     +0x3bc: movi    v0.4s, #0x0
     +0x3c0: stp     q0, q0, [x19]
     +0x3c4: stp     q0, q0, [x19, #32]
     +0x3c8: stp     q0, q0, [x19, #64]
     +0x3cc: stp     q0, q0, [x19, #96]
     +0x3d0: stp     q0, q0, [x19, #128]
     +0x3d4: stp     q0, q0, [x19, #160]
     +0x3d8: str     q0, [x19, #192]
     +0x3dc: mov     x11, #0x2320
     +0x3e0: add     x27, x20, x11
     +0x3e4: mov     x3, #0x40
     +0x3e8: mov     x7, x24
     +0x3ec: mov     x6, x26
     +0x3f0: mov     x5, x23
     +0x3f4: mov     x4, x21
     +0x3f8: mov     x0, x27
     +0x3fc: mov     x2, x28
     +0x400: mov     x1, x3
     +0x404: bl      <mld_H44>
     +0x408: movi    v0.4s, #0x0
     +0x40c: stp     q0, q0, [x28]
     +0x410: stp     q0, q0, [x28, #32]
     +0x414: b       <mldsa44_verify_internal+0xb4>
     +0x418: mov     x2, #0x2360
     +0x41c: add     x22, x20, x2
     +0x420: mov     w23, #0xfffffffa
     +0x424: b       <mldsa44_verify_internal+0x2ac>
     +0x428: add     x0, x20, #0x1, lsl #12
     +0x42c: mov     x12, #0x2020
     +0x430: mov     x13, #0x2320
     +0x434: mov     x14, #0x1c20
     +0x438: mov     x15, #0x1820
     +0x43c: mov     x16, #0x1420
     +0x440: mov     x17, #0x2360
     +0x444: mov     x18, #0x2380
     +0x448: add     x28, x20, x12
     +0x44c: add     x27, x20, x13
     +0x450: add     x26, x20, x14
     +0x454: add     x21, x20, x15
     +0x458: add     x19, x20, x16
     +0x45c: add     x22, x20, x17
     +0x460: mov     w23, #0xfffffffa
     +0x464: str     x0, [sp, #112]
     +0x468: add     x0, x20, x18
     +0x46c: str     x0, [sp, #120]
     +0x470: b       <mldsa44_verify_internal+0x2ac>
     +0x474: bl      <__stack_chk_fail@plt>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa44_verify_internal"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The signature sigb at sig  *)
(* (2420 bytes), the message M of mlen bytes at m and the prefix PRE of      *)
(* prelen bytes at pre (or, if ext is nonzero as a 32-bit integer, mu in the *)
(* first 64 bytes at m), the public key pkb at pk (1312 bytes): the result   *)
(* is 0 if the signature is accepted, and -6 otherwise. The stack is the     *)
(* 24816 bytes of the function and those of the callees below them.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 11040),11040))
              [(sig,2420); (m,mlen); (pre,prelen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
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
                 [memory :> bytes(word_sub stackpointer (word 11040),11040)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, the flag ext, the    *)
(* signature, the message, the prefix and the public key, all public, the    *)
(* address of memset and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset may read and the constants of the callees, and the writes within   *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 11040),11040))
              [(sig,2420); (m,mlen); (pre,prelen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
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
                              guard mf pc (word_sub stackpointer (word 11040))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; pre,prelen; pk,1312;
                         word_sub stackpointer (word 11040),11040;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [word_sub stackpointer (word 11040),11040]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 11040),11040)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
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
          ALL (nonoverlapping (word_sub stackpointer (word 11040),11040))
              [(sig,2420); (m,mlen); (pre,prelen); (pk,1312);
               (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
               (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
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
                              guard mf pc (word_sub stackpointer (word 11040))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; pre,prelen; pk,1312;
                         word_sub stackpointer (word 11040),11040;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [word_sub stackpointer (word 11040),11040]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(word_sub stackpointer (word 11040),11040)])`;;

let MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_VERIFY_INTERNAL_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
