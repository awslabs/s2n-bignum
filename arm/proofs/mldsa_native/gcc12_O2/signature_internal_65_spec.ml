(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing: the statement. This is the code for mldsa65_signature_internal   *)
(* (mld_sign_signature_internal in sign.c, with                              *)
(* mld_attempt_signature_generation and mld_compute_pack_z inlined) from     *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mldsa_native/README.md), which unpacks the secret key, computes mu (or    *)
(* takes it from m if ext is nonzero) and rho'', expands the matrix from     *)
(* rho, and makes up to 13106 attempts: each samples y, computes w = A y, w1 *)
(* packed, c~ and the challenge, then z, checking and packing each           *)
(* polynomial, and for each row checks w0 - c s2 and c t0, and finally packs *)
(* c~ and the hints, rejecting at the first check that fails. It returns 0   *)
(* with the signature of the first attempt that succeeds, or -4              *)
(* (MLD_ERR_SIGN_ATTEMPTS_EXHAUSTED) with the signature zeroed, and zeroes   *)
(* its buffers with memset. It is verified in the whole image (see           *)
(* libmldsa.ml) against mld_sign_ok and mld_sign_sig of                      *)
(* common/mldsa_native_sign.ml, using the theorems for the callees and the   *)
(* contracts memset_full_contract and memcpy_full_contract, assuming that    *)
(* the expansion of the matrix and the sampling of the challenge in each     *)
(* attempt terminate, and shown to be constant time and memory safe, with    *)
(* the events depending only on public values and those that the C code      *)
(* declassifies (mld_sign_declass).                                          *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stubs for memset and memcpy:

    mldsa65_signature_internal:
       +0x0: sub     sp, sp, #0x9c0
       +0x4: mov     x12, #0xe800
       +0x8: sub     sp, sp, #0x10, lsl #12
       +0xc: mov     x13, #0xa800
      +0x10: add     x8, sp, #0xbf
      +0x14: and     x9, x8, #0xffffffffffffffe0
      +0x18: add     x10, x9, #0x10, lsl #12
      +0x1c: add     x11, x9, #0x9, lsl #12
      +0x20: add     x10, x10, #0x700
      +0x24: add     x12, x9, x12
      +0x28: adrp    x8, <page>
      +0x2c: ldr     x8, [x8, #4088]
      +0x30: stp     x10, x9, [sp, #128]
      +0x34: add     x9, x9, x13
      +0x38: stp     x19, x20, [sp]
      +0x3c: mov     x20, x3
      +0x40: mov     x3, x9
      +0x44: stp     x21, x22, [sp, #16]
      +0x48: mov     x19, x5
      +0x4c: mov     x22, x2
      +0x50: stp     x23, x24, [sp, #32]
      +0x54: mov     w24, w7
      +0x58: mov     x23, x1
      +0x5c: stp     x25, x26, [sp, #48]
      +0x60: add     x25, x10, #0x20
      +0x64: mov     x21, x4
      +0x68: stp     x27, x28, [sp, #64]
      +0x6c: mov     x1, x25
      +0x70: mov     x26, x10
      +0x74: str     x30, [sp, #80]
      +0x78: add     x2, x10, #0x60
      +0x7c: str     x0, [sp, #96]
      +0x80: mov     x5, x11
      +0x84: str     x9, [sp, #104]
      +0x88: add     x9, sp, #0x10, lsl #12
      +0x8c: stp     x12, x11, [sp, #144]
      +0x90: add     x9, x9, #0x40
      +0x94: mov     x4, x12
      +0x98: ldr     x7, [x8]
      +0x9c: str     x7, [x9, #2424]
      +0xa0: mov     x7, #0x0
      +0xa4: mov     x0, x10
      +0xa8: bl      <mldsa65_unpack_sk>
      +0xac: cbnz    w24, <+0x4f0>
      +0xb0: mov     x3, #0x40
      +0xb4: mov     x7, x22
      +0xb8: mov     x6, x23
      +0xbc: mov     x5, x21
      +0xc0: mov     x4, x20
      +0xc4: mov     x2, x25
      +0xc8: add     x0, x26, #0x80
      +0xcc: mov     x1, x3
      +0xd0: bl      <mld_H65>
      +0xd4: ldp     x24, x22, [sp, #128]
      +0xd8: mov     x1, #0xd400
      +0xdc: mov     x4, x19
      +0xe0: mov     x5, #0x20
      +0xe4: mov     x8, #0x7800
      +0xe8: mov     x9, #0xfc00
      +0xec: mov     x3, x5
      +0xf0: mov     x7, #0x40
      +0xf4: add     x21, sp, #0x10, lsl #12
      +0xf8: add     x6, x24, #0x80
      +0xfc: add     x2, x24, #0x60
     +0x100: add     x27, x22, x1
     +0x104: add     x1, x22, #0x10, lsl #12
     +0x108: add     x1, x1, #0x400
     +0x10c: add     x0, x24, #0xc0
     +0x110: add     x26, x22, x8
     +0x114: add     x25, x22, #0x10, lsl #12
     +0x118: add     x20, x22, x9
     +0x11c: str     x1, [sp, #120]
     +0x120: mov     x1, x7
     +0x124: bl      <mld_H65>
     +0x128: add     x21, x21, #0x8e8
     +0x12c: add     x19, x22, #0xc, lsl #12
     +0x130: add     x25, x25, #0x800
     +0x134: add     x23, x22, #0x10, lsl #12
     +0x138: mov     x1, x24
     +0x13c: mov     x0, x22
     +0x140: str     wzr, [sp, #116]
     +0x144: bl      <mldsa65_polyvec_matrix_expand_eager>
     +0x148: ldrh    w2, [sp, #116]
     +0x14c: mov     x0, x27
     +0x150: ldr     x22, [sp, #128]
     +0x154: add     x1, x22, #0xc0
     +0x158: bl      <mldsa65_polyvecl_uniform_gamma1>
     +0x15c: ldr     x1, [sp, #136]
     +0x160: mov     x3, x19
     +0x164: mov     x2, x27
     +0x168: mov     x0, x26
     +0x16c: bl      <mldsa65_polyvec_matrix_pointwise_montgomery_yvec_eager>
     +0x170: mov     x0, x26
     +0x174: bl      <mldsa65_polyveck_caddq>
     +0x178: ldr     x24, [sp, #120]
     +0x17c: mov     x2, x19
     +0x180: mov     x1, x26
     +0x184: mov     x0, x24
     +0x188: bl      <mldsa65_polyveck_decompose_pack_w1>
     +0x18c: mov     x0, x21
     +0x190: bl      <mldsa_shake256_init>
     +0x194: add     x1, x22, #0x80
     +0x198: mov     x0, x21
     +0x19c: mov     x2, #0x40
     +0x1a0: bl      <mldsa_shake256_absorb>
     +0x1a4: mov     x1, x24
     +0x1a8: mov     x2, #0x300
     +0x1ac: mov     x0, x21
     +0x1b0: bl      <mldsa_shake256_absorb>
     +0x1b4: mov     x0, x21
     +0x1b8: bl      <mldsa_shake256_finalize>
     +0x1bc: mov     x2, x21
     +0x1c0: mov     x1, #0x30
     +0x1c4: mov     x0, x25
     +0x1c8: bl      <mldsa_shake256_squeeze>
     +0x1cc: mov     x0, x21
     +0x1d0: bl      <mldsa_shake256_release>
     +0x1d4: movi    v0.4s, #0x0
     +0x1d8: stp     q0, q0, [x21]
     +0x1dc: stp     q0, q0, [x21, #32]
     +0x1e0: stp     q0, q0, [x21, #64]
     +0x1e4: stp     q0, q0, [x21, #96]
     +0x1e8: stp     q0, q0, [x21, #128]
     +0x1ec: stp     q0, q0, [x21, #160]
     +0x1f0: str     q0, [x21, #192]
     +0x1f4: mov     x1, x25
     +0x1f8: mov     x0, x23
     +0x1fc: ldr     x28, [sp, #144]
     +0x200: bl      <mldsa65_poly_challenge>
     +0x204: mov     x24, x27
     +0x208: mov     x0, x23
     +0x20c: mov     w22, #0x0
     +0x210: bl      <mldsa_poly_ntt>
     +0x214: mov     x2, #0x400
     +0x218: mov     x1, x28
     +0x21c: mov     x0, x20
     +0x220: bl      <memcpy@plt>
     +0x224: mov     x1, x23
     +0x228: mov     x0, x20
     +0x22c: bl      <mldsa_poly_pointwise_montgomery>
     +0x230: mov     x0, x20
     +0x234: bl      <mldsa_poly_invntt_tomont>
     +0x238: mov     x2, #0x400
     +0x23c: mov     x1, x24
     +0x240: mov     x0, x19
     +0x244: bl      <memcpy@plt>
     +0x248: mov     x1, x19
     +0x24c: mov     x0, x20
     +0x250: bl      <mldsa_poly_add>
     +0x254: mov     x0, x20
     +0x258: bl      <mldsa_poly_reduce>
     +0x25c: mov     w1, #0xff3c
     +0x260: mov     x0, x20
     +0x264: movk    w1, #0x7, lsl #16
     +0x268: bl      <mldsa_poly_chknorm>
     +0x26c: cbnz    w0, <+0x4e8>
     +0x270: ldr     x0, [sp, #96]
     +0x274: mov     w2, w22
     +0x278: mov     x1, x20
     +0x27c: add     w22, w22, #0x1
     +0x280: add     x28, x28, #0x400
     +0x284: add     x24, x24, #0x400
     +0x288: bl      <mldsa65_pack_sig_z>
     +0x28c: cmp     w22, #0x5
     +0x290: b.ne    <+0x214>
     +0x294: ldr     x28, [sp, #104]
     +0x298: mov     x22, x26
     +0x29c: ldr     x24, [sp, #152]
     +0x2a0: mov     x2, #0x400
     +0x2a4: mov     x1, x24
     +0x2a8: mov     x0, x19
     +0x2ac: bl      <memcpy@plt>
     +0x2b0: mov     x1, x23
     +0x2b4: mov     x0, x19
     +0x2b8: bl      <mldsa_poly_pointwise_montgomery>
     +0x2bc: mov     x0, x19
     +0x2c0: bl      <mldsa_poly_invntt_tomont>
     +0x2c4: mov     x1, x19
     +0x2c8: mov     x0, x22
     +0x2cc: bl      <mldsa_poly_sub>
     +0x2d0: mov     x0, x22
     +0x2d4: bl      <mldsa_poly_reduce>
     +0x2d8: mov     w1, #0xfe3c
     +0x2dc: mov     x0, x22
     +0x2e0: movk    w1, #0x3, lsl #16
     +0x2e4: bl      <mldsa_poly_chknorm>
     +0x2e8: cbnz    w0, <+0x4e8>
     +0x2ec: mov     x2, #0x400
     +0x2f0: mov     x1, x28
     +0x2f4: mov     x0, x19
     +0x2f8: bl      <memcpy@plt>
     +0x2fc: mov     x1, x23
     +0x300: mov     x0, x19
     +0x304: bl      <mldsa_poly_pointwise_montgomery>
     +0x308: mov     x0, x19
     +0x30c: bl      <mldsa_poly_invntt_tomont>
     +0x310: mov     x0, x19
     +0x314: bl      <mldsa_poly_reduce>
     +0x318: mov     x0, x19
     +0x31c: mov     w1, #0x3ff00
     +0x320: bl      <mldsa_poly_chknorm>
     +0x324: cbnz    w0, <+0x4e8>
     +0x328: mov     x0, x22
     +0x32c: mov     x1, x19
     +0x330: bl      <mldsa_poly_add>
     +0x334: add     x24, x24, #0x400
     +0x338: ldr     x0, [sp, #104]
     +0x33c: add     x28, x28, #0x400
     +0x340: add     x22, x22, #0x400
     +0x344: cmp     x24, x0
     +0x348: b.ne    <+0x2a0>
     +0x34c: ldr     x22, [sp, #96]
     +0x350: mov     x1, x25
     +0x354: mov     x0, x22
     +0x358: bl      <mldsa65_pack_sig_c>
     +0x35c: ldr     x2, [sp, #120]
     +0x360: mov     x0, x22
     +0x364: mov     x3, x19
     +0x368: mov     x1, x26
     +0x36c: bl      <mldsa65_pack_sig_h>
     +0x370: mov     w22, w0
     +0x374: mov     x0, x20
     +0x378: mov     x2, #0x400
     +0x37c: mov     w1, #0x0
     +0x380: bl      <memset@plt>
     +0x384: mov     x2, #0x400
     +0x388: mov     x0, x23
     +0x38c: mov     w1, #0x0
     +0x390: bl      <memset@plt>
     +0x394: mov     x2, #0x1800
     +0x398: mov     x0, x26
     +0x39c: mov     w1, #0x0
     +0x3a0: bl      <memset@plt>
     +0x3a4: ldr     x24, [sp, #120]
     +0x3a8: mov     x2, #0x300
     +0x3ac: mov     w1, #0x0
     +0x3b0: mov     x0, x24
     +0x3b4: bl      <memset@plt>
     +0x3b8: mov     x2, #0x1400
     +0x3bc: mov     x0, x19
     +0x3c0: mov     w1, #0x0
     +0x3c4: bl      <memset@plt>
     +0x3c8: mov     x2, #0x1400
     +0x3cc: mov     x0, x27
     +0x3d0: mov     w1, #0x0
     +0x3d4: bl      <memset@plt>
     +0x3d8: stp     xzr, xzr, [x25]
     +0x3dc: stp     xzr, xzr, [x25, #16]
     +0x3e0: stp     xzr, xzr, [x25, #32]
     +0x3e4: cbz     w22, <+0x424>
     +0x3e8: cmn     w22, #0x1
     +0x3ec: b.ne    <+0x410>
     +0x3f0: ldr     w0, [sp, #116]
     +0x3f4: mov     w1, #0xfffa
     +0x3f8: add     w0, w0, #0x5
     +0x3fc: and     w2, w0, #0xffff
     +0x400: str     w2, [sp, #116]
     +0x404: cmp     w1, w0, uxth
     +0x408: b.ne    <+0x148>
     +0x40c: mov     w22, #0xfffffffc
     +0x410: ldr     x19, [sp, #96]
     +0x414: mov     x2, #0xced
     +0x418: mov     w1, #0x0
     +0x41c: mov     x0, x19
     +0x420: bl      <memset@plt>
     +0x424: ldr     x19, [sp, #152]
     +0x428: mov     x2, #0x1800
     +0x42c: mov     w1, #0x0
     +0x430: mov     x0, x19
     +0x434: bl      <memset@plt>
     +0x438: ldr     x19, [sp, #104]
     +0x43c: mov     x2, #0x1800
     +0x440: mov     w1, #0x0
     +0x444: mov     x0, x19
     +0x448: bl      <memset@plt>
     +0x44c: ldr     x19, [sp, #144]
     +0x450: mov     x2, #0x1400
     +0x454: mov     w1, #0x0
     +0x458: mov     x0, x19
     +0x45c: bl      <memset@plt>
     +0x460: ldr     x19, [sp, #136]
     +0x464: mov     x2, #0x7800
     +0x468: mov     w1, #0x0
     +0x46c: mov     x0, x19
     +0x470: bl      <memset@plt>
     +0x474: ldr     x0, [sp, #128]
     +0x478: movi    v0.4s, #0x0
     +0x47c: stp     q0, q0, [x0]
     +0x480: stp     q0, q0, [x0, #32]
     +0x484: stp     q0, q0, [x0, #64]
     +0x488: stp     q0, q0, [x0, #96]
     +0x48c: stp     q0, q0, [x0, #128]
     +0x490: stp     q0, q0, [x0, #160]
     +0x494: stp     q0, q0, [x0, #192]
     +0x498: stp     q0, q0, [x0, #224]
     +0x49c: adrp    x0, <page>
     +0x4a0: ldr     x0, [x0, #4088]
     +0x4a4: add     x2, sp, #0x10, lsl #12
     +0x4a8: add     x2, x2, #0x40
     +0x4ac: ldr     x3, [x2, #2424]
     +0x4b0: ldr     x1, [x0]
     +0x4b4: subs    x3, x3, x1
     +0x4b8: mov     x1, #0x0
     +0x4bc: b.ne    <+0x50c>
     +0x4c0: ldp     x19, x20, [sp]
     +0x4c4: mov     w0, w22
     +0x4c8: ldp     x21, x22, [sp, #16]
     +0x4cc: ldp     x23, x24, [sp, #32]
     +0x4d0: ldp     x25, x26, [sp, #48]
     +0x4d4: ldp     x27, x28, [sp, #64]
     +0x4d8: ldr     x30, [sp, #80]
     +0x4dc: add     sp, sp, #0x9c0
     +0x4e0: add     sp, sp, #0x10, lsl #12
     +0x4e4: ret
     +0x4e8: mov     w22, #0xffffffff
     +0x4ec: b       <+0x374>
     +0x4f0: ldr     x0, [sp, #128]
     +0x4f4: ldp     q2, q3, [x23]
     +0x4f8: add     x0, x0, #0x80
     +0x4fc: ldp     q0, q1, [x23, #32]
     +0x500: stp     q2, q3, [x0]
     +0x504: stp     q0, q1, [x0, #32]
     +0x508: b       <+0xd4>
     +0x50c: bl      <__stack_chk_fail@plt>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17

    memcpy@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4048]
       +0x8: add     x16, x16, #0xfd0
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_signature_internal"; layout_range "plt_memset";
    layout_range "plt_memcpy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for memset and memcpy. The secret key *)
(* skb at sk (4032 bytes), the message M of mlen bytes at m and the prefix   *)
(* PRE of prelen bytes at pre (or, if ext is nonzero as a 32-bit integer, mu *)
(* in the first 64 bytes at m), and the 32 bytes RND at rnd, with MU the mu  *)
(* that the code uses: the result is 0, with the signature mld_sign_sig at   *)
(* sig (3309 bytes), if one of the 13106 attempts succeeds (mld_sign_ok),    *)
(* and -4 with the signature zeroed otherwise. The stack is the 68032 bytes  *)
(* of the function and those of the callees below them.                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !sig m mlen pre prelen rnd sk ext skb M PRE RND MU guard
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          MU = (if word_zx ext = (word 0:int32)
                then mld_sign_mu (\j. skb(64 + j)) prelen PRE mlen M
                else M MOD 2 EXP 512) /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          mld_sign_terminates_65 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73088),73088)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73088),73088)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_signature_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; rnd; sk;
                                 ext] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_sign_ok_65 skb MU RND
                     then word 0 else word 4294967292) /\
                    (!t. t < 3309
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             mld_sign_sig_65 skb MU RND t))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 73088),73088)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, ext, rho, what the C *)
(* code declassifies in each attempt (mld_sign_declass), the addresses of    *)
(* memset and memcpy and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset and memcpy may read and the constants of the callees, and the      *)
(* writes within the signature and the stack.                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen rnd sk ext skb M PRE RND MU guard
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          MU = (if word_zx ext = (word 0:int32)
                then mld_sign_mu (\j. skb(64 + j)) prelen PRE mlen M
                else M MOD 2 EXP 512) /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          mld_sign_terminates_65 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73088),73088)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73088),73088)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_signature_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; rnd; sk;
                                 ext] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_sign_ok_65 skb MU RND
                     then word 0 else word 4294967292) /\
                    (!t. t < 3309
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             mld_sign_sig_65 skb MU RND t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen rnd sk ext
                             (mld_sk_rho skb)
                             (mld_sign_declass_65 skb MU RND)
                             guard mf mc pc
                             (word_sub stackpointer (word 73088))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; pre,prelen; rnd,32; sk,4032;
                         word_sub stackpointer (word 73088),73088;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
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
                        [sig,3309;
                         word_sub stackpointer (word 73088),73088]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 73088),73088)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e sig m mlen pre prelen rnd sk ext skb M PRE RND MU guard
                 pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mlen < 2 EXP 64 /\ prelen < 2 EXP 64 /\
          (~(word_zx ext = (word 0:int32)) ==> 64 <= mlen) /\
          MU = (if word_zx ext = (word 0:int32)
                then mld_sign_mu (\j. skb(64 + j)) prelen PRE mlen M
                else M MOD 2 EXP 512) /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          mld_sign_terminates_65 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73088),73088)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 73088),73088)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_signature_internal) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [sig; m; word mlen; pre; word prelen; rnd; sk;
                                 ext] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(m,mlen)) s = M /\
                    read (memory :> bytes(pre,prelen)) s = PRE /\
                    read (memory :> bytes(rnd,32)) s = RND /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen rnd sk ext
                             (mld_sk_rho skb)
                             (mld_sign_declass_65 skb MU RND)
                             guard mf mc pc
                             (word_sub stackpointer (word 73088))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; pre,prelen; rnd,32; sk,4032;
                         word_sub stackpointer (word 73088),73088;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
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
                        [sig,3309;
                         word_sub stackpointer (word 73088),73088]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 73088),73088)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
