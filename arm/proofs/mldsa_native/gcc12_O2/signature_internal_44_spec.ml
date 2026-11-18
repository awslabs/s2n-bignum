(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing: the statement. This is the code for mldsa44_signature_internal   *)
(* (mld_sign_signature_internal in sign.c, with                              *)
(* mld_attempt_signature_generation and mld_compute_pack_z inlined) from     *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mldsa_native/README.md), which unpacks the secret key, computes mu (or    *)
(* takes it from m if ext is nonzero) and rho'', expands the matrix from     *)
(* rho, and makes up to 16382 attempts: each samples y, computes w = A y, w1 *)
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

    mldsa44_signature_internal:
       +0x0: mov     x12, #0xadb0
       +0x4: sub     sp, sp, x12
       +0x8: add     x8, sp, #0xbf
       +0xc: mov     x11, #0xab00
      +0x10: and     x9, x8, #0xffffffffffffffe0
      +0x14: adrp    x8, <page>
      +0x18: ldr     x8, [x8, #4088]
      +0x1c: add     x10, x9, x11
      +0x20: add     x12, x9, #0x9, lsl #12
      +0x24: add     x11, x9, #0x7, lsl #12
      +0x28: stp     x19, x20, [sp]
      +0x2c: mov     x20, x3
      +0x30: mov     x19, x5
      +0x34: stp     x21, x22, [sp, #16]
      +0x38: mov     x21, x4
      +0x3c: mov     x4, x12
      +0x40: stp     x23, x24, [sp, #32]
      +0x44: mov     w24, w7
      +0x48: mov     x23, x1
      +0x4c: stp     x25, x26, [sp, #48]
      +0x50: add     x25, x10, #0x20
      +0x54: mov     x22, x2
      +0x58: stp     x27, x28, [sp, #64]
      +0x5c: mov     x1, x25
      +0x60: mov     x26, x10
      +0x64: str     x30, [sp, #80]
      +0x68: add     x2, x10, #0x60
      +0x6c: str     x0, [sp, #96]
      +0x70: mov     x5, x11
      +0x74: stp     x10, x9, [sp, #128]
      +0x78: add     x9, x9, #0x8, lsl #12
      +0x7c: mov     x3, x9
      +0x80: str     x9, [sp, #112]
      +0x84: mov     x0, x10
      +0x88: stp     x12, x11, [sp, #144]
      +0x8c: mov     x12, #0x8040
      +0x90: add     x9, sp, x12
      +0x94: ldr     x7, [x8]
      +0x98: str     x7, [x9, #11624]
      +0x9c: mov     x7, #0x0
      +0xa0: bl      <mldsa44_unpack_sk>
      +0xa4: cbnz    w24, <+0x4e0>
      +0xa8: mov     x3, #0x40
      +0xac: mov     x7, x22
      +0xb0: mov     x6, x23
      +0xb4: mov     x5, x21
      +0xb8: mov     x4, x20
      +0xbc: mov     x2, x25
      +0xc0: add     x0, x26, #0x80
      +0xc4: mov     x1, x3
      +0xc8: bl      <mld_H44>
      +0xcc: ldp     x24, x22, [sp, #128]
      +0xd0: mov     x2, #0xacd8
      +0xd4: mov     x4, x19
      +0xd8: mov     x5, #0x20
      +0xdc: mov     x8, #0xa800
      +0xe0: mov     x9, #0xac00
      +0xe4: mov     x10, #0xa400
      +0xe8: mov     x3, x5
      +0xec: add     x21, sp, x2
      +0xf0: mov     x7, #0x40
      +0xf4: add     x6, x24, #0x80
      +0xf8: add     x2, x24, #0x60
      +0xfc: add     x1, x22, x8
     +0x100: add     x0, x24, #0xc0
     +0x104: add     x26, x22, x9
     +0x108: add     x23, x22, x10
     +0x10c: str     x1, [sp, #120]
     +0x110: mov     x1, x7
     +0x114: bl      <mld_H44>
     +0x118: add     x27, x22, #0x6, lsl #12
     +0x11c: add     x19, x22, #0x5, lsl #12
     +0x120: add     x25, x22, #0x4, lsl #12
     +0x124: add     x20, x22, #0xa, lsl #12
     +0x128: mov     x1, x24
     +0x12c: mov     x0, x22
     +0x130: str     wzr, [sp, #108]
     +0x134: bl      <mldsa44_polyvec_matrix_expand_eager>
     +0x138: ldrh    w2, [sp, #108]
     +0x13c: mov     x0, x27
     +0x140: ldr     x22, [sp, #128]
     +0x144: add     x1, x22, #0xc0
     +0x148: bl      <mldsa44_polyvecl_uniform_gamma1>
     +0x14c: ldr     x1, [sp, #136]
     +0x150: mov     x3, x19
     +0x154: mov     x2, x27
     +0x158: mov     x0, x25
     +0x15c: bl      <mldsa44_polyvec_matrix_pointwise_montgomery_yvec_eager>
     +0x160: mov     x0, x25
     +0x164: bl      <mldsa44_polyveck_caddq>
     +0x168: ldr     x24, [sp, #120]
     +0x16c: mov     x2, x19
     +0x170: mov     x1, x25
     +0x174: mov     x0, x24
     +0x178: bl      <mldsa44_polyveck_decompose_pack_w1>
     +0x17c: mov     x0, x21
     +0x180: bl      <mldsa_shake256_init>
     +0x184: add     x1, x22, #0x80
     +0x188: mov     x0, x21
     +0x18c: mov     x2, #0x40
     +0x190: bl      <mldsa_shake256_absorb>
     +0x194: mov     x1, x24
     +0x198: mov     x2, #0x300
     +0x19c: mov     x0, x21
     +0x1a0: bl      <mldsa_shake256_absorb>
     +0x1a4: mov     x0, x21
     +0x1a8: bl      <mldsa_shake256_finalize>
     +0x1ac: mov     x2, x21
     +0x1b0: mov     x1, #0x20
     +0x1b4: mov     x0, x26
     +0x1b8: bl      <mldsa_shake256_squeeze>
     +0x1bc: mov     x0, x21
     +0x1c0: bl      <mldsa_shake256_release>
     +0x1c4: movi    v0.4s, #0x0
     +0x1c8: stp     q0, q0, [x21]
     +0x1cc: stp     q0, q0, [x21, #32]
     +0x1d0: stp     q0, q0, [x21, #64]
     +0x1d4: stp     q0, q0, [x21, #96]
     +0x1d8: stp     q0, q0, [x21, #128]
     +0x1dc: stp     q0, q0, [x21, #160]
     +0x1e0: str     q0, [x21, #192]
     +0x1e4: mov     x1, x26
     +0x1e8: mov     x0, x23
     +0x1ec: ldr     x28, [sp, #144]
     +0x1f0: bl      <mldsa44_poly_challenge>
     +0x1f4: mov     x24, x27
     +0x1f8: mov     x0, x23
     +0x1fc: mov     w22, #0x0
     +0x200: bl      <mldsa_poly_ntt>
     +0x204: mov     x2, #0x400
     +0x208: mov     x1, x28
     +0x20c: mov     x0, x20
     +0x210: bl      <memcpy@plt>
     +0x214: mov     x1, x23
     +0x218: mov     x0, x20
     +0x21c: bl      <mldsa_poly_pointwise_montgomery>
     +0x220: mov     x0, x20
     +0x224: bl      <mldsa_poly_invntt_tomont>
     +0x228: mov     x2, #0x400
     +0x22c: mov     x1, x24
     +0x230: mov     x0, x19
     +0x234: bl      <memcpy@plt>
     +0x238: mov     x1, x19
     +0x23c: mov     x0, x20
     +0x240: bl      <mldsa_poly_add>
     +0x244: mov     x0, x20
     +0x248: bl      <mldsa_poly_reduce>
     +0x24c: mov     w1, #0xffb2
     +0x250: mov     x0, x20
     +0x254: movk    w1, #0x1, lsl #16
     +0x258: bl      <mldsa_poly_chknorm>
     +0x25c: cbnz    w0, <+0x4d8>
     +0x260: ldr     x0, [sp, #96]
     +0x264: mov     w2, w22
     +0x268: mov     x1, x20
     +0x26c: add     w22, w22, #0x1
     +0x270: add     x28, x28, #0x400
     +0x274: add     x24, x24, #0x400
     +0x278: bl      <mldsa44_pack_sig_z>
     +0x27c: cmp     w22, #0x4
     +0x280: b.ne    <+0x204>
     +0x284: ldr     x28, [sp, #112]
     +0x288: mov     x22, x25
     +0x28c: ldr     x24, [sp, #152]
     +0x290: mov     x2, #0x400
     +0x294: mov     x1, x24
     +0x298: mov     x0, x19
     +0x29c: bl      <memcpy@plt>
     +0x2a0: mov     x1, x23
     +0x2a4: mov     x0, x19
     +0x2a8: bl      <mldsa_poly_pointwise_montgomery>
     +0x2ac: mov     x0, x19
     +0x2b0: bl      <mldsa_poly_invntt_tomont>
     +0x2b4: mov     x1, x19
     +0x2b8: mov     x0, x22
     +0x2bc: bl      <mldsa_poly_sub>
     +0x2c0: mov     x0, x22
     +0x2c4: bl      <mldsa_poly_reduce>
     +0x2c8: mov     w1, #0x73b2
     +0x2cc: mov     x0, x22
     +0x2d0: movk    w1, #0x1, lsl #16
     +0x2d4: bl      <mldsa_poly_chknorm>
     +0x2d8: cbnz    w0, <+0x4d8>
     +0x2dc: mov     x2, #0x400
     +0x2e0: mov     x1, x28
     +0x2e4: mov     x0, x19
     +0x2e8: bl      <memcpy@plt>
     +0x2ec: mov     x1, x23
     +0x2f0: mov     x0, x19
     +0x2f4: bl      <mldsa_poly_pointwise_montgomery>
     +0x2f8: mov     x0, x19
     +0x2fc: bl      <mldsa_poly_invntt_tomont>
     +0x300: mov     x0, x19
     +0x304: bl      <mldsa_poly_reduce>
     +0x308: mov     w1, #0x7400
     +0x30c: mov     x0, x19
     +0x310: movk    w1, #0x1, lsl #16
     +0x314: bl      <mldsa_poly_chknorm>
     +0x318: cbnz    w0, <+0x4d8>
     +0x31c: mov     x0, x22
     +0x320: mov     x1, x19
     +0x324: bl      <mldsa_poly_add>
     +0x328: add     x24, x24, #0x400
     +0x32c: ldr     x0, [sp, #112]
     +0x330: add     x28, x28, #0x400
     +0x334: add     x22, x22, #0x400
     +0x338: cmp     x24, x0
     +0x33c: b.ne    <+0x290>
     +0x340: ldr     x22, [sp, #96]
     +0x344: mov     x1, x26
     +0x348: mov     x0, x22
     +0x34c: bl      <mldsa44_pack_sig_c>
     +0x350: ldr     x2, [sp, #120]
     +0x354: mov     x0, x22
     +0x358: mov     x3, x19
     +0x35c: mov     x1, x25
     +0x360: bl      <mldsa44_pack_sig_h>
     +0x364: mov     w22, w0
     +0x368: mov     x0, x20
     +0x36c: mov     x2, #0x400
     +0x370: mov     w1, #0x0
     +0x374: bl      <memset@plt>
     +0x378: mov     x2, #0x400
     +0x37c: mov     x0, x23
     +0x380: mov     w1, #0x0
     +0x384: bl      <memset@plt>
     +0x388: mov     x2, #0x1000
     +0x38c: mov     x0, x25
     +0x390: mov     w1, #0x0
     +0x394: bl      <memset@plt>
     +0x398: ldr     x24, [sp, #120]
     +0x39c: mov     x2, #0x300
     +0x3a0: mov     w1, #0x0
     +0x3a4: mov     x0, x24
     +0x3a8: bl      <memset@plt>
     +0x3ac: mov     x2, #0x1000
     +0x3b0: mov     x0, x19
     +0x3b4: mov     w1, #0x0
     +0x3b8: bl      <memset@plt>
     +0x3bc: mov     x2, #0x1000
     +0x3c0: mov     x0, x27
     +0x3c4: mov     w1, #0x0
     +0x3c8: bl      <memset@plt>
     +0x3cc: stp     xzr, xzr, [x26]
     +0x3d0: stp     xzr, xzr, [x26, #16]
     +0x3d4: cbz     w22, <+0x414>
     +0x3d8: cmn     w22, #0x1
     +0x3dc: b.ne    <+0x400>
     +0x3e0: ldr     w0, [sp, #108]
     +0x3e4: mov     w1, #0xfff8
     +0x3e8: add     w0, w0, #0x4
     +0x3ec: and     w2, w0, #0xffff
     +0x3f0: str     w2, [sp, #108]
     +0x3f4: cmp     w1, w0, uxth
     +0x3f8: b.ne    <+0x138>
     +0x3fc: mov     w22, #0xfffffffc
     +0x400: ldr     x19, [sp, #96]
     +0x404: mov     x2, #0x974
     +0x408: mov     w1, #0x0
     +0x40c: mov     x0, x19
     +0x410: bl      <memset@plt>
     +0x414: ldr     x19, [sp, #152]
     +0x418: mov     x2, #0x1000
     +0x41c: mov     w1, #0x0
     +0x420: mov     x0, x19
     +0x424: bl      <memset@plt>
     +0x428: ldr     x19, [sp, #112]
     +0x42c: mov     x2, #0x1000
     +0x430: mov     w1, #0x0
     +0x434: mov     x0, x19
     +0x438: bl      <memset@plt>
     +0x43c: ldr     x19, [sp, #144]
     +0x440: mov     x2, #0x1000
     +0x444: mov     w1, #0x0
     +0x448: mov     x0, x19
     +0x44c: bl      <memset@plt>
     +0x450: ldr     x19, [sp, #136]
     +0x454: mov     x2, #0x4000
     +0x458: mov     w1, #0x0
     +0x45c: mov     x0, x19
     +0x460: bl      <memset@plt>
     +0x464: ldr     x0, [sp, #128]
     +0x468: movi    v0.4s, #0x0
     +0x46c: stp     q0, q0, [x0]
     +0x470: stp     q0, q0, [x0, #32]
     +0x474: stp     q0, q0, [x0, #64]
     +0x478: stp     q0, q0, [x0, #96]
     +0x47c: stp     q0, q0, [x0, #128]
     +0x480: stp     q0, q0, [x0, #160]
     +0x484: stp     q0, q0, [x0, #192]
     +0x488: stp     q0, q0, [x0, #224]
     +0x48c: adrp    x0, <page>
     +0x490: ldr     x0, [x0, #4088]
     +0x494: mov     x1, #0x8040
     +0x498: add     x2, sp, x1
     +0x49c: ldr     x3, [x2, #11624]
     +0x4a0: ldr     x1, [x0]
     +0x4a4: subs    x3, x3, x1
     +0x4a8: mov     x1, #0x0
     +0x4ac: b.ne    <+0x4fc>
     +0x4b0: ldp     x19, x20, [sp]
     +0x4b4: mov     w0, w22
     +0x4b8: ldp     x21, x22, [sp, #16]
     +0x4bc: mov     x12, #0xadb0
     +0x4c0: ldp     x23, x24, [sp, #32]
     +0x4c4: ldp     x25, x26, [sp, #48]
     +0x4c8: ldp     x27, x28, [sp, #64]
     +0x4cc: ldr     x30, [sp, #80]
     +0x4d0: add     sp, sp, x12
     +0x4d4: ret
     +0x4d8: mov     w22, #0xffffffff
     +0x4dc: b       <+0x368>
     +0x4e0: ldr     x0, [sp, #128]
     +0x4e4: ldp     q2, q3, [x23]
     +0x4e8: add     x0, x0, #0x80
     +0x4ec: ldp     q0, q1, [x23, #32]
     +0x4f0: stp     q2, q3, [x0]
     +0x4f4: stp     q0, q1, [x0, #32]
     +0x4f8: b       <+0xcc>
     +0x4fc: bl      <__stack_chk_fail@plt>

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

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_signature_internal"; layout_range "plt_memset";
    layout_range "plt_memcpy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for memset and memcpy. The secret key *)
(* skb at sk (2560 bytes), the message M of mlen bytes at m and the prefix   *)
(* PRE of prelen bytes at pre (or, if ext is nonzero as a 32-bit integer, mu *)
(* in the first 64 bytes at m), and the 32 bytes RND at rnd, with MU the mu  *)
(* that the code uses: the result is 0, with the signature mld_sign_sig at   *)
(* sig (2420 bytes), if one of the 16382 attempts succeeds (mld_sign_ok),    *)
(* and -4 with the signature zeroed otherwise. The stack is the 44464 bytes  *)
(* of the function and those of the callees below them.                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
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
          mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
          mld_sign_terminates_44 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49536),49536)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49536),49536)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa44_signature_internal) /\
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
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_sign_ok_44 skb MU RND
                     then word 0 else word 4294967292) /\
                    (!t. t < 2420
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             mld_sign_sig_44 skb MU RND t))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 49536),49536)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, ext, rho, what the C *)
(* code declassifies in each attempt (mld_sign_declass), the addresses of    *)
(* memset and memcpy and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset and memcpy may read and the constants of the callees, and the      *)
(* writes within the signature and the stack.                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
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
          mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
          mld_sign_terminates_44 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49536),49536)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49536),49536)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa44_signature_internal) /\
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
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_sign_ok_44 skb MU RND
                     then word 0 else word 4294967292) /\
                    (!t. t < 2420
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             mld_sign_sig_44 skb MU RND t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen rnd sk ext
                             (mld_sk_rho skb)
                             (mld_sign_declass_44 skb MU RND)
                             guard mf mc pc
                             (word_sub stackpointer (word 49536))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; pre,prelen; rnd,32; sk,2560;
                         word_sub stackpointer (word 49536),49536;
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
                           mldsa44_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const2),16]
                        [sig,2420;
                         word_sub stackpointer (word 49536),49536]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 49536),49536)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
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
          mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
          mld_sign_terminates_44 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49536),49536)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49536),49536)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa44_signature_internal) /\
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
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen rnd sk ext
                             (mld_sk_rho skb)
                             (mld_sign_declass_44 skb MU RND)
                             guard mf mc pc
                             (word_sub stackpointer (word 49536))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; pre,prelen; rnd,32; sk,2560;
                         word_sub stackpointer (word 49536),49536;
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
                           mldsa44_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const2),16]
                        [sig,2420;
                         word_sub stackpointer (word 49536),49536]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 49536),49536)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
