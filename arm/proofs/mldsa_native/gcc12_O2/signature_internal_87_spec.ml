(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing: the statement. This is the code for mldsa87_signature_internal   *)
(* (mld_sign_signature_internal in sign.c, with                              *)
(* mld_attempt_signature_generation and mld_compute_pack_z inlined) from     *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mldsa_native/README.md), which unpacks the secret key, computes mu (or    *)
(* takes it from m if ext is nonzero) and rho'', expands the matrix from     *)
(* rho, and makes up to 9361 attempts: each samples y, computes w = A y, w1  *)
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

    mldsa87_signature_internal:
       +0x0: sub     sp, sp, #0x2d0
       +0x4: sub     sp, sp, #0x1a, lsl #12
       +0x8: add     x8, sp, #0xbf
       +0xc: and     x9, x8, #0xffffffffffffffe0
      +0x10: add     x10, x9, #0x1a, lsl #12
      +0x14: add     x11, x9, #0x10, lsl #12
      +0x18: add     x12, x9, #0x17, lsl #12
      +0x1c: stp     x10, x9, [sp, #128]
      +0x20: add     x9, x9, #0x12, lsl #12
      +0x24: adrp    x8, <page>
      +0x28: ldr     x8, [x8, #4088]
      +0x2c: add     x12, x12, #0x800
      +0x30: stp     x19, x20, [sp]
      +0x34: mov     x20, x3
      +0x38: mov     x3, x9
      +0x3c: stp     x21, x22, [sp, #16]
      +0x40: mov     x19, x5
      +0x44: mov     x22, x2
      +0x48: stp     x23, x24, [sp, #32]
      +0x4c: mov     w24, w7
      +0x50: mov     x23, x1
      +0x54: stp     x25, x26, [sp, #48]
      +0x58: add     x25, x10, #0x20
      +0x5c: mov     x21, x4
      +0x60: stp     x27, x28, [sp, #64]
      +0x64: mov     x1, x25
      +0x68: mov     x26, x10
      +0x6c: str     x30, [sp, #80]
      +0x70: add     x2, x10, #0x60
      +0x74: str     x0, [sp, #96]
      +0x78: mov     x5, x11
      +0x7c: str     x9, [sp, #104]
      +0x80: add     x9, sp, #0x18, lsl #12
      +0x84: stp     x12, x11, [sp, #144]
      +0x88: add     x9, x9, #0x40
      +0x8c: mov     x4, x12
      +0x90: ldr     x7, [x8]
      +0x94: str     x7, [x9, #8840]
      +0x98: mov     x7, #0x0
      +0x9c: mov     x0, x10
      +0xa0: bl      <mldsa87_unpack_sk>
      +0xa4: cbnz    w24, <+0x4e8>
      +0xa8: mov     x6, x22
      +0xac: mov     x5, x23
      +0xb0: mov     x4, x21
      +0xb4: mov     x3, x20
      +0xb8: mov     x1, x25
      +0xbc: add     x0, x26, #0x80
      +0xc0: mov     x2, #0x40
      +0xc4: bl      <mld_H87>
      +0xc8: ldp     x24, x21, [sp, #128]
      +0xcc: mov     x3, x19
      +0xd0: mov     x4, #0x20
      +0xd4: mov     x2, x4
      +0xd8: mov     x6, #0x40
      +0xdc: add     x22, sp, #0x1a, lsl #12
      +0xe0: str     wzr, [sp, #116]
      +0xe4: add     x22, x22, #0x1f8
      +0xe8: add     x5, x24, #0x80
      +0xec: add     x1, x21, #0x19, lsl #12
      +0xf0: add     x1, x1, #0xc00
      +0xf4: add     x0, x24, #0xc0
      +0xf8: add     x27, x21, #0x15, lsl #12
      +0xfc: add     x25, x21, #0x1a, lsl #12
     +0x100: add     x23, x21, #0x19, lsl #12
     +0x104: add     x20, x21, #0x19, lsl #12
     +0x108: str     x1, [sp, #120]
     +0x10c: add     x1, x24, #0x60
     +0x110: bl      <mld_H87>
     +0x114: add     x27, x27, #0xc00
     +0x118: add     x19, x21, #0x14, lsl #12
     +0x11c: add     x26, x21, #0xe, lsl #12
     +0x120: add     x25, x25, #0x100
     +0x124: add     x23, x23, #0x800
     +0x128: add     x20, x20, #0x400
     +0x12c: mov     x1, x24
     +0x130: mov     x0, x21
     +0x134: bl      <mldsa87_polyvec_matrix_expand_eager>
     +0x138: ldrh    w2, [sp, #116]
     +0x13c: mov     x0, x27
     +0x140: ldr     x21, [sp, #128]
     +0x144: add     x1, x21, #0xc0
     +0x148: bl      <mldsa87_polyvecl_uniform_gamma1>
     +0x14c: ldr     x1, [sp, #136]
     +0x150: mov     x3, x19
     +0x154: mov     x2, x27
     +0x158: mov     x0, x26
     +0x15c: bl      <mldsa87_polyvec_matrix_pointwise_montgomery_yvec_eager>
     +0x160: mov     x0, x26
     +0x164: bl      <mldsa87_polyveck_caddq>
     +0x168: ldr     x24, [sp, #120]
     +0x16c: mov     x2, x19
     +0x170: mov     x1, x26
     +0x174: mov     x0, x24
     +0x178: bl      <mldsa87_polyveck_decompose_pack_w1>
     +0x17c: mov     x0, x22
     +0x180: bl      <mldsa_shake256_init>
     +0x184: add     x1, x21, #0x80
     +0x188: mov     x0, x22
     +0x18c: mov     x2, #0x40
     +0x190: bl      <mldsa_shake256_absorb>
     +0x194: mov     x1, x24
     +0x198: mov     x2, #0x400
     +0x19c: mov     x0, x22
     +0x1a0: bl      <mldsa_shake256_absorb>
     +0x1a4: mov     x0, x22
     +0x1a8: bl      <mldsa_shake256_finalize>
     +0x1ac: mov     x2, x22
     +0x1b0: mov     x1, #0x40
     +0x1b4: mov     x0, x25
     +0x1b8: bl      <mldsa_shake256_squeeze>
     +0x1bc: mov     x0, x22
     +0x1c0: bl      <mldsa_shake256_release>
     +0x1c4: movi    v0.4s, #0x0
     +0x1c8: stp     q0, q0, [x22]
     +0x1cc: stp     q0, q0, [x22, #32]
     +0x1d0: stp     q0, q0, [x22, #64]
     +0x1d4: stp     q0, q0, [x22, #96]
     +0x1d8: stp     q0, q0, [x22, #128]
     +0x1dc: stp     q0, q0, [x22, #160]
     +0x1e0: str     q0, [x22, #192]
     +0x1e4: mov     x1, x25
     +0x1e8: mov     x0, x23
     +0x1ec: ldr     x28, [sp, #144]
     +0x1f0: bl      <mldsa87_poly_challenge>
     +0x1f4: mov     x24, x27
     +0x1f8: mov     x0, x23
     +0x1fc: mov     w21, #0x0
     +0x200: bl      <mldsa_poly_ntt>
     +0x204: nop
     +0x208: mov     x2, #0x400
     +0x20c: mov     x1, x28
     +0x210: mov     x0, x20
     +0x214: bl      <memcpy@plt>
     +0x218: mov     x1, x23
     +0x21c: mov     x0, x20
     +0x220: bl      <mldsa_poly_pointwise_montgomery>
     +0x224: mov     x0, x20
     +0x228: bl      <mldsa_poly_invntt_tomont>
     +0x22c: mov     x2, #0x400
     +0x230: mov     x1, x24
     +0x234: mov     x0, x19
     +0x238: bl      <memcpy@plt>
     +0x23c: mov     x1, x19
     +0x240: mov     x0, x20
     +0x244: bl      <mldsa_poly_add>
     +0x248: mov     x0, x20
     +0x24c: bl      <mldsa_poly_reduce>
     +0x250: mov     w1, #0xff88
     +0x254: mov     x0, x20
     +0x258: movk    w1, #0x7, lsl #16
     +0x25c: bl      <mldsa_poly_chknorm>
     +0x260: cbnz    w0, <+0x4e0>
     +0x264: ldr     x0, [sp, #96]
     +0x268: mov     w2, w21
     +0x26c: mov     x1, x20
     +0x270: add     w21, w21, #0x1
     +0x274: add     x28, x28, #0x400
     +0x278: add     x24, x24, #0x400
     +0x27c: bl      <mldsa87_pack_sig_z>
     +0x280: cmp     w21, #0x7
     +0x284: b.ne    <+0x208>
     +0x288: ldr     x28, [sp, #104]
     +0x28c: mov     x21, x26
     +0x290: ldr     x24, [sp, #152]
     +0x294: nop
     +0x298: mov     x2, #0x400
     +0x29c: mov     x1, x24
     +0x2a0: mov     x0, x19
     +0x2a4: bl      <memcpy@plt>
     +0x2a8: mov     x1, x23
     +0x2ac: mov     x0, x19
     +0x2b0: bl      <mldsa_poly_pointwise_montgomery>
     +0x2b4: mov     x0, x19
     +0x2b8: bl      <mldsa_poly_invntt_tomont>
     +0x2bc: mov     x1, x19
     +0x2c0: mov     x0, x21
     +0x2c4: bl      <mldsa_poly_sub>
     +0x2c8: mov     x0, x21
     +0x2cc: bl      <mldsa_poly_reduce>
     +0x2d0: mov     w1, #0xfe88
     +0x2d4: mov     x0, x21
     +0x2d8: movk    w1, #0x3, lsl #16
     +0x2dc: bl      <mldsa_poly_chknorm>
     +0x2e0: cbnz    w0, <+0x4e0>
     +0x2e4: mov     x2, #0x400
     +0x2e8: mov     x1, x28
     +0x2ec: mov     x0, x19
     +0x2f0: bl      <memcpy@plt>
     +0x2f4: mov     x1, x23
     +0x2f8: mov     x0, x19
     +0x2fc: bl      <mldsa_poly_pointwise_montgomery>
     +0x300: mov     x0, x19
     +0x304: bl      <mldsa_poly_invntt_tomont>
     +0x308: mov     x0, x19
     +0x30c: bl      <mldsa_poly_reduce>
     +0x310: mov     x0, x19
     +0x314: mov     w1, #0x3ff00
     +0x318: bl      <mldsa_poly_chknorm>
     +0x31c: cbnz    w0, <+0x4e0>
     +0x320: mov     x0, x21
     +0x324: mov     x1, x19
     +0x328: bl      <mldsa_poly_add>
     +0x32c: add     x24, x24, #0x400
     +0x330: ldr     x0, [sp, #104]
     +0x334: add     x28, x28, #0x400
     +0x338: add     x21, x21, #0x400
     +0x33c: cmp     x24, x0
     +0x340: b.ne    <+0x298>
     +0x344: ldr     x21, [sp, #96]
     +0x348: mov     x1, x25
     +0x34c: mov     x0, x21
     +0x350: bl      <mldsa87_pack_sig_c>
     +0x354: ldr     x2, [sp, #120]
     +0x358: mov     x0, x21
     +0x35c: mov     x3, x19
     +0x360: mov     x1, x26
     +0x364: bl      <mldsa87_pack_sig_h>
     +0x368: mov     w21, w0
     +0x36c: mov     x0, x20
     +0x370: mov     x2, #0x400
     +0x374: mov     w1, #0x0
     +0x378: bl      <memset@plt>
     +0x37c: mov     x2, #0x400
     +0x380: mov     x0, x23
     +0x384: mov     w1, #0x0
     +0x388: bl      <memset@plt>
     +0x38c: mov     x2, #0x2000
     +0x390: mov     x0, x26
     +0x394: mov     w1, #0x0
     +0x398: bl      <memset@plt>
     +0x39c: ldr     x24, [sp, #120]
     +0x3a0: mov     x2, #0x400
     +0x3a4: mov     w1, #0x0
     +0x3a8: mov     x0, x24
     +0x3ac: bl      <memset@plt>
     +0x3b0: mov     x2, #0x1c00
     +0x3b4: mov     x0, x19
     +0x3b8: mov     w1, #0x0
     +0x3bc: bl      <memset@plt>
     +0x3c0: mov     x2, #0x1c00
     +0x3c4: mov     x0, x27
     +0x3c8: mov     w1, #0x0
     +0x3cc: bl      <memset@plt>
     +0x3d0: movi    v0.4s, #0x0
     +0x3d4: stp     q0, q0, [x25]
     +0x3d8: stp     q0, q0, [x25, #32]
     +0x3dc: cbz     w21, <+0x41c>
     +0x3e0: cmn     w21, #0x1
     +0x3e4: b.ne    <+0x408>
     +0x3e8: ldr     w0, [sp, #116]
     +0x3ec: mov     w1, #0xfff7
     +0x3f0: add     w0, w0, #0x7
     +0x3f4: and     w2, w0, #0xffff
     +0x3f8: str     w2, [sp, #116]
     +0x3fc: cmp     w1, w0, uxth
     +0x400: b.ne    <+0x138>
     +0x404: mov     w21, #0xfffffffc
     +0x408: ldr     x19, [sp, #96]
     +0x40c: mov     x2, #0x1213
     +0x410: mov     w1, #0x0
     +0x414: mov     x0, x19
     +0x418: bl      <memset@plt>
     +0x41c: ldr     x19, [sp, #152]
     +0x420: mov     x2, #0x2000
     +0x424: mov     w1, #0x0
     +0x428: mov     x0, x19
     +0x42c: bl      <memset@plt>
     +0x430: ldr     x19, [sp, #104]
     +0x434: mov     x2, #0x2000
     +0x438: mov     w1, #0x0
     +0x43c: mov     x0, x19
     +0x440: bl      <memset@plt>
     +0x444: ldr     x19, [sp, #144]
     +0x448: mov     x2, #0x1c00
     +0x44c: mov     w1, #0x0
     +0x450: mov     x0, x19
     +0x454: bl      <memset@plt>
     +0x458: ldr     x19, [sp, #136]
     +0x45c: mov     x2, #0xe000
     +0x460: mov     w1, #0x0
     +0x464: mov     x0, x19
     +0x468: bl      <memset@plt>
     +0x46c: ldr     x0, [sp, #128]
     +0x470: movi    v0.4s, #0x0
     +0x474: stp     q0, q0, [x0]
     +0x478: stp     q0, q0, [x0, #32]
     +0x47c: stp     q0, q0, [x0, #64]
     +0x480: stp     q0, q0, [x0, #96]
     +0x484: stp     q0, q0, [x0, #128]
     +0x488: stp     q0, q0, [x0, #160]
     +0x48c: stp     q0, q0, [x0, #192]
     +0x490: stp     q0, q0, [x0, #224]
     +0x494: adrp    x0, <page>
     +0x498: ldr     x0, [x0, #4088]
     +0x49c: add     x2, sp, #0x18, lsl #12
     +0x4a0: add     x2, x2, #0x40
     +0x4a4: ldr     x3, [x2, #8840]
     +0x4a8: ldr     x1, [x0]
     +0x4ac: subs    x3, x3, x1
     +0x4b0: mov     x1, #0x0
     +0x4b4: b.ne    <+0x504>
     +0x4b8: ldp     x19, x20, [sp]
     +0x4bc: mov     w0, w21
     +0x4c0: ldp     x21, x22, [sp, #16]
     +0x4c4: ldp     x23, x24, [sp, #32]
     +0x4c8: ldp     x25, x26, [sp, #48]
     +0x4cc: ldp     x27, x28, [sp, #64]
     +0x4d0: ldr     x30, [sp, #80]
     +0x4d4: add     sp, sp, #0x2d0
     +0x4d8: add     sp, sp, #0x1a, lsl #12
     +0x4dc: ret
     +0x4e0: mov     w21, #0xffffffff
     +0x4e4: b       <+0x36c>
     +0x4e8: ldr     x0, [sp, #128]
     +0x4ec: ldp     q2, q3, [x23]
     +0x4f0: add     x0, x0, #0x80
     +0x4f4: ldp     q0, q1, [x23, #32]
     +0x4f8: stp     q2, q3, [x0]
     +0x4fc: stp     q0, q1, [x0, #32]
     +0x500: b       <+0xc8>
     +0x504: bl      <__stack_chk_fail@plt>

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

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_signature_internal"; layout_range "plt_memset";
    layout_range "plt_memcpy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for memset and memcpy. The secret key *)
(* skb at sk (4896 bytes), the message M of mlen bytes at m and the prefix   *)
(* PRE of prelen bytes at pre (or, if ext is nonzero as a 32-bit integer, mu *)
(* in the first 64 bytes at m), and the 32 bytes RND at rnd, with MU the mu  *)
(* that the code uses: the result is 0, with the signature mld_sign_sig at   *)
(* sig (4627 bytes), if one of the 9361 attempts succeeds (mld_sign_ok), and *)
(* -4 with the signature zeroed otherwise. The stack is the 107216 bytes of  *)
(* the function and those of the callees below them.                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
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
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          mld_sign_terminates_87 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112272),112272)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112272),112272)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_signature_internal) /\
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
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_sign_ok_87 skb MU RND
                     then word 0 else word 4294967292) /\
                    (!t. t < 4627
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             mld_sign_sig_87 skb MU RND t))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112272),
                                  112272)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, ext, rho, what the C *)
(* code declassifies in each attempt (mld_sign_declass), the addresses of    *)
(* memset and memcpy and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset and memcpy may read and the constants of the callees, and the      *)
(* writes within the signature and the stack.                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
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
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          mld_sign_terminates_87 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112272),112272)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112272),112272)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_signature_internal) /\
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
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_sign_ok_87 skb MU RND
                     then word 0 else word 4294967292) /\
                    (!t. t < 4627
                         ==> read(memory :> bytes8(word_add sig (word t))) s =
                             mld_sign_sig_87 skb MU RND t) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen rnd sk ext
                             (mld_sk_rho skb)
                             (mld_sign_declass_87 skb MU RND)
                             guard mf mc pc
                             (word_sub stackpointer (word 112272))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; pre,prelen; rnd,32; sk,4896;
                         word_sub stackpointer (word 112272),112272;
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
                           mldsa87_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const2),16]
                        [sig,4627;
                         word_sub stackpointer (word 112272),112272]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112272),
                                  112272)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
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
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          mld_sign_terminates_87 skb MU RND /\
          PAIRWISE nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112272),112272)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112272),112272)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_signature_internal) /\
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
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events sig m mlen pre prelen rnd sk ext
                             (mld_sk_rho skb)
                             (mld_sign_declass_87 skb MU RND)
                             guard mf mc pc
                             (word_sub stackpointer (word 112272))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; pre,prelen; rnd,32; sk,4896;
                         word_sub stackpointer (word 112272),112272;
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
                           mldsa87_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const2),16]
                        [sig,4627;
                         word_sub stackpointer (word 112272),112272]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112272),
                                  112272)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
