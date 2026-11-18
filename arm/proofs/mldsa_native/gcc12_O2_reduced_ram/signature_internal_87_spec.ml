(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing: the statement. This is the code for mldsa87_signature_internal   *)
(* (mld_sign_signature_internal in sign.c, with                              *)
(* mld_attempt_signature_generation and mld_compute_pack_z inlined) from     *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 and  *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which unpacks the     *)
(* secret key, computes mu (or takes it from m if ext is nonzero) and rho'', *)
(* keeps rho for the entries of the matrix, which are sampled from it when   *)
(* used, and makes up to 9361 attempts: each computes w = A y, sampling each *)
(* polynomial of y when used, w1 packed, c~ and the challenge, then z,       *)
(* sampling each polynomial of y again and checking and packing it, and for  *)
(* each row checks w0 - c s2 and c t0, and finally packs c~ and the hints,   *)
(* rejecting at the first check that fails. It returns 0 with the signature  *)
(* of the first attempt that succeeds, or -4                                 *)
(* (MLD_ERR_SIGN_ATTEMPTS_EXHAUSTED) with the signature zeroed, and zeroes   *)
(* its buffers with memset. It is verified in the whole image (see           *)
(* libmldsa.ml) against mld_sign_ok and mld_sign_sig of                      *)
(* common/mldsa_native_sign.ml, using the theorems for the callees and the   *)
(* contracts memset_full_contract and memcpy_full_contract, assuming that    *)
(* the sampling of the entries of the matrix and of the challenge in each    *)
(* attempt terminate, and shown to be constant time and memory safe, with    *)
(* the events depending only on public values and those that the C code      *)
(* declassifies (mld_sign_declass).                                          *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stubs for memset and memcpy:

    mldsa87_signature_internal:
       +0x0: mov     x12, #0x3770
       +0x4: sub     sp, sp, x12
       +0x8: mov     x11, #0x3420
       +0xc: mov     x12, #0x3580
      +0x10: adrp    x8, <page>
      +0x14: ldr     x8, [x8, #4088]
      +0x18: stp     x23, x24, [sp, #32]
      +0x1c: add     x23, sp, #0xcf
      +0x20: and     x23, x23, #0xffffffffffffffe0
      +0x24: mov     x13, #0x35c0
      +0x28: add     x9, x23, x11
      +0x2c: add     x10, x23, x12
      +0x30: add     x11, x23, x13
      +0x34: mov     x14, #0x35a0
      +0x38: add     x12, x23, x14
      +0x3c: stp     x19, x20, [sp]
      +0x40: mov     x24, x1
      +0x44: stp     x21, x22, [sp, #16]
      +0x48: mov     x20, x3
      +0x4c: mov     x22, x2
      +0x50: stp     x25, x26, [sp, #48]
      +0x54: mov     w25, w7
      +0x58: add     x26, x9, #0x20
      +0x5c: stp     x27, x28, [sp, #64]
      +0x60: mov     x21, x4
      +0x64: mov     x19, x5
      +0x68: str     x30, [sp, #80]
      +0x6c: mov     x1, x26
      +0x70: str     x0, [sp, #104]
      +0x74: mov     x27, x9
      +0x78: str     x9, [sp, #136]
      +0x7c: add     x2, x9, #0x60
      +0x80: stp     x11, x10, [sp, #152]
      +0x84: mov     x5, x10
      +0x88: mov     x4, x11
      +0x8c: str     x12, [sp, #168]
      +0x90: mov     x3, x12
      +0x94: mov     x0, x9
      +0x98: ldr     x7, [x8]
      +0x9c: str     x7, [sp, #14184]
      +0xa0: mov     x7, #0x0
      +0xa4: bl      <mldsa87_unpack_sk>
      +0xa8: cbnz    w25, <mldsa87_signature_internal+0x4d8>
      +0xac: mov     x6, x22
      +0xb0: mov     x5, x24
      +0xb4: mov     x4, x21
      +0xb8: mov     x3, x20
      +0xbc: mov     x1, x26
      +0xc0: add     x0, x27, #0x80
      +0xc4: mov     x2, #0x40
      +0xc8: bl      <mld_H87.constprop.0>
      +0xcc: ldr     x22, [sp, #136]
      +0xd0: mov     x1, #0x3020
      +0xd4: mov     x5, #0x3560
      +0xd8: mov     x3, x19
      +0xdc: mov     x4, #0x20
      +0xe0: mov     x6, #0x3698
      +0xe4: mov     x7, #0x3520
      +0xe8: mov     x8, #0x2820
      +0xec: mov     x9, #0x2420
      +0xf0: mov     x10, #0x2c20
      +0xf4: mov     x2, x4
      +0xf8: add     x19, x23, x1
      +0xfc: add     x1, x23, x5
     +0x100: add     x5, x22, #0x80
     +0x104: mov     x0, #0x3600
     +0x108: add     x21, sp, x6
     +0x10c: mov     x6, #0x40
     +0x110: str     x1, [sp, #128]
     +0x114: add     x1, x23, x10
     +0x118: add     x26, x23, x0
     +0x11c: add     x28, x23, x7
     +0x120: add     x0, x22, #0xc0
     +0x124: add     x24, x23, x8
     +0x128: add     x20, x23, x9
     +0x12c: str     x1, [sp, #120]
     +0x130: add     x1, x22, #0x60
     +0x134: bl      <mld_H87.constprop.0>
     +0x138: str     wzr, [sp, #116]
     +0x13c: add     x0, x23, #0x2, lsl #12
     +0x140: mov     x1, x22
     +0x144: str     x0, [sp, #144]
     +0x148: bl      <mldsa87_polyvec_matrix_expand_lazy>
     +0x14c: nop
     +0x150: ldp     x2, x22, [sp, #128]
     +0x154: mov     x3, x19
     +0x158: ldr     x1, [sp, #144]
     +0x15c: mov     x0, x23
     +0x160: add     x4, x22, #0xc0
     +0x164: stur    x4, [x26, #-160]
     +0x168: ldrh    w4, [sp, #116]
     +0x16c: sturh   w4, [x26, #-152]
     +0x170: bl      <mldsa87_polyvec_matrix_pointwise_montgomery_yvec_lazy>
     +0x174: mov     x0, x23
     +0x178: bl      <mldsa87_polyveck_caddq>
     +0x17c: ldr     x25, [sp, #120]
     +0x180: mov     x2, x19
     +0x184: mov     x1, x23
     +0x188: mov     x0, x25
     +0x18c: bl      <mldsa87_polyveck_decompose_pack_w1>
     +0x190: mov     x0, x21
     +0x194: bl      <mldsa_shake256_init>
     +0x198: add     x1, x22, #0x80
     +0x19c: mov     x0, x21
     +0x1a0: mov     x2, #0x40
     +0x1a4: bl      <mldsa_shake256_absorb>
     +0x1a8: mov     x1, x25
     +0x1ac: mov     x2, #0x400
     +0x1b0: mov     x0, x21
     +0x1b4: bl      <mldsa_shake256_absorb>
     +0x1b8: mov     x0, x21
     +0x1bc: bl      <mldsa_shake256_finalize>
     +0x1c0: mov     x2, x21
     +0x1c4: mov     x1, #0x40
     +0x1c8: mov     x0, x28
     +0x1cc: bl      <mldsa_shake256_squeeze>
     +0x1d0: mov     x0, x21
     +0x1d4: bl      <mldsa_shake256_release>
     +0x1d8: movi    v0.4s, #0x0
     +0x1dc: stp     q0, q0, [x21]
     +0x1e0: stp     q0, q0, [x21, #32]
     +0x1e4: stp     q0, q0, [x21, #64]
     +0x1e8: stp     q0, q0, [x21, #96]
     +0x1ec: stp     q0, q0, [x21, #128]
     +0x1f0: stp     q0, q0, [x21, #160]
     +0x1f4: str     q0, [x21, #192]
     +0x1f8: mov     x1, x28
     +0x1fc: mov     x0, x24
     +0x200: bl      <mldsa87_poly_challenge>
     +0x204: mov     x25, #0x0
     +0x208: mov     x0, x24
     +0x20c: mov     w22, #0x0
     +0x210: bl      <mldsa_poly_ntt>
     +0x214: nop
     +0x218: ldr     x1, [x23, #13760]
     +0x21c: mov     x0, x20
     +0x220: add     x1, x1, x25
     +0x224: bl      <mldsa87_polyeta_unpack>
     +0x228: mov     x0, x20
     +0x22c: bl      <mldsa_poly_ntt>
     +0x230: mov     x1, x24
     +0x234: mov     x0, x20
     +0x238: bl      <mldsa_poly_pointwise_montgomery>
     +0x23c: mov     x0, x20
     +0x240: bl      <mldsa_poly_invntt_tomont>
     +0x244: ldur    x1, [x26, #-160]
     +0x248: mov     x0, x19
     +0x24c: ldurh   w2, [x26, #-152]
     +0x250: add     w2, w22, w2
     +0x254: bl      <mldsa87_poly_uniform_gamma1>
     +0x258: mov     x1, x19
     +0x25c: mov     x0, x20
     +0x260: bl      <mldsa_poly_add>
     +0x264: mov     x0, x20
     +0x268: bl      <mldsa_poly_reduce>
     +0x26c: mov     w1, #0xff88
     +0x270: mov     x0, x20
     +0x274: movk    w1, #0x7, lsl #16
     +0x278: bl      <mldsa_poly_chknorm>
     +0x27c: cbnz    w0, <mldsa87_signature_internal+0x4d0>
     +0x280: ldr     x0, [sp, #104]
     +0x284: mov     w2, w22
     +0x288: mov     x1, x20
     +0x28c: add     w22, w22, #0x1
     +0x290: add     x25, x25, #0x60
     +0x294: bl      <mldsa87_pack_sig_z>
     +0x298: cmp     w22, #0x7
     +0x29c: b.ne    <mldsa87_signature_internal+0x218>
     +0x2a0: mov     x22, x23
     +0x2a4: mov     x25, #0x0
     +0x2a8: mov     x27, #0x0
     +0x2ac: nop
     +0x2b0: ldr     x1, [x23, #13696]
     +0x2b4: mov     x0, x19
     +0x2b8: add     x1, x1, x27
     +0x2bc: bl      <mldsa87_polyeta_unpack>
     +0x2c0: mov     x0, x19
     +0x2c4: bl      <mldsa_poly_ntt>
     +0x2c8: mov     x1, x24
     +0x2cc: mov     x0, x19
     +0x2d0: bl      <mldsa_poly_pointwise_montgomery>
     +0x2d4: mov     x0, x19
     +0x2d8: bl      <mldsa_poly_invntt_tomont>
     +0x2dc: mov     x1, x19
     +0x2e0: mov     x0, x22
     +0x2e4: bl      <mldsa_poly_sub>
     +0x2e8: mov     x0, x22
     +0x2ec: bl      <mldsa_poly_reduce>
     +0x2f0: mov     w1, #0xfe88
     +0x2f4: mov     x0, x22
     +0x2f8: movk    w1, #0x3, lsl #16
     +0x2fc: bl      <mldsa_poly_chknorm>
     +0x300: cbnz    w0, <mldsa87_signature_internal+0x4d0>
     +0x304: ldr     x1, [x23, #13728]
     +0x308: mov     x0, x19
     +0x30c: add     x1, x1, x25
     +0x310: bl      <mldsa_polyt0_unpack>
     +0x314: mov     x0, x19
     +0x318: bl      <mldsa_poly_ntt>
     +0x31c: mov     x1, x24
     +0x320: mov     x0, x19
     +0x324: bl      <mldsa_poly_pointwise_montgomery>
     +0x328: mov     x0, x19
     +0x32c: bl      <mldsa_poly_invntt_tomont>
     +0x330: mov     x0, x19
     +0x334: bl      <mldsa_poly_reduce>
     +0x338: mov     x0, x19
     +0x33c: mov     w1, #0x3ff00
     +0x340: bl      <mldsa_poly_chknorm>
     +0x344: cbnz    w0, <mldsa87_signature_internal+0x4d0>
     +0x348: mov     x0, x22
     +0x34c: mov     x1, x19
     +0x350: add     x25, x25, #0x1a0
     +0x354: bl      <mldsa_poly_add>
     +0x358: add     x27, x27, #0x60
     +0x35c: add     x22, x22, #0x400
     +0x360: cmp     x25, #0xd00
     +0x364: b.ne    <mldsa87_signature_internal+0x2b0>
     +0x368: ldr     x22, [sp, #104]
     +0x36c: mov     x1, x28
     +0x370: mov     x0, x22
     +0x374: bl      <mldsa87_pack_sig_c>
     +0x378: ldr     x2, [sp, #120]
     +0x37c: mov     x0, x22
     +0x380: mov     x3, x19
     +0x384: mov     x1, x23
     +0x388: bl      <mldsa87_pack_sig_h>
     +0x38c: mov     w22, w0
     +0x390: mov     x0, x20
     +0x394: mov     x2, #0x400
     +0x398: mov     w1, #0x0
     +0x39c: bl      <memset@plt>
     +0x3a0: mov     x2, #0x400
     +0x3a4: mov     x0, x24
     +0x3a8: mov     w1, #0x0
     +0x3ac: bl      <memset@plt>
     +0x3b0: mov     x2, #0x2000
     +0x3b4: mov     x0, x23
     +0x3b8: mov     w1, #0x0
     +0x3bc: bl      <memset@plt>
     +0x3c0: ldr     x25, [sp, #120]
     +0x3c4: mov     x2, #0x400
     +0x3c8: mov     w1, #0x0
     +0x3cc: mov     x0, x25
     +0x3d0: bl      <memset@plt>
     +0x3d4: mov     x2, #0x400
     +0x3d8: mov     x0, x19
     +0x3dc: mov     w1, #0x0
     +0x3e0: bl      <memset@plt>
     +0x3e4: ldr     x0, [sp, #128]
     +0x3e8: stp     xzr, xzr, [x0]
     +0x3ec: movi    v0.4s, #0x0
     +0x3f0: stp     q0, q0, [x28]
     +0x3f4: stp     q0, q0, [x28, #32]
     +0x3f8: cbz     w22, <mldsa87_signature_internal+0x438>
     +0x3fc: cmn     w22, #0x1
     +0x400: b.ne    <mldsa87_signature_internal+0x424>
     +0x404: ldr     w0, [sp, #116]
     +0x408: mov     w1, #0xfff7
     +0x40c: add     w0, w0, #0x7
     +0x410: and     w2, w0, #0xffff
     +0x414: str     w2, [sp, #116]
     +0x418: cmp     w1, w0, uxth
     +0x41c: b.ne    <mldsa87_signature_internal+0x150>
     +0x420: mov     w22, #0xfffffffc
     +0x424: ldr     x19, [sp, #104]
     +0x428: mov     x2, #0x1213
     +0x42c: mov     w1, #0x0
     +0x430: mov     x0, x19
     +0x434: bl      <memset@plt>
     +0x438: ldr     x0, [sp, #160]
     +0x43c: str     xzr, [x23, #13696]
     +0x440: ldr     x0, [sp, #168]
     +0x444: str     xzr, [x23, #13728]
     +0x448: ldr     x0, [sp, #152]
     +0x44c: str     xzr, [x23, #13760]
     +0x450: ldr     x19, [sp, #144]
     +0x454: mov     x2, #0x420
     +0x458: mov     w1, #0x0
     +0x45c: mov     x0, x19
     +0x460: bl      <memset@plt>
     +0x464: ldr     x0, [sp, #136]
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
     +0x494: ldr     x2, [sp, #14184]
     +0x498: ldr     x1, [x0]
     +0x49c: subs    x2, x2, x1
     +0x4a0: mov     x1, #0x0
     +0x4a4: b.ne    <mldsa87_signature_internal+0x4f4>
     +0x4a8: ldp     x19, x20, [sp]
     +0x4ac: mov     w0, w22
     +0x4b0: ldp     x21, x22, [sp, #16]
     +0x4b4: mov     x12, #0x3770
     +0x4b8: ldp     x23, x24, [sp, #32]
     +0x4bc: ldp     x25, x26, [sp, #48]
     +0x4c0: ldp     x27, x28, [sp, #64]
     +0x4c4: ldr     x30, [sp, #80]
     +0x4c8: add     sp, sp, x12
     +0x4cc: ret
     +0x4d0: mov     w22, #0xffffffff
     +0x4d4: b       <mldsa87_signature_internal+0x390>
     +0x4d8: ldr     x0, [sp, #136]
     +0x4dc: ldp     q2, q3, [x24]
     +0x4e0: add     x0, x0, #0x80
     +0x4e4: ldp     q0, q1, [x24, #32]
     +0x4e8: stp     q2, q3, [x0]
     +0x4ec: stp     q0, q1, [x0, #32]
     +0x4f0: b       <mldsa87_signature_internal+0xcc>
     +0x4f4: bl      <__stack_chk_fail@plt>

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

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
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

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
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
           [(sig,4627); (word_sub stackpointer (word 15760),15760)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 15760),15760)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
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
                  memory :> bytes(word_sub stackpointer (word 15760),
                                  15760)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, ext, rho, what the C *)
(* code declassifies in each attempt (mld_sign_declass), the addresses of    *)
(* memset and memcpy and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset and memcpy may read and the constants of the callees, and the      *)
(* writes within the signature and the stack.                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
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
           [(sig,4627); (word_sub stackpointer (word 15760),15760)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 15760),15760)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
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
                             (word_sub stackpointer (word 15760))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; pre,prelen; rnd,32; sk,4896;
                         word_sub stackpointer (word 15760),15760;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [sig,4627;
                         word_sub stackpointer (word 15760),15760]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 15760),
                                  15760)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
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
           [(sig,4627); (word_sub stackpointer (word 15760),15760)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 15760),15760)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
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
                             (word_sub stackpointer (word 15760))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; pre,prelen; rnd,32; sk,4896;
                         word_sub stackpointer (word 15760),15760;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const1),16;
                         word(pc + mldsa_poly_pointwise_montgomery_const2),16]
                        [sig,4627;
                         word_sub stackpointer (word 15760),15760]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 15760),
                                  15760)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
