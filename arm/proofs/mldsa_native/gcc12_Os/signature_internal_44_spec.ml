(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing: the statement. This is the code for mldsa44_signature_internal   *)
(* (mld_sign_signature_internal in sign.c, with                              *)
(* mld_attempt_signature_generation and mld_compute_pack_z inlined) from     *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -Os (see *)
(* mldsa_native/README.md), which unpacks the secret key, computes mu (or    *)
(* takes it from m if ext is nonzero) and rho'', expands the matrix from     *)
(* rho, and makes up to 16382 attempts: each samples y, computes w = A y, w1 *)
(* packed, c~ and the challenge, then z, checking and packing each           *)
(* polynomial, and for each row checks w0 - c s2 and c t0, and finally packs *)
(* c~ and the hints, rejecting at the first check that fails. It returns 0   *)
(* with the signature of the first attempt that succeeds, or -4              *)
(* (MLD_ERR_SIGN_ATTEMPTS_EXHAUSTED) with the signature zeroed, and zeroes   *)
(* its buffers with mld_zeroize (a call of memset). It is verified in the    *)
(* whole image (see libmldsa.ml) against mld_sign_ok and mld_sign_sig of     *)
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
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memcpy:

    mldsa44_signature_internal:
       +0x0: mov     x12, #0xace0
       +0x4: sub     sp, sp, x12
       +0x8: mov     x8, #0xab00
       +0xc: stp     x23, x24, [sp, #32]
      +0x10: mov     x23, x0
      +0x14: mov     x24, x4
      +0x18: adrp    x0, <page>
      +0x1c: ldr     x0, [x0, #4088]
      +0x20: stp     x19, x20, [sp]
      +0x24: add     x19, sp, #0xbf
      +0x28: stp     x21, x22, [sp, #16]
      +0x2c: and     x19, x19, #0xffffffffffffffe0
      +0x30: add     x21, x19, x8
      +0x34: stp     x25, x26, [sp, #48]
      +0x38: mov     x26, x1
      +0x3c: mov     x25, x2
      +0x40: stp     x27, x28, [sp, #64]
      +0x44: mov     w27, w7
      +0x48: mov     x7, #0x8040
      +0x4c: str     x30, [sp, #80]
      +0x50: add     x1, sp, x7
      +0x54: add     x28, x21, #0x20
      +0x58: mov     x22, x3
      +0x5c: ldr     x2, [x0]
      +0x60: str     x2, [x1, #11416]
      +0x64: mov     x2, #0x0
      +0x68: add     x0, x19, #0x7, lsl #12
      +0x6c: str     x0, [sp, #128]
      +0x70: add     x0, x19, #0x9, lsl #12
      +0x74: str     x0, [sp, #136]
      +0x78: add     x0, x19, #0x8, lsl #12
      +0x7c: mov     x3, x0
      +0x80: mov     x20, x5
      +0x84: add     x4, x19, #0x9, lsl #12
      +0x88: add     x5, x19, #0x7, lsl #12
      +0x8c: add     x2, x21, #0x60
      +0x90: mov     x1, x28
      +0x94: str     x0, [sp, #144]
      +0x98: mov     x0, x21
      +0x9c: bl      <mldsa44_unpack_sk>
      +0xa0: add     x0, x21, #0x80
      +0xa4: cbnz    w27, <mldsa44_signature_internal+0x308>
      +0xa8: mov     x3, #0x40
      +0xac: mov     x7, x25
      +0xb0: mov     x6, x26
      +0xb4: mov     x5, x24
      +0xb8: mov     x4, x22
      +0xbc: mov     x2, x28
      +0xc0: mov     x1, x3
      +0xc4: bl      <mld_H44>
      +0xc8: mov     x5, #0x20
      +0xcc: mov     x4, x20
      +0xd0: mov     x3, x5
      +0xd4: add     x6, x21, #0x80
      +0xd8: add     x2, x21, #0x60
      +0xdc: mov     x7, #0x40
      +0xe0: add     x0, x21, #0xc0
      +0xe4: mov     x1, x7
      +0xe8: bl      <mld_H44>
      +0xec: mov     x0, x19
      +0xf0: mov     x1, x21
      +0xf4: bl      <mldsa44_polyvec_matrix_expand_eager>
      +0xf8: str     wzr, [sp, #124]
      +0xfc: mov     x4, #0xa800
     +0x100: add     x0, x19, x4
     +0x104: mov     x5, #0xac00
     +0x108: str     x0, [sp, #104]
     +0x10c: add     x0, x19, x5
     +0x110: str     x0, [sp, #112]
     +0x114: ldrh    w2, [sp, #124]
     +0x118: add     x27, x19, #0x6, lsl #12
     +0x11c: add     x1, x21, #0xc0
     +0x120: mov     x0, x27
     +0x124: add     x20, x19, #0x5, lsl #12
     +0x128: add     x24, x19, #0x4, lsl #12
     +0x12c: mov     w26, #0xffb2
     +0x130: add     x22, x19, #0xa, lsl #12
     +0x134: bl      <mldsa44_polyvecl_uniform_gamma1>
     +0x138: mov     x28, #0x0
     +0x13c: mov     x3, x20
     +0x140: mov     x2, x27
     +0x144: mov     x1, x19
     +0x148: mov     x0, x24
     +0x14c: bl      <mldsa44_polyvec_matrix_pointwise_montgomery_yvec_eager>
     +0x150: movk    w26, #0x1, lsl #16
     +0x154: mov     x0, x24
     +0x158: bl      <mldsa44_polyveck_caddq>
     +0x15c: ldr     x0, [sp, #104]
     +0x160: mov     x3, #0xa400
     +0x164: mov     x2, x20
     +0x168: add     x25, x19, x3
     +0x16c: mov     x1, x24
     +0x170: bl      <mldsa44_polyveck_decompose_pack_w1>
     +0x174: ldp     x4, x0, [sp, #104]
     +0x178: add     x2, x21, #0x80
     +0x17c: mov     x7, #0x0
     +0x180: mov     x6, #0x0
     +0x184: mov     x5, #0x300
     +0x188: mov     x3, #0x40
     +0x18c: mov     x1, #0x20
     +0x190: bl      <mld_H44>
     +0x194: ldr     x1, [sp, #112]
     +0x198: mov     x0, x25
     +0x19c: bl      <mldsa44_poly_challenge>
     +0x1a0: mov     x0, x25
     +0x1a4: bl      <mldsa_poly_ntt>
     +0x1a8: ldr     x0, [sp, #136]
     +0x1ac: lsl     x3, x28, #10
     +0x1b0: mov     x2, #0x400
     +0x1b4: str     x3, [sp, #152]
     +0x1b8: add     x1, x0, x28, lsl #10
     +0x1bc: mov     x0, x22
     +0x1c0: bl      <memcpy>
     +0x1c4: mov     x1, x25
     +0x1c8: mov     x0, x22
     +0x1cc: bl      <mldsa_poly_pointwise_montgomery>
     +0x1d0: mov     x0, x22
     +0x1d4: bl      <mldsa_poly_invntt_tomont>
     +0x1d8: ldr     x3, [sp, #152]
     +0x1dc: mov     x2, #0x400
     +0x1e0: mov     x0, x20
     +0x1e4: add     x1, x27, x3
     +0x1e8: bl      <memcpy>
     +0x1ec: mov     x1, x20
     +0x1f0: mov     x0, x22
     +0x1f4: bl      <mldsa_poly_add>
     +0x1f8: mov     x0, x22
     +0x1fc: bl      <mldsa_poly_reduce>
     +0x200: mov     w1, w26
     +0x204: mov     x0, x22
     +0x208: bl      <mldsa_poly_chknorm>
     +0x20c: cbnz    w0, <mldsa44_signature_internal+0x31c>
     +0x210: mov     w2, w28
     +0x214: mov     x1, x22
     +0x218: mov     x0, x23
     +0x21c: add     x28, x28, #0x1
     +0x220: bl      <mldsa44_pack_sig_z>
     +0x224: cmp     x28, #0x4
     +0x228: b.ne    <mldsa44_signature_internal+0x1a8>
     +0x22c: mov     x26, #0x0
     +0x230: ldr     x0, [sp, #128]
     +0x234: mov     x2, #0x400
     +0x238: add     x28, x24, x26
     +0x23c: add     x1, x0, x26
     +0x240: mov     x0, x20
     +0x244: bl      <memcpy>
     +0x248: mov     x1, x25
     +0x24c: mov     x0, x20
     +0x250: bl      <mldsa_poly_pointwise_montgomery>
     +0x254: mov     x0, x20
     +0x258: bl      <mldsa_poly_invntt_tomont>
     +0x25c: mov     x1, x20
     +0x260: mov     x0, x28
     +0x264: bl      <mldsa_poly_sub>
     +0x268: mov     x0, x28
     +0x26c: bl      <mldsa_poly_reduce>
     +0x270: mov     w1, #0x73b2
     +0x274: mov     x0, x28
     +0x278: movk    w1, #0x1, lsl #16
     +0x27c: bl      <mldsa_poly_chknorm>
     +0x280: cbnz    w0, <mldsa44_signature_internal+0x31c>
     +0x284: ldr     x0, [sp, #144]
     +0x288: mov     x2, #0x400
     +0x28c: add     x1, x0, x26
     +0x290: mov     x0, x20
     +0x294: bl      <memcpy>
     +0x298: mov     x1, x25
     +0x29c: mov     x0, x20
     +0x2a0: bl      <mldsa_poly_pointwise_montgomery>
     +0x2a4: mov     x0, x20
     +0x2a8: bl      <mldsa_poly_invntt_tomont>
     +0x2ac: mov     x0, x20
     +0x2b0: bl      <mldsa_poly_reduce>
     +0x2b4: mov     w1, #0x7400
     +0x2b8: mov     x0, x20
     +0x2bc: movk    w1, #0x1, lsl #16
     +0x2c0: bl      <mldsa_poly_chknorm>
     +0x2c4: cbnz    w0, <mldsa44_signature_internal+0x31c>
     +0x2c8: mov     x1, x20
     +0x2cc: mov     x0, x28
     +0x2d0: add     x26, x26, #0x400
     +0x2d4: bl      <mldsa_poly_add>
     +0x2d8: cmp     x26, #0x1, lsl #12
     +0x2dc: b.ne    <mldsa44_signature_internal+0x230>
     +0x2e0: ldr     x1, [sp, #112]
     +0x2e4: mov     x0, x23
     +0x2e8: bl      <mldsa44_pack_sig_c>
     +0x2ec: ldr     x2, [sp, #104]
     +0x2f0: mov     x3, x20
     +0x2f4: mov     x1, x24
     +0x2f8: mov     x0, x23
     +0x2fc: bl      <mldsa44_pack_sig_h>
     +0x300: mov     w26, w0
     +0x304: b       <mldsa44_signature_internal+0x320>
     +0x308: ldp     q0, q1, [x26]
     +0x30c: stp     q0, q1, [x0]
     +0x310: ldp     q0, q1, [x26, #32]
     +0x314: stp     q0, q1, [x0, #32]
     +0x318: b       <mldsa44_signature_internal+0xc8>
     +0x31c: mov     w26, #0xffffffff
     +0x320: mov     x0, x22
     +0x324: mov     x1, #0x400
     +0x328: bl      <mld_zeroize_2>
     +0x32c: mov     x0, x25
     +0x330: mov     x1, #0x400
     +0x334: bl      <mld_zeroize_2>
     +0x338: mov     x0, x24
     +0x33c: mov     x1, #0x1000
     +0x340: bl      <mld_zeroize_2>
     +0x344: ldr     x0, [sp, #104]
     +0x348: mov     x1, #0x300
     +0x34c: bl      <mld_zeroize_2>
     +0x350: mov     x0, x20
     +0x354: mov     x1, #0x1000
     +0x358: bl      <mld_zeroize_2>
     +0x35c: mov     x0, x27
     +0x360: mov     x1, #0x1000
     +0x364: bl      <mld_zeroize_2>
     +0x368: ldr     x0, [sp, #112]
     +0x36c: mov     x1, #0x20
     +0x370: bl      <mld_zeroize_2>
     +0x374: cbz     w26, <mldsa44_signature_internal+0x3ac>
     +0x378: cmn     w26, #0x1
     +0x37c: b.ne    <mldsa44_signature_internal+0x3a0>
     +0x380: ldr     w0, [sp, #124]
     +0x384: add     w0, w0, #0x4
     +0x388: and     w1, w0, #0xffff
     +0x38c: str     w1, [sp, #124]
     +0x390: mov     w1, #0xfff8
     +0x394: cmp     w1, w0, uxth
     +0x398: b.ne    <mldsa44_signature_internal+0x114>
     +0x39c: mov     w26, #0xfffffffc
     +0x3a0: mov     x0, x23
     +0x3a4: mov     x1, #0x974
     +0x3a8: bl      <mld_zeroize_2>
     +0x3ac: ldr     x0, [sp, #128]
     +0x3b0: mov     x1, #0x1000
     +0x3b4: bl      <mld_zeroize_2>
     +0x3b8: ldr     x0, [sp, #144]
     +0x3bc: mov     x1, #0x1000
     +0x3c0: bl      <mld_zeroize_2>
     +0x3c4: ldr     x0, [sp, #136]
     +0x3c8: mov     x1, #0x1000
     +0x3cc: bl      <mld_zeroize_2>
     +0x3d0: mov     x0, x19
     +0x3d4: mov     x1, #0x4000
     +0x3d8: bl      <mld_zeroize_2>
     +0x3dc: mov     x0, x21
     +0x3e0: mov     x1, #0x100
     +0x3e4: bl      <mld_zeroize_2>
     +0x3e8: adrp    x0, <page>
     +0x3ec: ldr     x0, [x0, #4088]
     +0x3f0: mov     x1, #0x8040
     +0x3f4: add     x2, sp, x1
     +0x3f8: ldr     x3, [x2, #11416]
     +0x3fc: ldr     x1, [x0]
     +0x400: subs    x3, x3, x1
     +0x404: mov     x1, #0x0
     +0x408: b.eq    <mldsa44_signature_internal+0x410>
     +0x40c: bl      <stack_chk_fail>
     +0x410: ldp     x19, x20, [sp]
     +0x414: mov     w0, w26
     +0x418: ldp     x21, x22, [sp, #16]
     +0x41c: mov     x12, #0xace0
     +0x420: ldp     x23, x24, [sp, #32]
     +0x424: ldp     x25, x26, [sp, #48]
     +0x428: ldp     x27, x28, [sp, #64]
     +0x42c: ldr     x30, [sp, #80]
     +0x430: add     sp, sp, x12
     +0x434: ret
    plt_memcpy:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4048]
       +0x8: add     x16, x16, #0xfd0
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa44_signature_internal"; layout_range "plt_memcpy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for memset and memcpy. The secret key *)
(* skb at sk (2560 bytes), the message M of mlen bytes at m and the prefix   *)
(* PRE of prelen bytes at pre (or, if ext is nonzero as a 32-bit integer, mu *)
(* in the first 64 bytes at m), and the 32 bytes RND at rnd, with MU the mu  *)
(* that the code uses: the result is 0, with the signature mld_sign_sig at   *)
(* sig (2420 bytes), if one of the 16382 attempts succeeds (mld_sign_ok),    *)
(* and -4 with the signature zeroed otherwise. The stack is the 44256 bytes  *)
(* of the function and those of the callees below them.                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
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
           [(sig,2420); (word_sub stackpointer (word 49360),49360)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49360),49360)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                  memory :> bytes(word_sub stackpointer (word 49360),49360)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the lengths, ext, rho, what the C *)
(* code declassifies in each attempt (mld_sign_declass), the addresses of *)
(* memset and memcpy and the stack, with all accesses within the arguments,  *)
(* the stack, the GOT entries and the stack guard, the region (ea,el) that   *)
(* memset and memcpy may read, the constants of the callees and the empty    *)
(* region at address 0 (the NULL third input of mld_H), and the writes       *)
(* within the signature and the stack.                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
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
           [(sig,2420); (word_sub stackpointer (word 49360),49360)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49360),49360)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                             (word_sub stackpointer (word 49360))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; pre,prelen; rnd,32; sk,2560;
                         word_sub stackpointer (word 49360),49360;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el; word 0,0;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const2),16]
                        [sig,2420;
                         word_sub stackpointer (word 49360),49360]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 49360),49360)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
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
           [(sig,2420); (word_sub stackpointer (word 49360),49360)] /\
          ALLPAIRS nonoverlapping
           [(sig,2420); (word_sub stackpointer (word 49360),49360)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,2560);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                             (word_sub stackpointer (word 49360))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,2420; m,mlen; pre,prelen; rnd,32; sk,2560;
                         word_sub stackpointer (word 49360),49360;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el; word 0,0;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa44_polyvecl_pointwise_acc_montgomery_const2),16]
                        [sig,2420;
                         word_sub stackpointer (word 49360),49360]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,2420);
                  memory :> bytes(word_sub stackpointer (word 49360),49360)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
