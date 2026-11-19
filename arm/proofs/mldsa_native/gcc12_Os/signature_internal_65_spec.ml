(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing: the statement. This is the code for mldsa65_signature_internal   *)
(* (mld_sign_signature_internal in sign.c, with                              *)
(* mld_attempt_signature_generation and mld_compute_pack_z inlined) from     *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -Os (see *)
(* mldsa_native/README.md), which unpacks the secret key, computes mu (or    *)
(* takes it from m if ext is nonzero) and rho'', expands the matrix from     *)
(* rho, and makes up to 13106 attempts: each samples y, computes w = A y, w1 *)
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

    mldsa65_signature_internal:
       +0x0: sub     sp, sp, #0x8f0
       +0x4: mov     x8, #0xa800
       +0x8: sub     sp, sp, #0x10, lsl #12
       +0xc: stp     x23, x24, [sp, #32]
      +0x10: mov     x23, x0
      +0x14: mov     x24, x4
      +0x18: adrp    x0, <page>
      +0x1c: ldr     x0, [x0, #4088]
      +0x20: stp     x19, x20, [sp]
      +0x24: add     x19, sp, #0xbf
      +0x28: stp     x21, x22, [sp, #16]
      +0x2c: and     x19, x19, #0xffffffffffffffe0
      +0x30: add     x21, x19, #0x10, lsl #12
      +0x34: stp     x25, x26, [sp, #48]
      +0x38: mov     x26, x1
      +0x3c: add     x1, sp, #0x10, lsl #12
      +0x40: stp     x27, x28, [sp, #64]
      +0x44: add     x1, x1, #0x40
      +0x48: mov     x25, x2
      +0x4c: str     x30, [sp, #80]
      +0x50: add     x21, x21, #0x700
      +0x54: mov     w27, w7
      +0x58: mov     x7, #0xe800
      +0x5c: ldr     x2, [x0]
      +0x60: str     x2, [x1, #2216]
      +0x64: mov     x2, #0x0
      +0x68: add     x0, x19, #0x9, lsl #12
      +0x6c: str     x0, [sp, #128]
      +0x70: add     x0, x19, x7
      +0x74: add     x28, x21, #0x20
      +0x78: str     x0, [sp, #136]
      +0x7c: add     x0, x19, x8
      +0x80: mov     x22, x3
      +0x84: mov     x20, x5
      +0x88: mov     x3, x0
      +0x8c: add     x5, x19, #0x9, lsl #12
      +0x90: add     x2, x21, #0x60
      +0x94: mov     x1, x28
      +0x98: mov     x4, #0xe800
      +0x9c: add     x4, x19, x4
      +0xa0: str     x0, [sp, #144]
      +0xa4: mov     x0, x21
      +0xa8: bl      <mldsa65_unpack_sk>
      +0xac: add     x0, x21, #0x80
      +0xb0: cbnz    w27, <mldsa65_signature_internal+0x31c>
      +0xb4: mov     x3, #0x40
      +0xb8: mov     x7, x25
      +0xbc: mov     x6, x26
      +0xc0: mov     x5, x24
      +0xc4: mov     x4, x22
      +0xc8: mov     x2, x28
      +0xcc: mov     x1, x3
      +0xd0: bl      <mld_H65>
      +0xd4: mov     x5, #0x20
      +0xd8: add     x6, x21, #0x80
      +0xdc: mov     x4, x20
      +0xe0: mov     x3, x5
      +0xe4: add     x2, x21, #0x60
      +0xe8: mov     x7, #0x40
      +0xec: add     x0, x21, #0xc0
      +0xf0: mov     x1, x7
      +0xf4: bl      <mld_H65>
      +0xf8: mov     x0, x19
      +0xfc: mov     x1, x21
     +0x100: bl      <mldsa65_polyvec_matrix_expand_eager>
     +0x104: str     wzr, [sp, #124]
     +0x108: add     x0, x19, #0x10, lsl #12
     +0x10c: add     x0, x0, #0x400
     +0x110: str     x0, [sp, #104]
     +0x114: add     x0, x19, #0x10, lsl #12
     +0x118: add     x0, x0, #0x800
     +0x11c: str     x0, [sp, #112]
     +0x120: ldrh    w2, [sp, #124]
     +0x124: mov     x0, #0xd400
     +0x128: add     x27, x19, x0
     +0x12c: add     x1, x21, #0xc0
     +0x130: mov     x0, x27
     +0x134: add     x20, x19, #0xc, lsl #12
     +0x138: add     x25, x19, #0x10, lsl #12
     +0x13c: mov     w26, #0xff3c
     +0x140: bl      <mldsa65_polyvecl_uniform_gamma1>
     +0x144: mov     x28, #0x0
     +0x148: mov     x1, #0x7800
     +0x14c: mov     x3, x20
     +0x150: add     x24, x19, x1
     +0x154: mov     x2, x27
     +0x158: mov     x1, x19
     +0x15c: mov     x0, x24
     +0x160: bl      <mldsa65_polyvec_matrix_pointwise_montgomery_yvec_eager>
     +0x164: movk    w26, #0x7, lsl #16
     +0x168: mov     x0, x24
     +0x16c: bl      <mldsa65_polyveck_caddq>
     +0x170: ldr     x0, [sp, #104]
     +0x174: mov     x3, #0xfc00
     +0x178: mov     x2, x20
     +0x17c: mov     x1, x24
     +0x180: add     x22, x19, x3
     +0x184: bl      <mldsa65_polyveck_decompose_pack_w1>
     +0x188: ldp     x4, x0, [sp, #104]
     +0x18c: add     x2, x21, #0x80
     +0x190: mov     x7, #0x0
     +0x194: mov     x6, #0x0
     +0x198: mov     x5, #0x300
     +0x19c: mov     x3, #0x40
     +0x1a0: mov     x1, #0x30
     +0x1a4: bl      <mld_H65>
     +0x1a8: ldr     x1, [sp, #112]
     +0x1ac: mov     x0, x25
     +0x1b0: bl      <mldsa65_poly_challenge>
     +0x1b4: mov     x0, x25
     +0x1b8: bl      <mldsa_poly_ntt>
     +0x1bc: ldr     x0, [sp, #136]
     +0x1c0: lsl     x3, x28, #10
     +0x1c4: mov     x2, #0x400
     +0x1c8: str     x3, [sp, #152]
     +0x1cc: add     x1, x0, x28, lsl #10
     +0x1d0: mov     x0, x22
     +0x1d4: bl      <memcpy>
     +0x1d8: mov     x1, x25
     +0x1dc: mov     x0, x22
     +0x1e0: bl      <mldsa_poly_pointwise_montgomery>
     +0x1e4: mov     x0, x22
     +0x1e8: bl      <mldsa_poly_invntt_tomont>
     +0x1ec: ldr     x3, [sp, #152]
     +0x1f0: mov     x2, #0x400
     +0x1f4: mov     x0, x20
     +0x1f8: add     x1, x3, x27
     +0x1fc: bl      <memcpy>
     +0x200: mov     x1, x20
     +0x204: mov     x0, x22
     +0x208: bl      <mldsa_poly_add>
     +0x20c: mov     x0, x22
     +0x210: bl      <mldsa_poly_reduce>
     +0x214: mov     w1, w26
     +0x218: mov     x0, x22
     +0x21c: bl      <mldsa_poly_chknorm>
     +0x220: cbnz    w0, <mldsa65_signature_internal+0x330>
     +0x224: mov     w2, w28
     +0x228: mov     x1, x22
     +0x22c: mov     x0, x23
     +0x230: add     x28, x28, #0x1
     +0x234: bl      <mldsa65_pack_sig_z>
     +0x238: cmp     x28, #0x5
     +0x23c: b.ne    <mldsa65_signature_internal+0x1bc>
     +0x240: mov     x26, #0x0
     +0x244: ldr     x0, [sp, #128]
     +0x248: mov     x2, #0x400
     +0x24c: add     x28, x24, x26
     +0x250: add     x1, x0, x26
     +0x254: mov     x0, x20
     +0x258: bl      <memcpy>
     +0x25c: mov     x1, x25
     +0x260: mov     x0, x20
     +0x264: bl      <mldsa_poly_pointwise_montgomery>
     +0x268: mov     x0, x20
     +0x26c: bl      <mldsa_poly_invntt_tomont>
     +0x270: mov     x1, x20
     +0x274: mov     x0, x28
     +0x278: bl      <mldsa_poly_sub>
     +0x27c: mov     x0, x28
     +0x280: bl      <mldsa_poly_reduce>
     +0x284: mov     w1, #0xfe3c
     +0x288: mov     x0, x28
     +0x28c: movk    w1, #0x3, lsl #16
     +0x290: bl      <mldsa_poly_chknorm>
     +0x294: cbnz    w0, <mldsa65_signature_internal+0x330>
     +0x298: ldr     x0, [sp, #144]
     +0x29c: mov     x2, #0x400
     +0x2a0: add     x1, x26, x0
     +0x2a4: mov     x0, x20
     +0x2a8: bl      <memcpy>
     +0x2ac: mov     x1, x25
     +0x2b0: mov     x0, x20
     +0x2b4: bl      <mldsa_poly_pointwise_montgomery>
     +0x2b8: mov     x0, x20
     +0x2bc: bl      <mldsa_poly_invntt_tomont>
     +0x2c0: mov     x0, x20
     +0x2c4: bl      <mldsa_poly_reduce>
     +0x2c8: mov     x0, x20
     +0x2cc: mov     w1, #0x3ff00
     +0x2d0: bl      <mldsa_poly_chknorm>
     +0x2d4: cbnz    w0, <mldsa65_signature_internal+0x330>
     +0x2d8: mov     x0, x28
     +0x2dc: mov     x1, x20
     +0x2e0: add     x26, x26, #0x400
     +0x2e4: bl      <mldsa_poly_add>
     +0x2e8: mov     x0, #0x1800
     +0x2ec: cmp     x26, x0
     +0x2f0: b.ne    <mldsa65_signature_internal+0x244>
     +0x2f4: ldr     x1, [sp, #112]
     +0x2f8: mov     x0, x23
     +0x2fc: bl      <mldsa65_pack_sig_c>
     +0x300: ldr     x2, [sp, #104]
     +0x304: mov     x3, x20
     +0x308: mov     x1, x24
     +0x30c: mov     x0, x23
     +0x310: bl      <mldsa65_pack_sig_h>
     +0x314: mov     w26, w0
     +0x318: b       <mldsa65_signature_internal+0x334>
     +0x31c: ldp     q0, q1, [x26]
     +0x320: stp     q0, q1, [x0]
     +0x324: ldp     q0, q1, [x26, #32]
     +0x328: stp     q0, q1, [x0, #32]
     +0x32c: b       <mldsa65_signature_internal+0xd4>
     +0x330: mov     w26, #0xffffffff
     +0x334: mov     x0, x22
     +0x338: mov     x1, #0x400
     +0x33c: bl      <mld_zeroize_4>
     +0x340: mov     x0, x25
     +0x344: mov     x1, #0x400
     +0x348: bl      <mld_zeroize_4>
     +0x34c: mov     x0, x24
     +0x350: mov     x1, #0x1800
     +0x354: bl      <mld_zeroize_4>
     +0x358: ldr     x0, [sp, #104]
     +0x35c: mov     x1, #0x300
     +0x360: bl      <mld_zeroize_4>
     +0x364: mov     x0, x20
     +0x368: mov     x1, #0x1400
     +0x36c: bl      <mld_zeroize_4>
     +0x370: mov     x0, x27
     +0x374: mov     x1, #0x1400
     +0x378: bl      <mld_zeroize_4>
     +0x37c: ldr     x0, [sp, #112]
     +0x380: mov     x1, #0x30
     +0x384: bl      <mld_zeroize_4>
     +0x388: cbz     w26, <mldsa65_signature_internal+0x3c0>
     +0x38c: cmn     w26, #0x1
     +0x390: b.ne    <mldsa65_signature_internal+0x3b4>
     +0x394: ldr     w0, [sp, #124]
     +0x398: add     w0, w0, #0x5
     +0x39c: and     w1, w0, #0xffff
     +0x3a0: str     w1, [sp, #124]
     +0x3a4: mov     w1, #0xfffa
     +0x3a8: cmp     w1, w0, uxth
     +0x3ac: b.ne    <mldsa65_signature_internal+0x120>
     +0x3b0: mov     w26, #0xfffffffc
     +0x3b4: mov     x0, x23
     +0x3b8: mov     x1, #0xced
     +0x3bc: bl      <mld_zeroize_4>
     +0x3c0: ldr     x0, [sp, #128]
     +0x3c4: mov     x1, #0x1800
     +0x3c8: bl      <mld_zeroize_4>
     +0x3cc: ldr     x0, [sp, #144]
     +0x3d0: mov     x1, #0x1800
     +0x3d4: bl      <mld_zeroize_4>
     +0x3d8: ldr     x0, [sp, #136]
     +0x3dc: mov     x1, #0x1400
     +0x3e0: bl      <mld_zeroize_4>
     +0x3e4: mov     x0, x19
     +0x3e8: mov     x1, #0x7800
     +0x3ec: bl      <mld_zeroize_4>
     +0x3f0: mov     x0, x21
     +0x3f4: mov     x1, #0x100
     +0x3f8: bl      <mld_zeroize_4>
     +0x3fc: adrp    x0, <page>
     +0x400: ldr     x0, [x0, #4088]
     +0x404: add     x2, sp, #0x10, lsl #12
     +0x408: add     x2, x2, #0x40
     +0x40c: ldr     x3, [x2, #2216]
     +0x410: ldr     x1, [x0]
     +0x414: subs    x3, x3, x1
     +0x418: mov     x1, #0x0
     +0x41c: b.eq    <mldsa65_signature_internal+0x424>
     +0x420: bl      <stack_chk_fail>
     +0x424: ldp     x19, x20, [sp]
     +0x428: mov     w0, w26
     +0x42c: ldp     x21, x22, [sp, #16]
     +0x430: ldp     x23, x24, [sp, #32]
     +0x434: ldp     x25, x26, [sp, #48]
     +0x438: ldp     x27, x28, [sp, #64]
     +0x43c: ldr     x30, [sp, #80]
     +0x440: add     sp, sp, #0x8f0
     +0x444: add     sp, sp, #0x10, lsl #12
     +0x448: ret
    plt_memcpy:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4048]
       +0x8: add     x16, x16, #0xfd0
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa65_signature_internal"; layout_range "plt_memcpy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for memset and memcpy. The secret key *)
(* skb at sk (4032 bytes), the message M of mlen bytes at m and the prefix   *)
(* PRE of prelen bytes at pre (or, if ext is nonzero as a 32-bit integer, mu *)
(* in the first 64 bytes at m), and the 32 bytes RND at rnd, with MU the mu  *)
(* that the code uses: the result is 0, with the signature mld_sign_sig at   *)
(* sig (3309 bytes), if one of the 13106 attempts succeeds (mld_sign_ok),    *)
(* and -4 with the signature zeroed otherwise. The stack is the 67824 bytes  *)
(* of the function and those of the callees below them.                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
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
           [(sig,3309); (word_sub stackpointer (word 72912),72912)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 72912),72912)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                  memory :> bytes(word_sub stackpointer (word 72912),72912)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

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

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
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
           [(sig,3309); (word_sub stackpointer (word 72912),72912)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 72912),72912)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                             (word_sub stackpointer (word 72912))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; pre,prelen; rnd,32; sk,4032;
                         word_sub stackpointer (word 72912),72912;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el; word 0,0;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const2),16]
                        [sig,3309;
                         word_sub stackpointer (word 72912),72912]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 72912),72912)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
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
           [(sig,3309); (word_sub stackpointer (word 72912),72912)] /\
          ALLPAIRS nonoverlapping
           [(sig,3309); (word_sub stackpointer (word 72912),72912)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4032);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                             (word_sub stackpointer (word 72912))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,3309; m,mlen; pre,prelen; rnd,32; sk,4032;
                         word_sub stackpointer (word 72912),72912;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el; word 0,0;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const2),16]
                        [sig,3309;
                         word_sub stackpointer (word 72912),72912]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,3309);
                  memory :> bytes(word_sub stackpointer (word 72912),72912)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
