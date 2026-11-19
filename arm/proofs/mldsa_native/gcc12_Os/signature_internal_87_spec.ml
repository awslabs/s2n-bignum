(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Signing: the statement. This is the code for mldsa87_signature_internal   *)
(* (mld_sign_signature_internal in sign.c, with                              *)
(* mld_attempt_signature_generation and mld_compute_pack_z inlined) from     *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -Os (see *)
(* mldsa_native/README.md), which unpacks the secret key, computes mu (or    *)
(* takes it from m if ext is nonzero) and rho'', expands the matrix from     *)
(* rho, and makes up to 9361 attempts: each samples y, computes w = A y, w1 *)
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

    mldsa87_signature_internal:
       +0x0: sub     sp, sp, #0x200
       +0x4: sub     sp, sp, #0x1a, lsl #12
       +0x8: stp     x23, x24, [sp, #32]
       +0xc: mov     x23, x0
      +0x10: mov     x24, x4
      +0x14: adrp    x0, <page>
      +0x18: ldr     x0, [x0, #4088]
      +0x1c: stp     x19, x20, [sp]
      +0x20: add     x19, sp, #0xbf
      +0x24: stp     x21, x22, [sp, #16]
      +0x28: and     x19, x19, #0xffffffffffffffe0
      +0x2c: add     x21, x19, #0x1a, lsl #12
      +0x30: stp     x25, x26, [sp, #48]
      +0x34: mov     x26, x1
      +0x38: add     x1, sp, #0x18, lsl #12
      +0x3c: stp     x27, x28, [sp, #64]
      +0x40: add     x1, x1, #0x40
      +0x44: mov     x25, x2
      +0x48: str     x30, [sp, #80]
      +0x4c: add     x28, x21, #0x20
      +0x50: add     x4, x19, #0x17, lsl #12
      +0x54: mov     x22, x3
      +0x58: ldr     x2, [x0]
      +0x5c: str     x2, [x1, #8632]
      +0x60: mov     x2, #0x0
      +0x64: add     x0, x19, #0x10, lsl #12
      +0x68: str     x0, [sp, #128]
      +0x6c: add     x0, x19, #0x17, lsl #12
      +0x70: add     x0, x0, #0x800
      +0x74: str     x0, [sp, #136]
      +0x78: add     x0, x19, #0x12, lsl #12
      +0x7c: mov     x20, x5
      +0x80: mov     x3, x0
      +0x84: mov     w27, w7
      +0x88: add     x5, x19, #0x10, lsl #12
      +0x8c: add     x4, x4, #0x800
      +0x90: add     x2, x21, #0x60
      +0x94: mov     x1, x28
      +0x98: str     x0, [sp, #144]
      +0x9c: mov     x0, x21
      +0xa0: bl      <mldsa87_unpack_sk>
      +0xa4: add     x0, x21, #0x80
      +0xa8: cbnz    w27, <mldsa87_signature_internal+0x304>
      +0xac: mov     x6, x25
      +0xb0: mov     x5, x26
      +0xb4: mov     x4, x24
      +0xb8: mov     x3, x22
      +0xbc: mov     x1, x28
      +0xc0: mov     x2, #0x40
      +0xc4: bl      <mld_H87>
      +0xc8: mov     x4, #0x20
      +0xcc: add     x5, x21, #0x80
      +0xd0: mov     x3, x20
      +0xd4: mov     x2, x4
      +0xd8: mov     x6, #0x40
      +0xdc: add     x1, x21, #0x60
      +0xe0: add     x0, x21, #0xc0
      +0xe4: bl      <mld_H87>
      +0xe8: mov     x0, x19
      +0xec: mov     x1, x21
      +0xf0: bl      <mldsa87_polyvec_matrix_expand_eager>
      +0xf4: add     x27, x19, #0x15, lsl #12
      +0xf8: add     x0, x19, #0x19, lsl #12
      +0xfc: add     x24, x19, #0x19, lsl #12
     +0x100: add     x0, x0, #0xc00
     +0x104: add     x27, x27, #0xc00
     +0x108: add     x24, x24, #0x800
     +0x10c: str     x0, [sp, #104]
     +0x110: add     x0, x19, #0x1a, lsl #12
     +0x114: str     wzr, [sp, #124]
     +0x118: add     x0, x0, #0x100
     +0x11c: str     x0, [sp, #112]
     +0x120: ldrh    w2, [sp, #124]
     +0x124: add     x1, x21, #0xc0
     +0x128: mov     x0, x27
     +0x12c: add     x20, x19, #0x14, lsl #12
     +0x130: add     x25, x19, #0xe, lsl #12
     +0x134: add     x22, x19, #0x19, lsl #12
     +0x138: mov     w26, #0xff88
     +0x13c: add     x22, x22, #0x400
     +0x140: bl      <mldsa87_polyvecl_uniform_gamma1>
     +0x144: mov     x28, #0x0
     +0x148: mov     x3, x20
     +0x14c: mov     x2, x27
     +0x150: mov     x1, x19
     +0x154: mov     x0, x25
     +0x158: bl      <mldsa87_polyvec_matrix_pointwise_montgomery_yvec_eager>
     +0x15c: movk    w26, #0x7, lsl #16
     +0x160: mov     x0, x25
     +0x164: bl      <mldsa87_polyveck_caddq>
     +0x168: ldr     x0, [sp, #104]
     +0x16c: mov     x2, x20
     +0x170: mov     x1, x25
     +0x174: bl      <mldsa87_polyveck_decompose_pack_w1>
     +0x178: ldp     x3, x0, [sp, #104]
     +0x17c: add     x1, x21, #0x80
     +0x180: mov     x6, #0x0
     +0x184: mov     x5, #0x0
     +0x188: mov     x4, #0x400
     +0x18c: mov     x2, #0x40
     +0x190: bl      <mld_H87>
     +0x194: ldr     x1, [sp, #112]
     +0x198: mov     x0, x24
     +0x19c: bl      <mldsa87_poly_challenge>
     +0x1a0: mov     x0, x24
     +0x1a4: bl      <mldsa_poly_ntt>
     +0x1a8: ldr     x0, [sp, #136]
     +0x1ac: lsl     x3, x28, #10
     +0x1b0: mov     x2, #0x400
     +0x1b4: str     x3, [sp, #152]
     +0x1b8: add     x1, x0, x28, lsl #10
     +0x1bc: mov     x0, x22
     +0x1c0: bl      <memcpy>
     +0x1c4: mov     x1, x24
     +0x1c8: mov     x0, x22
     +0x1cc: bl      <mldsa_poly_pointwise_montgomery>
     +0x1d0: mov     x0, x22
     +0x1d4: bl      <mldsa_poly_invntt_tomont>
     +0x1d8: ldr     x3, [sp, #152]
     +0x1dc: mov     x2, #0x400
     +0x1e0: mov     x0, x20
     +0x1e4: add     x1, x3, x27
     +0x1e8: bl      <memcpy>
     +0x1ec: mov     x1, x20
     +0x1f0: mov     x0, x22
     +0x1f4: bl      <mldsa_poly_add>
     +0x1f8: mov     x0, x22
     +0x1fc: bl      <mldsa_poly_reduce>
     +0x200: mov     w1, w26
     +0x204: mov     x0, x22
     +0x208: bl      <mldsa_poly_chknorm>
     +0x20c: cbnz    w0, <mldsa87_signature_internal+0x318>
     +0x210: mov     w2, w28
     +0x214: mov     x1, x22
     +0x218: mov     x0, x23
     +0x21c: add     x28, x28, #0x1
     +0x220: bl      <mldsa87_pack_sig_z>
     +0x224: cmp     x28, #0x7
     +0x228: b.ne    <mldsa87_signature_internal+0x1a8>
     +0x22c: mov     x26, #0x0
     +0x230: ldr     x0, [sp, #128]
     +0x234: mov     x2, #0x400
     +0x238: add     x28, x25, x26
     +0x23c: add     x1, x0, x26
     +0x240: mov     x0, x20
     +0x244: bl      <memcpy>
     +0x248: mov     x1, x24
     +0x24c: mov     x0, x20
     +0x250: bl      <mldsa_poly_pointwise_montgomery>
     +0x254: mov     x0, x20
     +0x258: bl      <mldsa_poly_invntt_tomont>
     +0x25c: mov     x1, x20
     +0x260: mov     x0, x28
     +0x264: bl      <mldsa_poly_sub>
     +0x268: mov     x0, x28
     +0x26c: bl      <mldsa_poly_reduce>
     +0x270: mov     w1, #0xfe88
     +0x274: mov     x0, x28
     +0x278: movk    w1, #0x3, lsl #16
     +0x27c: bl      <mldsa_poly_chknorm>
     +0x280: cbnz    w0, <mldsa87_signature_internal+0x318>
     +0x284: ldr     x0, [sp, #144]
     +0x288: mov     x2, #0x400
     +0x28c: add     x1, x0, x26
     +0x290: mov     x0, x20
     +0x294: bl      <memcpy>
     +0x298: mov     x1, x24
     +0x29c: mov     x0, x20
     +0x2a0: bl      <mldsa_poly_pointwise_montgomery>
     +0x2a4: mov     x0, x20
     +0x2a8: bl      <mldsa_poly_invntt_tomont>
     +0x2ac: mov     x0, x20
     +0x2b0: bl      <mldsa_poly_reduce>
     +0x2b4: mov     x0, x20
     +0x2b8: mov     w1, #0x3ff00
     +0x2bc: bl      <mldsa_poly_chknorm>
     +0x2c0: cbnz    w0, <mldsa87_signature_internal+0x318>
     +0x2c4: mov     x1, x20
     +0x2c8: mov     x0, x28
     +0x2cc: add     x26, x26, #0x400
     +0x2d0: bl      <mldsa_poly_add>
     +0x2d4: cmp     x26, #0x2, lsl #12
     +0x2d8: b.ne    <mldsa87_signature_internal+0x230>
     +0x2dc: ldr     x1, [sp, #112]
     +0x2e0: mov     x0, x23
     +0x2e4: bl      <mldsa87_pack_sig_c>
     +0x2e8: ldr     x2, [sp, #104]
     +0x2ec: mov     x3, x20
     +0x2f0: mov     x1, x25
     +0x2f4: mov     x0, x23
     +0x2f8: bl      <mldsa87_pack_sig_h>
     +0x2fc: mov     w26, w0
     +0x300: b       <mldsa87_signature_internal+0x31c>
     +0x304: ldp     q0, q1, [x26]
     +0x308: stp     q0, q1, [x0]
     +0x30c: ldp     q0, q1, [x26, #32]
     +0x310: stp     q0, q1, [x0, #32]
     +0x314: b       <mldsa87_signature_internal+0xc8>
     +0x318: mov     w26, #0xffffffff
     +0x31c: mov     x0, x22
     +0x320: mov     x1, #0x400
     +0x324: bl      <mld_zeroize_6>
     +0x328: mov     x0, x24
     +0x32c: mov     x1, #0x400
     +0x330: bl      <mld_zeroize_6>
     +0x334: mov     x0, x25
     +0x338: mov     x1, #0x2000
     +0x33c: bl      <mld_zeroize_6>
     +0x340: ldr     x0, [sp, #104]
     +0x344: mov     x1, #0x400
     +0x348: bl      <mld_zeroize_6>
     +0x34c: mov     x0, x20
     +0x350: mov     x1, #0x1c00
     +0x354: bl      <mld_zeroize_6>
     +0x358: mov     x0, x27
     +0x35c: mov     x1, #0x1c00
     +0x360: bl      <mld_zeroize_6>
     +0x364: ldr     x0, [sp, #112]
     +0x368: mov     x1, #0x40
     +0x36c: bl      <mld_zeroize_6>
     +0x370: cbz     w26, <mldsa87_signature_internal+0x3a8>
     +0x374: cmn     w26, #0x1
     +0x378: b.ne    <mldsa87_signature_internal+0x39c>
     +0x37c: ldr     w0, [sp, #124]
     +0x380: add     w0, w0, #0x7
     +0x384: and     w1, w0, #0xffff
     +0x388: str     w1, [sp, #124]
     +0x38c: mov     w1, #0xfff7
     +0x390: cmp     w1, w0, uxth
     +0x394: b.ne    <mldsa87_signature_internal+0x120>
     +0x398: mov     w26, #0xfffffffc
     +0x39c: mov     x0, x23
     +0x3a0: mov     x1, #0x1213
     +0x3a4: bl      <mld_zeroize_6>
     +0x3a8: ldr     x0, [sp, #128]
     +0x3ac: mov     x1, #0x2000
     +0x3b0: bl      <mld_zeroize_6>
     +0x3b4: ldr     x0, [sp, #144]
     +0x3b8: mov     x1, #0x2000
     +0x3bc: bl      <mld_zeroize_6>
     +0x3c0: ldr     x0, [sp, #136]
     +0x3c4: mov     x1, #0x1c00
     +0x3c8: bl      <mld_zeroize_6>
     +0x3cc: mov     x0, x19
     +0x3d0: mov     x1, #0xe000
     +0x3d4: bl      <mld_zeroize_6>
     +0x3d8: mov     x0, x21
     +0x3dc: mov     x1, #0x100
     +0x3e0: bl      <mld_zeroize_6>
     +0x3e4: adrp    x0, <page>
     +0x3e8: ldr     x0, [x0, #4088]
     +0x3ec: add     x2, sp, #0x18, lsl #12
     +0x3f0: add     x2, x2, #0x40
     +0x3f4: ldr     x3, [x2, #8632]
     +0x3f8: ldr     x1, [x0]
     +0x3fc: subs    x3, x3, x1
     +0x400: mov     x1, #0x0
     +0x404: b.eq    <mldsa87_signature_internal+0x40c>
     +0x408: bl      <stack_chk_fail>
     +0x40c: ldp     x19, x20, [sp]
     +0x410: mov     w0, w26
     +0x414: ldp     x21, x22, [sp, #16]
     +0x418: ldp     x23, x24, [sp, #32]
     +0x41c: ldp     x25, x26, [sp, #48]
     +0x420: ldp     x27, x28, [sp, #64]
     +0x424: ldr     x30, [sp, #80]
     +0x428: add     sp, sp, #0x200
     +0x42c: add     sp, sp, #0x1a, lsl #12
     +0x430: ret
    plt_memcpy:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4048]
       +0x8: add     x16, x16, #0xfd0
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa87_signature_internal"; layout_range "plt_memcpy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for memset and memcpy. The secret key *)
(* skb at sk (4896 bytes), the message M of mlen bytes at m and the prefix   *)
(* PRE of prelen bytes at pre (or, if ext is nonzero as a 32-bit integer, mu *)
(* in the first 64 bytes at m), and the 32 bytes RND at rnd, with MU the mu  *)
(* that the code uses: the result is 0, with the signature mld_sign_sig at   *)
(* sig (4627 bytes), if one of the 9361 attempts succeeds (mld_sign_ok), and *)
(* -4 with the signature zeroed otherwise. The stack is the 107008 bytes of  *)
(* the function and those of the callees below them.                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
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
           [(sig,4627); (word_sub stackpointer (word 112096),112096)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112096),112096)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                  memory :> bytes(word_sub stackpointer (word 112096),
                                  112096)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

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

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
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
           [(sig,4627); (word_sub stackpointer (word 112096),112096)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112096),112096)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                             (word_sub stackpointer (word 112096))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; pre,prelen; rnd,32; sk,4896;
                         word_sub stackpointer (word 112096),112096;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el; word 0,0;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const2),16]
                        [sig,4627;
                         word_sub stackpointer (word 112096),112096]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112096),
                                  112096)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
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
           [(sig,4627); (word_sub stackpointer (word 112096),112096)] /\
          ALLPAIRS nonoverlapping
           [(sig,4627); (word_sub stackpointer (word 112096),112096)]
           [(m,mlen); (pre,prelen); (rnd,32); (sk,4896);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (word(pc + got_memcpy),8);
            (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                             (word_sub stackpointer (word 112096))
                             returnaddress /\
                       memaccess_inbounds e2
                        [sig,4627; m,mlen; pre,prelen; rnd,32; sk,4896;
                         word_sub stackpointer (word 112096),112096;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8;
                         ea,el; word 0,0;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const2),16]
                        [sig,4627;
                         word_sub stackpointer (word 112096),112096]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(sig,4627);
                  memory :> bytes(word_sub stackpointer (word 112096),
                                  112096)])`;;

let MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SIGNATURE_INTERNAL_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
