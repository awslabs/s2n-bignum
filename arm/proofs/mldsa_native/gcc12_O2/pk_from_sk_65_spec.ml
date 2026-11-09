(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The public key of a secret key: the statement. This is the code for       *)
(* mldsa65_pk_from_sk (mld_sign_pk_from_sk in sign.c) from mldsa-native's    *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mldsa_native/README.md), which copies rho, the key and tr from the secret *)
(* key, unpacks s1 with mldsa65_polyvecl_unpack_eta and checks it and s2     *)
(* with mldsa65_polyvecl_chknorm and mldsa65_polyveck_unpack_eta_chknorm,    *)
(* transforms s1 with mldsa65_polyvecl_ntt, recomputes t1 into the public    *)
(* key and t0 into a buffer with mld_compute_pack_t0_t165, compares t0 with  *)
(* that in the secret key, hashes the public key with mldsa_shake256 and     *)
(* compares the hash with tr, all in constant time, and then zeroes the      *)
(* public key if a check failed and the buffers with memset. It is verified  *)
(* in the whole image (see libmldsa.ml) against mld_pk_from_sk_pk and        *)
(* mld_pk_from_sk_valid of common/mldsa_native_sign.ml, using the theorems   *)
(* for the callees and the contract memset_full_contract of                  *)
(* utils/mlkem_native_libc_full.ml for memset, assuming that the expansion   *)
(* of the matrix terminates (mld_matrix_terminates), and shown to be         *)
(* constant time and memory safe, with the events depending on rho, which is *)
(* part of the public key, and on the result of the checks, which the C code *)
(* declassifies.                                                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sign.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_unpack_eta_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_chknorm_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyveck_unpack_eta_chknorm_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_ntt_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/compute_pack_t0_t1_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa65_pk_from_sk:
       +0x0: mov     x12, #0x2310
       +0x4: sub     sp, sp, x12
       +0x8: add     x4, x1, #0x40
       +0xc: mov     x8, #0x2400
      +0x10: mov     x9, #0x1dc0
      +0x14: mov     x10, #0x2260
      +0x18: stp     x19, x20, [sp]
      +0x1c: mov     x20, x1
      +0x20: add     x19, sp, #0x8f
      +0x24: stp     x21, x22, [sp, #16]
      +0x28: and     x19, x19, #0xffffffffffffffe0
      +0x2c: add     x1, x19, x8
      +0x30: stp     x23, x24, [sp, #32]
      +0x34: sub     x3, x1, #0x200
      +0x38: sub     x2, x1, #0x1c0
      +0x3c: stp     x25, x26, [sp, #48]
      +0x40: mov     x11, #0x1400
      +0x44: add     x26, x19, x9
      +0x48: stp     x27, x28, [sp, #64]
      +0x4c: sub     x28, x1, #0x1a0
      +0x50: add     x23, x19, x10
      +0x54: str     x30, [sp, #80]
      +0x58: add     x24, x19, x11
      +0x5c: mov     x21, x0
      +0x60: add     x1, x20, #0x80
      +0x64: ldp     q6, q7, [x4]
      +0x68: mov     x0, x19
      +0x6c: ldp     q0, q1, [x4, #32]
      +0x70: add     x22, x20, #0x300
      +0x74: adrp    x4, <page>
      +0x78: ldr     x4, [x4, #4088]
      +0x7c: ldp     q4, q5, [x20]
      +0x80: ldr     x5, [x4]
      +0x84: str     x5, [sp, #8968]
      +0x88: mov     x5, #0x0
      +0x8c: ldp     q2, q3, [x20, #32]
      +0x90: stp     q6, q7, [x3]
      +0x94: stp     q4, q5, [x28]
      +0x98: stp     q2, q3, [x2]
      +0x9c: stp     q0, q1, [x3, #32]
      +0xa0: bl      <mldsa65_polyvecl_unpack_eta>
      +0xa4: mov     w1, #0x5
      +0xa8: mov     x0, x19
      +0xac: bl      <mldsa65_polyvecl_chknorm>
      +0xb0: mov     x2, x26
      +0xb4: mov     w1, #0x5
      +0xb8: mov     w25, w0
      +0xbc: mov     x0, x22
      +0xc0: bl      <mldsa65_polyveck_unpack_eta_chknorm>
      +0xc4: mov     w27, w0
      +0xc8: mov     x0, x19
      +0xcc: bl      <mldsa65_polyvecl_ntt>
      +0xd0: ldp     q0, q1, [x28]
      +0xd4: mov     x3, x22
      +0xd8: mov     x4, x23
      +0xdc: mov     x1, x24
      +0xe0: mov     x2, x19
      +0xe4: add     x0, x21, #0x20
      +0xe8: stp     q0, q1, [x21]
      +0xec: bl      <mld_compute_pack_t0_t165>
      +0xf0: mov     w22, w0
      +0xf4: cbz     w0, <+0x1b8>
      +0xf8: mov     x6, #0x21c0
      +0xfc: mov     x7, #0x2200
     +0x100: add     x28, x19, x6
     +0x104: add     x20, x19, x7
     +0x108: mov     x0, x21
     +0x10c: mov     x2, #0x7a0
     +0x110: mov     w1, #0x0
     +0x114: bl      <memset@plt>
     +0x118: mov     x0, x24
     +0x11c: mov     x2, #0x9c0
     +0x120: mov     w1, #0x0
     +0x124: bl      <memset@plt>
     +0x128: mov     x2, #0x400
     +0x12c: mov     x0, x26
     +0x130: mov     w1, #0x0
     +0x134: bl      <memset@plt>
     +0x138: mov     x2, #0x1400
     +0x13c: mov     x0, x19
     +0x140: mov     w1, #0x0
     +0x144: bl      <memset@plt>
     +0x148: mov     x0, #0x2240
     +0x14c: add     x19, x19, x0
     +0x150: stp     xzr, xzr, [x19]
     +0x154: stp     xzr, xzr, [x19, #16]
     +0x158: movi    v0.4s, #0x0
     +0x15c: stp     q0, q0, [x28]
     +0x160: stp     q0, q0, [x28, #32]
     +0x164: stp     q0, q0, [x20]
     +0x168: stp     q0, q0, [x20, #32]
     +0x16c: stp     xzr, xzr, [x23]
     +0x170: stp     xzr, xzr, [x23, #16]
     +0x174: adrp    x0, <page>
     +0x178: ldr     x0, [x0, #4088]
     +0x17c: ldr     x2, [sp, #8968]
     +0x180: ldr     x1, [x0]
     +0x184: subs    x2, x2, x1
     +0x188: mov     x1, #0x0
     +0x18c: b.ne    <+0x324>
     +0x190: ldp     x19, x20, [sp]
     +0x194: mov     w0, w22
     +0x198: ldp     x21, x22, [sp, #16]
     +0x19c: mov     x12, #0x2310
     +0x1a0: ldp     x23, x24, [sp, #32]
     +0x1a4: ldp     x25, x26, [sp, #48]
     +0x1a8: ldp     x27, x28, [sp, #64]
     +0x1ac: ldr     x30, [sp, #80]
     +0x1b0: add     sp, sp, x12
     +0x1b4: ret
     +0x1b8: movi    v1.4s, #0x0
     +0x1bc: add     x20, x20, #0x600
     +0x1c0: mov     x0, x24
     +0x1c4: add     x1, x24, #0x9c0
     +0x1c8: mov     v2.16b, v1.16b
     +0x1cc: nop
     +0x1d0: ldr     q0, [x20], #16
     +0x1d4: ldr     q3, [x0], #16
     +0x1d8: eor     v0.16b, v0.16b, v3.16b
     +0x1dc: orr     v2.16b, v2.16b, v0.16b
     +0x1e0: eor     v1.16b, v1.16b, v0.16b
     +0x1e4: cmp     x1, x0
     +0x1e8: b.ne    <+0x1d0>
     +0x1ec: movi    v0.4s, #0x0
     +0x1f0: ext     v4.16b, v2.16b, v0.16b, #8
     +0x1f4: ext     v3.16b, v1.16b, v0.16b, #8
     +0x1f8: orr     v4.16b, v4.16b, v2.16b
     +0x1fc: eor     v3.16b, v3.16b, v1.16b
     +0x200: ext     v2.16b, v4.16b, v0.16b, #4
     +0x204: ext     v1.16b, v3.16b, v0.16b, #4
     +0x208: orr     v2.16b, v2.16b, v4.16b
     +0x20c: eor     v1.16b, v1.16b, v3.16b
     +0x210: ext     v4.16b, v2.16b, v0.16b, #2
     +0x214: ext     v3.16b, v1.16b, v0.16b, #2
     +0x218: orr     v4.16b, v4.16b, v2.16b
     +0x21c: eor     v3.16b, v3.16b, v1.16b
     +0x220: ext     v1.16b, v4.16b, v0.16b, #1
     +0x224: ext     v2.16b, v3.16b, v0.16b, #1
     +0x228: orr     v1.16b, v1.16b, v4.16b
     +0x22c: eor     v2.16b, v2.16b, v3.16b
     +0x230: umov    w0, v1.b[0]
     +0x234: umov    w1, v2.b[0]
     +0x238: neg     x0, x0
     +0x23c: asr     x0, x0, #32
     +0x240: eor     w0, w1, w0
     +0x244: and     w0, w0, #0xff
     +0x248: mov     x5, #0x2200
     +0x24c: eor     w4, w0, w1
     +0x250: mov     x2, #0x21c0
     +0x254: add     x28, x19, x2
     +0x258: add     x20, x19, x5
     +0x25c: mov     x0, x28
     +0x260: mov     x2, x21
     +0x264: mov     x1, #0x40
     +0x268: mov     x3, #0x7a0
     +0x26c: str     w4, [sp, #108]
     +0x270: bl      <mldsa_shake256>
     +0x274: movi    v0.4s, #0x0
     +0x278: ldr     w4, [sp, #108]
     +0x27c: mov     x0, x28
     +0x280: add     x2, x28, #0x40
     +0x284: mov     x1, x20
     +0x288: mov     v2.16b, v0.16b
     +0x28c: ldr     q1, [x0], #16
     +0x290: ldr     q3, [x1], #16
     +0x294: eor     v1.16b, v1.16b, v3.16b
     +0x298: orr     v2.16b, v2.16b, v1.16b
     +0x29c: eor     v0.16b, v0.16b, v1.16b
     +0x2a0: cmp     x0, x2
     +0x2a4: b.ne    <+0x28c>
     +0x2a8: movi    v1.4s, #0x0
     +0x2ac: ext     v5.16b, v2.16b, v1.16b, #8
     +0x2b0: ext     v3.16b, v0.16b, v1.16b, #8
     +0x2b4: orr     v5.16b, v5.16b, v2.16b
     +0x2b8: eor     v2.16b, v3.16b, v0.16b
     +0x2bc: ext     v4.16b, v5.16b, v1.16b, #4
     +0x2c0: ext     v0.16b, v2.16b, v1.16b, #4
     +0x2c4: orr     v4.16b, v4.16b, v5.16b
     +0x2c8: eor     v0.16b, v0.16b, v2.16b
     +0x2cc: ext     v3.16b, v4.16b, v1.16b, #2
     +0x2d0: ext     v2.16b, v0.16b, v1.16b, #2
     +0x2d4: orr     v3.16b, v3.16b, v4.16b
     +0x2d8: eor     v2.16b, v2.16b, v0.16b
     +0x2dc: ext     v0.16b, v3.16b, v1.16b, #1
     +0x2e0: ext     v1.16b, v2.16b, v1.16b, #1
     +0x2e4: orr     v0.16b, v0.16b, v3.16b
     +0x2e8: eor     v1.16b, v1.16b, v2.16b
     +0x2ec: umov    w0, v0.b[0]
     +0x2f0: umov    w1, v1.b[0]
     +0x2f4: neg     x0, x0
     +0x2f8: asr     x0, x0, #32
     +0x2fc: eor     w0, w1, w0
     +0x300: and     w0, w0, #0xff
     +0x304: orr     w25, w25, w27
     +0x308: eor     w0, w0, w1
     +0x30c: orr     w0, w4, w0
     +0x310: orr     w0, w0, w25
     +0x314: tst     w0, #0xff
     +0x318: b.eq    <+0x118>
     +0x31c: mov     w22, #0xfffffff9
     +0x320: b       <+0x108>
     +0x324: bl      <__stack_chk_fail@plt>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_pk_from_sk"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The secret key at sk is    *)
(* the 4032 bytes skb; if it passes the checks, mld_pk_from_sk_valid, the    *)
(* public key at pk becomes mld_pk_from_sk_pk and the result is 0, and       *)
(* otherwise the public key is zeroed and the result is MLD_ERR_INVALID_KEY  *)
(* (-7 as a 32-bit integer). The expansion of the matrix from rho is assumed *)
(* to terminate. The stack is the 8976 bytes of the function and the 37936   *)
(* of the callees below them.                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          nonoverlapping (pk,1952) (word_sub stackpointer (word 46912),46912) /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (word_sub stackpointer (word 46912),46912)]
           [(sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_pk_from_sk_valid 6 5 4 mld_polyeta_unpack_4 128
                          skb
                     then word 0 else word 4294967289) /\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             if mld_pk_from_sk_valid 6 5 4
                                  mld_polyeta_unpack_4 128 skb
                             then mld_pk_from_sk_pk 5 mld_polyeta_unpack_4 128
                                   skb j
                             else word 0))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952);
                  memory :> bytes(word_sub stackpointer (word 46912),46912)])`;;

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the result of the checks,    *)
(* the address of memset and the stack, with all accesses within the         *)
(* arguments, the stack, the GOT entries and the stack guard, the region     *)
(* (ea,el) that memset may read and the constants of the callees, and the    *)
(* writes within the public key and the stack.                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          nonoverlapping (pk,1952) (word_sub stackpointer (word 46912),46912) /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (word_sub stackpointer (word 46912),46912)]
           [(sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_pk_from_sk_valid 6 5 4 mld_polyeta_unpack_4 128
                          skb
                     then word 0 else word 4294967289) /\
                    (!j. j < 1952
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             if mld_pk_from_sk_valid 6 5 4
                                  mld_polyeta_unpack_4 128 skb
                             then mld_pk_from_sk_pk 5 mld_polyeta_unpack_4 128
                                   skb j
                             else word 0) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk (mld_sk_rho skb)
                              (mld_pk_from_sk_valid 6 5 4 mld_polyeta_unpack_4
                                128 skb)
                              guard mf pc (word_sub stackpointer (word 46912))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sk,4032; pk,1952;
                         word_sub stackpointer (word 46912),46912;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const2),16]
                        [pk,1952; word_sub stackpointer (word 46912),46912]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952);
                  memory :> bytes(word_sub stackpointer (word 46912),46912)])`;;

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          nonoverlapping (pk,1952) (word_sub stackpointer (word 46912),46912) /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (word_sub stackpointer (word 46912),46912)]
           [(sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4032
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk (mld_sk_rho skb)
                              (mld_pk_from_sk_valid 6 5 4 mld_polyeta_unpack_4
                                128 skb)
                              guard mf pc (word_sub stackpointer (word 46912))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sk,4032; pk,1952;
                         word_sub stackpointer (word 46912),46912;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa65_polyvecl_pointwise_acc_montgomery_const2),16]
                        [pk,1952; word_sub stackpointer (word 46912),46912]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952);
                  memory :> bytes(word_sub stackpointer (word 46912),46912)])`;;

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
