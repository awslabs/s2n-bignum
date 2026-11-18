(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The public key of a secret key: the statement. This is the code for       *)
(* mldsa87_pk_from_sk (mld_sign_pk_from_sk in sign.c) from mldsa-native's    *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mldsa_native/README.md), which copies rho, the key and tr from the secret *)
(* key, unpacks s1 with mldsa87_polyvecl_unpack_eta and checks it and s2     *)
(* with mldsa87_polyvecl_chknorm and mldsa87_polyveck_unpack_eta_chknorm,    *)
(* transforms s1 with mldsa87_polyvecl_ntt, recomputes t1 into the public    *)
(* key and t0 into a buffer with mld_compute_pack_t0_t187, compares t0 with  *)
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
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_unpack_eta_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_chknorm_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyveck_unpack_eta_chknorm_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyvecl_ntt_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/compute_pack_t0_t1_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa87_pk_from_sk:
       +0x0: mov     x12, #0x2e50
       +0x4: sub     sp, sp, x12
       +0x8: adrp    x4, <page>
       +0xc: ldr     x4, [x4, #4088]
      +0x10: mov     x8, #0x2c00
      +0x14: stp     x19, x20, [sp]
      +0x18: mov     x20, x1
      +0x1c: add     x1, x1, #0x40
      +0x20: add     x19, sp, #0x8f
      +0x24: stp     x21, x22, [sp, #16]
      +0x28: and     x19, x19, #0xffffffffffffffe0
      +0x2c: stp     x23, x24, [sp, #32]
      +0x30: add     x2, x19, x8
      +0x34: add     x3, x2, #0x140
      +0x38: stp     x25, x26, [sp, #48]
      +0x3c: add     x22, x2, #0x1a0
      +0x40: mov     x9, #0x2900
      +0x44: stp     x27, x28, [sp, #64]
      +0x48: mov     x10, #0x2da0
      +0x4c: mov     x11, #0x1c00
      +0x50: str     x30, [sp, #80]
      +0x54: add     x26, x19, x9
      +0x58: add     x23, x19, x10
      +0x5c: add     x24, x19, x11
      +0x60: ldp     q6, q7, [x1]
      +0x64: ldr     x5, [x4]
      +0x68: str     x5, [sp, #11848]
      +0x6c: mov     x5, #0x0
      +0x70: ldp     q4, q5, [x20]
      +0x74: mov     x21, x0
      +0x78: ldp     q2, q3, [x1, #32]
      +0x7c: mov     x0, x19
      +0x80: ldp     q0, q1, [x20, #32]
      +0x84: add     x1, x20, #0x80
      +0x88: stp     q6, q7, [x3]
      +0x8c: add     x28, x20, #0x320
      +0x90: stp     q4, q5, [x22]
      +0x94: stp     q2, q3, [x3, #32]
      +0x98: stp     q0, q1, [x2, #384]
      +0x9c: bl      <mldsa87_polyvecl_unpack_eta>
      +0xa0: mov     w1, #0x3
      +0xa4: mov     x0, x19
      +0xa8: bl      <mldsa87_polyvecl_chknorm>
      +0xac: mov     x2, x26
      +0xb0: mov     w1, #0x3
      +0xb4: mov     w25, w0
      +0xb8: mov     x0, x28
      +0xbc: bl      <mldsa87_polyveck_unpack_eta_chknorm>
      +0xc0: mov     w27, w0
      +0xc4: mov     x0, x19
      +0xc8: bl      <mldsa87_polyvecl_ntt>
      +0xcc: ldp     q0, q1, [x22]
      +0xd0: mov     x3, x28
      +0xd4: mov     x4, x23
      +0xd8: mov     x1, x24
      +0xdc: mov     x2, x19
      +0xe0: add     x0, x21, #0x20
      +0xe4: stp     q0, q1, [x21]
      +0xe8: bl      <mld_compute_pack_t0_t187>
      +0xec: mov     w22, w0
      +0xf0: cbz     w0, <mldsa87_pk_from_sk+0x1b4>
      +0xf4: mov     x6, #0x2d00
      +0xf8: mov     x7, #0x2d40
      +0xfc: add     x28, x19, x6
     +0x100: add     x20, x19, x7
     +0x104: mov     x0, x21
     +0x108: mov     x2, #0xa20
     +0x10c: mov     w1, #0x0
     +0x110: bl      <memset>
     +0x114: mov     x0, x24
     +0x118: mov     x2, #0xd00
     +0x11c: mov     w1, #0x0
     +0x120: bl      <memset>
     +0x124: mov     x2, #0x400
     +0x128: mov     x0, x26
     +0x12c: mov     w1, #0x0
     +0x130: bl      <memset>
     +0x134: mov     x2, #0x1c00
     +0x138: mov     x0, x19
     +0x13c: mov     w1, #0x0
     +0x140: bl      <memset>
     +0x144: mov     x0, #0x2d80
     +0x148: add     x19, x19, x0
     +0x14c: stp     xzr, xzr, [x19]
     +0x150: stp     xzr, xzr, [x19, #16]
     +0x154: movi    v0.4s, #0x0
     +0x158: stp     q0, q0, [x28]
     +0x15c: stp     q0, q0, [x28, #32]
     +0x160: stp     q0, q0, [x20]
     +0x164: stp     q0, q0, [x20, #32]
     +0x168: stp     xzr, xzr, [x23]
     +0x16c: stp     xzr, xzr, [x23, #16]
     +0x170: adrp    x0, <page>
     +0x174: ldr     x0, [x0, #4088]
     +0x178: ldr     x2, [sp, #11848]
     +0x17c: ldr     x1, [x0]
     +0x180: subs    x2, x2, x1
     +0x184: mov     x1, #0x0
     +0x188: b.ne    <mldsa87_pk_from_sk+0x31c>
     +0x18c: ldp     x19, x20, [sp]
     +0x190: mov     w0, w22
     +0x194: ldp     x21, x22, [sp, #16]
     +0x198: mov     x12, #0x2e50
     +0x19c: ldp     x23, x24, [sp, #32]
     +0x1a0: ldp     x25, x26, [sp, #48]
     +0x1a4: ldp     x27, x28, [sp, #64]
     +0x1a8: ldr     x30, [sp, #80]
     +0x1ac: add     sp, sp, x12
     +0x1b0: ret
     +0x1b4: movi    v1.4s, #0x0
     +0x1b8: add     x20, x20, #0x620
     +0x1bc: mov     x0, x24
     +0x1c0: add     x1, x24, #0xd00
     +0x1c4: mov     v2.16b, v1.16b
     +0x1c8: ldr     q0, [x20], #16
     +0x1cc: ldr     q3, [x0], #16
     +0x1d0: eor     v0.16b, v0.16b, v3.16b
     +0x1d4: orr     v2.16b, v2.16b, v0.16b
     +0x1d8: eor     v1.16b, v1.16b, v0.16b
     +0x1dc: cmp     x1, x0
     +0x1e0: b.ne    <mldsa87_pk_from_sk+0x1c8>
     +0x1e4: movi    v0.4s, #0x0
     +0x1e8: ext     v4.16b, v2.16b, v0.16b, #8
     +0x1ec: ext     v3.16b, v1.16b, v0.16b, #8
     +0x1f0: orr     v4.16b, v4.16b, v2.16b
     +0x1f4: eor     v3.16b, v3.16b, v1.16b
     +0x1f8: ext     v2.16b, v4.16b, v0.16b, #4
     +0x1fc: ext     v1.16b, v3.16b, v0.16b, #4
     +0x200: orr     v2.16b, v2.16b, v4.16b
     +0x204: eor     v1.16b, v1.16b, v3.16b
     +0x208: ext     v4.16b, v2.16b, v0.16b, #2
     +0x20c: ext     v3.16b, v1.16b, v0.16b, #2
     +0x210: orr     v4.16b, v4.16b, v2.16b
     +0x214: eor     v3.16b, v3.16b, v1.16b
     +0x218: ext     v1.16b, v4.16b, v0.16b, #1
     +0x21c: ext     v2.16b, v3.16b, v0.16b, #1
     +0x220: orr     v1.16b, v1.16b, v4.16b
     +0x224: eor     v2.16b, v2.16b, v3.16b
     +0x228: umov    w0, v1.b[0]
     +0x22c: umov    w1, v2.b[0]
     +0x230: neg     x0, x0
     +0x234: asr     x0, x0, #32
     +0x238: eor     w0, w1, w0
     +0x23c: and     w0, w0, #0xff
     +0x240: mov     x5, #0x2d40
     +0x244: eor     w4, w0, w1
     +0x248: mov     x2, #0x2d00
     +0x24c: add     x28, x19, x2
     +0x250: add     x20, x19, x5
     +0x254: mov     x0, x28
     +0x258: mov     x2, x21
     +0x25c: mov     x1, #0x40
     +0x260: mov     x3, #0xa20
     +0x264: str     w4, [sp, #108]
     +0x268: bl      <mldsa_shake256>
     +0x26c: movi    v0.4s, #0x0
     +0x270: ldr     w4, [sp, #108]
     +0x274: mov     x0, x28
     +0x278: add     x2, x28, #0x40
     +0x27c: mov     x1, x20
     +0x280: mov     v2.16b, v0.16b
     +0x284: ldr     q1, [x0], #16
     +0x288: ldr     q3, [x1], #16
     +0x28c: eor     v1.16b, v1.16b, v3.16b
     +0x290: orr     v2.16b, v2.16b, v1.16b
     +0x294: eor     v0.16b, v0.16b, v1.16b
     +0x298: cmp     x0, x2
     +0x29c: b.ne    <mldsa87_pk_from_sk+0x284>
     +0x2a0: movi    v1.4s, #0x0
     +0x2a4: ext     v5.16b, v2.16b, v1.16b, #8
     +0x2a8: ext     v3.16b, v0.16b, v1.16b, #8
     +0x2ac: orr     v5.16b, v5.16b, v2.16b
     +0x2b0: eor     v2.16b, v3.16b, v0.16b
     +0x2b4: ext     v4.16b, v5.16b, v1.16b, #4
     +0x2b8: ext     v0.16b, v2.16b, v1.16b, #4
     +0x2bc: orr     v4.16b, v4.16b, v5.16b
     +0x2c0: eor     v0.16b, v0.16b, v2.16b
     +0x2c4: ext     v3.16b, v4.16b, v1.16b, #2
     +0x2c8: ext     v2.16b, v0.16b, v1.16b, #2
     +0x2cc: orr     v3.16b, v3.16b, v4.16b
     +0x2d0: eor     v2.16b, v2.16b, v0.16b
     +0x2d4: ext     v0.16b, v3.16b, v1.16b, #1
     +0x2d8: ext     v1.16b, v2.16b, v1.16b, #1
     +0x2dc: orr     v0.16b, v0.16b, v3.16b
     +0x2e0: eor     v1.16b, v1.16b, v2.16b
     +0x2e4: umov    w0, v0.b[0]
     +0x2e8: umov    w1, v1.b[0]
     +0x2ec: neg     x0, x0
     +0x2f0: asr     x0, x0, #32
     +0x2f4: eor     w0, w1, w0
     +0x2f8: and     w0, w0, #0xff
     +0x2fc: orr     w25, w25, w27
     +0x300: eor     w0, w0, w1
     +0x304: orr     w0, w4, w0
     +0x308: orr     w0, w0, w25
     +0x30c: tst     w0, #0xff
     +0x310: b.eq    <mldsa87_pk_from_sk+0x114>
     +0x314: mov     w22, #0xfffffff9
     +0x318: b       <mldsa87_pk_from_sk+0x104>
     +0x31c: bl      <stack_chk_fail>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_pk_from_sk"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The secret key at sk is    *)
(* the 4896 bytes skb; if it passes the checks, mld_pk_from_sk_valid, the    *)
(* public key at pk becomes mld_pk_from_sk_pk and the result is 0, and       *)
(* otherwise the public key is zeroed and the result is MLD_ERR_INVALID_KEY  *)
(* (-7 as a 32-bit integer). The expansion of the matrix from rho is assumed *)
(* to terminate. The stack is the 11856 bytes of the function and the 64560  *)
(* of the callees below them.                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          nonoverlapping (pk,2592) (word_sub stackpointer (word 76416),76416) /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (word_sub stackpointer (word 76416),76416)]
           [(sk,4896); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2 96
                          skb
                     then word 0 else word 4294967289) /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             if mld_pk_from_sk_valid 8 7 2
                                  mld_polyeta_unpack_2 96 skb
                             then mld_pk_from_sk_pk 7 mld_polyeta_unpack_2 96
                                   skb j
                             else word 0))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592);
                  memory :> bytes(word_sub stackpointer (word 76416),76416)])`;;

let MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the result of the checks,    *)
(* the address of memset and the stack, with all accesses within the         *)
(* arguments, the stack, the GOT entries and the stack guard, the region     *)
(* (ea,el) that memset may read and the constants of the callees, and the    *)
(* writes within the public key and the stack.                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          nonoverlapping (pk,2592) (word_sub stackpointer (word 76416),76416) /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (word_sub stackpointer (word 76416),76416)]
           [(sk,4896); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2 96
                          skb
                     then word 0 else word 4294967289) /\
                    (!j. j < 2592
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             if mld_pk_from_sk_valid 8 7 2
                                  mld_polyeta_unpack_2 96 skb
                             then mld_pk_from_sk_pk 7 mld_polyeta_unpack_2 96
                                   skb j
                             else word 0) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk (mld_sk_rho skb)
                              (mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2
                                96 skb)
                              guard mf pc (word_sub stackpointer (word 76416))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sk,4896; pk,2592;
                         word_sub stackpointer (word 76416),76416;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const2),16]
                        [pk,2592; word_sub stackpointer (word 76416),76416]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592);
                  memory :> bytes(word_sub stackpointer (word 76416),76416)])`;;

let MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 8 7 (mld_sk_rho skb) /\
          nonoverlapping (pk,2592) (word_sub stackpointer (word 76416),76416) /\
          ALLPAIRS nonoverlapping
           [(pk,2592); (word_sub stackpointer (word 76416),76416)]
           [(sk,4896); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa87_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 4896
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk (mld_sk_rho skb)
                              (mld_pk_from_sk_valid 8 7 2 mld_polyeta_unpack_2
                                96 skb)
                              guard mf pc (word_sub stackpointer (word 76416))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sk,4896; pk,2592;
                         word_sub stackpointer (word 76416),76416;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024;
                         word(pc + mldsa_poly_invntt_tomont_consts),48;
                         word(pc + mldsa_poly_reduce_consts),16;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const1),16;
                         word(pc +
                           mldsa87_polyvecl_pointwise_acc_montgomery_const2),16]
                        [pk,2592; word_sub stackpointer (word 76416),76416]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,2592);
                  memory :> bytes(word_sub stackpointer (word 76416),76416)])`;;

let MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
