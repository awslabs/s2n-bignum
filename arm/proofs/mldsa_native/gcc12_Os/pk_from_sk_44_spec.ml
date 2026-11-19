(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The public key of a secret key: the statement. This is the code for       *)
(* mldsa44_pk_from_sk (mld_sign_pk_from_sk in sign.c) from mldsa-native's    *)
(* portable C implementation compiled by gcc 12 with -Os (see                *)
(* mldsa_native/README.md), which copies rho, the key and tr from the secret *)
(* key, unpacks s1 with mldsa44_polyvecl_unpack_eta and checks it and s2     *)
(* with mldsa44_polyvecl_chknorm and mldsa44_polyveck_unpack_eta_chknorm,    *)
(* transforms s1 with mldsa44_polyvecl_ntt, recomputes t1 into the public    *)
(* key and t0 into a buffer with mld_compute_pack_t0_t144, compares t0 with  *)
(* that in the secret key and, after hashing the public key with             *)
(* mldsa_shake256, the hash with tr, all in constant time with               *)
(* mld_ct_memcmp_1, and then zeroes the public key if a check failed and the *)
(* buffers with mld_zeroize_2 (a call of memset). It is verified in the      *)
(* whole image (see libmldsa.ml) against mld_pk_from_sk_pk and               *)
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
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_unpack_eta_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_chknorm_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyveck_unpack_eta_chknorm_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_ntt_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/compute_pack_t0_t1_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/ct_memcmp_1_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/zeroize_2_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa44_pk_from_sk:
       +0x0: mov     x12, #0x1bd0
       +0x4: sub     sp, sp, x12
       +0x8: mov     x4, #0x1c00
       +0xc: mov     x3, #0x1ac0
      +0x10: mov     x2, #0x1b20
      +0x14: stp     x21, x22, [sp, #16]
      +0x18: mov     x21, x0
      +0x1c: adrp    x0, <page>
      +0x20: ldr     x0, [x0, #4088]
      +0x24: stp     x25, x26, [sp, #48]
      +0x28: mov     x25, x1
      +0x2c: stp     x19, x20, [sp]
      +0x30: add     x19, sp, #0x8f
      +0x34: and     x19, x19, #0xffffffffffffffe0
      +0x38: stp     x23, x24, [sp, #32]
      +0x3c: add     x23, x1, #0x200
      +0x40: mov     x1, #0x1680
      +0x44: stp     x27, x28, [sp, #64]
      +0x48: add     x28, x19, x1
      +0x4c: add     x27, x19, x3
      +0x50: str     x30, [sp, #80]
      +0x54: add     x26, x19, x2
      +0x58: add     x24, x19, #0x1, lsl #12
      +0x5c: ldp     q0, q1, [x25]
      +0x60: ldr     x1, [x0]
      +0x64: str     x1, [sp, #7112]
      +0x68: mov     x1, #0x0
      +0x6c: add     x0, x19, x4
      +0x70: add     x1, x25, #0x40
      +0x74: sub     x22, x0, #0xe0
      +0x78: stp     q0, q1, [x22]
      +0x7c: ldp     q0, q1, [x25, #32]
      +0x80: stp     q0, q1, [x0, #-256]
      +0x84: sub     x0, x0, #0x140
      +0x88: ldp     q0, q1, [x1]
      +0x8c: stp     q0, q1, [x0]
      +0x90: ldp     q0, q1, [x1, #32]
      +0x94: add     x1, x25, #0x80
      +0x98: stp     q0, q1, [x0, #32]
      +0x9c: mov     x0, x19
      +0xa0: bl      <mldsa44_polyvecl_unpack_eta>
      +0xa4: mov     w1, #0x3
      +0xa8: mov     x0, x19
      +0xac: bl      <mldsa44_polyvecl_chknorm>
      +0xb0: mov     w20, w0
      +0xb4: mov     x2, x28
      +0xb8: mov     w1, #0x3
      +0xbc: mov     x0, x23
      +0xc0: bl      <mldsa44_polyveck_unpack_eta_chknorm>
      +0xc4: str     w0, [sp, #104]
      +0xc8: mov     x0, x19
      +0xcc: bl      <mldsa44_polyvecl_ntt>
      +0xd0: ldp     q0, q1, [x22]
      +0xd4: mov     x3, x23
      +0xd8: mov     x4, x26
      +0xdc: mov     x2, x19
      +0xe0: mov     x1, x24
      +0xe4: add     x0, x21, #0x20
      +0xe8: stp     q0, q1, [x21]
      +0xec: bl      <mld_compute_pack_t0_t144>
      +0xf0: mov     x5, #0x1a80
      +0xf4: mov     w22, w0
      +0xf8: add     x23, x19, x5
      +0xfc: cbnz    w0, <mldsa44_pk_from_sk+0x15c>
     +0x100: add     x1, x25, #0x380
     +0x104: mov     x0, x24
     +0x108: mov     x2, #0x680
     +0x10c: bl      <mld_ct_memcmp_1>
     +0x110: and     w4, w0, #0xff
     +0x114: mov     x3, #0x520
     +0x118: mov     x2, x21
     +0x11c: mov     x0, x23
     +0x120: mov     x1, #0x40
     +0x124: str     w4, [sp, #108]
     +0x128: bl      <mldsa_shake256>
     +0x12c: mov     x1, x23
     +0x130: mov     x0, x27
     +0x134: mov     x2, #0x40
     +0x138: bl      <mld_ct_memcmp_1>
     +0x13c: ldp     w1, w4, [sp, #104]
     +0x140: and     w0, w0, #0xff
     +0x144: orr     w20, w20, w1
     +0x148: orr     w4, w4, w0
     +0x14c: orr     w20, w20, w4
     +0x150: tst     w20, #0xff
     +0x154: b.eq    <mldsa44_pk_from_sk+0x168>
     +0x158: mov     w22, #0xfffffff9
     +0x15c: mov     x0, x21
     +0x160: mov     x1, #0x520
     +0x164: bl      <mld_zeroize_2>
     +0x168: mov     x0, x24
     +0x16c: mov     x1, #0x680
     +0x170: bl      <mld_zeroize_2>
     +0x174: mov     x0, x28
     +0x178: mov     x1, #0x400
     +0x17c: bl      <mld_zeroize_2>
     +0x180: mov     x0, x19
     +0x184: mov     x1, #0x1000
     +0x188: bl      <mld_zeroize_2>
     +0x18c: mov     x1, #0x20
     +0x190: mov     x0, #0x1b00
     +0x194: add     x0, x19, x0
     +0x198: bl      <mld_zeroize_2>
     +0x19c: mov     x0, x23
     +0x1a0: mov     x1, #0x40
     +0x1a4: bl      <mld_zeroize_2>
     +0x1a8: mov     x0, x27
     +0x1ac: mov     x1, #0x40
     +0x1b0: bl      <mld_zeroize_2>
     +0x1b4: mov     x0, x26
     +0x1b8: mov     x1, #0x20
     +0x1bc: bl      <mld_zeroize_2>
     +0x1c0: adrp    x0, <page>
     +0x1c4: ldr     x0, [x0, #4088]
     +0x1c8: ldr     x2, [sp, #7112]
     +0x1cc: ldr     x1, [x0]
     +0x1d0: subs    x2, x2, x1
     +0x1d4: mov     x1, #0x0
     +0x1d8: b.eq    <mldsa44_pk_from_sk+0x1e0>
     +0x1dc: bl      <stack_chk_fail>
     +0x1e0: ldp     x19, x20, [sp]
     +0x1e4: mov     w0, w22
     +0x1e8: ldp     x21, x22, [sp, #16]
     +0x1ec: mov     x12, #0x1bd0
     +0x1f0: ldp     x23, x24, [sp, #32]
     +0x1f4: ldp     x25, x26, [sp, #48]
     +0x1f8: ldp     x27, x28, [sp, #64]
     +0x1fc: ldr     x30, [sp, #80]
     +0x200: add     sp, sp, x12
     +0x204: ret
 ***)

let MLDSA_NATIVE_PK_FROM_SK_44_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa44_pk_from_sk"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The secret key at sk is    *)
(* the 2560 bytes skb; if it passes the checks, mld_pk_from_sk_valid, the    *)
(* public key at pk becomes mld_pk_from_sk_pk and the result is 0, and       *)
(* otherwise the public key is zeroed and the result is MLD_ERR_INVALID_KEY  *)
(* (-7 as a 32-bit integer). The expansion of the matrix from rho is assumed *)
(* to terminate. The stack is the 7120 bytes of the function and the 23680   *)
(* of the callees below them.                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
          nonoverlapping (pk,1312) (word_sub stackpointer (word 30800),30800) /\
          ALLPAIRS nonoverlapping
           [(pk,1312); (word_sub stackpointer (word 30800),30800)]
           [(sk,2560); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j))
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_pk_from_sk_valid 4 4 2 mld_polyeta_unpack_2 96
                          skb
                     then word 0 else word 4294967289) /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             if mld_pk_from_sk_valid 4 4 2
                                  mld_polyeta_unpack_2 96 skb
                             then mld_pk_from_sk_pk 4 mld_polyeta_unpack_2 96
                                   skb j
                             else word 0))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1312);
                  memory :> bytes(word_sub stackpointer (word 30800),30800)])`;;

let MLDSA_NATIVE_PK_FROM_SK_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the result of the checks,    *)
(* the address of memset and the stack, with all accesses within the         *)
(* arguments, the stack, the GOT entries and the stack guard, the region     *)
(* (ea,el) that memset may read and the constants of the callees, and the    *)
(* writes within the public key and the stack.                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
          nonoverlapping (pk,1312) (word_sub stackpointer (word 30800),30800) /\
          ALLPAIRS nonoverlapping
           [(pk,1312); (word_sub stackpointer (word 30800),30800)]
           [(sk,2560); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    C_RETURN s =
                    (if mld_pk_from_sk_valid 4 4 2 mld_polyeta_unpack_2 96
                          skb
                     then word 0 else word 4294967289) /\
                    (!j. j < 1312
                         ==> read(memory :> bytes8(word_add pk (word j))) s =
                             if mld_pk_from_sk_valid 4 4 2
                                  mld_polyeta_unpack_2 96 skb
                             then mld_pk_from_sk_pk 4 mld_polyeta_unpack_2 96
                                   skb j
                             else word 0) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk (mld_sk_rho skb)
                              (mld_pk_from_sk_valid 4 4 2 mld_polyeta_unpack_2
                                96 skb)
                              guard mf pc (word_sub stackpointer (word 30800))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sk,2560; pk,1312;
                         word_sub stackpointer (word 30800),30800;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024]
                        [pk,1312; word_sub stackpointer (word 30800),30800]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1312);
                  memory :> bytes(word_sub stackpointer (word 30800),30800)])`;;

let MLDSA_NATIVE_PK_FROM_SK_44_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 4 4 (mld_sk_rho skb) /\
          nonoverlapping (pk,1312) (word_sub stackpointer (word 30800),30800) /\
          ALLPAIRS nonoverlapping
           [(pk,1312); (word_sub stackpointer (word 30800),30800)]
           [(sk,2560); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_pk_from_sk) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [pk; sk] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!j. j < 2560
                         ==> read(memory :> bytes8(word_add sk (word j))) s =
                             skb j) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events pk sk (mld_sk_rho skb)
                              (mld_pk_from_sk_valid 4 4 2 mld_polyeta_unpack_2
                                96 skb)
                              guard mf pc (word_sub stackpointer (word 30800))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sk,2560; pk,1312;
                         word_sub stackpointer (word 30800),30800;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024]
                        [pk,1312; word_sub stackpointer (word 30800),30800]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1312);
                  memory :> bytes(word_sub stackpointer (word 30800),30800)])`;;

let MLDSA_NATIVE_PK_FROM_SK_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
