(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The public key of a secret key: the statement. This is the code for       *)
(* mldsa65_pk_from_sk (mld_sign_pk_from_sk in sign.c) from mldsa-native's    *)
(* portable C implementation compiled by gcc 12 with -Os (see                *)
(* mldsa_native/README.md), which copies rho, the key and tr from the secret *)
(* key, unpacks s1 with mldsa65_polyvecl_unpack_eta and checks it and s2     *)
(* with mldsa65_polyvecl_chknorm and mldsa65_polyveck_unpack_eta_chknorm,    *)
(* transforms s1 with mldsa65_polyvecl_ntt, recomputes t1 into the public    *)
(* key and t0 into a buffer with mld_compute_pack_t0_t165, compares t0 with  *)
(* that in the secret key and, after hashing the public key with             *)
(* mldsa_shake256, the hash with tr, all in constant time with               *)
(* mld_ct_memcmp_2, and then zeroes the public key if a check failed and the *)
(* buffers with mld_zeroize_4 (a call of memset). It is verified in the      *)
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
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_unpack_eta_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_chknorm_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyveck_unpack_eta_chknorm_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyvecl_ntt_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/compute_pack_t0_t1_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/ct_memcmp_2_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/zeroize_4_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa65_pk_from_sk:
       +0x0: mov     x12, #0x2310
       +0x4: sub     sp, sp, x12
       +0x8: mov     x5, #0x2400
       +0xc: mov     x3, #0x1400
      +0x10: mov     x4, #0x2200
      +0x14: mov     x2, #0x2260
      +0x18: stp     x21, x22, [sp, #16]
      +0x1c: mov     x21, x0
      +0x20: adrp    x0, <page>
      +0x24: ldr     x0, [x0, #4088]
      +0x28: stp     x25, x26, [sp, #48]
      +0x2c: mov     x25, x1
      +0x30: stp     x19, x20, [sp]
      +0x34: add     x19, sp, #0x8f
      +0x38: and     x19, x19, #0xffffffffffffffe0
      +0x3c: stp     x23, x24, [sp, #32]
      +0x40: add     x23, x1, #0x300
      +0x44: mov     x1, #0x1dc0
      +0x48: stp     x27, x28, [sp, #64]
      +0x4c: add     x28, x19, x1
      +0x50: add     x24, x19, x3
      +0x54: str     x30, [sp, #80]
      +0x58: add     x27, x19, x4
      +0x5c: add     x26, x19, x2
      +0x60: ldp     q0, q1, [x25]
      +0x64: ldr     x1, [x0]
      +0x68: str     x1, [sp, #8968]
      +0x6c: mov     x1, #0x0
      +0x70: add     x0, x19, x5
      +0x74: sub     x22, x0, #0x1a0
      +0x78: sub     x1, x0, #0x1c0
      +0x7c: sub     x0, x0, #0x200
      +0x80: stp     q0, q1, [x22]
      +0x84: ldp     q0, q1, [x25, #32]
      +0x88: stp     q0, q1, [x1]
      +0x8c: add     x1, x25, #0x40
      +0x90: ldp     q0, q1, [x1]
      +0x94: stp     q0, q1, [x0]
      +0x98: ldp     q0, q1, [x1, #32]
      +0x9c: add     x1, x25, #0x80
      +0xa0: stp     q0, q1, [x0, #32]
      +0xa4: mov     x0, x19
      +0xa8: bl      <mldsa65_polyvecl_unpack_eta>
      +0xac: mov     w1, #0x5
      +0xb0: mov     x0, x19
      +0xb4: bl      <mldsa65_polyvecl_chknorm>
      +0xb8: mov     w20, w0
      +0xbc: mov     x2, x28
      +0xc0: mov     w1, #0x5
      +0xc4: mov     x0, x23
      +0xc8: bl      <mldsa65_polyveck_unpack_eta_chknorm>
      +0xcc: str     w0, [sp, #104]
      +0xd0: mov     x0, x19
      +0xd4: bl      <mldsa65_polyvecl_ntt>
      +0xd8: ldp     q0, q1, [x22]
      +0xdc: mov     x3, x23
      +0xe0: mov     x4, x26
      +0xe4: mov     x2, x19
      +0xe8: mov     x1, x24
      +0xec: add     x0, x21, #0x20
      +0xf0: stp     q0, q1, [x21]
      +0xf4: bl      <mld_compute_pack_t0_t165>
      +0xf8: mov     x6, #0x21c0
      +0xfc: mov     w22, w0
     +0x100: add     x23, x19, x6
     +0x104: cbnz    w0, <mldsa65_pk_from_sk+0x164>
     +0x108: add     x1, x25, #0x600
     +0x10c: mov     x0, x24
     +0x110: mov     x2, #0x9c0
     +0x114: bl      <mld_ct_memcmp_2>
     +0x118: and     w4, w0, #0xff
     +0x11c: mov     x3, #0x7a0
     +0x120: mov     x2, x21
     +0x124: mov     x0, x23
     +0x128: mov     x1, #0x40
     +0x12c: str     w4, [sp, #108]
     +0x130: bl      <mldsa_shake256>
     +0x134: mov     x1, x23
     +0x138: mov     x0, x27
     +0x13c: mov     x2, #0x40
     +0x140: bl      <mld_ct_memcmp_2>
     +0x144: ldp     w1, w4, [sp, #104]
     +0x148: and     w0, w0, #0xff
     +0x14c: orr     w20, w20, w1
     +0x150: orr     w4, w4, w0
     +0x154: orr     w20, w20, w4
     +0x158: tst     w20, #0xff
     +0x15c: b.eq    <mldsa65_pk_from_sk+0x170>
     +0x160: mov     w22, #0xfffffff9
     +0x164: mov     x0, x21
     +0x168: mov     x1, #0x7a0
     +0x16c: bl      <mld_zeroize_4>
     +0x170: mov     x0, x24
     +0x174: mov     x1, #0x9c0
     +0x178: bl      <mld_zeroize_4>
     +0x17c: mov     x0, x28
     +0x180: mov     x1, #0x400
     +0x184: bl      <mld_zeroize_4>
     +0x188: mov     x0, x19
     +0x18c: mov     x1, #0x1400
     +0x190: bl      <mld_zeroize_4>
     +0x194: mov     x1, #0x20
     +0x198: mov     x0, #0x2240
     +0x19c: add     x0, x19, x0
     +0x1a0: bl      <mld_zeroize_4>
     +0x1a4: mov     x0, x23
     +0x1a8: mov     x1, #0x40
     +0x1ac: bl      <mld_zeroize_4>
     +0x1b0: mov     x0, x27
     +0x1b4: mov     x1, #0x40
     +0x1b8: bl      <mld_zeroize_4>
     +0x1bc: mov     x0, x26
     +0x1c0: mov     x1, #0x20
     +0x1c4: bl      <mld_zeroize_4>
     +0x1c8: adrp    x0, <page>
     +0x1cc: ldr     x0, [x0, #4088]
     +0x1d0: ldr     x2, [sp, #8968]
     +0x1d4: ldr     x1, [x0]
     +0x1d8: subs    x2, x2, x1
     +0x1dc: mov     x1, #0x0
     +0x1e0: b.eq    <mldsa65_pk_from_sk+0x1e8>
     +0x1e4: bl      <stack_chk_fail>
     +0x1e8: ldp     x19, x20, [sp]
     +0x1ec: mov     w0, w22
     +0x1f0: ldp     x21, x22, [sp, #16]
     +0x1f4: mov     x12, #0x2310
     +0x1f8: ldp     x23, x24, [sp, #32]
     +0x1fc: ldp     x25, x26, [sp, #48]
     +0x200: ldp     x27, x28, [sp, #64]
     +0x204: ldr     x30, [sp, #80]
     +0x208: add     sp, sp, x12
     +0x20c: ret
 ***)

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa65_pk_from_sk"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The secret key at sk is    *)
(* the 4032 bytes skb; if it passes the checks, mld_pk_from_sk_valid, the    *)
(* public key at pk becomes mld_pk_from_sk_pk and the result is 0, and       *)
(* otherwise the public key is zeroed and the result is MLD_ERR_INVALID_KEY  *)
(* (-7 as a 32-bit integer). The expansion of the matrix from rho is assumed *)
(* to terminate. The stack is the 8976 bytes of the function and the 37984   *)
(* of the callees below them.                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          nonoverlapping (pk,1952) (word_sub stackpointer (word 46960),46960) /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (word_sub stackpointer (word 46960),46960)]
           [(sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                  memory :> bytes(word_sub stackpointer (word 46960),46960)])`;;

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho, the result of the checks,    *)
(* the address of memset and the stack, with all accesses within the         *)
(* arguments, the stack, the GOT entries and the stack guard, the region     *)
(* (ea,el) that memset may read and the constants of the callees, and the    *)
(* writes within the public key and the stack.                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          nonoverlapping (pk,1952) (word_sub stackpointer (word 46960),46960) /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (word_sub stackpointer (word 46960),46960)]
           [(sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                              guard mf pc (word_sub stackpointer (word 46960))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sk,4032; pk,1952;
                         word_sub stackpointer (word 46960),46960;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024]
                        [pk,1952; word_sub stackpointer (word 46960),46960]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952);
                  memory :> bytes(word_sub stackpointer (word 46960),46960)])`;;

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e pk sk skb guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_matrix_terminates 6 5 (mld_sk_rho skb) /\
          nonoverlapping (pk,1952) (word_sub stackpointer (word 46960),46960) /\
          ALLPAIRS nonoverlapping
           [(pk,1952); (word_sub stackpointer (word 46960),46960)]
           [(sk,4032); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                              guard mf pc (word_sub stackpointer (word 46960))
                              returnaddress /\
                       memaccess_inbounds e2
                        [sk,4032; pk,1952;
                         word_sub stackpointer (word 46960),46960;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + rodata_mld_zetas),1024]
                        [pk,1952; word_sub stackpointer (word 46960),46960]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(pk,1952);
                  memory :> bytes(word_sub stackpointer (word 46960),46960)])`;;

let MLDSA_NATIVE_PK_FROM_SK_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_PK_FROM_SK_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
