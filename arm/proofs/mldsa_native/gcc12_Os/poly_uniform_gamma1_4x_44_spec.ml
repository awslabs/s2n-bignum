(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of the four polynomials of y in [-gamma1 + 1, gamma1]    *)
(* for ML-DSA-44 (gamma1 = 2^17): the statement. This is the code for        *)
(* mldsa44_poly_uniform_gamma1_4x (mld_poly_uniform_gamma1_4x in poly_kl.c)  *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -Os *)
(* (see mldsa_native/README.md), which extends the seed of 64 bytes with     *)
(* each of the four 16-bit nonces, absorbs the four into a fourfold SHAKE256 *)
(* state, squeezes 5 blocks of 136 bytes of each and unpacks each polynomial *)
(* from the first 576 bytes with mldsa44_polyz_unpack, before releasing the  *)
(* state and zeroing the buffers with two calls of mld_zeroize_1 (which      *)
(* calls memset). It is verified in the whole image (see libmldsa.ml)        *)
(* against mld_poly_uniform_gamma1_17 of common/mldsa_native_sampling.ml,    *)
(* using the theorems for the callees and the contract memset_full_contract  *)
(* of utils/mlkem_native_libc_full.ml for memset. The first three nonces are *)
(* the low 16 bits of the sixth to eighth arguments, the fourth the 16 bits  *)
(* that the caller puts on the stack. It is also shown to be constant time   *)
(* and memory safe, with the events depending only on the addresses.         *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256x4_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256x4_absorb_once_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256x4_squeezeblocks_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256x4_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyz_unpack_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/zeroize_1_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa44_poly_uniform_gamma1_4x:
       +0x0: mov     x12, #0x1020
       +0x4: sub     sp, sp, x12
       +0x8: stp     x19, x20, [sp]
       +0xc: add     x19, sp, #0x7f
      +0x10: and     x19, x19, #0xffffffffffffffe0
      +0x14: stp     x21, x22, [sp, #16]
      +0x18: add     x20, x19, #0xb00
      +0x1c: add     x21, x19, #0xb60
      +0x20: stp     x23, x24, [sp, #32]
      +0x24: mov     x24, x1
      +0x28: mov     x23, x2
      +0x2c: stp     x25, x26, [sp, #48]
      +0x30: mov     x25, x0
      +0x34: add     x26, x19, #0xbc0
      +0x38: stp     x27, x28, [sp, #64]
      +0x3c: add     x27, x19, #0xc20
      +0x40: add     x28, sp, #0xcf8
      +0x44: str     x30, [sp, #80]
      +0x48: mov     x22, x3
      +0x4c: adrp    x0, <page>
      +0x50: ldr     x0, [x0, #4088]
      +0x54: ldp     q0, q1, [x4, #32]
      +0x58: ldr     x1, [x0]
      +0x5c: str     x1, [sp, #4120]
      +0x60: mov     x1, #0x0
      +0x64: ldp     q2, q3, [x4]
      +0x68: stp     q0, q1, [x21, #32]
      +0x6c: stp     q0, q1, [x26, #32]
      +0x70: stp     q0, q1, [x20, #32]
      +0x74: stp     q2, q3, [x21]
      +0x78: stp     q2, q3, [x26]
      +0x7c: stp     q2, q3, [x27]
      +0x80: stp     q2, q3, [x20]
      +0x84: stp     q0, q1, [x27, #32]
      +0x88: ldrh    w0, [sp, #4128]
      +0x8c: strh    w5, [x19, #2880]
      +0x90: strh    w6, [x19, #2976]
      +0x94: strh    w7, [x19, #3072]
      +0x98: strh    w0, [x19, #3168]
      +0x9c: mov     x0, x28
      +0xa0: bl      <mldsa_shake256x4_init>
      +0xa4: mov     x4, x27
      +0xa8: mov     x3, x26
      +0xac: mov     x2, x21
      +0xb0: mov     x1, x20
      +0xb4: mov     x0, x28
      +0xb8: add     x21, x19, #0x840
      +0xbc: add     x26, x19, #0x580
      +0xc0: mov     x5, #0x42
      +0xc4: bl      <mldsa_shake256x4_absorb_once>
      +0xc8: add     x27, x19, #0x2c0
      +0xcc: mov     x2, x26
      +0xd0: mov     x5, x28
      +0xd4: mov     x3, x21
      +0xd8: mov     x4, #0x5
      +0xdc: mov     x1, x27
      +0xe0: mov     x0, x19
      +0xe4: bl      <mldsa_shake256x4_squeezeblocks>
      +0xe8: mov     x1, x19
      +0xec: mov     x0, x25
      +0xf0: bl      <mldsa44_polyz_unpack>
      +0xf4: mov     x1, x27
      +0xf8: mov     x0, x24
      +0xfc: bl      <mldsa44_polyz_unpack>
     +0x100: mov     x1, x26
     +0x104: mov     x0, x23
     +0x108: bl      <mldsa44_polyz_unpack>
     +0x10c: mov     x1, x21
     +0x110: mov     x0, x22
     +0x114: bl      <mldsa44_polyz_unpack>
     +0x118: mov     x0, x28
     +0x11c: bl      <mldsa_shake256x4_release>
     +0x120: mov     x0, x19
     +0x124: mov     x1, #0xb00
     +0x128: bl      <mld_zeroize_1>
     +0x12c: mov     x0, x20
     +0x130: mov     x1, #0x180
     +0x134: bl      <mld_zeroize_1>
     +0x138: adrp    x0, <page>
     +0x13c: ldr     x0, [x0, #4088]
     +0x140: ldr     x2, [sp, #4120]
     +0x144: ldr     x1, [x0]
     +0x148: subs    x2, x2, x1
     +0x14c: mov     x1, #0x0
     +0x150: b.eq    <mldsa44_poly_uniform_gamma1_4x+0x158>
     +0x154: bl      <stack_chk_fail>
     +0x158: ldp     x19, x20, [sp]
     +0x15c: mov     x12, #0x1020
     +0x160: ldp     x21, x22, [sp, #16]
     +0x164: ldp     x23, x24, [sp, #32]
     +0x168: ldp     x25, x26, [sp, #48]
     +0x16c: ldp     x27, x28, [sp, #64]
     +0x170: ldr     x30, [sp, #80]
     +0x174: add     sp, sp, x12
     +0x178: ret
 ***)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa44_poly_uniform_gamma1_4x"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The seed is the 64 bytes   *)
(* sd at seed, and polynomial j becomes mld_poly_uniform_gamma1_17 sd of the *)
(* nonce j. The stack is the 4128 bytes of the function and the 336 below    *)
(* them of mldsa_shake256x4_absorb_once, and the fourth nonce is the 16 bits *)
(* at the stack pointer.                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !r0 r1 r2 r3 seed sd n0 n1 n2 n3 guard pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 4464),4464)] /\
          ALLPAIRS nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 4464),4464)]
           [(seed,64); (stackpointer,2);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_poly_uniform_gamma1_4x) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r0; r1; r2; r3; seed; n0; n1; n2] s /\
                    read (memory :> bytes16 stackpointer) s = n3 /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,64)) s = sd)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r0 (word(4 * i))))
                               s =
                             mld_poly_uniform_gamma1_17 sd (word_zx n0) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                               s =
                             mld_poly_uniform_gamma1_17 sd (word_zx n1) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                               s =
                             mld_poly_uniform_gamma1_17 sd (word_zx n2) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                               s =
                             mld_poly_uniform_gamma1_17 sd n3 i))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                  memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                  memory :> bytes(word_sub stackpointer (word 4464),4464)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the address of memset and the     *)
(* stack, with all accesses within the arguments, the stack, the GOT entries *)
(* and the stack guard, the region (ea,el) that memset may read and the      *)
(* round constants of Keccak, and the writes within the polynomials and the  *)
(* stack; and constant time and memory safety alone.                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e r0 r1 r2 r3 seed sd n0 n1 n2 n3 guard pc stackpointer
                 returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 4464),4464)] /\
          ALLPAIRS nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 4464),4464)]
           [(seed,64); (stackpointer,2);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_poly_uniform_gamma1_4x) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r0; r1; r2; r3; seed; n0; n1; n2] s /\
                    read (memory :> bytes16 stackpointer) s = n3 /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,64)) s = sd /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r0 (word(4 * i))))
                               s =
                             mld_poly_uniform_gamma1_17 sd (word_zx n0) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                               s =
                             mld_poly_uniform_gamma1_17 sd (word_zx n1) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                               s =
                             mld_poly_uniform_gamma1_17 sd (word_zx n2) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                               s =
                             mld_poly_uniform_gamma1_17 sd n3 i) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events r0 r1 r2 r3 seed guard mf pc
                              (word_sub stackpointer (word 4464))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,64; stackpointer,2;
                         r0,1024; r1,1024; r2,1024; r3,1024;
                         word_sub stackpointer (word 4464),4464;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [r0,1024; r1,1024; r2,1024; r3,1024;
                         word_sub stackpointer (word 4464),4464]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                  memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                  memory :> bytes(word_sub stackpointer (word 4464),4464)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e r0 r1 r2 r3 seed n0 n1 n2 guard pc stackpointer
                 returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 4464),4464)] /\
          ALLPAIRS nonoverlapping
           [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
            (word_sub stackpointer (word 4464),4464)]
           [(seed,64); (stackpointer,2);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_poly_uniform_gamma1_4x) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r0; r1; r2; r3; seed; n0; n1; n2] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events r0 r1 r2 r3 seed guard mf pc
                              (word_sub stackpointer (word 4464))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,64; stackpointer,2;
                         r0,1024; r1,1024; r2,1024; r3,1024;
                         word_sub stackpointer (word 4464),4464;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [r0,1024; r1,1024; r2,1024; r3,1024;
                         word_sub stackpointer (word 4464),4464]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                  memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                  memory :> bytes(word_sub stackpointer (word 4464),4464)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
