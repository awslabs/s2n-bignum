(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of the four polynomials of y in [-gamma1 + 1, gamma1]    *)
(* for ML-DSA-65 (gamma1 = 2^19): the statement. This is the code for        *)
(* mldsa65_poly_uniform_gamma1_4x (mld_poly_uniform_gamma1_4x in poly_kl.c)  *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -O2 *)
(* (see mldsa_native/README.md), which extends the seed of 64 bytes with     *)
(* each of the four 16-bit nonces, absorbs the four into a fourfold SHAKE256 *)
(* state, squeezes 5 blocks of 136 bytes of each and unpacks each polynomial *)
(* from the first 640 bytes with mldsa65_polyz_unpack, before zeroing the    *)
(* state and the buffers. It is verified in the whole image (see             *)
(* libmldsa.ml) against mld_poly_uniform_gamma1_19 of                        *)
(* common/mldsa_native_sampling.ml, using the theorems for the callees and   *)
(* the contract memset_full_contract of utils/mlkem_native_libc_full.ml for  *)
(* memset. The first three nonces are the low 16 bits of the sixth to eighth *)
(* arguments, the fourth the 16 bits that the caller puts on the stack. It   *)
(* is also shown to be constant time and memory safe, with the events        *)
(* depending only on the addresses.                                          *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256x4_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256x4_absorb_once_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256x4_squeezeblocks_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256x4_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/polyz_unpack_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa65_poly_uniform_gamma1_4x:
       +0x0: mov     x12, #0x1040
       +0x4: sub     sp, sp, x12
       +0x8: mov     x8, x4
       +0xc: adrp    x9, <page>
      +0x10: ldr     x9, [x9, #4088]
      +0x14: stp     x19, x20, [sp]
      +0x18: add     x19, sp, #0x9f
      +0x1c: stp     x21, x22, [sp, #16]
      +0x20: and     x19, x19, #0xffffffffffffffe0
      +0x24: add     x20, x19, #0xb00
      +0x28: stp     x23, x24, [sp, #32]
      +0x2c: add     x22, x19, #0xb60
      +0x30: add     x23, x19, #0xbc0
      +0x34: stp     x25, x26, [sp, #48]
      +0x38: add     x21, sp, #0xd18
      +0x3c: mov     x24, x1
      +0x40: stp     x27, x28, [sp, #64]
      +0x44: mov     x25, x0
      +0x48: mov     x0, x21
      +0x4c: str     x30, [sp, #80]
      +0x50: add     x26, x19, #0x840
      +0x54: add     x27, x19, #0x580
      +0x58: add     x28, x19, #0x2c0
      +0x5c: ldp     q0, q1, [x4, #32]
      +0x60: add     x4, x19, #0xc20
      +0x64: ldp     q2, q3, [x8]
      +0x68: mov     x8, x9
      +0x6c: ldr     x9, [x8]
      +0x70: str     x9, [sp, #4152]
      +0x74: mov     x9, #0x0
      +0x78: ldrh    w8, [sp, #4160]
      +0x7c: stp     q0, q1, [x20, #32]
      +0x80: stp     q0, q1, [x22, #32]
      +0x84: stp     x2, x3, [sp, #104]
      +0x88: stp     q2, q3, [x20]
      +0x8c: stp     q2, q3, [x22]
      +0x90: stp     q2, q3, [x23]
      +0x94: stp     q0, q1, [x23, #32]
      +0x98: stp     q2, q3, [x4]
      +0x9c: stp     q0, q1, [x4, #32]
      +0xa0: str     x4, [sp, #120]
      +0xa4: strh    w5, [x19, #2880]
      +0xa8: strh    w6, [x19, #2976]
      +0xac: strh    w7, [x19, #3072]
      +0xb0: strh    w8, [x19, #3168]
      +0xb4: bl      <mldsa_shake256x4_init>
      +0xb8: ldr     x4, [sp, #120]
      +0xbc: mov     x3, x23
      +0xc0: mov     x2, x22
      +0xc4: mov     x1, x20
      +0xc8: mov     x0, x21
      +0xcc: mov     x5, #0x42
      +0xd0: bl      <mldsa_shake256x4_absorb_once>
      +0xd4: mov     x3, x26
      +0xd8: mov     x2, x27
      +0xdc: mov     x5, x21
      +0xe0: mov     x4, #0x5
      +0xe4: mov     x1, x28
      +0xe8: mov     x0, x19
      +0xec: bl      <mldsa_shake256x4_squeezeblocks>
      +0xf0: mov     x1, x19
      +0xf4: mov     x0, x25
      +0xf8: bl      <mldsa65_polyz_unpack>
      +0xfc: mov     x1, x28
     +0x100: mov     x0, x24
     +0x104: bl      <mldsa65_polyz_unpack>
     +0x108: ldr     x0, [sp, #104]
     +0x10c: mov     x1, x27
     +0x110: bl      <mldsa65_polyz_unpack>
     +0x114: ldr     x0, [sp, #112]
     +0x118: mov     x1, x26
     +0x11c: bl      <mldsa65_polyz_unpack>
     +0x120: mov     x0, x21
     +0x124: bl      <mldsa_shake256x4_release>
     +0x128: mov     x0, x19
     +0x12c: mov     x2, #0xb00
     +0x130: mov     w1, #0x0
     +0x134: bl      <memset@plt>
     +0x138: mov     x2, #0x180
     +0x13c: mov     x0, x20
     +0x140: mov     w1, #0x0
     +0x144: bl      <memset@plt>
     +0x148: adrp    x0, <page>
     +0x14c: ldr     x0, [x0, #4088]
     +0x150: ldr     x2, [sp, #4152]
     +0x154: ldr     x1, [x0]
     +0x158: subs    x2, x2, x1
     +0x15c: mov     x1, #0x0
     +0x160: b.ne    <mldsa65_poly_uniform_gamma1_4x+0x188>
     +0x164: ldp     x19, x20, [sp]
     +0x168: mov     x12, #0x1040
     +0x16c: ldp     x21, x22, [sp, #16]
     +0x170: ldp     x23, x24, [sp, #32]
     +0x174: ldp     x25, x26, [sp, #48]
     +0x178: ldp     x27, x28, [sp, #64]
     +0x17c: ldr     x30, [sp, #80]
     +0x180: add     sp, sp, x12
     +0x184: ret
     +0x188: bl      <__stack_chk_fail@plt>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_poly_uniform_gamma1_4x"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The seed is the 64 bytes   *)
(* sd at seed, and polynomial j becomes mld_poly_uniform_gamma1_19 sd of the *)
(* nonce j. The stack is the 4160 bytes of the function and the 304 below    *)
(* them of mldsa_shake256x4_absorb_once, and the fourth nonce is the 16 bits *)
(* at the stack pointer.                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
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
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_poly_uniform_gamma1_4x) /\
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
                             mld_poly_uniform_gamma1_19 sd (word_zx n0) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                               s =
                             mld_poly_uniform_gamma1_19 sd (word_zx n1) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                               s =
                             mld_poly_uniform_gamma1_19 sd (word_zx n2) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                               s =
                             mld_poly_uniform_gamma1_19 sd n3 i))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                  memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                  memory :> bytes(word_sub stackpointer (word 4464),4464)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the address of memset and the     *)
(* stack, with all accesses within the arguments, the stack, the GOT entries *)
(* and the stack guard, the region (ea,el) that memset may read and the      *)
(* round constants of Keccak, and the writes within the polynomials and the  *)
(* stack; and constant time and memory safety alone.                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
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
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_poly_uniform_gamma1_4x) /\
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
                             mld_poly_uniform_gamma1_19 sd (word_zx n0) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                               s =
                             mld_poly_uniform_gamma1_19 sd (word_zx n1) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                               s =
                             mld_poly_uniform_gamma1_19 sd (word_zx n2) i) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                               s =
                             mld_poly_uniform_gamma1_19 sd n3 i) /\
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

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
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
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_poly_uniform_gamma1_4x) /\
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

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
