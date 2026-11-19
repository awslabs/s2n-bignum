(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of four polynomials mod q from four seeds by rejection:  *)
(* the statement. This is the code for mldsa_poly_uniform_4x                 *)
(* (mld_poly_uniform_4x in poly.c) from mldsa-native's portable C            *)
(* implementation compiled by gcc 12 with -Os (see mldsa_native/README.md),  *)
(* which absorbs the four seeds of 34 bytes, 64 bytes apart, into a fourfold *)
(* SHAKE128 state, squeezes 5 blocks of 168 bytes of each and samples the    *)
(* coefficients below q from them with mld_rej_uniform_c, and then squeezes  *)
(* one more block of each and samples from all four until each polynomial    *)
(* has 256 coefficients, before zeroing the state and the buffers. It is     *)
(* verified in the whole image (see libmldsa.ml) against mld_poly_uniform of *)
(* common/mldsa_native_sampling.ml, using the theorems for the callees and   *)
(* the contract memset_full_contract of utils/mlkem_native_libc_full.ml for  *)
(* memset, and assuming that the SHAKE128 output of each seed has 256        *)
(* acceptable groups of 3 bytes (mld_rej_uniform_terminates), without which  *)
(* the code does not terminate. It is also shown to be constant time and     *)
(* memory safe, with the events depending on the seeds, which are public     *)
(* (rho and the indices of the matrix entries).                              *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake128x4_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake128x4_absorb_once_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake128x4_squeezeblocks_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake128x4_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/rej_uniform_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa_poly_uniform_4x:
       +0x0: mov     x12, #0x1140
       +0x4: sub     sp, sp, x12
       +0x8: stp     x0, x1, [sp, #104]
       +0xc: adrp    x0, <page>
      +0x10: ldr     x0, [x0, #4088]
      +0x14: stp     x19, x20, [sp]
      +0x18: add     x19, sp, #0x9f
      +0x1c: stp     x21, x22, [sp, #16]
      +0x20: mov     x20, x4
      +0x24: and     x19, x19, #0xffffffffffffffe0
      +0x28: stp     x23, x24, [sp, #32]
      +0x2c: add     x23, sp, #0xe18
      +0x30: mov     x24, x2
      +0x34: stp     x25, x26, [sp, #48]
      +0x38: mov     x25, x3
      +0x3c: add     x26, x19, #0xa20
      +0x40: stp     x27, x28, [sp, #64]
      +0x44: add     x27, x19, #0x6c0
      +0x48: add     x28, x19, #0x360
      +0x4c: str     x30, [sp, #80]
      +0x50: ldr     x1, [x0]
      +0x54: str     x1, [sp, #4408]
      +0x58: mov     x1, #0x0
      +0x5c: mov     x0, x23
      +0x60: bl      <mldsa_shake128x4_init>
      +0x64: add     x4, x20, #0xc0
      +0x68: add     x3, x20, #0x80
      +0x6c: add     x2, x20, #0x40
      +0x70: mov     x1, x20
      +0x74: mov     x0, x23
      +0x78: mov     x5, #0x22
      +0x7c: bl      <mldsa_shake128x4_absorb_once>
      +0x80: mov     x5, x23
      +0x84: mov     x4, #0x5
      +0x88: mov     x3, x26
      +0x8c: mov     x2, x27
      +0x90: mov     x1, x28
      +0x94: mov     x0, x19
      +0x98: bl      <mldsa_shake128x4_squeezeblocks>
      +0x9c: ldr     x0, [sp, #104]
      +0xa0: mov     w3, #0x348
      +0xa4: mov     x2, x19
      +0xa8: mov     w1, #0x0
      +0xac: bl      <mld_rej_uniform_c>
      +0xb0: mov     w21, w0
      +0xb4: ldr     x0, [sp, #112]
      +0xb8: mov     x2, x28
      +0xbc: mov     w1, #0x0
      +0xc0: bl      <mld_rej_uniform_c>
      +0xc4: mov     w22, w0
      +0xc8: mov     x2, x27
      +0xcc: mov     w1, #0x0
      +0xd0: mov     x0, x24
      +0xd4: bl      <mld_rej_uniform_c>
      +0xd8: mov     x2, x26
      +0xdc: mov     w20, w0
      +0xe0: mov     w1, #0x0
      +0xe4: mov     x0, x25
      +0xe8: bl      <mld_rej_uniform_c>
      +0xec: mov     w6, w0
      +0xf0: cmp     w21, #0xff
      +0xf4: b.ls    <mldsa_poly_uniform_4x+0x148>
      +0xf8: cmp     w22, #0xff
      +0xfc: b.ls    <mldsa_poly_uniform_4x+0x148>
     +0x100: cmp     w20, #0xff
     +0x104: b.ls    <mldsa_poly_uniform_4x+0x148>
     +0x108: cmp     w0, #0xff
     +0x10c: b.ls    <mldsa_poly_uniform_4x+0x148>
     +0x110: mov     x0, x23
     +0x114: bl      <mldsa_shake128x4_release>
     +0x118: mov     x0, x19
     +0x11c: mov     x2, #0xd80
     +0x120: mov     w1, #0x0
     +0x124: bl      <memset>
     +0x128: adrp    x0, <page>
     +0x12c: ldr     x0, [x0, #4088]
     +0x130: ldr     x2, [sp, #4408]
     +0x134: ldr     x1, [x0]
     +0x138: subs    x2, x2, x1
     +0x13c: mov     x1, #0x0
     +0x140: b.eq    <mldsa_poly_uniform_4x+0x1b8>
     +0x144: bl      <stack_chk_fail>
     +0x148: mov     x5, x23
     +0x14c: mov     x4, #0x1
     +0x150: mov     x3, x26
     +0x154: mov     x2, x27
     +0x158: mov     x1, x28
     +0x15c: mov     x0, x19
     +0x160: str     w6, [sp, #124]
     +0x164: bl      <mldsa_shake128x4_squeezeblocks>
     +0x168: ldr     x0, [sp, #104]
     +0x16c: mov     w1, w21
     +0x170: mov     w3, #0xa8
     +0x174: mov     x2, x19
     +0x178: bl      <mld_rej_uniform_c>
     +0x17c: mov     w21, w0
     +0x180: ldr     x0, [sp, #112]
     +0x184: mov     w1, w22
     +0x188: mov     x2, x28
     +0x18c: bl      <mld_rej_uniform_c>
     +0x190: mov     w22, w0
     +0x194: mov     w1, w20
     +0x198: mov     x2, x27
     +0x19c: mov     x0, x24
     +0x1a0: bl      <mld_rej_uniform_c>
     +0x1a4: ldr     w6, [sp, #124]
     +0x1a8: mov     w20, w0
     +0x1ac: mov     x2, x26
     +0x1b0: mov     w1, w6
     +0x1b4: b       <mldsa_poly_uniform_4x+0xe4>
     +0x1b8: ldp     x19, x20, [sp]
     +0x1bc: mov     x12, #0x1140
     +0x1c0: ldp     x21, x22, [sp, #16]
     +0x1c4: ldp     x23, x24, [sp, #32]
     +0x1c8: ldp     x25, x26, [sp, #48]
     +0x1cc: ldp     x27, x28, [sp, #64]
     +0x1d0: ldr     x30, [sp, #80]
     +0x1d4: add     sp, sp, x12
     +0x1d8: ret

    plt_memset:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa_poly_uniform_4x"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The seeds are the 34 bytes *)
(* M0, ..., M3 at seed, seed + 64, seed + 128 and seed + 192, and polynomial *)
(* j becomes mld_poly_uniform Mj, if the SHAKE128 output of each seed has    *)
(* 256 acceptable groups. The stack is the 4416 bytes of the function and    *)
(* the 336 below them of mldsa_shake128x4_absorb_once.                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !vec0 vec1 vec2 vec3 seed M0 M1 M2 M3 guard pc stackpointer
          returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M0) /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M1) /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M2) /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M3) /\
          PAIRWISE nonoverlapping
           [(vec0,1024); (vec1,1024); (vec2,1024); (vec3,1024);
            (word_sub stackpointer (word 4752),4752)] /\
          ALLPAIRS nonoverlapping
           [(vec0,1024); (vec1,1024); (vec2,1024); (vec3,1024);
            (word_sub stackpointer (word 4752),4752)]
           [(seed,34); (word_add seed (word 64),34);
            (word_add seed (word 128),34); (word_add seed (word 192),34);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa_poly_uniform_4x) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [vec0; vec1; vec2; vec3; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,34)) s = M0 /\
                    read (memory :> bytes(word_add seed (word 64),34)) s = M1 /\
                    read (memory :> bytes(word_add seed (word 128),34)) s =
                    M2 /\
                    read (memory :> bytes(word_add seed (word 192),34)) s =
                    M3)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :>
                                  bytes32(word_add vec0 (word(4 * i)))) s =
                             mld_poly_uniform M0 i) /\
                    (!i. i < 256
                         ==> read(memory :>
                                  bytes32(word_add vec1 (word(4 * i)))) s =
                             mld_poly_uniform M1 i) /\
                    (!i. i < 256
                         ==> read(memory :>
                                  bytes32(word_add vec2 (word(4 * i)))) s =
                             mld_poly_uniform M2 i) /\
                    (!i. i < 256
                         ==> read(memory :>
                                  bytes32(word_add vec3 (word(4 * i)))) s =
                             mld_poly_uniform M3 i))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(vec0,1024); memory :> bytes(vec1,1024);
                  memory :> bytes(vec2,1024); memory :> bytes(vec3,1024);
                  memory :> bytes(word_sub stackpointer (word 4752),4752)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the seeds, the address of memset  *)
(* and the stack, with all accesses within the arguments, the stack, the GOT *)
(* entries and the stack guard, the region (ea,el) that memset may read and  *)
(* the round constants of Keccak, and the writes within the polynomials and  *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e vec0 vec1 vec2 vec3 seed M0 M1 M2 M3 guard pc stackpointer
                 returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M0) /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M1) /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M2) /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M3) /\
          PAIRWISE nonoverlapping
           [(vec0,1024); (vec1,1024); (vec2,1024); (vec3,1024);
            (word_sub stackpointer (word 4752),4752)] /\
          ALLPAIRS nonoverlapping
           [(vec0,1024); (vec1,1024); (vec2,1024); (vec3,1024);
            (word_sub stackpointer (word 4752),4752)]
           [(seed,34); (word_add seed (word 64),34);
            (word_add seed (word 128),34); (word_add seed (word 192),34);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa_poly_uniform_4x) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [vec0; vec1; vec2; vec3; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,34)) s = M0 /\
                    read (memory :> bytes(word_add seed (word 64),34)) s = M1 /\
                    read (memory :> bytes(word_add seed (word 128),34)) s =
                    M2 /\
                    read (memory :> bytes(word_add seed (word 192),34)) s =
                    M3 /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :>
                                  bytes32(word_add vec0 (word(4 * i)))) s =
                             mld_poly_uniform M0 i) /\
                    (!i. i < 256
                         ==> read(memory :>
                                  bytes32(word_add vec1 (word(4 * i)))) s =
                             mld_poly_uniform M1 i) /\
                    (!i. i < 256
                         ==> read(memory :>
                                  bytes32(word_add vec2 (word(4 * i)))) s =
                             mld_poly_uniform M2 i) /\
                    (!i. i < 256
                         ==> read(memory :>
                                  bytes32(word_add vec3 (word(4 * i)))) s =
                             mld_poly_uniform M3 i) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events vec0 vec1 vec2 vec3 seed M0 M1 M2 M3 guard
                              mf pc (word_sub stackpointer (word 4752))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,34; word_add seed (word 64),34;
                         word_add seed (word 128),34;
                         word_add seed (word 192),34;
                         vec0,1024; vec1,1024; vec2,1024; vec3,1024;
                         word_sub stackpointer (word 4752),4752;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [vec0,1024; vec1,1024; vec2,1024; vec3,1024;
                         word_sub stackpointer (word 4752),4752]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(vec0,1024); memory :> bytes(vec1,1024);
                  memory :> bytes(vec2,1024); memory :> bytes(vec3,1024);
                  memory :> bytes(word_sub stackpointer (word 4752),4752)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* seeds as above.                                                           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e vec0 vec1 vec2 vec3 seed M0 M1 M2 M3 guard pc stackpointer
                 returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M0) /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M1) /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M2) /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M3) /\
          PAIRWISE nonoverlapping
           [(vec0,1024); (vec1,1024); (vec2,1024); (vec3,1024);
            (word_sub stackpointer (word 4752),4752)] /\
          ALLPAIRS nonoverlapping
           [(vec0,1024); (vec1,1024); (vec2,1024); (vec3,1024);
            (word_sub stackpointer (word 4752),4752)]
           [(seed,34); (word_add seed (word 64),34);
            (word_add seed (word 128),34); (word_add seed (word 192),34);
            (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa_poly_uniform_4x) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [vec0; vec1; vec2; vec3; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,34)) s = M0 /\
                    read (memory :> bytes(word_add seed (word 64),34)) s = M1 /\
                    read (memory :> bytes(word_add seed (word 128),34)) s =
                    M2 /\
                    read (memory :> bytes(word_add seed (word 192),34)) s =
                    M3 /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events vec0 vec1 vec2 vec3 seed M0 M1 M2 M3 guard
                              mf pc (word_sub stackpointer (word 4752))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,34; word_add seed (word 64),34;
                         word_add seed (word 128),34;
                         word_add seed (word 192),34;
                         vec0,1024; vec1,1024; vec2,1024; vec3,1024;
                         word_sub stackpointer (word 4752),4752;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [vec0,1024; vec1,1024; vec2,1024; vec3,1024;
                         word_sub stackpointer (word 4752),4752]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(vec0,1024); memory :> bytes(vec1,1024);
                  memory :> bytes(vec2,1024); memory :> bytes(vec3,1024);
                  memory :> bytes(word_sub stackpointer (word 4752),4752)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
