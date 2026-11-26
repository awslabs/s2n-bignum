(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of a polynomial mod q from a seed by rejection: the      *)
(* statement. This is the code for mldsa_poly_uniform (mld_poly_uniform in   *)
(* poly.c) from mldsa-native's portable C implementation compiled by clang   *)
(* 23 with -O3 as a monolithic build with MLD_CONFIG_REDUCE_RAM (see         *)
(* mldsa_native/README.md). Clang inlined the SHAKE128 functions and the    *)
(* rejection sampling loop: the function zeroes a Keccak state on its stack *)
(* (the buffer is aligned to 32 bytes with an and of the stack pointer),    *)
(* XORs the seed of 34 bytes and the padding into it, copies the 840 bytes  *)
(* of the                                                                    *)
(* first 5 blocks of 168 bytes with a loop of memcpy and mldsa_keccakf1600_  *)
(* permute, samples the coefficients below q from them, and then, until the  *)
(* polynomial has 256 coefficients, copies one block of 168 bytes at a time  *)
(* and samples from it, before zeroing the state and the buffer with memset. *)
(* It is verified in the whole image (see libmldsa.ml) against               *)
(* mld_poly_uniform of common/mldsa_native_sampling.ml, using the theorem    *)
(* for mldsa_keccakf1600_permute and the contracts memset_full_contract and  *)
(* memcpy_full_contract of utils/mldsa_native_libc.ml, and assuming that the *)
(* SHAKE128 output of the seed has 256 acceptable groups of 3 bytes          *)
(* (mld_rej_uniform_terminates), without which the code does not terminate.  *)
(* It is also shown to be constant time and memory safe, with the events     *)
(* depending on the seed, which is public (rho and the indices of the matrix *)
(* entry).                                                                   *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_uniform:
       +0x0: stp     x29, x30, [sp, #-96]!
       +0x4: stp     x28, x27, [sp, #16]
       +0x8: stp     x26, x25, [sp, #32]
       +0xc: stp     x24, x23, [sp, #48]
      +0x10: stp     x22, x21, [sp, #64]
      +0x14: stp     x20, x19, [sp, #80]
      +0x18: mov     x29, sp
      +0x1c: sub     x9, sp, #0x440
      +0x20: and     sp, x9, #0xffffffffffffffe0
      +0x24: adrp    x8, <page>
      +0x28: ldr     xzr, [sp]
      +0x2c: movi    v0.2d, #0x0
      +0x30: ldr     x8, [x8, #4088]
      +0x34: add     x24, sp, #0x10
      +0x38: mov     x19, x0
      +0x3c: mov     x23, xzr
      +0x40: mov     w25, #0xa8
      +0x44: mov     w26, #0x348
      +0x48: ldr     x8, [x8]
      +0x4c: add     x27, sp, #0xe0
      +0x50: mov     w22, #0xa8
      +0x54: str     x8, [sp, #1080]
      +0x58: stur    q0, [sp, #40]
      +0x5c: ldrb    w8, [x1, #25]
      +0x60: ldr     b1, [x1, #24]
      +0x64: stur    q0, [x24, #184]
      +0x68: ldr     s2, [x1, #28]
      +0x6c: ldr     d4, [x1, #16]
      +0x70: stur    q0, [x24, #168]
      +0x74: ldrb    w10, [x1, #33]
      +0x78: stur    q0, [x24, #152]
      +0x7c: zip1    v2.8b, v2.8b, v2.8b
      +0x80: stur    q0, [x24, #136]
      +0x84: ldrb    w9, [sp, #41]
      +0x88: ldr     s3, [sp, #44]
      +0x8c: ldrb    w11, [sp, #49]
      +0x90: stur    q0, [sp, #136]
      +0x94: eor     w8, w9, w8
      +0x98: ldrb    w9, [sp, #42]
      +0x9c: zip1    v3.8b, v3.8b, v3.8b
      +0xa0: mov     v1.b[1], w8
      +0xa4: ldrb    w8, [x1, #26]
      +0xa8: stur    q0, [sp, #120]
      +0xac: stur    q0, [sp, #104]
      +0xb0: eor     w8, w9, w8
      +0xb4: ldrb    w9, [x1, #27]
      +0xb8: stur    q0, [sp, #88]
      +0xbc: eor     v2.8b, v3.8b, v2.8b
      +0xc0: stur    q0, [sp, #72]
      +0xc4: mov     v1.b[2], w8
      +0xc8: ldrb    w8, [sp, #43]
      +0xcc: stur    q0, [sp, #56]
      +0xd0: str     wzr, [sp, #216]
      +0xd4: eor     w8, w8, w9
      +0xd8: ldrb    w9, [sp, #48]
      +0xdc: str     w25, [sp, #216]
      +0xe0: mov     v1.b[3], w8
      +0xe4: ldrb    w8, [x1, #32]
      +0xe8: eor     w8, w9, w8
      +0xec: eor     w9, w11, w10
      +0xf0: strb    w8, [sp, #48]
      +0xf4: ldrb    w8, [sp, #50]
      +0xf8: mov     v4.d[1], v1.d[0]
      +0xfc: uzp1    v1.8b, v2.8b, v0.8b
     +0x100: strb    w9, [sp, #49]
     +0x104: ldrb    w9, [sp, #183]
     +0x108: ldr     q0, [x1]
     +0x10c: eor     w8, w8, #0x1f
     +0x110: strb    w8, [sp, #50]
     +0x114: eor     w9, w9, #0x80
     +0x118: mov     v4.s[3], v1.s[0]
     +0x11c: strb    w9, [sp, #183]
     +0x120: stp     q0, q4, [sp, #16]
     +0x124: b       <mldsa_poly_uniform+0x158>
     +0x128: sub     w8, w25, w22
     +0x12c: add     x21, x24, w22, uxtw
     +0x130: cmp     x26, x8
     +0x134: csel    x20, x26, x8, cc
     +0x138: add     x0, x27, x23
     +0x13c: mov     x1, x21
     +0x140: mov     x2, x20
     +0x144: bl      <memcpy>
     +0x148: subs    x26, x26, x20
     +0x14c: add     w22, w22, w20
     +0x150: add     x23, x20, x23
     +0x154: b.eq    <mldsa_poly_uniform+0x17c>
     +0x158: cmp     w22, #0xa8
     +0x15c: b.ne    <mldsa_poly_uniform+0x128>
     +0x160: add     x0, sp, #0x10
     +0x164: add     x21, sp, #0x10
     +0x168: bl      <mldsa_keccakf1600_permute>
     +0x16c: cmp     x26, #0xa8
     +0x170: mov     w22, wzr
     +0x174: csel    x20, x26, x25, cc
     +0x178: b       <mldsa_poly_uniform+0x138>
     +0x17c: mov     w23, #0xe001
     +0x180: mov     x8, xzr
     +0x184: mov     x24, xzr
     +0x188: movk    w23, #0x7f, lsl #16
     +0x18c: add     x9, sp, #0xe0
     +0x190: str     w22, [sp, #216]
     +0x194: add     x11, x9, x8
     +0x198: ldrh    w10, [x11]
     +0x19c: ldrb    w11, [x11, #2]
     +0x1a0: bfi     w10, w11, #16, #7
     +0x1a4: cmp     w10, w23
     +0x1a8: b.cs    <mldsa_poly_uniform+0x1b8>
     +0x1ac: add     x11, x24, #0x1
     +0x1b0: str     w10, [x19, x24, lsl #2]
     +0x1b4: mov     x24, x11
     +0x1b8: add     x8, x8, #0x3
     +0x1bc: cmp     x8, #0x345
     +0x1c0: b.hi    <mldsa_poly_uniform+0x1cc>
     +0x1c4: cmp     x24, #0x100
     +0x1c8: b.cc    <mldsa_poly_uniform+0x194>
     +0x1cc: cmp     x24, #0xff
     +0x1d0: b.hi    <mldsa_poly_uniform+0x29c>
     +0x1d4: add     x25, sp, #0xe0
     +0x1d8: mov     w26, #0xa8
     +0x1dc: add     x27, sp, #0x10
     +0x1e0: str     x19, [sp, #8]
     +0x1e4: b       <mldsa_poly_uniform+0x1f0>
     +0x1e8: cmp     x24, #0xff
     +0x1ec: b.hi    <mldsa_poly_uniform+0x29c>
     +0x1f0: mov     x28, xzr
     +0x1f4: mov     w19, #0xa8
     +0x1f8: b       <mldsa_poly_uniform+0x22c>
     +0x1fc: sub     w8, w26, w22
     +0x200: add     x21, x27, w22, uxtw
     +0x204: cmp     x19, x8
     +0x208: csel    x20, x19, x8, cc
     +0x20c: add     x0, x25, x28
     +0x210: mov     x1, x21
     +0x214: mov     x2, x20
     +0x218: bl      <memcpy>
     +0x21c: subs    x19, x19, x20
     +0x220: add     w22, w22, w20
     +0x224: add     x28, x20, x28
     +0x228: b.eq    <mldsa_poly_uniform+0x250>
     +0x22c: cmp     w22, #0xa8
     +0x230: b.ne    <mldsa_poly_uniform+0x1fc>
     +0x234: add     x0, sp, #0x10
     +0x238: add     x21, sp, #0x10
     +0x23c: bl      <mldsa_keccakf1600_permute>
     +0x240: cmp     x19, #0xa8
     +0x244: mov     w22, wzr
     +0x248: csel    x20, x19, x26, cc
     +0x24c: b       <mldsa_poly_uniform+0x20c>
     +0x250: ldr     x19, [sp, #8]
     +0x254: orr     x8, x25, #0x2
     +0x258: mov     w9, #0x3
     +0x25c: str     w22, [sp, #216]
     +0x260: ldurh   w10, [x8, #-2]
     +0x264: ldrb    w11, [x8]
     +0x268: bfi     w10, w11, #16, #7
     +0x26c: cmp     w10, w23
     +0x270: b.cs    <mldsa_poly_uniform+0x280>
     +0x274: add     x11, x24, #0x1
     +0x278: str     w10, [x19, x24, lsl #2]
     +0x27c: mov     x24, x11
     +0x280: cmp     x9, #0xa5
     +0x284: b.hi    <mldsa_poly_uniform+0x1e8>
     +0x288: cmp     x24, #0x100
     +0x28c: add     x8, x8, #0x3
     +0x290: add     x9, x9, #0x3
     +0x294: b.cc    <mldsa_poly_uniform+0x260>
     +0x298: b       <mldsa_poly_uniform+0x1e8>
     +0x29c: movi    v0.2d, #0x0
     +0x2a0: add     x8, sp, #0x10
     +0x2a4: add     x0, sp, #0xe0
     +0x2a8: mov     w1, wzr
     +0x2ac: mov     w2, #0x348
     +0x2b0: add     x19, sp, #0xe0
     +0x2b4: stp     q0, q0, [sp, #32]
     +0x2b8: stp     q0, q0, [sp, #64]
     +0x2bc: stp     q0, q0, [sp, #96]
     +0x2c0: stp     q0, q0, [sp, #128]
     +0x2c4: stp     q0, q0, [sp, #160]
     +0x2c8: stp     q0, q0, [sp, #192]
     +0x2cc: str     q0, [sp, #16]
     +0x2d0: bl      <memset>
     +0x2d4: adrp    x8, <page>
     +0x2d8: ldr     x8, [x8, #4088]
     +0x2dc: ldr     x9, [sp, #1080]
     +0x2e0: ldr     x8, [x8]
     +0x2e4: cmp     x8, x9
     +0x2e8: b.ne    <mldsa_poly_uniform+0x328>
     +0x2ec: mov     sp, x29
     +0x2f0: ldp     x20, x19, [sp, #80]
     +0x2f4: ldp     x22, x21, [sp, #64]
     +0x2f8: ldp     x24, x23, [sp, #48]
     +0x2fc: ldp     x26, x25, [sp, #32]
     +0x300: ldp     x28, x27, [sp, #16]
     +0x304: ldp     x29, x30, [sp], #96
     +0x308: mov     x0, #0x0
     +0x30c: mov     x1, #0x0
     +0x310: mov     x2, #0x0
     +0x314: mov     x8, #0x0
     +0x318: mov     x9, #0x0
     +0x31c: mov     x10, #0x0
     +0x320: mov     x11, #0x0
     +0x324: ret     
     +0x328: bl      <__stack_chk_fail>
 ***)

let MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa_poly_uniform";
    layout_range "plt_memcpy";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contracts for memset and memcpy. The seed is    *)
(* the 34 bytes M at seed, and the polynomial at a becomes mld_poly_uniform  *)
(* M, if the SHAKE128 output of the seed has 256 acceptable groups. The      *)
(* stack is the 1472 bytes of the function (1200, with the alignment of the  *)
(* buffer) and of mldsa_keccakf1600_permute (256) below the stack pointer.   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\ memcpy_full_contract mc ea el ev
     ==> !a seed M guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M) /\
          nonoverlapping (a,1024) (word_sub stackpointer (word 1472),1472) /\
          ALLPAIRS nonoverlapping
           [(a,1024); (word_sub stackpointer (word 1472),1472)]
           [(seed,34); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa_poly_uniform) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,34)) s = M)
               (\s. read PC s = returnaddress /\
                    !i. i < 256
                        ==> read(memory :> bytes32(word_add a (word(4 * i))))
                              s = mld_poly_uniform M i)
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(a,1024);
                  memory :> bytes(word_sub stackpointer (word 1472),1472)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the seed, the address of memset   *)
(* and the stack, with all accesses within the arguments, the stack, the GOT *)
(* entries and the stack guard, the region (ea,el) that memset may read and  *)
(* the round constants of Keccak, and the writes within the polynomial and   *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e a seed M guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M) /\
          nonoverlapping (a,1024) (word_sub stackpointer (word 1472),1472) /\
          ALLPAIRS nonoverlapping
           [(a,1024); (word_sub stackpointer (word 1472),1472)]
           [(seed,34); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa_poly_uniform) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,34)) s = M /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add a (word(4 * i))))
                               s = mld_poly_uniform M i) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events a seed M guard mf mc pc
                              (word_sub stackpointer (word 1472))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,34; a,1024;
                         word_sub stackpointer (word 1472),1472;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [a,1024; word_sub stackpointer (word 1472),1472]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(a,1024);
                  memory :> bytes(word_sub stackpointer (word 1472),1472)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* seed as above.                                                            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\ memcpy_full_contract mc ea el ev
     ==> exists f_events.
          forall e a seed M guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M) /\
          nonoverlapping (a,1024) (word_sub stackpointer (word 1472),1472) /\
          ALLPAIRS nonoverlapping
           [(a,1024); (word_sub stackpointer (word 1472),1472)]
           [(seed,34); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa_poly_uniform) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,34)) s = M /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events a seed M guard mf mc pc
                              (word_sub stackpointer (word 1472))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,34; a,1024;
                         word_sub stackpointer (word 1472),1472;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [a,1024; word_sub stackpointer (word 1472),1472]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(a,1024);
                  memory :> bytes(word_sub stackpointer (word 1472),1472)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
