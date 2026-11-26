(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The challenge polynomial (SampleInBall): the statement. This is the code  *)
(* for mldsa44_poly_challenge (mld_poly_challenge in poly_kl.c, for ML-      *)
(* DSA-44) from mldsa-native's portable C implementation compiled by clang   *)
(* 23 with -O3 as a monolithic build with MLD_CONFIG_REDUCE_RAM (see         *)
(* mldsa_native/README.md). Clang inlined the SHAKE256 functions: the        *)
(* function aligns its frame to 32 bytes (the stack pointer of the caller is *)
(* a multiple of 16 only), zeroes a Keccak state on its stack, XORs the seed *)
(* of 32 bytes and the padding into it with straight-line vector code, calls *)
(* mldsa_keccakf1600_permute, and copies the first block of 136 bytes of the *)
(* state to a buffer. It loads the sign bits from the first 8 bytes of the   *)
(* buffer into a register, zeroes the polynomial with memset, and then for i *)
(* from 256 - 39 to 255 reads bytes j of the buffer from position 8 on,      *)
(* calling mldsa_keccakf1600_permute and copying the next block when the     *)
(* buffer is used up, until j <= i, and sets c[i] = c[j] and c[j] = 1 or -1  *)
(* by the next sign bit, before it zeroes the state, the buffer and the      *)
(* signs. It is verified in the whole image (see libmldsa.ml) against        *)
(* mld_poly_challenge 39 32 of common/mldsa_native_challenge.ml, using the   *)
(* theorem for mldsa_keccakf1600_permute and the contract                    *)
(* memset_full_contract of utils/mlkem_native_libc_full.ml for memset, and   *)
(* assuming mld_poly_challenge_terminates 39 32, that the SHAKE256 output of *)
(* the seed has 39 acceptable bytes after its first 8, without which the     *)
(* code does not terminate. It is also shown to be constant time and memory  *)
(* safe, with the events depending on the seed, which is public (c~ is       *)
(* declassified when signing and is part of the signature).                  *)
(*                                                                           *)
(* The stack is the 768 bytes below the stack pointer of the caller: the 80  *)
(* bytes of saved registers, the frame of 400 bytes (the realignment of the  *)
(* stack pointer costs up to 16 more) and 240 bytes of                       *)
(* mldsa_keccakf1600_permute. The events depend on whether the stack pointer *)
(* is a multiple of 32, as the frame is aligned by rounding down.            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_challenge.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa44_poly_challenge:
       +0x0: stp     x29, x30, [sp, #-80]!
       +0x4: stp     x28, x25, [sp, #16]
       +0x8: stp     x24, x23, [sp, #32]
       +0xc: stp     x22, x21, [sp, #48]
      +0x10: stp     x20, x19, [sp, #64]
      +0x14: mov     x29, sp
      +0x18: sub     x9, sp, #0x190
      +0x1c: and     sp, x9, #0xffffffffffffffe0
      +0x20: adrp    x8, <page>
      +0x24: movi    v0.2d, #0x0
      +0x28: add     x20, sp, #0x10
      +0x2c: ldr     x8, [x8, #4088]
      +0x30: mov     x19, x0
      +0x34: mov     w21, #0x88
      +0x38: add     x0, sp, #0x10
      +0x3c: ldr     x8, [x8]
      +0x40: str     x8, [sp, #376]
      +0x44: stur    q0, [sp, #40]
      +0x48: ldrb    w8, [x1, #25]
      +0x4c: ldr     b1, [x1, #24]
      +0x50: stur    q0, [x20, #184]
      +0x54: ldr     s2, [x1, #28]
      +0x58: stur    q0, [x20, #168]
      +0x5c: stur    q0, [x20, #152]
      +0x60: zip1    v2.8b, v2.8b, v2.8b
      +0x64: stur    q0, [x20, #136]
      +0x68: stur    q0, [x20, #120]
      +0x6c: ldrb    w9, [sp, #41]
      +0x70: ldr     s3, [sp, #44]
      +0x74: stur    q0, [sp, #120]
      +0x78: stur    q0, [sp, #104]
      +0x7c: eor     w8, w9, w8
      +0x80: ldrb    w9, [sp, #42]
      +0x84: zip1    v3.8b, v3.8b, v3.8b
      +0x88: mov     v1.b[1], w8
      +0x8c: ldrb    w8, [x1, #26]
      +0x90: stur    q0, [sp, #88]
      +0x94: stur    q0, [sp, #72]
      +0x98: eor     w8, w9, w8
      +0x9c: ldrb    w9, [x1, #27]
      +0xa0: stur    q0, [sp, #56]
      +0xa4: eor     v2.8b, v3.8b, v2.8b
      +0xa8: ldr     d3, [x1, #16]
      +0xac: str     wzr, [sp, #216]
      +0xb0: mov     v1.b[2], w8
      +0xb4: ldrb    w8, [sp, #43]
      +0xb8: str     w21, [sp, #216]
      +0xbc: eor     w8, w8, w9
      +0xc0: ldrb    w9, [sp, #151]
      +0xc4: mov     v1.b[3], w8
      +0xc8: ldrb    w8, [sp, #48]
      +0xcc: eor     w9, w9, #0x80
      +0xd0: strb    w9, [sp, #151]
      +0xd4: eor     w8, w8, #0x1f
      +0xd8: strb    w8, [sp, #48]
      +0xdc: mov     v3.d[1], v1.d[0]
      +0xe0: uzp1    v1.8b, v2.8b, v0.8b
      +0xe4: ldr     q0, [x1]
      +0xe8: mov     v3.s[3], v1.s[0]
      +0xec: stp     q0, q3, [sp, #16]
      +0xf0: bl      <mldsa_keccakf1600_permute>
      +0xf4: ldp     q0, q1, [sp, #80]
      +0xf8: mov     x0, x19
      +0xfc: ldr     x8, [sp, #144]
     +0x100: mov     w1, wzr
     +0x104: mov     w2, #0x400
     +0x108: str     w21, [sp, #216]
     +0x10c: stp     q0, q1, [x20, #272]
     +0x110: ldp     q2, q0, [sp, #112]
     +0x114: str     x8, [sp, #352]
     +0x118: stp     q2, q0, [x20, #304]
     +0x11c: ldp     q1, q0, [sp, #16]
     +0x120: stp     q1, q0, [x20, #208]
     +0x124: ldp     q2, q0, [sp, #48]
     +0x128: ldr     x22, [sp, #224]
     +0x12c: stp     q2, q0, [x20, #240]
     +0x130: bl      <memset>
     +0x134: mov     w8, #0x8
     +0x138: mov     w23, #0xd9
     +0x13c: add     x24, sp, #0xe0
     +0x140: mov     w25, #0x1
     +0x144: b       <mldsa44_poly_challenge+0x158>
     +0x148: ldrb    w9, [x24, x8]
     +0x14c: add     x8, x8, #0x1
     +0x150: cmp     w9, w23, uxtb
     +0x154: b.ls    <mldsa44_poly_challenge+0x19c>
     +0x158: cmp     x8, #0x88
     +0x15c: b.cc    <mldsa44_poly_challenge+0x148>
     +0x160: add     x0, sp, #0x10
     +0x164: bl      <mldsa_keccakf1600_permute>
     +0x168: ldp     q0, q1, [sp, #80]
     +0x16c: mov     x8, xzr
     +0x170: ldr     x9, [sp, #144]
     +0x174: str     w21, [sp, #216]
     +0x178: stp     q0, q1, [x20, #272]
     +0x17c: ldp     q2, q0, [sp, #112]
     +0x180: str     x9, [sp, #352]
     +0x184: stp     q2, q0, [x20, #304]
     +0x188: ldp     q1, q0, [sp, #16]
     +0x18c: stp     q1, q0, [x20, #208]
     +0x190: ldp     q2, q0, [sp, #48]
     +0x194: stp     q2, q0, [x20, #240]
     +0x198: b       <mldsa44_poly_challenge+0x148>
     +0x19c: ldr     w10, [x19, w9, uxtw #2]
     +0x1a0: str     w10, [x19, x23, lsl #2]
     +0x1a4: ubfiz   w10, w22, #1, #1
     +0x1a8: add     x23, x23, #0x1
     +0x1ac: lsr     x22, x22, #1
     +0x1b0: cmp     x23, #0x100
     +0x1b4: sub     w10, w25, w10
     +0x1b8: str     w10, [x19, w9, uxtw #2]
     +0x1bc: b.ne    <mldsa44_poly_challenge+0x158>
     +0x1c0: movi    v0.2d, #0x0
     +0x1c4: str     x22, [sp, #8]
     +0x1c8: add     x8, sp, #0x10
     +0x1cc: stp     q0, q0, [sp, #16]
     +0x1d0: stp     q0, q0, [sp, #48]
     +0x1d4: stp     q0, q0, [sp, #80]
     +0x1d8: stp     q0, q0, [sp, #112]
     +0x1dc: stp     q0, q0, [x20, #128]
     +0x1e0: stp     q0, q0, [x20, #160]
     +0x1e4: str     q0, [x20, #192]
     +0x1e8: str     xzr, [sp, #352]
     +0x1ec: add     x8, sp, #0xe0
     +0x1f0: stp     q0, q0, [x20, #208]
     +0x1f4: stp     q0, q0, [x20, #240]
     +0x1f8: stp     q0, q0, [x20, #272]
     +0x1fc: stp     q0, q0, [x20, #304]
     +0x200: add     x8, sp, #0x8
     +0x204: str     xzr, [sp, #8]
     +0x208: adrp    x8, <page>
     +0x20c: ldr     x8, [x8, #4088]
     +0x210: ldr     x9, [sp, #376]
     +0x214: ldr     x8, [x8]
     +0x218: cmp     x8, x9
     +0x21c: b.ne    <mldsa44_poly_challenge+0x254>
     +0x220: mov     sp, x29
     +0x224: ldp     x20, x19, [sp, #64]
     +0x228: ldp     x22, x21, [sp, #48]
     +0x22c: ldp     x24, x23, [sp, #32]
     +0x230: ldp     x28, x25, [sp, #16]
     +0x234: ldp     x29, x30, [sp], #80
     +0x238: mov     x0, #0x0
     +0x23c: mov     x1, #0x0
     +0x240: mov     x2, #0x0
     +0x244: mov     x8, #0x0
     +0x248: mov     x9, #0x0
     +0x24c: mov     x10, #0x0
     +0x250: ret     
     +0x254: bl      <__stack_chk_fail>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa44_poly_challenge";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The seed is the 32 bytes C *)
(* at seed, and the polynomial at c becomes mld_poly_challenge 39 32 C, if   *)
(* mld_poly_challenge_terminates 39 32 C. The seed may overlap the           *)
(* polynomial, as it is only read before the polynomial is written. The      *)
(* stack is the 768 bytes below the stack pointer, see above; the address of *)
(* the stack guard is read from the GOT.                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !c seed C guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_poly_challenge_terminates 39 32 C /\
          nonoverlapping (c,1024) (word_sub stackpointer (word 768),768) /\
          nonoverlapping (seed,32) (word_sub stackpointer (word 768),768) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 768),768)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_poly_challenge) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                         s = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,32)) s = C)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add c (word(4 * i))))
                               s =
                             mld_poly_challenge 39 32 C i))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 768),768)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the seed C, the address of memset *)
(* and the stack, with all accesses within the seed, the polynomial, the     *)
(* stack, the GOT entries and the stack guard, the region (ea,el) that       *)
(* memset may read and the round constants of Keccak, and the writes within  *)
(* the polynomial and the stack.                                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e c seed C guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_poly_challenge_terminates 39 32 C /\
          nonoverlapping (c,1024) (word_sub stackpointer (word 768),768) /\
          nonoverlapping (seed,32) (word_sub stackpointer (word 768),768) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 768),768)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_poly_challenge) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                         s = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,32)) s = C /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add c (word(4 * i))))
                               s =
                             mld_poly_challenge 39 32 C i) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events c seed C guard mf pc
                              (word_sub stackpointer (word 768))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; c,1024;
                         word_sub stackpointer (word 768),768;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [c,1024; word_sub stackpointer (word 768),768]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 768),768)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone: the same events, which depend on   *)
(* the seed C, and the same accesses.                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e c seed C guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_poly_challenge_terminates 39 32 C /\
          nonoverlapping (c,1024) (word_sub stackpointer (word 768),768) /\
          nonoverlapping (seed,32) (word_sub stackpointer (word 768),768) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 768),768)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa44_poly_challenge) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                         s = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,32)) s = C /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events c seed C guard mf pc
                              (word_sub stackpointer (word 768))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; c,1024;
                         word_sub stackpointer (word 768),768;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [c,1024; word_sub stackpointer (word 768),768]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 768),768)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
