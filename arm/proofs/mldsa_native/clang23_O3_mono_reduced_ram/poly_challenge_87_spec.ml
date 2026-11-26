(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The challenge polynomial (SampleInBall): the statement. This is the code  *)
(* for mldsa87_poly_challenge (mld_poly_challenge in poly_kl.c, for ML-      *)
(* DSA-87) from mldsa-native's portable C implementation compiled by clang   *)
(* 23 with -O3 as a monolithic build with MLD_CONFIG_REDUCE_RAM (see         *)
(* mldsa_native/README.md). Clang inlined the SHAKE256 functions: the        *)
(* function aligns its frame to 32 bytes (the stack pointer of the caller is *)
(* a multiple of 16 only), zeroes a Keccak state on its stack, XORs the seed *)
(* of 64 bytes and the padding into it with straight-line vector code, calls *)
(* mldsa_keccakf1600_permute, and copies the first block of 136 bytes of the *)
(* state to a buffer. It loads the sign bits from the first 8 bytes of the   *)
(* buffer into a register, zeroes the polynomial with memset, and then for i *)
(* from 256 - 60 to 255 reads bytes j of the buffer from position 8 on,      *)
(* calling mldsa_keccakf1600_permute and copying the next block when the     *)
(* buffer is used up, until j <= i, and sets c[i] = c[j] and c[j] = 1 or -1  *)
(* by the next sign bit, before it zeroes the state, the buffer and the      *)
(* signs. It is verified in the whole image (see libmldsa.ml) against        *)
(* mld_poly_challenge 60 64 of common/mldsa_native_challenge.ml, using the   *)
(* theorem for mldsa_keccakf1600_permute and the contract                    *)
(* memset_full_contract of utils/mlkem_native_libc_full.ml for memset, and   *)
(* assuming mld_poly_challenge_terminates 60 64, that the SHAKE256 output of *)
(* the seed has 60 acceptable bytes after its first 8, without which the     *)
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

    mldsa87_poly_challenge:
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
      +0x44: stur    q0, [x20, #188]
      +0x48: stp     q0, q0, [x20, #128]
      +0x4c: stp     q0, q0, [x20, #160]
      +0x50: stp     q0, q0, [sp, #48]
      +0x54: ldrb    w9, [sp, #151]
      +0x58: stp     q0, q0, [sp, #80]
      +0x5c: stp     q0, q0, [sp, #112]
      +0x60: ldp     q1, q0, [x1]
      +0x64: ldrb    w8, [sp, #80]
      +0x68: str     w21, [sp, #216]
      +0x6c: stp     q1, q0, [sp, #16]
      +0x70: ldp     q2, q0, [x1, #32]
      +0x74: eor     w8, w8, #0x1f
      +0x78: strb    w8, [sp, #80]
      +0x7c: eor     w8, w9, #0x80
      +0x80: stp     q2, q0, [sp, #48]
      +0x84: strb    w8, [sp, #151]
      +0x88: bl      <mldsa_keccakf1600_permute>
      +0x8c: ldp     q0, q1, [sp, #80]
      +0x90: mov     x0, x19
      +0x94: ldr     x8, [sp, #144]
      +0x98: mov     w1, wzr
      +0x9c: mov     w2, #0x400
      +0xa0: str     w21, [sp, #216]
      +0xa4: stp     q0, q1, [x20, #272]
      +0xa8: ldp     q2, q0, [sp, #112]
      +0xac: str     x8, [sp, #352]
      +0xb0: stp     q2, q0, [x20, #304]
      +0xb4: ldp     q1, q0, [sp, #16]
      +0xb8: stp     q1, q0, [x20, #208]
      +0xbc: ldp     q2, q0, [sp, #48]
      +0xc0: ldr     x22, [sp, #224]
      +0xc4: stp     q2, q0, [x20, #240]
      +0xc8: bl      <memset>
      +0xcc: mov     w8, #0x8
      +0xd0: mov     w23, #0xc4
      +0xd4: add     x24, sp, #0xe0
      +0xd8: mov     w25, #0x1
      +0xdc: b       <mldsa87_poly_challenge+0xf0>
      +0xe0: ldrb    w9, [x24, x8]
      +0xe4: add     x8, x8, #0x1
      +0xe8: cmp     w9, w23, uxtb
      +0xec: b.ls    <mldsa87_poly_challenge+0x134>
      +0xf0: cmp     x8, #0x88
      +0xf4: b.cc    <mldsa87_poly_challenge+0xe0>
      +0xf8: add     x0, sp, #0x10
      +0xfc: bl      <mldsa_keccakf1600_permute>
     +0x100: ldp     q0, q1, [sp, #80]
     +0x104: mov     x8, xzr
     +0x108: ldr     x9, [sp, #144]
     +0x10c: str     w21, [sp, #216]
     +0x110: stp     q0, q1, [x20, #272]
     +0x114: ldp     q2, q0, [sp, #112]
     +0x118: str     x9, [sp, #352]
     +0x11c: stp     q2, q0, [x20, #304]
     +0x120: ldp     q1, q0, [sp, #16]
     +0x124: stp     q1, q0, [x20, #208]
     +0x128: ldp     q2, q0, [sp, #48]
     +0x12c: stp     q2, q0, [x20, #240]
     +0x130: b       <mldsa87_poly_challenge+0xe0>
     +0x134: ldr     w10, [x19, w9, uxtw #2]
     +0x138: str     w10, [x19, x23, lsl #2]
     +0x13c: ubfiz   w10, w22, #1, #1
     +0x140: add     x23, x23, #0x1
     +0x144: lsr     x22, x22, #1
     +0x148: cmp     x23, #0x100
     +0x14c: sub     w10, w25, w10
     +0x150: str     w10, [x19, w9, uxtw #2]
     +0x154: b.ne    <mldsa87_poly_challenge+0xf0>
     +0x158: movi    v0.2d, #0x0
     +0x15c: str     x22, [sp, #8]
     +0x160: add     x8, sp, #0x10
     +0x164: stp     q0, q0, [sp, #16]
     +0x168: stp     q0, q0, [sp, #48]
     +0x16c: stp     q0, q0, [sp, #80]
     +0x170: stp     q0, q0, [sp, #112]
     +0x174: stp     q0, q0, [x20, #128]
     +0x178: stp     q0, q0, [x20, #160]
     +0x17c: str     q0, [x20, #192]
     +0x180: str     xzr, [sp, #352]
     +0x184: add     x8, sp, #0xe0
     +0x188: stp     q0, q0, [x20, #208]
     +0x18c: stp     q0, q0, [x20, #240]
     +0x190: stp     q0, q0, [x20, #272]
     +0x194: stp     q0, q0, [x20, #304]
     +0x198: add     x8, sp, #0x8
     +0x19c: str     xzr, [sp, #8]
     +0x1a0: adrp    x8, <page>
     +0x1a4: ldr     x8, [x8, #4088]
     +0x1a8: ldr     x9, [sp, #376]
     +0x1ac: ldr     x8, [x8]
     +0x1b0: cmp     x8, x9
     +0x1b4: b.ne    <mldsa87_poly_challenge+0x1ec>
     +0x1b8: mov     sp, x29
     +0x1bc: ldp     x20, x19, [sp, #64]
     +0x1c0: ldp     x22, x21, [sp, #48]
     +0x1c4: ldp     x24, x23, [sp, #32]
     +0x1c8: ldp     x28, x25, [sp, #16]
     +0x1cc: ldp     x29, x30, [sp], #80
     +0x1d0: mov     x0, #0x0
     +0x1d4: mov     x1, #0x0
     +0x1d8: mov     x2, #0x0
     +0x1dc: mov     x8, #0x0
     +0x1e0: mov     x9, #0x0
     +0x1e4: mov     x10, #0x0
     +0x1e8: ret     
     +0x1ec: bl      <__stack_chk_fail>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa87_poly_challenge";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The seed is the 64 bytes C *)
(* at seed, and the polynomial at c becomes mld_poly_challenge 60 64 C, if   *)
(* mld_poly_challenge_terminates 60 64 C. The seed may overlap the           *)
(* polynomial, as it is only read before the polynomial is written. The      *)
(* stack is the 768 bytes below the stack pointer, see above; the address of *)
(* the stack guard is read from the GOT.                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !c seed C guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_poly_challenge_terminates 60 64 C /\
          nonoverlapping (c,1024) (word_sub stackpointer (word 768),768) /\
          nonoverlapping (seed,64) (word_sub stackpointer (word 768),768) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 768),768)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa87_poly_challenge) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                         s = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,64)) s = C)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add c (word(4 * i))))
                               s =
                             mld_poly_challenge 60 64 C i))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 768),768)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the seed C, the address of memset *)
(* and the stack, with all accesses within the seed, the polynomial, the     *)
(* stack, the GOT entries and the stack guard, the region (ea,el) that       *)
(* memset may read and the round constants of Keccak, and the writes within  *)
(* the polynomial and the stack.                                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e c seed C guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_poly_challenge_terminates 60 64 C /\
          nonoverlapping (c,1024) (word_sub stackpointer (word 768),768) /\
          nonoverlapping (seed,64) (word_sub stackpointer (word 768),768) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 768),768)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa87_poly_challenge) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                         s = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,64)) s = C /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add c (word(4 * i))))
                               s =
                             mld_poly_challenge 60 64 C i) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events c seed C guard mf pc
                              (word_sub stackpointer (word 768))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,64; c,1024;
                         word_sub stackpointer (word 768),768;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [c,1024; word_sub stackpointer (word 768),768]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 768),768)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone: the same events, which depend on   *)
(* the seed C, and the same accesses.                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e c seed C guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_poly_challenge_terminates 60 64 C /\
          nonoverlapping (c,1024) (word_sub stackpointer (word 768),768) /\
          nonoverlapping (seed,64) (word_sub stackpointer (word 768),768) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 768),768)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read PC s = word (pc + mldsa87_poly_challenge) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                         s = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,64)) s = C /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events c seed C guard mf pc
                              (word_sub stackpointer (word 768))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,64; c,1024;
                         word_sub stackpointer (word 768),768;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [c,1024; word_sub stackpointer (word 768),768]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 768),768)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
