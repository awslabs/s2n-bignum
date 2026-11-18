(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The challenge polynomial (SampleInBall): the statement. This is the code  *)
(* for mldsa65_poly_challenge (mld_poly_challenge in poly_kl.c, for          *)
(* ML-DSA-65) from mldsa-native's portable C implementation compiled by gcc  *)
(* 12 with -O2 (see mldsa_native/README.md), which absorbs the seed of 48    *)
(* bytes into a SHAKE256 context on its stack with mldsa_shake256_init,      *)
(* _absorb and _finalize, squeezes a block of 136 bytes into a buffer        *)
(* aligned to 32 bytes, takes the sign bits from its first 8 bytes with a    *)
(* loop, zeroes the polynomial with memset, and then for i from 256 - 49 to  *)
(* 255 reads bytes j of the buffer, squeezing a new block when it is used    *)
(* up, until j <= i, and sets c[i] = c[j] and c[j] = 1 or -1 by the next     *)
(* sign bit, before releasing the context and zeroing the buffer and the     *)
(* signs. It is verified in the whole image (see libmldsa.ml) against        *)
(* mld_poly_challenge 49 48 of common/mldsa_native_challenge.ml, using the   *)
(* theorems for the callees and the contract memset_full_contract of         *)
(* utils/mlkem_native_libc_full.ml for memset, and assuming                  *)
(* mld_poly_challenge_terminates 49 48, that the SHAKE256 output of the seed *)
(* has 49 acceptable bytes after its first 8, without which the code does    *)
(* not terminate. It is also shown to be constant time and memory safe, with *)
(* the events depending on the seed, which is public (c~ is declassified     *)
(* when signing and is part of the signature).                               *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_challenge.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_absorb_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_finalize_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_squeeze_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa65_poly_challenge:
       +0x0: stp     x19, x20, [sp, #-448]!
       +0x4: mov     x19, x1
       +0x8: adrp    x3, <page>
       +0xc: ldr     x3, [x3, #4088]
      +0x10: add     x2, sp, #0x5f
      +0x14: stp     x21, x22, [sp, #16]
      +0x18: add     x21, sp, #0xe8
      +0x1c: and     x20, x2, #0xffffffffffffffe0
      +0x20: stp     x23, x30, [sp, #32]
      +0x24: mov     x23, x0
      +0x28: ldr     x0, [x3]
      +0x2c: str     x0, [sp, #440]
      +0x30: mov     x0, #0x0
      +0x34: mov     x0, x21
      +0x38: bl      <mldsa_shake256_init>
      +0x3c: mov     x1, x19
      +0x40: mov     x2, #0x30
      +0x44: mov     x0, x21
      +0x48: bl      <mldsa_shake256_absorb>
      +0x4c: mov     x0, x21
      +0x50: bl      <mldsa_shake256_finalize>
      +0x54: mov     x2, x21
      +0x58: mov     x0, x20
      +0x5c: mov     x1, #0x88
      +0x60: bl      <mldsa_shake256_squeeze>
      +0x64: mov     x2, x20
      +0x68: mov     w0, #0x0
      +0x6c: mov     x3, #0x0
      +0x70: ldrb    w1, [x2], #1
      +0x74: lsl     x1, x1, x0
      +0x78: add     w0, w0, #0x8
      +0x7c: orr     x3, x3, x1
      +0x80: cmp     w0, #0x40
      +0x84: b.ne    <mldsa65_poly_challenge+0x70>
      +0x88: mov     x0, x23
      +0x8c: mov     x2, #0x400
      +0x90: mov     w1, #0x0
      +0x94: str     x3, [sp, #56]
      +0x98: bl      <memset>
      +0x9c: mov     x19, #0xcf
      +0xa0: mov     w22, #0x1
      +0xa4: mov     w0, #0x8
      +0xa8: b       <mldsa65_poly_challenge+0xbc>
      +0xac: ldrb    w1, [x20, w0, uxtw]
      +0xb0: add     w0, w0, #0x1
      +0xb4: cmp     w1, w19
      +0xb8: b.ls    <mldsa65_poly_challenge+0xe4>
      +0xbc: cmp     w0, #0x88
      +0xc0: b.ne    <mldsa65_poly_challenge+0xac>
      +0xc4: mov     x0, x20
      +0xc8: mov     x1, #0x88
      +0xcc: mov     x2, x21
      +0xd0: bl      <mldsa_shake256_squeeze>
      +0xd4: ldrb    w1, [x20]
      +0xd8: mov     w0, #0x1
      +0xdc: cmp     w1, w19
      +0xe0: b.hi    <mldsa65_poly_challenge+0xac>
      +0xe4: ldr     x2, [sp, #56]
      +0xe8: ldr     w4, [x23, x1, lsl #2]
      +0xec: str     w4, [x23, x19, lsl #2]
      +0xf0: add     x19, x19, #0x1
      +0xf4: ubfiz   x3, x2, #1, #1
      +0xf8: lsr     x2, x2, #1
      +0xfc: sub     w3, w22, w3
     +0x100: str     w3, [x23, x1, lsl #2]
     +0x104: str     x2, [sp, #56]
     +0x108: cmp     x19, #0x100
     +0x10c: b.ne    <mldsa65_poly_challenge+0xbc>
     +0x110: mov     x0, x21
     +0x114: bl      <mldsa_shake256_release>
     +0x118: movi    v0.4s, #0x0
     +0x11c: str     xzr, [x20, #128]
     +0x120: stp     q0, q0, [x20]
     +0x124: stp     q0, q0, [x20, #32]
     +0x128: stp     q0, q0, [x20, #64]
     +0x12c: stp     q0, q0, [x20, #96]
     +0x130: add     x0, sp, #0x38
     +0x134: str     xzr, [sp, #56]
     +0x138: adrp    x0, <page>
     +0x13c: ldr     x0, [x0, #4088]
     +0x140: ldr     x2, [sp, #440]
     +0x144: ldr     x1, [x0]
     +0x148: subs    x2, x2, x1
     +0x14c: mov     x1, #0x0
     +0x150: b.ne    <mldsa65_poly_challenge+0x164>
     +0x154: ldp     x21, x22, [sp, #16]
     +0x158: ldp     x23, x30, [sp, #32]
     +0x15c: ldp     x19, x20, [sp], #448
     +0x160: ret
     +0x164: bl      <stack_chk_fail>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_poly_challenge"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The seed is the 48 bytes C *)
(* at seed, and the polynomial at c becomes mld_poly_challenge 49 48 C, if   *)
(* mld_poly_challenge_terminates 49 48 C. The seed may overlap the           *)
(* polynomial, as it is only read before the polynomial is written. The      *)
(* stack is the 448 bytes of the function and the 256 below them used by     *)
(* absorbing and squeezing; the address of the stack guard is read from the  *)
(* GOT.                                                                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !c seed C guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_poly_challenge_terminates 49 48 C /\
          nonoverlapping (c,1024) (word_sub stackpointer (word 704),704) /\
          nonoverlapping (seed,48) (word_sub stackpointer (word 704),704) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 704),704)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_poly_challenge) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                         s = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,48)) s = C)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add c (word(4 * i))))
                               s =
                             mld_poly_challenge 49 48 C i))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 704),704)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the seed C, the address of memset *)
(* and the stack, with all accesses within the seed, the polynomial, the     *)
(* stack, the GOT entries and the stack guard, the region (ea,el) that       *)
(* memset may read and the round constants of Keccak, and the writes within  *)
(* the polynomial and the stack.                                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e c seed C guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_poly_challenge_terminates 49 48 C /\
          nonoverlapping (c,1024) (word_sub stackpointer (word 704),704) /\
          nonoverlapping (seed,48) (word_sub stackpointer (word 704),704) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 704),704)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_poly_challenge) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                         s = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,48)) s = C /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add c (word(4 * i))))
                               s =
                             mld_poly_challenge 49 48 C i) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events c seed C guard mf pc
                              (word_sub stackpointer (word 704))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,48; c,1024;
                         word_sub stackpointer (word 704),704;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [c,1024; word_sub stackpointer (word 704),704]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 704),704)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone: the same events, which depend on   *)
(* the seed C, and the same accesses.                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e c seed C guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_poly_challenge_terminates 49 48 C /\
          nonoverlapping (c,1024) (word_sub stackpointer (word 704),704) /\
          nonoverlapping (seed,48) (word_sub stackpointer (word 704),704) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 704),704)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa65_poly_challenge) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                         s = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,48)) s = C /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events c seed C guard mf pc
                              (word_sub stackpointer (word 704))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,48; c,1024;
                         word_sub stackpointer (word 704),704;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [c,1024; word_sub stackpointer (word 704),704]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 704),704)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
