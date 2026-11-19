(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The challenge polynomial (SampleInBall): the statement. This is the code  *)
(* for mldsa65_poly_challenge (mld_poly_challenge in poly_kl.c, for          *)
(* ML-DSA-65) from mldsa-native's portable C implementation compiled by gcc  *)
(* 12 with -Os (see mldsa_native/README.md), which absorbs the seed of 48    *)
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
needs "arm/proofs/mldsa_native/gcc12_Os/shake256_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256_absorb_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256_finalize_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256_squeeze_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/zeroize_3_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa65_poly_challenge:
       +0x0: stp     x19, x20, [sp, #-464]!
       +0x4: mov     x19, x1
       +0x8: stp     x21, x22, [sp, #16]
       +0xc: mov     x22, x0
      +0x10: add     x21, sp, #0xf8
      +0x14: adrp    x0, <page>
      +0x18: ldr     x0, [x0, #4088]
      +0x1c: stp     x23, x24, [sp, #32]
      +0x20: add     x20, sp, #0x6f
      +0x24: str     x30, [sp, #48]
      +0x28: and     x20, x20, #0xffffffffffffffe0
      +0x2c: ldr     x1, [x0]
      +0x30: str     x1, [sp, #456]
      +0x34: mov     x1, #0x0
      +0x38: mov     x0, x21
      +0x3c: bl      <mldsa_shake256_init>
      +0x40: mov     x1, x19
      +0x44: mov     x2, #0x30
      +0x48: mov     x0, x21
      +0x4c: bl      <mldsa_shake256_absorb>
      +0x50: mov     x0, x21
      +0x54: mov     x19, #0x0
      +0x58: bl      <mldsa_shake256_finalize>
      +0x5c: mov     x0, x20
      +0x60: mov     x2, x21
      +0x64: mov     x1, #0x88
      +0x68: bl      <mldsa_shake256_squeeze>
      +0x6c: mov     x0, #0x0
      +0x70: ldrb    w1, [x19, x20]
      +0x74: lsl     w2, w19, #3
      +0x78: add     x19, x19, #0x1
      +0x7c: lsl     x1, x1, x2
      +0x80: orr     x0, x0, x1
      +0x84: cmp     x19, #0x8
      +0x88: b.ne    <mldsa65_poly_challenge+0x70>
      +0x8c: mov     x2, #0x400
      +0x90: mov     w1, #0x0
      +0x94: mov     x23, #0xcf
      +0x98: mov     w24, #0x1
      +0x9c: str     x0, [sp, #72]
      +0xa0: mov     x0, x22
      +0xa4: bl      <memset>
      +0xa8: cmp     w19, #0x88
      +0xac: b.ne    <mldsa65_poly_challenge+0x144>
      +0xb0: mov     x0, x20
      +0xb4: mov     x2, x21
      +0xb8: mov     x1, #0x88
      +0xbc: bl      <mldsa_shake256_squeeze>
      +0xc0: mov     w0, #0x0
      +0xc4: add     w19, w0, #0x1
      +0xc8: ldrb    w0, [x20, w0, uxtw]
      +0xcc: cmp     w0, w23
      +0xd0: b.hi    <mldsa65_poly_challenge+0xa8>
      +0xd4: ubfiz   x0, x0, #2, #8
      +0xd8: ldr     w1, [x22, x0]
      +0xdc: str     w1, [x22, x23, lsl #2]
      +0xe0: add     x23, x23, #0x1
      +0xe4: ldr     x1, [sp, #72]
      +0xe8: ubfiz   x2, x1, #1, #1
      +0xec: lsr     x1, x1, #1
      +0xf0: sub     w2, w24, w2
      +0xf4: str     w2, [x22, x0]
      +0xf8: str     x1, [sp, #72]
      +0xfc: cmp     x23, #0x100
     +0x100: b.ne    <mldsa65_poly_challenge+0xa8>
     +0x104: mov     x0, x21
     +0x108: bl      <mldsa_shake256_release>
     +0x10c: mov     x0, x20
     +0x110: mov     x1, #0x88
     +0x114: bl      <mld_zeroize_3>
     +0x118: add     x0, sp, #0x48
     +0x11c: mov     x1, #0x8
     +0x120: bl      <mld_zeroize_3>
     +0x124: adrp    x0, <page>
     +0x128: ldr     x0, [x0, #4088]
     +0x12c: ldr     x2, [sp, #456]
     +0x130: ldr     x1, [x0]
     +0x134: subs    x2, x2, x1
     +0x138: mov     x1, #0x0
     +0x13c: b.eq    <mldsa65_poly_challenge+0x14c>
     +0x140: bl      <stack_chk_fail>
     +0x144: mov     w0, w19
     +0x148: b       <mldsa65_poly_challenge+0xc4>
     +0x14c: ldp     x21, x22, [sp, #16]
     +0x150: ldp     x23, x24, [sp, #32]
     +0x154: ldr     x30, [sp, #48]
     +0x158: ldp     x19, x20, [sp], #464
     +0x15c: ret
    plt_memset:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa65_poly_challenge"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The seed is the 48 bytes C *)
(* at seed, and the polynomial at c becomes mld_poly_challenge 49 48 C, if   *)
(* mld_poly_challenge_terminates 49 48 C. The seed may overlap the           *)
(* polynomial, as it is only read before the polynomial is written. The      *)
(* stack is the 464 bytes of the function and the 304 below them used by     *)
(* absorbing and squeezing; the address of the stack guard is read from the  *)
(* GOT.                                                                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !c seed C guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_poly_challenge_terminates 49 48 C /\
          nonoverlapping (c,1024) (word_sub stackpointer (word 768),768) /\
          nonoverlapping (seed,48) (word_sub stackpointer (word 768),768) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 768),768)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                  memory :> bytes(word_sub stackpointer (word 768),768)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the seed C, the address of memset *)
(* and the stack, with all accesses within the seed, the polynomial, the     *)
(* stack, the GOT entries and the stack guard, the region (ea,el) that       *)
(* memset may read and the round constants of Keccak, and the writes within  *)
(* the polynomial and the stack.                                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e c seed C guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_poly_challenge_terminates 49 48 C /\
          nonoverlapping (c,1024) (word_sub stackpointer (word 768),768) /\
          nonoverlapping (seed,48) (word_sub stackpointer (word 768),768) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 768),768)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                              (word_sub stackpointer (word 768))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,48; c,1024;
                         word_sub stackpointer (word 768),768;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [c,1024; word_sub stackpointer (word 768),768]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 768),768)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone: the same events, which depend on   *)
(* the seed C, and the same accesses.                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e c seed C guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_poly_challenge_terminates 49 48 C /\
          nonoverlapping (c,1024) (word_sub stackpointer (word 768),768) /\
          nonoverlapping (seed,48) (word_sub stackpointer (word 768),768) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 768),768)]
           [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
            (guard,8); (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
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
                              (word_sub stackpointer (word 768))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,48; c,1024;
                         word_sub stackpointer (word 768),768;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [c,1024; word_sub stackpointer (word 768),768]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 768),768)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
