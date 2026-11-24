(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 18 bits per coefficient, of 2^17 - a: the    *)
(* statement. This is the code for mldsa44_polyz_pack (mld_polyz_pack in     *)
(* poly_kl.c with MLDSA_GAMMA1 = 2^17, for ML-DSA-44) from mldsa-native's    *)
(* portable C implementation compiled by gcc 12 with -O2 and                 *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which writes 9 bytes  *)
(* for each 4 coefficients, 8 of them as one 64-bit word assembled in a      *)
(* vector register, with a stack protector. Its stack frame of 48 bytes      *)
(* holds the return address, the 16 bytes of a temporary array, which the    *)
(* code zeroes with one store of two zero registers, and the canary, which   *)
(* it checks against the stack guard before it returns. It is verified in    *)
(* the whole image (see libmldsa.ml) against mld_polyz_pack_17 of            *)
(* common/mldsa_native_packing.ml, byte by byte, with the address of the     *)
(* stack guard in the global offset table. It is also shown to be constant   *)
(* time and memory safe.                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyz_pack:
       +0x0: adrp    x2, <page>
       +0x4: ldr     x2, [x2, #4088]
       +0x8: str     x30, [sp, #-48]!
       +0xc: add     x9, x1, #0x400
      +0x10: mov     w6, #0x20000
      +0x14: ldr     x3, [x2]
      +0x18: str     x3, [sp, #40]
      +0x1c: mov     x3, #0x0
      +0x20: nop
      +0x24: ldp     w2, w4, [x1]
      +0x28: add     x0, x0, #0x9
      +0x2c: ldp     w3, w5, [x1, #8]
      +0x30: sub     w2, w6, w2
      +0x34: fmov    s0, w2
      +0x38: sub     w4, w6, w4
      +0x3c: sub     w3, w6, w3
      +0x40: add     x1, x1, #0x10
      +0x44: ushr    v1.2s, v0.2s, #8
      +0x48: fmov    s0, w4
      +0x4c: ubfiz   w7, w4, #2, #6
      +0x50: ubfiz   w8, w3, #4, #4
      +0x54: ushr    v3.2s, v0.2s, #6
      +0x58: fmov    d0, x2
      +0x5c: orr     w7, w7, w2, lsr #16
      +0x60: orr     w4, w8, w4, lsr #14
      +0x64: mov     v0.b[1], v1.b[0]
      +0x68: fmov    s1, w3
      +0x6c: sub     w2, w6, w5
      +0x70: ushr    v2.2s, v1.2s, #4
      +0x74: fmov    s1, w2
      +0x78: ubfiz   w5, w2, #6, #2
      +0x7c: lsr     w2, w2, #10
      +0x80: mov     v0.b[2], w7
      +0x84: orr     w3, w5, w3, lsr #12
      +0x88: ushr    v1.2s, v1.2s, #2
      +0x8c: sturb   w2, [x0, #-1]
      +0x90: mov     v0.b[3], v3.b[0]
      +0x94: mov     v0.b[4], w4
      +0x98: mov     v0.b[5], v2.b[0]
      +0x9c: mov     v0.b[6], w3
      +0xa0: mov     v0.b[7], v1.b[0]
      +0xa4: stur    d0, [x0, #-9]
      +0xa8: cmp     x9, x1
      +0xac: b.ne    <mldsa44_polyz_pack+0x24>
      +0xb0: add     x0, sp, #0x18
      +0xb4: stp     xzr, xzr, [sp, #24]
      +0xb8: adrp    x0, <page>
      +0xbc: ldr     x0, [x0, #4088]
      +0xc0: ldr     x2, [sp, #40]
      +0xc4: ldr     x1, [x0]
      +0xc8: subs    x2, x2, x1
      +0xcc: mov     x1, #0x0
      +0xd0: b.ne    <mldsa44_polyz_pack+0xdc>
      +0xd4: ldr     x30, [sp], #48
      +0xd8: ret
      +0xdc: bl      <stack_chk_fail>
 ***)

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa44_polyz_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The stack frame of 48 bytes, below the stack pointer, is     *)
(* the only memory besides the output that the code writes.                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,576); (word_sub stackpointer (word 48),48)] /\
        ALLPAIRS nonoverlapping
         [(r,576); (word_sub stackpointer (word 48),48)]
         [(a,1024); (word pc,libmldsa_size);
          (word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read PC s = word (pc + mldsa44_polyz_pack) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  (!j. j < 576
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyz_pack_17 x j))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,576);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* input, the output, the stack frame, the GOT entry of the stack guard and  *)
(* the guard, and the writes within the output and the stack frame.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,576); (word_sub stackpointer (word 48),48)] /\
        ALLPAIRS nonoverlapping
         [(r,576); (word_sub stackpointer (word 48),48)]
         [(a,1024); (word pc,libmldsa_size);
          (word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read PC s = word (pc + mldsa44_polyz_pack) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!j. j < 576
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyz_pack_17 x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a guard pc
                            (word_sub stackpointer (word 48))
                            returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; r,576; word_sub stackpointer (word 48),48;
                       word(pc + got_stack_chk_guard),8; guard,8]
                      [r,576; word_sub stackpointer (word 48),48]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,576);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,576); (word_sub stackpointer (word 48),48)] /\
        ALLPAIRS nonoverlapping
         [(r,576); (word_sub stackpointer (word 48),48)]
         [(a,1024); (word pc,libmldsa_size);
          (word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read PC s = word (pc + mldsa44_polyz_pack) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a guard pc
                            (word_sub stackpointer (word 48))
                            returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; r,576; word_sub stackpointer (word 48),48;
                       word(pc + got_stack_chk_guard),8; guard,8]
                      [r,576; word_sub stackpointer (word 48),48]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,576);
                memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYZ_PACK_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
