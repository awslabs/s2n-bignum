(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 13 bits per coefficient, of 2^12 - a: the    *)
(* statement. This is the code for mldsa_polyt0_pack (mld_polyt0_pack in     *)
(* poly.c) from mldsa-native's portable C implementation compiled by clang   *)
(* 23 with -O3 as a monolithic build with MLD_CONFIG_REDUCE_RAM (see         *)
(* mldsa_native/README.md). Each of the 32 iterations of its loop loads 8    *)
(* coefficients and writes the 13 bytes with 13 single-byte stores. The code *)
(* has a stack protector: it saves the return address and the stack guard in *)
(* a frame of 64 bytes, zeroes the 32 bytes of the temporary array in the    *)
(* frame with one store of two zero vector registers, and checks the guard   *)
(* before it returns. It also clears the caller-saved registers x0-x3 and    *)
(* x8-x18 before returning. It is verified in the whole image (see           *)
(* libmldsa.ml) against mld_polyt0_pack of common/mldsa_native_packing.ml,   *)
(* byte by byte, with the address of the stack guard in the global offset    *)
(* table. It is also shown to be constant time and memory safe.              *)
(*                                                                           *)
(* The statement is that of the gcc 12 -O2 build: the frame is 64 bytes as  *)
(* there. Only its layout differs (guard at offset 40, return address at 48).*)
(* The clang code also uses x18 as a scratch register, which                 *)
(* MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI does not cover, so the frame    *)
(* has MAYCHANGE [X18] added.                                                *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa_polyt0_pack:
       +0x0: sub     sp, sp, #0x40
       +0x4: str     x30, [sp, #48]
       +0x8: adrp    x9, <page>
       +0xc: add     x8, x0, #0x6
      +0x10: mov     w10, #0x20
      +0x14: ldr     x9, [x9, #4088]
      +0x18: mov     w11, #0x1000
      +0x1c: ldr     x9, [x9]
      +0x20: str     x9, [sp, #40]
      +0x24: add     x9, x1, #0x10
      +0x28: ldp     w12, w13, [x9, #-16]
      +0x2c: ldp     w14, w15, [x9, #-8]
      +0x30: ldp     w16, w17, [x9]
      +0x34: sub     w13, w11, w13
      +0x38: sub     w12, w11, w12
      +0x3c: subs    x10, x10, #0x1
      +0x40: lsl     w1, w13, #5
      +0x44: sub     w14, w11, w14
      +0x48: sub     w15, w11, w15
      +0x4c: ldp     w18, w0, [x9, #8]
      +0x50: sturb   w12, [x8, #-6]
      +0x54: lsl     w3, w14, #2
      +0x58: orr     w12, w1, w12, lsr #8
      +0x5c: lsl     w1, w15, #7
      +0x60: sub     w16, w11, w16
      +0x64: lsr     w2, w13, #3
      +0x68: orr     w13, w3, w13, lsr #11
      +0x6c: sturb   w12, [x8, #-5]
      +0x70: lsl     w12, w16, #4
      +0x74: orr     w14, w1, w14, lsr #6
      +0x78: sub     w17, w11, w17
      +0x7c: sub     w18, w11, w18
      +0x80: sturb   w13, [x8, #-3]
      +0x84: lsr     w13, w15, #1
      +0x88: orr     w12, w12, w15, lsr #9
      +0x8c: sturb   w14, [x8, #-2]
      +0x90: lsl     w14, w17, #1
      +0x94: lsl     w15, w18, #6
      +0x98: sturb   w13, [x8, #-1]
      +0x9c: lsr     w13, w16, #4
      +0xa0: sub     w0, w11, w0
      +0xa4: strb    w12, [x8]
      +0xa8: orr     w12, w14, w16, lsr #12
      +0xac: lsl     w14, w0, #3
      +0xb0: strb    w13, [x8, #1]
      +0xb4: orr     w13, w15, w17, lsr #7
      +0xb8: add     x9, x9, #0x20
      +0xbc: strb    w12, [x8, #2]
      +0xc0: lsr     w12, w18, #2
      +0xc4: strb    w13, [x8, #3]
      +0xc8: orr     w13, w14, w18, lsr #10
      +0xcc: strb    w12, [x8, #4]
      +0xd0: lsr     w12, w0, #5
      +0xd4: sturb   w2, [x8, #-4]
      +0xd8: strb    w13, [x8, #5]
      +0xdc: strb    w12, [x8, #6]
      +0xe0: add     x8, x8, #0xd
      +0xe4: b.ne    <mldsa_polyt0_pack+0x28>
      +0xe8: movi    v0.2d, #0x0
      +0xec: mov     x8, sp
      +0xf0: stp     q0, q0, [sp]
      +0xf4: adrp    x8, <page>
      +0xf8: ldr     x8, [x8, #4088]
      +0xfc: ldr     x9, [sp, #40]
     +0x100: ldr     x8, [x8]
     +0x104: cmp     x8, x9
     +0x108: b.ne    <mldsa_polyt0_pack+0x154>
     +0x10c: ldr     x30, [sp, #48]
     +0x110: add     sp, sp, #0x40
     +0x114: mov     x0, #0x0
     +0x118: mov     x1, #0x0
     +0x11c: mov     x2, #0x0
     +0x120: mov     x3, #0x0
     +0x124: mov     x8, #0x0
     +0x128: mov     x9, #0x0
     +0x12c: mov     x10, #0x0
     +0x130: mov     x11, #0x0
     +0x134: mov     x12, #0x0
     +0x138: mov     x13, #0x0
     +0x13c: mov     x14, #0x0
     +0x140: mov     x15, #0x0
     +0x144: mov     x16, #0x0
     +0x148: mov     x17, #0x0
     +0x14c: mov     x18, #0x0
     +0x150: ret     
     +0x154: bl      <__stack_chk_fail>
 ***)

let MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa_polyt0_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,416); (word_sub stackpointer (word 64),64)] /\
        ALLPAIRS nonoverlapping
         [(r,416); (word_sub stackpointer (word 64),64)]
         [(a,1024); (word pc,libmldsa_size);
          (word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mldsa_polyt0_pack) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  !j. j < 416
                      ==> read(memory :> bytes8(word_add r (word j))) s =
                          mld_polyt0_pack x j)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(r,416);
                memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* input, the output, the stack frame, the GOT entry of the stack guard and  *)
(* the guard, and the writes within the output and the stack frame.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,416); (word_sub stackpointer (word 64),64)] /\
        ALLPAIRS nonoverlapping
         [(r,416); (word_sub stackpointer (word 64),64)]
         [(a,1024); (word pc,libmldsa_size);
          (word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mldsa_polyt0_pack) /\
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
                  (!j. j < 416
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyt0_pack x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a guard pc
                            (word_sub stackpointer (word 64)) returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; r,416; word_sub stackpointer (word 64),64;
                       word(pc + got_stack_chk_guard),8; guard,8]
                      [r,416; word_sub stackpointer (word 64),64]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(r,416);
                memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,416); (word_sub stackpointer (word 64),64)] /\
        ALLPAIRS nonoverlapping
         [(r,416); (word_sub stackpointer (word 64),64)]
         [(a,1024); (word pc,libmldsa_size);
          (word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read PC s = word (pc + mldsa_polyt0_pack) /\
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
                            (word_sub stackpointer (word 64)) returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; r,416; word_sub stackpointer (word 64),64;
                       word(pc + got_stack_chk_guard),8; guard,8]
                      [r,416; word_sub stackpointer (word 64),64]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(r,416);
                memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYT0_PACK_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
