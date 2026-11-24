(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 4 bits per coefficient, of 4 - a: the        *)
(* statement. This is the code for mldsa65_polyeta_pack (mld_polyeta_pack in *)
(* poly_kl.c with MLDSA_ETA = 4, for ML-DSA-65) from mldsa-native's portable *)
(* C implementation compiled by gcc 12 with -O2 (see                         *)
(* mldsa_native/README.md), which writes a byte for each 2 coefficients,     *)
(* with a stack protector. It has a stack frame of 32 bytes for x30, the     *)
(* temporary array of 8 bytes and the stack guard, zeroes the array with a   *)
(* single store, and checks the stack guard before it returns. It is         *)
(* verified in the whole image (see libmldsa.ml) against mld_polyeta_pack_4  *)
(* of common/mldsa_native_packing.ml, byte by byte, with the address of the  *)
(* stack guard in the global offset table. It is also shown to be constant   *)
(* time and memory safe.                                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_polyeta_pack:
       +0x0: adrp    x2, <page>
       +0x4: ldr     x2, [x2, #4088]
       +0x8: str     x30, [sp, #-32]!
       +0xc: add     x5, x1, #0x400
      +0x10: mov     w4, #0x4
      +0x14: ldr     x3, [x2]
      +0x18: str     x3, [sp, #24]
      +0x1c: mov     x3, #0x0
      +0x20: ldr     w2, [x1, #4]
      +0x24: ldr     w3, [x1], #8
      +0x28: sub     w2, w4, w2
      +0x2c: sub     w3, w4, w3
      +0x30: ubfiz   w2, w2, #4, #8
      +0x34: orr     w2, w2, w3
      +0x38: strb    w2, [x0], #1
      +0x3c: cmp     x5, x1
      +0x40: b.ne    <mldsa65_polyeta_pack+0x20>
      +0x44: add     x0, sp, #0x10
      +0x48: str     xzr, [sp, #16]
      +0x4c: adrp    x0, <page>
      +0x50: ldr     x0, [x0, #4088]
      +0x54: ldr     x2, [sp, #24]
      +0x58: ldr     x1, [x0]
      +0x5c: subs    x2, x2, x1
      +0x60: mov     x1, #0x0
      +0x64: b.ne    <mldsa65_polyeta_pack+0x70>
      +0x68: ldr     x30, [sp], #32
      +0x6c: ret
      +0x70: bl      <stack_chk_fail>
 ***)

let MLDSA_NATIVE_POLYETA_PACK_65_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_polyeta_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The stack frame is the 32 bytes below the stack pointer: x30 *)
(* at the bottom, the 8 bytes of the temporary array and the stack guard.    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,128); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
         [(r,128); (word_sub stackpointer (word 32),32)]
         [(a,1024); (word pc,libmldsa_size);
          (word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa65_polyeta_pack) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                       s = guard /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  !j. j < 128
                      ==> read(memory :> bytes8(word_add r (word j))) s =
                          mld_polyeta_pack_4 x j)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,128);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYETA_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYETA_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* input, the output, the stack frame, the GOT entry of the stack guard and  *)
(* the guard, and the writes within the output and the stack frame.          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r a x guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,128); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
         [(r,128); (word_sub stackpointer (word 32),32)]
         [(a,1024); (word pc,libmldsa_size);
          (word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa65_polyeta_pack) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                       s = guard /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!j. j < 128
                       ==> read(memory :> bytes8(word_add r (word j))) s =
                           mld_polyeta_pack_4 x j) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a guard pc
                            (word_sub stackpointer (word 32))
                            returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; r,128; word_sub stackpointer (word 32),32;
                       word(pc + got_stack_chk_guard),8; guard,8]
                      [r,128; word_sub stackpointer (word 32),32]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,128);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYETA_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYETA_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r a guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(r,128); (word_sub stackpointer (word 32),32)] /\
        ALLPAIRS nonoverlapping
         [(r,128); (word_sub stackpointer (word 32),32)]
         [(a,1024); (word pc,libmldsa_size);
          (word(pc + got_stack_chk_guard),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa65_polyeta_pack) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [r; a] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                       s = guard /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r a guard pc
                            (word_sub stackpointer (word 32))
                            returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; r,128; word_sub stackpointer (word 32),32;
                       word(pc + got_stack_chk_guard),8; guard,8]
                      [r,128; word_sub stackpointer (word 32),32]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r,128);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYETA_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYETA_PACK_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
