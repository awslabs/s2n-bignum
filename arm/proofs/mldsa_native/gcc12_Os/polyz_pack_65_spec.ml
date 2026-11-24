(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 20 bits per coefficient, of 2^19 - a: the    *)
(* statement. This is the code for mldsa65_polyz_pack (mld_polyz_pack in     *)
(* poly_kl.c with MLDSA_GAMMA1 = 2^19, for ML-DSA-65) from mldsa-native's    *)
(* portable C implementation compiled by gcc 12 with -Os (see                *)
(* mldsa_native/README.md), which writes 5 bytes for each 2 coefficients,    *)
(* with a stack protector. It keeps the last 2 coefficients in a temporary   *)
(* array on its stack, zeroes it with mld_zeroize_3, which calls memset, and *)
(* checks the stack guard before it returns. It is verified in the whole     *)
(* image (see libmldsa.ml) against mld_polyz_pack_19 of                      *)
(* common/mldsa_native_packing.ml, byte by byte, with the theorem for        *)
(* mld_zeroize_3 and the contract memset_full_contract of                    *)
(* utils/mlkem_native_libc_full.ml, and with the address of the stack guard  *)
(* in the global offset table. It is also shown to be constant time and      *)
(* memory safe.                                                              *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_pack.ml";;
needs "common/mldsa_native_packing.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;

(*** The code in the image:

    mldsa65_polyz_pack:
       +0x0: adrp    x2, <page>
       +0x4: ldr     x2, [x2, #4088]
       +0x8: str     x30, [sp, #-48]!
       +0xc: add     x9, x0, #0x280
      +0x10: mov     w8, #0x80000
      +0x14: ldr     x3, [x2]
      +0x18: str     x3, [sp, #40]
      +0x1c: mov     x3, #0x0
      +0x20: mov     x2, x0
      +0x24: ldp     w3, w5, [x1]
      +0x28: add     x2, x2, #0x5
      +0x2c: add     x1, x1, #0x8
      +0x30: sub     w3, w8, w3
      +0x34: sub     w5, w8, w5
      +0x38: sturb   w3, [x2, #-5]
      +0x3c: lsr     w4, w3, #8
      +0x40: sturb   w4, [x2, #-4]
      +0x44: ubfiz   w4, w5, #4, #4
      +0x48: ubfx    x7, x5, #4, #8
      +0x4c: orr     w4, w4, w3, lsr #16
      +0x50: ubfx    x6, x5, #12, #8
      +0x54: and     w4, w4, #0xff
      +0x58: sturb   w4, [x2, #-3]
      +0x5c: sturb   w7, [x2, #-2]
      +0x60: sturb   w6, [x2, #-1]
      +0x64: cmp     x9, x2
      +0x68: b.ne    <mldsa65_polyz_pack+0x24>
      +0x6c: add     x1, x0, #0x200
      +0x70: stp     w3, w5, [sp, #24]
      +0x74: sturh   w3, [x1, #123]
      +0x78: mov     x1, #0x10
      +0x7c: strb    w4, [x0, #637]
      +0x80: strb    w7, [x0, #638]
      +0x84: strb    w6, [x0, #639]
      +0x88: add     x0, sp, #0x18
      +0x8c: bl      <mld_zeroize_3>
      +0x90: adrp    x0, <page>
      +0x94: ldr     x0, [x0, #4088]
      +0x98: ldr     x2, [sp, #40]
      +0x9c: ldr     x1, [x0]
      +0xa0: subs    x2, x2, x1
      +0xa4: mov     x1, #0x0
      +0xa8: b.eq    <mldsa65_polyz_pack+0xb0>
      +0xac: bl      <stack_chk_fail>
      +0xb0: ldr     x30, [sp], #48
      +0xb4: ret
 ***)

let MLDSA_NATIVE_POLYZ_PACK_65_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa65_polyz_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, with the combined contract for memset of                     *)
(* utils/mlkem_native_libc_full.ml, which mld_zeroize needs: the memory      *)
(* (ea,el) that memset reads and keeps must not overlap the output or the    *)
(* stack frame, which includes that of mld_zeroize.                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !r a x guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(r,640); (word_sub stackpointer (word 64),64)] /\
          ALLPAIRS nonoverlapping
           [(r,640); (word_sub stackpointer (word 64),64)]
           [(a,1024); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa65_polyz_pack) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                         s = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add a (word(4 * i))))
                               s = x i))
               (\s. read PC s = returnaddress /\
                    (!j. j < 640
                         ==> read(memory :> bytes8(word_add r (word j))) s =
                             mld_polyz_pack_19 x j))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r,640);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_POLYZ_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYZ_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* input, the output, the stack frame, the GOT entries of the stack guard    *)
(* and of memset, the guard and (ea,el), and the writes within the output    *)
(* and the stack frame.                                                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e r a x guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(r,640); (word_sub stackpointer (word 64),64)] /\
          ALLPAIRS nonoverlapping
           [(r,640); (word_sub stackpointer (word 64),64)]
           [(a,1024); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa65_polyz_pack) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                         s = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add a (word(4 * i))))
                               s = x i) /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!j. j < 640
                         ==> read(memory :> bytes8(word_add r (word j))) s =
                             mld_polyz_pack_19 x j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events r a guard mf pc
                              (word_sub stackpointer (word 64))
                              returnaddress /\
                       memaccess_inbounds e2
                        [a,1024; r,640; word_sub stackpointer (word 64),64;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el]
                        [r,640; word_sub stackpointer (word 64),64]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r,640);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_POLYZ_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYZ_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e r a guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(r,640); (word_sub stackpointer (word 64),64)] /\
          ALLPAIRS nonoverlapping
           [(r,640); (word_sub stackpointer (word 64),64)]
           [(a,1024); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa65_polyz_pack) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [r; a] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard)))
                         s = guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events r a guard mf pc
                              (word_sub stackpointer (word 64))
                              returnaddress /\
                       memaccess_inbounds e2
                        [a,1024; r,640; word_sub stackpointer (word 64),64;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el]
                        [r,640; word_sub stackpointer (word 64),64]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r,640);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_POLYZ_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYZ_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
