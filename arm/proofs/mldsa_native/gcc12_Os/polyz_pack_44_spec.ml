(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 18 bits per coefficient, of 2^17 - a: the    *)
(* statement. This is the code for mldsa44_polyz_pack (mld_polyz_pack in     *)
(* poly_kl.c with MLDSA_GAMMA1 = 2^17, for ML-DSA-44) from mldsa-native's    *)
(* portable C implementation compiled by gcc 12 with -Os (see                *)
(* mldsa_native/README.md), which writes 9 bytes for each 4 coefficients,    *)
(* with a stack protector. It keeps the last 4 coefficients in a temporary   *)
(* array on its stack, zeroes it with mld_zeroize_1, which calls memset, and *)
(* checks the stack guard before it returns. It is verified in the whole     *)
(* image (see libmldsa.ml) against mld_polyz_pack_17 of                      *)
(* common/mldsa_native_packing.ml, byte by byte, with the theorem for        *)
(* mld_zeroize_1 and the contract memset_full_contract of                    *)
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

    mldsa44_polyz_pack:
       +0x0: adrp    x2, <page>
       +0x4: ldr     x2, [x2, #4088]
       +0x8: str     x30, [sp, #-48]!
       +0xc: add     x15, x0, #0x240
      +0x10: mov     w10, #0x20000
      +0x14: ldr     x3, [x2]
      +0x18: str     x3, [sp, #40]
      +0x1c: mov     x3, #0x0
      +0x20: mov     x2, x0
      +0x24: ldp     w3, w9, [x1]
      +0x28: add     x2, x2, #0x9
      +0x2c: ldp     w8, w7, [x1, #8]
      +0x30: sub     w3, w10, w3
      +0x34: sub     w9, w10, w9
      +0x38: sturb   w3, [x2, #-9]
      +0x3c: sub     w8, w10, w8
      +0x40: sub     w7, w10, w7
      +0x44: lsr     w4, w3, #8
      +0x48: ubfiz   w6, w9, #2, #6
      +0x4c: ubfiz   w5, w8, #4, #4
      +0x50: sturb   w4, [x2, #-8]
      +0x54: ubfiz   w4, w7, #6, #2
      +0x58: orr     w6, w6, w3, lsr #16
      +0x5c: orr     w5, w5, w9, lsr #14
      +0x60: orr     w4, w4, w8, lsr #12
      +0x64: and     w6, w6, #0xff
      +0x68: ubfx    x14, x9, #6, #8
      +0x6c: and     w5, w5, #0xff
      +0x70: ubfx    x13, x8, #4, #8
      +0x74: and     w4, w4, #0xff
      +0x78: ubfx    x12, x7, #2, #8
      +0x7c: ubfx    x11, x7, #10, #8
      +0x80: sturb   w6, [x2, #-7]
      +0x84: sturb   w14, [x2, #-6]
      +0x88: add     x1, x1, #0x10
      +0x8c: sturb   w5, [x2, #-5]
      +0x90: sturb   w13, [x2, #-4]
      +0x94: sturb   w4, [x2, #-3]
      +0x98: sturb   w12, [x2, #-2]
      +0x9c: sturb   w11, [x2, #-1]
      +0xa0: cmp     x15, x2
      +0xa4: b.ne    <mldsa44_polyz_pack+0x24>
      +0xa8: add     x1, x0, #0x200
      +0xac: stp     w3, w9, [sp, #24]
      +0xb0: stp     w8, w7, [sp, #32]
      +0xb4: sturh   w3, [x1, #55]
      +0xb8: mov     x1, #0x10
      +0xbc: strb    w6, [x0, #569]
      +0xc0: strb    w14, [x0, #570]
      +0xc4: strb    w5, [x0, #571]
      +0xc8: strb    w13, [x0, #572]
      +0xcc: strb    w4, [x0, #573]
      +0xd0: strb    w12, [x0, #574]
      +0xd4: strb    w11, [x0, #575]
      +0xd8: add     x0, sp, #0x18
      +0xdc: bl      <mld_zeroize_1>
      +0xe0: adrp    x0, <page>
      +0xe4: ldr     x0, [x0, #4088]
      +0xe8: ldr     x2, [sp, #40]
      +0xec: ldr     x1, [x0]
      +0xf0: subs    x2, x2, x1
      +0xf4: mov     x1, #0x0
      +0xf8: b.eq    <mldsa44_polyz_pack+0x100>
      +0xfc: bl      <stack_chk_fail>
     +0x100: ldr     x30, [sp], #48
     +0x104: ret
 ***)

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa44_polyz_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, with the combined contract for memset of                     *)
(* utils/mlkem_native_libc_full.ml, which mld_zeroize needs: the memory      *)
(* (ea,el) that memset reads and keeps must not overlap the output or the    *)
(* stack frame, which includes that of mld_zeroize.                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !r a x guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(r,576); (word_sub stackpointer (word 64),64)] /\
          ALLPAIRS nonoverlapping
           [(r,576); (word_sub stackpointer (word 64),64)]
           [(a,1024); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_polyz_pack) /\
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
                    (!j. j < 576
                         ==> read(memory :> bytes8(word_add r (word j))) s =
                             mld_polyz_pack_17 x j))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r,576);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYZ_PACK_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* input, the output, the stack frame, the GOT entries of the stack guard    *)
(* and of memset, the guard and (ea,el), and the writes within the output    *)
(* and the stack frame.                                                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e r a x guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(r,576); (word_sub stackpointer (word 64),64)] /\
          ALLPAIRS nonoverlapping
           [(r,576); (word_sub stackpointer (word 64),64)]
           [(a,1024); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_polyz_pack) /\
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
                    (!j. j < 576
                         ==> read(memory :> bytes8(word_add r (word j))) s =
                             mld_polyz_pack_17 x j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events r a guard mf pc
                              (word_sub stackpointer (word 64))
                              returnaddress /\
                       memaccess_inbounds e2
                        [a,1024; r,576; word_sub stackpointer (word 64),64;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el]
                        [r,576; word_sub stackpointer (word 64),64]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r,576);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYZ_PACK_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e r a guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(r,576); (word_sub stackpointer (word 64),64)] /\
          ALLPAIRS nonoverlapping
           [(r,576); (word_sub stackpointer (word 64),64)]
           [(a,1024); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa44_polyz_pack) /\
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
                        [a,1024; r,576; word_sub stackpointer (word 64),64;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el]
                        [r,576; word_sub stackpointer (word 64),64]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r,576);
                  memory :> bytes(word_sub stackpointer (word 64),64)])`;;

let MLDSA_NATIVE_POLYZ_PACK_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYZ_PACK_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
