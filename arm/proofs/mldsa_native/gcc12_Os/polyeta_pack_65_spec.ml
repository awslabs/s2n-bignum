(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 4 bits per coefficient, of 4 - a: the        *)
(* statement. This is the code for mldsa65_polyeta_pack (mld_polyeta_pack in *)
(* poly_kl.c with MLDSA_ETA = 4, for ML-DSA-65) from mldsa-native's portable *)
(* C implementation compiled by gcc 12 with -Os (see                         *)
(* mldsa_native/README.md), which writes a byte for each 2 coefficients,     *)
(* with a stack protector. It keeps the last 2 coefficients in a temporary   *)
(* array on its stack, zeroes it with mld_zeroize_3, which calls memset, and *)
(* checks the stack guard before it returns. It is verified in the whole     *)
(* image (see libmldsa.ml) against mld_polyeta_pack_4 of                     *)
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

    mldsa65_polyeta_pack:
       +0x0: adrp    x2, <page>
       +0x4: ldr     x2, [x2, #4088]
       +0x8: str     x30, [sp, #-32]!
       +0xc: mov     x4, #0x0
      +0x10: mov     w5, #0x4
      +0x14: ldr     x3, [x2]
      +0x18: str     x3, [sp, #24]
      +0x1c: mov     x3, #0x0
      +0x20: ldp     w3, w2, [x1]
      +0x24: add     x1, x1, #0x8
      +0x28: sub     w2, w5, w2
      +0x2c: sub     w3, w5, w3
      +0x30: and     w3, w3, #0xff
      +0x34: and     w6, w2, #0xff
      +0x38: ubfiz   w2, w2, #4, #8
      +0x3c: orr     w2, w3, w2
      +0x40: strb    w2, [x0, x4]
      +0x44: add     x4, x4, #0x1
      +0x48: cmp     x4, #0x80
      +0x4c: b.ne    <mldsa65_polyeta_pack+0x20>
      +0x50: add     x0, sp, #0x10
      +0x54: mov     x1, #0x8
      +0x58: strb    w3, [sp, #16]
      +0x5c: strb    w6, [sp, #17]
      +0x60: bl      <mld_zeroize_3>
      +0x64: adrp    x0, <page>
      +0x68: ldr     x0, [x0, #4088]
      +0x6c: ldr     x2, [sp, #24]
      +0x70: ldr     x1, [x0]
      +0x74: subs    x2, x2, x1
      +0x78: mov     x1, #0x0
      +0x7c: b.eq    <mldsa65_polyeta_pack+0x84>
      +0x80: bl      <stack_chk_fail>
      +0x84: ldr     x30, [sp], #32
      +0x88: ret
 ***)

let MLDSA_NATIVE_POLYETA_PACK_65_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa65_polyeta_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, with the combined contract for memset of                     *)
(* utils/mlkem_native_libc_full.ml, which mld_zeroize needs: the memory      *)
(* (ea,el) that memset reads and keeps must not overlap the output or the    *)
(* stack frame, which includes that of mld_zeroize.                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !r a x guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(r,128); (word_sub stackpointer (word 48),48)] /\
          ALLPAIRS nonoverlapping
           [(r,128); (word_sub stackpointer (word 48),48)]
           [(a,1024); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa65_polyeta_pack) /\
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
                    (!j. j < 128
                         ==> read(memory :> bytes8(word_add r (word j))) s =
                             mld_polyeta_pack_4 x j))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r,128);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYETA_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYETA_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* input, the output, the stack frame, the GOT entries of the stack guard    *)
(* and of memset, the guard and (ea,el), and the writes within the output    *)
(* and the stack frame.                                                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e r a x guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(r,128); (word_sub stackpointer (word 48),48)] /\
          ALLPAIRS nonoverlapping
           [(r,128); (word_sub stackpointer (word 48),48)]
           [(a,1024); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa65_polyeta_pack) /\
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
                    (!j. j < 128
                         ==> read(memory :> bytes8(word_add r (word j))) s =
                             mld_polyeta_pack_4 x j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events r a guard mf pc
                              (word_sub stackpointer (word 48))
                              returnaddress /\
                       memaccess_inbounds e2
                        [a,1024; r,128; word_sub stackpointer (word 48),48;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el]
                        [r,128; word_sub stackpointer (word 48),48]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r,128);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYETA_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYETA_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e r a guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(r,128); (word_sub stackpointer (word 48),48)] /\
          ALLPAIRS nonoverlapping
           [(r,128); (word_sub stackpointer (word 48),48)]
           [(a,1024); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa65_polyeta_pack) /\
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
                              (word_sub stackpointer (word 48))
                              returnaddress /\
                       memaccess_inbounds e2
                        [a,1024; r,128; word_sub stackpointer (word 48),48;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el]
                        [r,128; word_sub stackpointer (word 48),48]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r,128);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYETA_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYETA_PACK_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
