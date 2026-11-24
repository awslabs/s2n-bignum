(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 3 bits per coefficient, of 2 - a: the        *)
(* statement. This is the code for mldsa87_polyeta_pack (mld_polyeta_pack in *)
(* poly_kl.c with MLDSA_ETA = 2, for ML-DSA-87) from mldsa-native's portable *)
(* C implementation compiled by gcc 12 with -Os (see                         *)
(* mldsa_native/README.md), which writes 3 bytes for each 8 coefficients,    *)
(* with a stack protector. It keeps the last 8 bytes in a temporary array on *)
(* its stack, zeroes it with mld_zeroize_5, which calls memset, and checks   *)
(* the stack guard before it returns. It is verified in the whole image (see *)
(* libmldsa.ml) against mld_polyeta_pack_2 of                                *)
(* common/mldsa_native_packing.ml, byte by byte, with the theorem for        *)
(* mld_zeroize_5 and the contract memset_full_contract of                    *)
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

    mldsa87_polyeta_pack:
       +0x0: adrp    x2, <page>
       +0x4: ldr     x2, [x2, #4088]
       +0x8: stp     x19, x30, [sp, #-32]!
       +0xc: mov     x8, x0
      +0x10: ldr     x3, [x2]
      +0x14: str     x3, [sp, #24]
      +0x18: mov     x3, #0x0
      +0x1c: add     x14, x1, #0x400
      +0x20: mov     w6, #0x2
      +0x24: ldp     w5, w2, [x1, #8]
      +0x28: add     x8, x8, #0x3
      +0x2c: ldp     w30, w17, [x1, #16]
      +0x30: sub     w2, w6, w2
      +0x34: ldp     w7, w3, [x1]
      +0x38: sub     w30, w6, w30
      +0x3c: ldp     w4, w18, [x1, #24]
      +0x40: sub     w5, w6, w5
      +0x44: sub     w17, w6, w17
      +0x48: sub     w3, w6, w3
      +0x4c: sub     w4, w6, w4
      +0x50: sub     w18, w6, w18
      +0x54: sub     w7, w6, w7
      +0x58: and     w16, w2, #0xff
      +0x5c: and     w12, w30, #0xff
      +0x60: ubfiz   w2, w2, #1, #8
      +0x64: ubfiz   w30, w30, #4, #8
      +0x68: ubfiz   w19, w5, #6, #8
      +0x6c: orr     w2, w2, w30
      +0x70: and     w15, w3, #0xff
      +0x74: ubfiz   w30, w17, #7, #8
      +0x78: and     w13, w5, #0xff
      +0x7c: and     w10, w4, #0xff
      +0x80: and     w9, w18, #0xff
      +0x84: ubfiz   w3, w3, #3, #8
      +0x88: ubfx    x5, x5, #2, #6
      +0x8c: ubfiz   w4, w4, #2, #8
      +0x90: ubfiz   w18, w18, #5, #8
      +0x94: sxtb    w7, w7
      +0x98: and     w11, w17, #0xff
      +0x9c: orr     w3, w3, w19
      +0xa0: orr     w5, w5, w30
      +0xa4: orr     w4, w4, w18
      +0xa8: ubfx    x17, x17, #1, #7
      +0xac: orr     w3, w7, w3
      +0xb0: orr     w2, w2, w5
      +0xb4: orr     w4, w4, w17
      +0xb8: and     w3, w3, #0xff
      +0xbc: and     w2, w2, #0xff
      +0xc0: and     w4, w4, #0xff
      +0xc4: add     x1, x1, #0x20
      +0xc8: sturb   w3, [x8, #-3]
      +0xcc: sturb   w2, [x8, #-2]
      +0xd0: sturb   w4, [x8, #-1]
      +0xd4: cmp     x14, x1
      +0xd8: b.ne    <mldsa87_polyeta_pack+0x24>
      +0xdc: strb    w3, [x0, #93]
      +0xe0: mov     x1, #0x8
      +0xe4: strb    w2, [x0, #94]
      +0xe8: strb    w4, [x0, #95]
      +0xec: add     x0, sp, #0x10
      +0xf0: strb    w7, [sp, #16]
      +0xf4: strb    w15, [sp, #17]
      +0xf8: strb    w13, [sp, #18]
      +0xfc: strb    w16, [sp, #19]
     +0x100: strb    w12, [sp, #20]
     +0x104: strb    w11, [sp, #21]
     +0x108: strb    w10, [sp, #22]
     +0x10c: strb    w9, [sp, #23]
     +0x110: bl      <mld_zeroize_5>
     +0x114: adrp    x0, <page>
     +0x118: ldr     x0, [x0, #4088]
     +0x11c: ldr     x2, [sp, #24]
     +0x120: ldr     x1, [x0]
     +0x124: subs    x2, x2, x1
     +0x128: mov     x1, #0x0
     +0x12c: b.eq    <mldsa87_polyeta_pack+0x134>
     +0x130: bl      <stack_chk_fail>
     +0x134: ldp     x19, x30, [sp], #32
     +0x138: ret
 ***)

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa87_polyeta_pack"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, with the combined contract for memset of                     *)
(* utils/mlkem_native_libc_full.ml, which mld_zeroize needs: the memory      *)
(* (ea,el) that memset reads and keeps must not overlap the output or the    *)
(* stack frame, which includes that of mld_zeroize.                          *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !r a x guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(r,96); (word_sub stackpointer (word 48),48)] /\
          ALLPAIRS nonoverlapping
           [(r,96); (word_sub stackpointer (word 48),48)]
           [(a,1024); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa87_polyeta_pack) /\
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
                    (!j. j < 96
                         ==> read(memory :> bytes8(word_add r (word j))) s =
                             mld_polyeta_pack_2 x j))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r,96);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYETA_PACK_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* input, the output, the stack frame, the GOT entries of the stack guard    *)
(* and of memset, the guard and (ea,el), and the writes within the output    *)
(* and the stack frame.                                                      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e r a x guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(r,96); (word_sub stackpointer (word 48),48)] /\
          ALLPAIRS nonoverlapping
           [(r,96); (word_sub stackpointer (word 48),48)]
           [(a,1024); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa87_polyeta_pack) /\
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
                    (!j. j < 96
                         ==> read(memory :> bytes8(word_add r (word j))) s =
                             mld_polyeta_pack_2 x j) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events r a guard mf pc
                              (word_sub stackpointer (word 48))
                              returnaddress /\
                       memaccess_inbounds e2
                        [a,1024; r,96; word_sub stackpointer (word 48),48;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el]
                        [r,96; word_sub stackpointer (word 48),48]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r,96);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYETA_PACK_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e r a guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          PAIRWISE nonoverlapping
           [(r,96); (word_sub stackpointer (word 48),48)] /\
          ALLPAIRS nonoverlapping
           [(r,96); (word_sub stackpointer (word 48),48)]
           [(a,1024); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa87_polyeta_pack) /\
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
                        [a,1024; r,96; word_sub stackpointer (word 48),48;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el]
                        [r,96; word_sub stackpointer (word 48),48]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(r,96);
                  memory :> bytes(word_sub stackpointer (word 48),48)])`;;

let MLDSA_NATIVE_POLYETA_PACK_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYETA_PACK_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
