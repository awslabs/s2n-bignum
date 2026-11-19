(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 of up to three inputs: the statement. This is the code for       *)
(* mld_H44 (mld_H in sign.c, for ML-DSA-44) from mldsa-native's portable C   *)
(* implementation compiled by gcc 12 with -Os (see mldsa_native/README.md),  *)
(* which initializes a context on its stack, absorbs in1, and in2 and in3    *)
(* unless their lengths are zero, finalizes, squeezes outlen bytes and       *)
(* releases the context, by calls of mldsa_shake256_init, _absorb,           *)
(* _finalize, _squeeze and _release, and then zeroes the context with        *)
(* mld_zeroize2, a call of memset. It is verified in the whole image (see    *)
(* libmldsa.ml) against mld_shake256_byte of common/mldsa_native_fips202.ml  *)
(* for the concatenation of the three inputs, with the contract              *)
(* memset_full_contract of utils/mlkem_native_libc_full.ml for memset; the   *)
(* inputs and the output may overlap, and a pointer with a zero length may   *)
(* be anything (NULL). The stack is the 304 bytes of the function and the    *)
(* 304 used by absorbing or squeezing below them; the address of the stack   *)
(* guard and that of memset are read from the GOT. It is also shown to be    *)
(* constant time and memory safe.                                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_absorb.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256_absorb_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256_finalize_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256_squeeze_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256_release_spec.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/zeroize_2_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mld_H44:
       +0x0: stp     x19, x20, [sp, #-304]!
       +0x4: mov     x20, x7
       +0x8: stp     x21, x22, [sp, #16]
       +0xc: mov     x22, x0
      +0x10: add     x19, sp, #0x58
      +0x14: adrp    x0, <page>
      +0x18: ldr     x0, [x0, #4088]
      +0x1c: stp     x23, x24, [sp, #32]
      +0x20: mov     x23, x1
      +0x24: stp     x25, x26, [sp, #48]
      +0x28: mov     x21, x5
      +0x2c: mov     x26, x2
      +0x30: stp     x27, x30, [sp, #64]
      +0x34: mov     x25, x4
      +0x38: mov     x27, x3
      +0x3c: ldr     x1, [x0]
      +0x40: str     x1, [sp, #296]
      +0x44: mov     x1, #0x0
      +0x48: mov     x24, x6
      +0x4c: mov     x0, x19
      +0x50: bl      <mldsa_shake256_init>
      +0x54: mov     x2, x27
      +0x58: mov     x1, x26
      +0x5c: mov     x0, x19
      +0x60: bl      <mldsa_shake256_absorb>
      +0x64: cbz     x21, <mld_H44+0x78>
      +0x68: mov     x2, x21
      +0x6c: mov     x1, x25
      +0x70: mov     x0, x19
      +0x74: bl      <mldsa_shake256_absorb>
      +0x78: cbz     x20, <mld_H44+0x8c>
      +0x7c: mov     x2, x20
      +0x80: mov     x1, x24
      +0x84: mov     x0, x19
      +0x88: bl      <mldsa_shake256_absorb>
      +0x8c: mov     x0, x19
      +0x90: bl      <mldsa_shake256_finalize>
      +0x94: mov     x2, x19
      +0x98: mov     x1, x23
      +0x9c: mov     x0, x22
      +0xa0: bl      <mldsa_shake256_squeeze>
      +0xa4: mov     x0, x19
      +0xa8: bl      <mldsa_shake256_release>
      +0xac: mov     x0, x19
      +0xb0: mov     x1, #0xd0
      +0xb4: bl      <mld_zeroize_2>
      +0xb8: adrp    x0, <page>
      +0xbc: ldr     x0, [x0, #4088]
      +0xc0: ldr     x2, [sp, #296]
      +0xc4: ldr     x1, [x0]
      +0xc8: subs    x2, x2, x1
      +0xcc: mov     x1, #0x0
      +0xd0: b.eq    <mld_H44+0xd8>
      +0xd4: bl      <stack_chk_fail>
      +0xd8: ldp     x21, x22, [sp, #16]
      +0xdc: ldp     x23, x24, [sp, #32]
      +0xe0: ldp     x25, x26, [sp, #48]
      +0xe4: ldp     x27, x30, [sp, #64]
      +0xe8: ldp     x19, x20, [sp], #304
      +0xec: ret
 ***)

let MLDSA_NATIVE_H_44_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mld_H44"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The output is SHAKE256 of in1 || in2 || in3, the bytes M1,   *)
(* M2 and M3 as numbers.                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf ea el ev.
   memset_full_contract mf ea el ev
   ==> !out outlen in1 in1len in2 in2len in3 in3len M1 M2 M3 guard pc
        stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 608),608))
         [(out,outlen); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 608),608)]
         [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mld_H44) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; in1; word in1len; in2;
                               word in2len; in3; word in3len] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(in1,in1len)) s = M1 /\
                  read (memory :> bytes(in2,in2len)) s = M2 /\
                  read (memory :> bytes(in3,in3len)) s = M3)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist
                   (list_of_seq
                     (mld_shake256_byte (in1len + in2len + in3len)
                       (M1 + 2 EXP (8 * in1len) *
                             (M2 + 2 EXP (8 * in2len) * M3)))
                     outlen))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 608),608)])`;;

let MLDSA_NATIVE_H_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_H_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the lengths only (which give   *)
(* the calls and their arguments), with all accesses within the output, the  *)
(* inputs, the stack, the GOT entry of the stack guard, the guard and the    *)
(* round constants of the permutation, and the writes within the output and  *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf ea el ev.
   memset_full_contract mf ea el ev
   ==> exists f_events.
     forall e out outlen in1 in1len in2 in2len in3 in3len M1 M2 M3 guard pc
            stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 608),608))
         [(out,outlen); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 608),608)]
         [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mld_H44) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; in1; word in1len; in2;
                               word in2len; in3; word in3len] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(in1,in1len)) s = M1 /\
                  read (memory :> bytes(in2,in2len)) s = M2 /\
                  read (memory :> bytes(in3,in3len)) s = M3 /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist
                   (list_of_seq
                     (mld_shake256_byte (in1len + in2len + in3len)
                       (M1 + 2 EXP (8 * in1len) *
                             (M2 + 2 EXP (8 * in2len) * M3)))
                     outlen) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out outlen in1 in1len in2 in2len in3 in3len
                                 guard mf pc
                                 (word_sub stackpointer (word 608))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,outlen; in1,in1len; in2,in2len; in3,in3len;
                       word_sub stackpointer (word 608),608;
                       word(pc + got_stack_chk_guard),8; guard,8;
                       word(pc + got_memset),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [out,outlen; word_sub stackpointer (word 608),608]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 608),608)])`;;

let MLDSA_NATIVE_H_44_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_H_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf ea el ev.
   memset_full_contract mf ea el ev
   ==> exists f_events.
     forall e out outlen in1 in1len in2 in2len in3 in3len guard pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 608),608))
         [(out,outlen); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 608),608)]
         [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
          (guard,8); (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + mld_H44) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; in1; word in1len; in2;
                               word in2len; in3; word in3len] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out outlen in1 in1len in2 in2len in3 in3len
                                 guard mf pc
                                 (word_sub stackpointer (word 608))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,outlen; in1,in1len; in2,in2len; in3,in3len;
                       word_sub stackpointer (word 608),608;
                       word(pc + got_stack_chk_guard),8; guard,8;
                       word(pc + got_memset),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [out,outlen; word_sub stackpointer (word 608),608]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 608),608)])`;;

let MLDSA_NATIVE_H_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_H_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
