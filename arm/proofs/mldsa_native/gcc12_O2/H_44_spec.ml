(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 of up to three inputs: the statement. This is the code for       *)
(* mld_H44 (mld_H in sign.c, for ML-DSA-44) from mldsa-native's portable C   *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which initializes a context on its stack, absorbs in1, and in2 and in3    *)
(* unless their lengths are zero, finalizes, squeezes outlen bytes and       *)
(* releases the context, by calls of mldsa_shake256_init, _absorb,           *)
(* _finalize, _squeeze and _release, and then zeroes the context with        *)
(* inlined stores. It is verified in the whole image (see libmldsa.ml)       *)
(* against mld_shake256_byte of common/mldsa_native_fips202.ml for the       *)
(* concatenation of the three inputs; the inputs and the output may overlap, *)
(* and a pointer with a zero length may be anything (NULL). The stack is the *)
(* 304 bytes of the function and the 256 used by absorbing or squeezing      *)
(* below them; the address of the stack guard is read from the GOT. It is    *)
(* also shown to be constant time and memory safe.                           *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_absorb.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_absorb_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_finalize_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_squeeze_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake256_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mld_H44:
       +0x0: stp     x19, x20, [sp, #-304]!
       +0x4: mov     x20, x7
       +0x8: adrp    x8, <page>
       +0xc: ldr     x8, [x8, #4088]
      +0x10: stp     x21, x22, [sp, #16]
      +0x14: add     x19, sp, #0x58
      +0x18: stp     x23, x24, [sp, #32]
      +0x1c: mov     x22, x0
      +0x20: mov     x24, x2
      +0x24: stp     x25, x26, [sp, #48]
      +0x28: mov     x23, x1
      +0x2c: mov     x25, x3
      +0x30: stp     x27, x30, [sp, #64]
      +0x34: mov     x21, x5
      +0x38: mov     x26, x4
      +0x3c: ldr     x0, [x8]
      +0x40: str     x0, [sp, #296]
      +0x44: mov     x0, #0x0
      +0x48: mov     x27, x6
      +0x4c: mov     x0, x19
      +0x50: bl      <mldsa_shake256_init>
      +0x54: mov     x2, x25
      +0x58: mov     x1, x24
      +0x5c: mov     x0, x19
      +0x60: bl      <mldsa_shake256_absorb>
      +0x64: cbnz    x21, <mld_H44+0xe0>
      +0x68: cbnz    x20, <mld_H44+0xf4>
      +0x6c: mov     x0, x19
      +0x70: bl      <mldsa_shake256_finalize>
      +0x74: mov     x2, x19
      +0x78: mov     x1, x23
      +0x7c: mov     x0, x22
      +0x80: bl      <mldsa_shake256_squeeze>
      +0x84: mov     x0, x19
      +0x88: bl      <mldsa_shake256_release>
      +0x8c: movi    v0.4s, #0x0
      +0x90: stp     q0, q0, [x19]
      +0x94: stp     q0, q0, [x19, #32]
      +0x98: stp     q0, q0, [x19, #64]
      +0x9c: stp     q0, q0, [x19, #96]
      +0xa0: stp     q0, q0, [x19, #128]
      +0xa4: stp     q0, q0, [x19, #160]
      +0xa8: str     q0, [x19, #192]
      +0xac: adrp    x0, <page>
      +0xb0: ldr     x0, [x0, #4088]
      +0xb4: ldr     x2, [sp, #296]
      +0xb8: ldr     x1, [x0]
      +0xbc: subs    x2, x2, x1
      +0xc0: mov     x1, #0x0
      +0xc4: b.ne    <mld_H44+0x108>
      +0xc8: ldp     x21, x22, [sp, #16]
      +0xcc: ldp     x23, x24, [sp, #32]
      +0xd0: ldp     x25, x26, [sp, #48]
      +0xd4: ldp     x27, x30, [sp, #64]
      +0xd8: ldp     x19, x20, [sp], #304
      +0xdc: ret
      +0xe0: mov     x2, x21
      +0xe4: mov     x1, x26
      +0xe8: mov     x0, x19
      +0xec: bl      <mldsa_shake256_absorb>
      +0xf0: cbz     x20, <mld_H44+0x6c>
      +0xf4: mov     x2, x20
      +0xf8: mov     x1, x27
      +0xfc: mov     x0, x19
     +0x100: bl      <mldsa_shake256_absorb>
     +0x104: b       <mld_H44+0x6c>
     +0x108: bl      <__stack_chk_fail@plt>
 ***)

let MLDSA_NATIVE_H_44_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mld_H44"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The output is SHAKE256 of in1 || in2 || in3, the bytes M1,   *)
(* M2 and M3 as numbers.                                                     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!out outlen in1 in1len in2 in2len in3 in3len M1 M2 M3 guard pc stackpointer
   returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 560),560))
         [(out,outlen); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 560),560)]
         [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mld_H44) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; in1; word in1len; in2;
                               word in2len; in3; word in3len] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
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
                memory :> bytes(word_sub stackpointer (word 560),560)])`;;

let MLDSA_NATIVE_H_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_H_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the lengths only (which give   *)
(* the calls and their arguments), with all accesses within the output, the  *)
(* inputs, the stack, the GOT entry of the stack guard, the guard and the    *)
(* round constants of the permutation, and the writes within the output and  *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e out outlen in1 in1len in2 in2len in3 in3len M1 M2 M3 guard pc
            stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 560),560))
         [(out,outlen); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 560),560)]
         [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mld_H44) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; in1; word in1len; in2;
                               word in2len; in3; word in3len] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
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
                                 guard pc (word_sub stackpointer (word 560))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,outlen; in1,in1len; in2,in2len; in3,in3len;
                       word_sub stackpointer (word 560),560;
                       word(pc + got_stack_chk_guard),8; guard,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [out,outlen; word_sub stackpointer (word 560),560]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 560),560)])`;;

let MLDSA_NATIVE_H_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_H_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e out outlen in1 in1len in2 in2len in3 in3len guard pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        ALL (nonoverlapping (word_sub stackpointer (word 560),560))
         [(out,outlen); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 560),560)]
         [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mld_H44) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; in1; word in1len; in2;
                               word in2len; in3; word in3len] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out outlen in1 in1len in2 in2len in3 in3len
                                 guard pc (word_sub stackpointer (word 560))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,outlen; in1,in1len; in2,in2len; in3,in3len;
                       word_sub stackpointer (word 560),560;
                       word(pc + got_stack_chk_guard),8; guard,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [out,outlen; word_sub stackpointer (word 560),560]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 560),560)])`;;

let MLDSA_NATIVE_H_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_H_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
