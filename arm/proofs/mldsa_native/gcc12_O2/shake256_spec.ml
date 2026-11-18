(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* One-shot SHAKE256: the statement. This is the code for mldsa_shake256     *)
(* (mld_shake256 in fips202.c) from mldsa-native's portable C implementation *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), which absorbs   *)
(* the inlen input bytes into a fresh context on its stack, finalizes it,    *)
(* squeezes outlen bytes and zeroes the context, by calls of                 *)
(* mldsa_shake256_init, _absorb, _finalize, _squeeze and _release. It is     *)
(* verified in the whole image (see libmldsa.ml) against mld_shake256_byte   *)
(* of common/mldsa_native_fips202.ml. The input and the output may overlap,  *)
(* as the input is read before the output is written. The stack is the 272   *)
(* bytes of the function and the 256 used by absorbing or squeezing below    *)
(* them; the address of the stack guard is read from the GOT. It is also     *)
(* shown to be constant time and memory safe.                                *)
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

    mldsa_shake256:
       +0x0: stp     x19, x20, [sp, #-272]!
       +0x4: mov     x20, x0
       +0x8: adrp    x4, 1f000 <page>
       +0xc: ldr     x4, [x4, #4088]
      +0x10: stp     x21, x22, [sp, #16]
      +0x14: add     x19, sp, #0x38
      +0x18: stp     x23, x30, [sp, #32]
      +0x1c: mov     x21, x1
      +0x20: mov     x23, x3
      +0x24: ldr     x0, [x4]
      +0x28: str     x0, [sp, #264]
      +0x2c: mov     x0, #0x0
      +0x30: mov     x22, x2
      +0x34: mov     x0, x19
      +0x38: bl      <mldsa_shake256_init>
      +0x3c: mov     x2, x23
      +0x40: mov     x1, x22
      +0x44: mov     x0, x19
      +0x48: bl      <mldsa_shake256_absorb>
      +0x4c: mov     x0, x19
      +0x50: bl      <mldsa_shake256_finalize>
      +0x54: mov     x2, x19
      +0x58: mov     x1, x21
      +0x5c: mov     x0, x20
      +0x60: bl      <mldsa_shake256_squeeze>
      +0x64: mov     x0, x19
      +0x68: bl      <mldsa_shake256_release>
      +0x6c: adrp    x0, 1f000 <page>
      +0x70: ldr     x0, [x0, #4088]
      +0x74: ldr     x2, [sp, #264]
      +0x78: ldr     x1, [x0]
      +0x7c: subs    x2, x2, x1
      +0x80: mov     x1, #0x0
      +0x84: b.ne    <mldsa_shake256+0x98>
      +0x88: ldp     x21, x22, [sp, #16]
      +0x8c: ldp     x23, x30, [sp, #32]
      +0x90: ldp     x19, x20, [sp], #272
      +0x94: ret
      +0x98: bl      <__stack_chk_fail@plt>
 ***)

let MLDSA_NATIVE_SHAKE256_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_shake256"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!out outlen src inlen M guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (out,outlen) (word_sub stackpointer (word 528),528) /\
        nonoverlapping (src,inlen) (word_sub stackpointer (word 528),528) /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 528),528)]
         [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_shake256) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; src; word inlen] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(src,inlen)) s = M)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist
                   (list_of_seq (mld_shake256_byte inlen M) outlen))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE [memory :> bytes(out,outlen);
                         memory :> bytes(word_sub stackpointer (word 528),528)])`;;

let MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the lengths only, with all     *)
(* accesses within the output, the input, the stack, the GOT entry of the    *)
(* stack guard, the guard and the round constants of the permutation, and    *)
(* the writes within the output and the stack.                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e out outlen src inlen M guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (out,outlen) (word_sub stackpointer (word 528),528) /\
        nonoverlapping (src,inlen) (word_sub stackpointer (word 528),528) /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 528),528)]
         [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_shake256) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; src; word inlen] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(src,inlen)) s = M /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist
                   (list_of_seq (mld_shake256_byte inlen M) outlen) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out outlen src inlen guard pc
                                 (word_sub stackpointer (word 528))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,outlen; src,inlen;
                       word_sub stackpointer (word 528),528;
                       word(pc + got_stack_chk_guard),8; guard,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [out,outlen; word_sub stackpointer (word 528),528]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 528),528)])`;;

let MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e out outlen src inlen guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (out,outlen) (word_sub stackpointer (word 528),528) /\
        nonoverlapping (src,inlen) (word_sub stackpointer (word 528),528) /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 528),528)]
         [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_shake256) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; src; word inlen] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out outlen src inlen guard pc
                                 (word_sub stackpointer (word 528))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,outlen; src,inlen;
                       word_sub stackpointer (word 528),528;
                       word(pc + got_stack_chk_guard),8; guard,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [out,outlen; word_sub stackpointer (word 528),528]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 528),528)])`;;

let MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
