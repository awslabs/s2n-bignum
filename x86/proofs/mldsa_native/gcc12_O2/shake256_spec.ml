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
(* as the input is read before the output is written. The stack is the 248   *)
(* bytes of the function, the return address of the calls and the 320 bytes  *)
(* used by absorbing or squeezing below them. Initializing and zeroing the   *)
(* context use REP STOSQ, so the direction flag must be clear, as the ABI    *)
(* requires on entry. It is also shown to be constant time and memory safe.  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_keccak.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_init_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_absorb_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_finalize_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_squeeze_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_release_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_shake256:
       +0x0  push    r14
       +0x2  mov     r14, rcx
       +0x5  push    r13
       +0x7  mov     r13, rdx
       +0xa  push    r12
       +0xc  mov     r12, rsi
       +0xf  push    rbp
      +0x10  mov     rbp, rdi
      +0x13  push    rbx
      +0x14  sub     rsp, 0xd0
      +0x1b  mov     rbx, rsp
      +0x1e  mov     rdi, rbx
      +0x21  call    mldsa_shake256_init
     after_mldsa_shake256_init:
      +0x26  mov     rdx, r14
      +0x29  mov     rsi, r13
      +0x2c  mov     rdi, rbx
      +0x2f  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb:
      +0x34  mov     rdi, rbx
      +0x37  call    mldsa_shake256_finalize
     after_mldsa_shake256_finalize:
      +0x3c  mov     rdx, rbx
      +0x3f  mov     rsi, r12
      +0x42  mov     rdi, rbp
      +0x45  call    mldsa_shake256_squeeze
     after_mldsa_shake256_squeeze:
      +0x4a  mov     rdi, rbx
      +0x4d  call    mldsa_shake256_release
     after_mldsa_shake256_release:
      +0x52  add     rsp, 0xd0
      +0x59  pop     rbx
      +0x5a  pop     rbp
      +0x5b  pop     r12
      +0x5d  pop     r13
      +0x5f  pop     r14
     ret:
      +0x61  ret
 ***)

let MLDSA_NATIVE_SHAKE256_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_shake256"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!out outlen src inlen M pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (out,outlen))
            [(word_sub stackpointer (word 576),576); (stackpointer,8)] /\
        nonoverlapping (src,inlen) (word_sub stackpointer (word 576),576) /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 576),576)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_shake256) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; src; word inlen] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(src,inlen)) s = M)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist
                   (list_of_seq (mld_shake256_byte inlen M) outlen))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 576),576)])`;;

let MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the lengths only, with all     *)
(* accesses within the output, the input, the stack, the slot of the return  *)
(* address and the round constants of the permutation, and the writes within *)
(* the output and the stack.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e out outlen src inlen M pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (out,outlen))
            [(word_sub stackpointer (word 576),576); (stackpointer,8)] /\
        nonoverlapping (src,inlen) (word_sub stackpointer (word 576),576) /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 576),576)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_shake256) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; src; word inlen] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(src,inlen)) s = M /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist
                   (list_of_seq (mld_shake256_byte inlen M) outlen) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out outlen src inlen pc
                                 (word_sub stackpointer (word 576))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,outlen; src,inlen;
                       word_sub stackpointer (word 576),576; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [out,outlen; word_sub stackpointer (word 576),576]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 576),576)])`;;

let MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e out outlen src inlen pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (out,outlen))
            [(word_sub stackpointer (word 576),576); (stackpointer,8)] /\
        nonoverlapping (src,inlen) (word_sub stackpointer (word 576),576) /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 576),576)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_shake256) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; src; word inlen] s /\
                  (read DF s <=> false) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out outlen src inlen pc
                                 (word_sub stackpointer (word 576))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,outlen; src,inlen;
                       word_sub stackpointer (word 576),576; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [out,outlen; word_sub stackpointer (word 576),576]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 576),576)])`;;

let MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
