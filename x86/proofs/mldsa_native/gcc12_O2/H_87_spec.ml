(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 of up to three inputs: the statement. This is the code for       *)
(* mld_H87 (mld_H in sign.c, for ML-DSA-87) from mldsa-native's portable C   *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* where the output length is fixed at 64 bytes: all the calls in ML-DSA-87  *)
(* have outlen = 64 (the lengths of tr, mu, rhoprime and the challenge), so  *)
(* the compiler has dropped the argument. It initializes a context on its    *)
(* stack, absorbs in1, and in2 and in3 unless their lengths are zero,        *)
(* finalizes, squeezes 64 bytes and releases the context, by calls of        *)
(* mldsa_shake256_init, _absorb, _finalize, _squeeze and _release, and then  *)
(* zeroes the context with a memset that gcc inlines with REP STOSQ, so the  *)
(* direction flag must be clear, as the ABI requires on entry. It is         *)
(* verified in the whole image (see libmldsa.ml) against mld_shake256_byte   *)
(* of common/mldsa_native_fips202.ml for the concatenation of the three      *)
(* inputs; the inputs and the output may overlap, and a pointer with a zero  *)
(* length may be anything (NULL). It is also shown to be constant time and   *)
(* memory safe.                                                              *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_init_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_absorb_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_finalize_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_squeeze_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_release_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mld_H87:
       +0x0  push    r15
       +0x2  mov     r15, r8
       +0x5  push    r14
       +0x7  mov     r14, rcx
       +0xa  push    r13
       +0xc  mov     r13, r9
       +0xf  push    r12
      +0x11  mov     r12, rsi
      +0x14  push    rbp
      +0x15  mov     rbp, rdi
      +0x18  push    rbx
      +0x19  sub     rsp, 0xe8
      +0x20  lea     rbx, [rsp+0x10]
      +0x25  mov     QWORD PTR [rsp+0x8], rdx
      +0x2a  mov     rdi, rbx
      +0x2d  call    mldsa_shake256_init
     after_mldsa_shake256_init:
      +0x32  mov     rdx, QWORD PTR [rsp+0x8]
      +0x37  mov     rsi, r12
      +0x3a  mov     rdi, rbx
      +0x3d  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_1:
      +0x42  test    r15, r15
      +0x45  jne     join2
      +0x47  cmp     QWORD PTR [rsp+0x120], 0x0
      +0x50  jne     join3
     join1:
      +0x52  mov     rdi, rbx
      +0x55  call    mldsa_shake256_finalize
     after_mldsa_shake256_finalize:
      +0x5a  mov     rdx, rbx
      +0x5d  mov     esi, 0x40
      +0x62  mov     rdi, rbp
      +0x65  call    mldsa_shake256_squeeze
     after_mldsa_shake256_squeeze:
      +0x6a  mov     rdi, rbx
      +0x6d  call    mldsa_shake256_release
     after_mldsa_shake256_release:
      +0x72  xor     eax, eax
      +0x74  mov     rdi, rbx
      +0x77  mov     ecx, 0x1a
      +0x7c  rep stos QWORD PTR es:[rdi], rax
      +0x7f  add     rsp, 0xe8
      +0x86  pop     rbx
      +0x87  pop     rbp
      +0x88  pop     r12
      +0x8a  pop     r13
      +0x8c  pop     r14
      +0x8e  pop     r15
     ret:
      +0x90  ret
      +0x91  nop     DWORD PTR [rax+0x0]
     join2:
      +0x98  mov     rdx, r15
      +0x9b  mov     rsi, r14
      +0x9e  mov     rdi, rbx
      +0xa1  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_2:
      +0xa6  cmp     QWORD PTR [rsp+0x120], 0x0
      +0xaf  je      join1
     join3:
      +0xb1  mov     rdx, QWORD PTR [rsp+0x120]
      +0xb9  mov     rsi, r13
      +0xbc  mov     rdi, rbx
      +0xbf  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb_3:
      +0xc4  jmp     join1
 ***)

let MLDSA_NATIVE_H_87_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mld_H87"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The output is SHAKE256 of in1 || in2 || in3, the bytes M1,   *)
(* M2 and M3 as numbers. The last argument, in3len, is on the stack above    *)
(* the return address. The function saves six registers below the return     *)
(* address and reserves 232 bytes for the context, below which the calls of  *)
(* mldsa_shake256_absorb and mldsa_shake256_squeeze use 328 bytes with their *)
(* return addresses: 608 bytes of stack below the return address in all.     *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!out in1 in1len in2 in2len in3 in3len M1 M2 M3 pc stackpointer
   returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (word_sub stackpointer (word 608),608))
         [(out,64); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        nonoverlapping (out,64) (stackpointer,8) /\
        ALLPAIRS nonoverlapping
         [(out,64); (word_sub stackpointer (word 608),608)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mld_H87) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out; in1; word in1len; in2; word in2len;
                               in3] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  word in3len /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(in1,in1len)) s = M1 /\
                  read (memory :> bytes(in2,in2len)) s = M2 /\
                  read (memory :> bytes(in3,in3len)) s = M3)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(out,64)) s =
                  num_of_bytelist
                   (list_of_seq
                     (mld_shake256_byte (in1len + in2len + in3len)
                       (M1 + 2 EXP (8 * in1len) *
                             (M2 + 2 EXP (8 * in2len) * M3)))
                     64))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(out,64);
                memory :> bytes(word_sub stackpointer (word 608),608)])`;;

let MLDSA_NATIVE_H_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_H_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the lengths only (which give   *)
(* the calls and their arguments), with all accesses within the output, the  *)
(* inputs, the stack, the return address, the arguments on the stack and the *)
(* round constants of the permutation, and the writes within the output and  *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e out in1 in1len in2 in2len in3 in3len M1 M2 M3 pc
            stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (word_sub stackpointer (word 608),608))
         [(out,64); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        nonoverlapping (out,64) (stackpointer,8) /\
        ALLPAIRS nonoverlapping
         [(out,64); (word_sub stackpointer (word 608),608)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mld_H87) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out; in1; word in1len; in2; word in2len;
                               in3] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  word in3len /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(in1,in1len)) s = M1 /\
                  read (memory :> bytes(in2,in2len)) s = M2 /\
                  read (memory :> bytes(in3,in3len)) s = M3 /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(out,64)) s =
                  num_of_bytelist
                   (list_of_seq
                     (mld_shake256_byte (in1len + in2len + in3len)
                       (M1 + 2 EXP (8 * in1len) *
                             (M2 + 2 EXP (8 * in2len) * M3)))
                     64) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out in1 in1len in2 in2len in3 in3len pc
                                 (word_sub stackpointer (word 608))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,64; in1,in1len; in2,in2len; in3,in3len;
                       word_sub stackpointer (word 608),608; stackpointer,8;
                       word_add stackpointer (word 8),8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [out,64; word_sub stackpointer (word 608),608]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(out,64);
                memory :> bytes(word_sub stackpointer (word 608),608)])`;;

let MLDSA_NATIVE_H_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_H_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_H_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e out in1 in1len in2 in2len in3 in3len pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (word_sub stackpointer (word 608),608))
         [(out,64); (in1,in1len); (in2,in2len); (in3,in3len)] /\
        nonoverlapping (out,64) (stackpointer,8) /\
        ALLPAIRS nonoverlapping
         [(out,64); (word_sub stackpointer (word 608),608)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mld_H87) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [out; in1; word in1len; in2; word in2len;
                               in3] s /\
                  read (memory :> bytes64(word_add stackpointer (word 8))) s =
                  word in3len /\
                  (read DF s <=> false) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out in1 in1len in2 in2len in3 in3len pc
                                 (word_sub stackpointer (word 608))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,64; in1,in1len; in2,in2len; in3,in3len;
                       word_sub stackpointer (word 608),608; stackpointer,8;
                       word_add stackpointer (word 8),8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [out,64; word_sub stackpointer (word 608),608]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(out,64);
                memory :> bytes(word_sub stackpointer (word 608),608)])`;;

let MLDSA_NATIVE_H_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_H_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
