(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The challenge polynomial (SampleInBall): the statement. This is the code  *)
(* for mldsa44_poly_challenge (mld_poly_challenge in poly_kl.c, for          *)
(* ML-DSA-44) from mldsa-native's portable C implementation compiled by gcc  *)
(* 12 with -O2 (see mldsa_native/README.md), which aligns its stack frame to *)
(* 32 bytes, absorbs the seed of 32 bytes into a SHAKE256 context on its     *)
(* stack with mldsa_shake256_init, _absorb and _finalize, squeezes a block   *)
(* of 136 bytes into a buffer, takes the sign bits from its first 8 bytes    *)
(* with a loop, zeroes the polynomial with a memset that gcc inlines with    *)
(* REP STOSQ, and then for i from 256 - 39 to 255 reads bytes j of the       *)
(* buffer, squeezing a new block when it is used up, until j <= i, and sets  *)
(* c[i] = c[j] and c[j] = 1 or -1 by the next sign bit, before releasing the *)
(* context and zeroing the buffer (with REP STOSQ) and the signs. The        *)
(* direction flag must be clear for the REP STOSQ, as the ABI requires on    *)
(* entry. It is verified in the whole image (see libmldsa.ml) against        *)
(* mld_poly_challenge 39 32 of common/mldsa_native_challenge.ml, using the   *)
(* theorems for the callees, and assuming mld_poly_challenge_terminates 39   *)
(* 32, that the SHAKE256 output of the seed has 39 acceptable bytes after    *)
(* its first 8, without which the code does not terminate. It is also shown  *)
(* to be constant time and memory safe, with the events depending on the     *)
(* seed, which is public (c~ is declassified when signing and is part of the *)
(* signature).                                                               *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_challenge.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_init_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_absorb_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_finalize_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_squeeze_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_release_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_poly_challenge:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r15
       +0x6  push    r14
       +0x8  mov     r14, rdi
       +0xb  push    r13
       +0xd  push    r12
       +0xf  push    rbx
      +0x10  mov     rbx, rsi
      +0x13  and     rsp, 0xffffffffffffffe0
      +0x17  sub     rsp, 0x180
      +0x1e  lea     r12, [rsp+0xb0]
      +0x26  mov     rdi, r12
      +0x29  call    mldsa_shake256_init
     after_mldsa_shake256_init:
      +0x2e  mov     rsi, rbx
      +0x31  mov     edx, 0x20
      +0x36  mov     rdi, r12
      +0x39  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb:
      +0x3e  lea     rbx, [rsp+0x20]
      +0x43  mov     rdi, r12
      +0x46  call    mldsa_shake256_finalize
     after_mldsa_shake256_finalize:
      +0x4b  mov     esi, 0x88
      +0x50  mov     rdi, rbx
      +0x53  mov     rdx, r12
      +0x56  call    mldsa_shake256_squeeze
     after_mldsa_shake256_squeeze_1:
      +0x5b  mov     rax, rbx
      +0x5e  lea     rdi, [rsp+0x28]
      +0x63  xor     ecx, ecx
      +0x65  xor     esi, esi
      +0x67  nop     WORD PTR [rax+rax*1+0x0]
     loop1:
      +0x70  movzx   edx, BYTE PTR [rax]
      +0x73  add     rax, 0x1
      +0x77  shl     rdx, cl
      +0x7a  add     ecx, 0x8
      +0x7d  or      rsi, rdx
     loop1_test:
      +0x80  cmp     rax, rdi
     loop1_back:
      +0x83  jne     loop1
     loop1_exit:
      +0x85  lea     rdi, [r14+0x8]
      +0x89  mov     rcx, r14
      +0x8c  xor     eax, eax
      +0x8e  mov     QWORD PTR [rsp+0x18], rsi
      +0x93  and     rdi, 0xfffffffffffffff8
      +0x97  mov     QWORD PTR [r14], 0x0
      +0x9e  mov     r15d, 0xd9
      +0xa4  mov     r13d, 0x1
      +0xaa  mov     QWORD PTR [r14+0x3f8], 0x0
      +0xb5  sub     rcx, rdi
      +0xb8  add     ecx, 0x400
      +0xbe  shr     ecx, 0x3
      +0xc1  rep stos QWORD PTR es:[rdi], rax
      +0xc4  mov     ecx, 0x8
      +0xc9  jmp     join3
      +0xcb  nop     DWORD PTR [rax+rax*1+0x0]
     join1:
      +0xd0  mov     eax, ecx
     join2:
      +0xd2  movzx   edx, BYTE PTR [rsp+rax*1+0x20]
      +0xd7  lea     ecx, [rax+0x1]
      +0xda  cmp     r15d, edx
      +0xdd  jae     join4
     join3:
      +0xdf  cmp     ecx, 0x88
      +0xe5  jne     join1
      +0xe7  mov     rdx, r12
      +0xea  mov     esi, 0x88
      +0xef  mov     rdi, rbx
      +0xf2  call    mldsa_shake256_squeeze
     after_mldsa_shake256_squeeze_2:
      +0xf7  movzx   edx, BYTE PTR [rsp+0x20]
      +0xfc  mov     eax, 0x1
     +0x101  cmp     r15d, edx
     +0x104  jb      join2
     +0x106  mov     ecx, 0x1
     join4:
     +0x10b  mov     eax, DWORD PTR [r14+rdx*4]
     +0x10f  mov     edi, r13d
     +0x112  mov     DWORD PTR [r14+r15*4], eax
     +0x116  mov     rax, QWORD PTR [rsp+0x18]
     +0x11b  add     r15, 0x1
     +0x11f  mov     rsi, rax
     +0x122  shr     rax, 1
     +0x125  and     esi, 0x1
     +0x128  mov     QWORD PTR [rsp+0x18], rax
     +0x12d  add     rsi, rsi
     +0x130  sub     edi, esi
     +0x132  mov     DWORD PTR [r14+rdx*4], edi
     +0x136  cmp     r15, 0x100
     +0x13d  jne     join3
     +0x13f  mov     rdi, r12
     +0x142  call    mldsa_shake256_release
     after_mldsa_shake256_release:
     +0x147  xor     eax, eax
     +0x149  mov     rdi, rbx
     +0x14c  mov     ecx, 0x11
     +0x151  rep stos QWORD PTR es:[rdi], rax
     +0x154  mov     QWORD PTR [rsp+0x18], 0x0
     +0x15d  lea     rax, [rsp+0x18]
     +0x162  lea     rsp, [rbp-0x28]
     +0x166  pop     rbx
     +0x167  pop     r12
     +0x169  pop     r13
     +0x16b  pop     r14
     +0x16d  pop     r15
     +0x16f  pop     rbp
     ret:
     +0x170  ret
 ***)

let MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_poly_challenge"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The seed is the 32 bytes C at seed, and the polynomial at c  *)
(* becomes mld_poly_challenge 39 32 C, if mld_poly_challenge_terminates 39   *)
(* 32 C. The seed may overlap the polynomial, as it is only read before the  *)
(* polynomial is written. The function saves six registers below the return  *)
(* address, aligns the stack pointer down to a multiple of 32, which may     *)
(* lower it by up to 31 bytes, and reserves 384 bytes for the signs, the     *)
(* buffer and the context, below which absorbing and squeezing use 328 bytes *)
(* with their return addresses: 791 bytes of stack below the return address. *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!c seed C pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_poly_challenge_terminates 39 32 C /\
          ALL (nonoverlapping (c,1024))
              [(word_sub stackpointer (word 791),791); (stackpointer,8)] /\
          nonoverlapping (seed,32) (word_sub stackpointer (word 791),791) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 791),791)]
           [(word pc,libmldsa_size)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa44_poly_challenge) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes(seed,32)) s = C)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add c (word(4 * i))))
                               s =
                             mld_poly_challenge 39 32 C i))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 791),791)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the seed C and the stack, with    *)
(* all accesses within the seed, the polynomial, the stack, the slot of the  *)
(* return address and the round constants of Keccak, and the writes within   *)
(* the polynomial and the stack.                                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e c seed C pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_poly_challenge_terminates 39 32 C /\
          ALL (nonoverlapping (c,1024))
              [(word_sub stackpointer (word 791),791); (stackpointer,8)] /\
          nonoverlapping (seed,32) (word_sub stackpointer (word 791),791) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 791),791)]
           [(word pc,libmldsa_size)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa44_poly_challenge) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes(seed,32)) s = C /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add c (word(4 * i))))
                               s =
                             mld_poly_challenge 39 32 C i) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events c seed C pc
                              (word_sub stackpointer (word 791))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; c,1024;
                         word_sub stackpointer (word 791),791; stackpointer,8;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [c,1024; word_sub stackpointer (word 791),791]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 791),791)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone: the same events, which depend on   *)
(* the seed C, and the same accesses.                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e c seed C pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_poly_challenge_terminates 39 32 C /\
          ALL (nonoverlapping (c,1024))
              [(word_sub stackpointer (word 791),791); (stackpointer,8)] /\
          nonoverlapping (seed,32) (word_sub stackpointer (word 791),791) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 791),791)]
           [(word pc,libmldsa_size)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read RIP s = word (pc + mldsa44_poly_challenge) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    (read DF s <=> false) /\
                    read (memory :> bytes(seed,32)) s = C /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events c seed C pc
                              (word_sub stackpointer (word 791))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; c,1024;
                         word_sub stackpointer (word 791),791; stackpointer,8;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [c,1024; word_sub stackpointer (word 791),791]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 791),791)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
