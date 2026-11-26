(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The challenge polynomial (SampleInBall): the statement. This is the code  *)
(* for mldsa44_poly_challenge (mld_poly_challenge in poly_kl.c, for          *)
(* ML-DSA-44) from mldsa-native's portable C implementation compiled by      *)
(* clang 23 with -O3 as a monolithic build with MLD_CONFIG_REDUCE_RAM (see   *)
(* mldsa_native/README.md). Clang inlined the SHAKE256 functions: the        *)
(* function saves six registers, aligns its frame to 32 bytes, zeroes a      *)
(* Keccak state on its stack and puts the seed of 32 bytes and the padding   *)
(* into it with straight-line SSE code (with four 16-byte constants of its   *)
(* own, mldsa44_poly_challenge_consts), calls mldsa_keccakf1600_permute and  *)
(* copies the first block of 136 bytes of the state to a buffer with memcpy. *)
(* It loads the sign bits from the first 8 bytes of the buffer, zeroes the   *)
(* polynomial with memset, and then for i from 256 - 39 to 255 reads bytes j *)
(* of the buffer from position 8 on, calling mldsa_keccakf1600_permute and   *)
(* memcpy for the next block when the buffer is used up, until j <= i, and   *)
(* sets c[i] = c[j] and c[j] = 1 or -1 by the next sign bit, before it       *)
(* zeroes the signs, the state and the buffer. It is verified in the whole   *)
(* image (see libmldsa.ml) against mld_poly_challenge 39 32 of               *)
(* common/mldsa_native_challenge.ml, using the theorem for                   *)
(* mldsa_keccakf1600_permute and the contracts memset_full_contract and      *)
(* memcpy_full_contract of utils/mldsa_native_libc.ml, and assuming          *)
(* mld_poly_challenge_terminates 39 32, that the SHAKE256 output of the seed *)
(* has 39 acceptable bytes after its first 8, without which the code does    *)
(* not terminate. It is also shown to be constant time and memory safe, with *)
(* the events depending on the seed, which is public (c~ is declassified     *)
(* when signing and is part of the signature).                               *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_challenge.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa44_poly_challenge:
       +0x0: push    %rbp
       +0x1: mov     %rsp,%rbp
       +0x4: push    %r15
       +0x6: push    %r14
       +0x8: push    %r13
       +0xa: push    %r12
       +0xc: push    %rbx
       +0xd: and     $0xffffffffffffffe0,%rsp
      +0x11: sub     $0x180,%rsp
      +0x18: mov     %rdi,%rbx
      +0x1b: xorps   %xmm0,%xmm0
      +0x1e: movups  %xmm0,0xc8(%rsp)
      +0x26: movups  %xmm0,0xb8(%rsp)
      +0x2e: movups  %xmm0,0xa8(%rsp)
      +0x36: movups  %xmm0,0x98(%rsp)
      +0x3e: movups  %xmm0,0x88(%rsp)
      +0x46: movups  %xmm0,0x78(%rsp)
      +0x4b: movups  %xmm0,0x68(%rsp)
      +0x50: movups  %xmm0,0x58(%rsp)
      +0x55: movups  %xmm0,0x48(%rsp)
      +0x5a: movups  %xmm0,0x38(%rsp)
      +0x5f: movups  %xmm0,0x28(%rsp)
      +0x64: movl    $0x0,0xd8(%rsp)
      +0x6f: movups  (%rsi),%xmm0
      +0x72: movaps  %xmm0,0x10(%rsp)
      +0x77: movzbl  0x10(%rsi),%eax
      +0x7b: mov     %al,0x20(%rsp)
      +0x7f: movq    0x11(%rsi),%xmm0
      +0x84: movd    0x19(%rsi),%xmm1
      +0x89: movzwl  0x1e(%rsi),%eax
      +0x8d: movd    %eax,%xmm2
      +0x91: movq    0x29(%rsp),%xmm3
      +0x97: movdqa  0x1d7d1(%rip),%xmm4
      +0x9f: pand    %xmm4,%xmm1
      +0xa3: movzbl  0x1d(%rsi),%eax
      +0xa7: movd    %eax,%xmm5
      +0xab: pshufd  $0x50,%xmm5,%xmm5
      +0xb0: pandn   %xmm5,%xmm4
      +0xb4: por     %xmm1,%xmm4
      +0xb8: pand    0x1d7c0(%rip),%xmm4
      +0xc0: por     0x1d7c8(%rip),%xmm4
      +0xc8: movdqa  0x1d7d0(%rip),%xmm1
      +0xd0: pand    %xmm1,%xmm4
      +0xd4: psllq   $0x28,%xmm2
      +0xd9: pandn   %xmm2,%xmm1
      +0xdd: por     %xmm4,%xmm1
      +0xe1: pxor    %xmm3,%xmm1
      +0xe5: punpcklqdq %xmm1,%xmm0
      +0xe9: movdqu  %xmm0,0x21(%rsp)
      +0xef: xorb    $0x80,0x97(%rsp)
      +0xf7: movl    $0x88,0xd8(%rsp)
     +0x102: lea     0x10(%rsp),%r14
     +0x107: mov     %r14,%rdi
     +0x10a: call    <mldsa_keccakf1600_permute>
     +0x10f: lea     0xe0(%rsp),%r15
     +0x117: mov     $0x88,%edx
     +0x11c: mov     %r15,%rdi
     +0x11f: mov     %r14,%rsi
     +0x122: call    <memcpy>
     +0x127: movl    $0x88,0xd8(%rsp)
     +0x132: mov     0xe0(%rsp),%r12
     +0x13a: mov     $0x400,%edx
     +0x13f: mov     %rbx,%rdi
     +0x142: xor     %esi,%esi
     +0x144: call    <memset>
     +0x149: mov     $0x8,%eax
     +0x14e: mov     $0xd9,%r13d
     +0x154: jmp     <mldsa44_poly_challenge+0x171>
     +0x156: cs      nopw 0x0(%rax,%rax,1)
     +0x160: mov     %eax,%ecx
     +0x162: inc     %eax
     +0x164: movzbl  0xe0(%rsp,%rcx,1),%ecx
     +0x16c: cmp     %r13b,%cl
     +0x16f: jbe     <mldsa44_poly_challenge+0x19f>
     +0x171: cmp     $0x88,%eax
     +0x176: jb      <mldsa44_poly_challenge+0x160>
     +0x178: mov     %r14,%rdi
     +0x17b: call    <mldsa_keccakf1600_permute>
     +0x180: mov     $0x88,%edx
     +0x185: mov     %r15,%rdi
     +0x188: mov     %r14,%rsi
     +0x18b: call    <memcpy>
     +0x190: movl    $0x88,0xd8(%rsp)
     +0x19b: xor     %eax,%eax
     +0x19d: jmp     <mldsa44_poly_challenge+0x160>
     +0x19f: mov     (%rbx,%rcx,4),%edx
     +0x1a2: mov     %edx,(%rbx,%r13,4)
     +0x1a6: lea     (%r12,%r12,1),%edx
     +0x1aa: and     $0x2,%edx
     +0x1ad: mov     $0x1,%esi
     +0x1b2: sub     %edx,%esi
     +0x1b4: mov     %esi,(%rbx,%rcx,4)
     +0x1b7: shr     $1,%r12
     +0x1ba: inc     %r13
     +0x1bd: cmp     $0x100,%r13
     +0x1c4: jne     <mldsa44_poly_challenge+0x171>
     +0x1c6: mov     %r12,0x8(%rsp)
     +0x1cb: pxor    %xmm0,%xmm0
     +0x1cf: movdqa  %xmm0,0x10(%rsp)
     +0x1d5: movdqa  %xmm0,0x20(%rsp)
     +0x1db: movdqa  %xmm0,0x30(%rsp)
     +0x1e1: movdqa  %xmm0,0x40(%rsp)
     +0x1e7: movdqa  %xmm0,0x50(%rsp)
     +0x1ed: movdqa  %xmm0,0x60(%rsp)
     +0x1f3: movdqa  %xmm0,0x70(%rsp)
     +0x1f9: movdqa  %xmm0,0x80(%rsp)
     +0x202: movdqa  %xmm0,0x90(%rsp)
     +0x20b: movdqa  %xmm0,0xa0(%rsp)
     +0x214: movdqa  %xmm0,0xb0(%rsp)
     +0x21d: movdqa  %xmm0,0xc0(%rsp)
     +0x226: movdqa  %xmm0,0xd0(%rsp)
     +0x22f: lea     0x10(%rsp),%rax
     +0x234: movdqa  %xmm0,0x150(%rsp)
     +0x23d: movdqa  %xmm0,0x140(%rsp)
     +0x246: movdqa  %xmm0,0x130(%rsp)
     +0x24f: movdqa  %xmm0,0x120(%rsp)
     +0x258: movdqa  %xmm0,0x110(%rsp)
     +0x261: movdqa  %xmm0,0x100(%rsp)
     +0x26a: movdqa  %xmm0,0xf0(%rsp)
     +0x273: movdqa  %xmm0,0xe0(%rsp)
     +0x27c: movq    $0x0,0x160(%rsp)
     +0x288: lea     0xe0(%rsp),%rax
     +0x290: movq    $0x0,0x8(%rsp)
     +0x299: lea     0x8(%rsp),%rax
     +0x29e: lea     -0x28(%rbp),%rsp
     +0x2a2: pop     %rbx
     +0x2a3: pop     %r12
     +0x2a5: pop     %r13
     +0x2a7: pop     %r14
     +0x2a9: pop     %r15
     +0x2ab: pop     %rbp
     +0x2ac: xor     %eax,%eax
     +0x2ae: xor     %ecx,%ecx
     +0x2b0: xor     %edi,%edi
     +0x2b2: xor     %edx,%edx
     +0x2b4: xor     %esi,%esi
     +0x2b6: ret     
 ***)

let MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa44_poly_challenge";
    layout_range "plt_memcpy";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The seed is the 32 bytes C at seed, and the polynomial at c  *)
(* becomes mld_poly_challenge 39 32 C, if mld_poly_challenge_terminates 39   *)
(* 32 C. The seed may overlap the polynomial, as it is only read before the  *)
(* polynomial is written. The function saves six registers below the return  *)
(* address, aligns the stack pointer down to a multiple of 32, which may     *)
(* lower it by up to 31 bytes, and reserves 384 bytes for the signs, the     *)
(* Keccak state and the buffer, below which mldsa_keccakf1600_permute uses   *)
(* 288 bytes and its return address 8: 759 bytes of stack below the return   *)
(* address. memset and memcpy are called through the PLT with the addresses  *)
(* from the GOT, and are assumed not to use the stack.                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !c seed C pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_poly_challenge_terminates 39 32 C /\
          ALL (nonoverlapping (c,1024))
              [(word_sub stackpointer (word 759),759); (stackpointer,8)] /\
          nonoverlapping (seed,32) (word_sub stackpointer (word 759),759) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 759),759)]
           [(word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa44_poly_challenge) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
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
                  memory :> bytes(word_sub stackpointer (word 759),759)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the seed C, the addresses of     *)
(* memset and memcpy and the stack, with all accesses within the seed, the   *)
(* polynomial, the stack, the slot of the return address, the GOT entries,   *)
(* the region (ea,el) of the C library, the round constants of Keccak and    *)
(* the constants of the function, and the writes within the polynomial and   *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e c seed C pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_poly_challenge_terminates 39 32 C /\
          ALL (nonoverlapping (c,1024))
              [(word_sub stackpointer (word 759),759); (stackpointer,8)] /\
          nonoverlapping (seed,32) (word_sub stackpointer (word 759),759) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 759),759)]
           [(word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa44_poly_challenge) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
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
                       e2 = f_events c seed C mf mc pc
                              (word_sub stackpointer (word 759))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; c,1024;
                         word_sub stackpointer (word 759),759; stackpointer,8;
                       word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + mldsa44_poly_challenge_consts),64]
                        [c,1024; word_sub stackpointer (word 759),759]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 759),759)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone: the same events, which depend on   *)
(* the seed C, and the same accesses.                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e c seed C pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_poly_challenge_terminates 39 32 C /\
          ALL (nonoverlapping (c,1024))
              [(word_sub stackpointer (word 759),759); (stackpointer,8)] /\
          nonoverlapping (seed,32) (word_sub stackpointer (word 759),759) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 759),759)]
           [(word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa44_poly_challenge) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,32)) s = C /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events c seed C mf mc pc
                              (word_sub stackpointer (word 759))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,32; c,1024;
                         word_sub stackpointer (word 759),759; stackpointer,8;
                       word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + mldsa44_poly_challenge_consts),64]
                        [c,1024; word_sub stackpointer (word 759),759]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 759),759)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_44_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
