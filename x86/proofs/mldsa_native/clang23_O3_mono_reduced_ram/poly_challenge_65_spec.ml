(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The challenge polynomial (SampleInBall): the statement. This is the code  *)
(* for mldsa65_poly_challenge (mld_poly_challenge in poly_kl.c, for ML-      *)
(* DSA-65) from mldsa-native's portable C implementation compiled by clang   *)
(* 23 with -O3 as a monolithic build with MLD_CONFIG_REDUCE_RAM (see         *)
(* mldsa_native/README.md). Clang inlined the SHAKE256 functions: the        *)
(* function saves six registers, aligns its frame to 32 bytes, zeroes a      *)
(* Keccak state on its stack and puts the seed of 48 bytes and the padding   *)
(* into it with straight-line SSE code (with three 16-byte constants of its  *)
(* own, mldsa65_poly_challenge_consts), calls mldsa_keccakf1600_permute and  *)
(* copies the first block of 136 bytes of the state to a buffer with memcpy. *)
(* It loads the sign bits from the first 8 bytes of the buffer, zeroes the   *)
(* polynomial with memset, and then for i from 256 - 49 to 255 reads bytes j *)
(* of the buffer from position 8 on, calling mldsa_keccakf1600_permute and   *)
(* memcpy for the next block when the buffer is used up, until j <= i, and   *)
(* sets c[i] = c[j] and c[j] = 1 or -1 by the next sign bit, before it       *)
(* zeroes the signs, the state and the buffer. It is verified in the whole   *)
(* image (see libmldsa.ml) against mld_poly_challenge 49 48 of               *)
(* common/mldsa_native_challenge.ml, using the theorem for                   *)
(* mldsa_keccakf1600_permute and the contracts memset_full_contract and      *)
(* memcpy_full_contract of utils/mldsa_native_libc.ml, and assuming          *)
(* mld_poly_challenge_terminates 49 48, that the SHAKE256 output of the seed *)
(* has 49 acceptable bytes after its first 8, without which the code does    *)
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

    mldsa65_poly_challenge:
       +0x0: push    %rbp
       +0x1: mov     %rsp,%rbp
       +0x4: push    %r15
       +0x6: push    %r14
       +0x8: push    %r13
       +0xa: push    %r12
       +0xc: push    %rbx
       +0xd: and     $0xffffffffffffffe0,%rsp
      +0x11: sub     $0x180,%rsp
      +0x18: xorps   %xmm0,%xmm0
      +0x1b: movups  %xmm0,0xc8(%rsp)
      +0x23: movups  %xmm0,0xb8(%rsp)
      +0x2b: movups  %xmm0,0xa8(%rsp)
      +0x33: movups  %xmm0,0x98(%rsp)
      +0x3b: movups  %xmm0,0x88(%rsp)
      +0x43: movups  %xmm0,0x78(%rsp)
      +0x48: movups  %xmm0,0x68(%rsp)
      +0x4d: movups  %xmm0,0x58(%rsp)
      +0x52: movups  %xmm0,0x48(%rsp)
      +0x57: movups  %xmm0,0x38(%rsp)
      +0x5c: movups  %xmm0,0x28(%rsp)
      +0x61: movl    $0x0,0xd8(%rsp)
      +0x6c: movups  (%rsi),%xmm0
      +0x6f: movaps  %xmm0,0x10(%rsp)
      +0x74: movzbl  0x10(%rsi),%eax
      +0x78: mov     %al,0x20(%rsp)
      +0x7c: mov     0x29(%rsp),%rax
      +0x81: xor     0x19(%rsi),%rax
      +0x85: mov     %rdi,%rbx
      +0x88: movq    %rax,%xmm0
      +0x8d: movq    0x11(%rsi),%xmm1
      +0x92: punpcklqdq %xmm0,%xmm1
      +0x96: movdqu  %xmm1,0x21(%rsp)
      +0x9c: movd    0x29(%rsi),%xmm0
      +0xa1: movzwl  0x2e(%rsi),%eax
      +0xa5: movd    %eax,%xmm1
      +0xa9: movups  0x31(%rsp),%xmm2
      +0xae: pshufd  $0x50,%xmm0,%xmm0
      +0xb3: punpckldq 0x11af5(%rip),%xmm0
      +0xbb: movzbl  0x2d(%rsi),%eax
      +0xbf: movd    %eax,%xmm3
      +0xc3: pshufd  $0x0,%xmm3,%xmm3
      +0xc8: movdqa  0x11af0(%rip),%xmm4
      +0xd0: pand    %xmm4,%xmm0
      +0xd4: pandn   %xmm3,%xmm4
      +0xd8: por     %xmm0,%xmm4
      +0xdc: movdqa  0x11aec(%rip),%xmm0
      +0xe4: pand    %xmm0,%xmm4
      +0xe8: pslldq  $0xd,%xmm1
      +0xed: pandn   %xmm1,%xmm0
      +0xf1: por     %xmm4,%xmm0
      +0xf5: movlps  0x21(%rsi),%xmm0
      +0xf9: xorps   %xmm2,%xmm0
      +0xfc: movups  %xmm0,0x31(%rsp)
     +0x101: xorb    $0x80,0x97(%rsp)
     +0x109: movl    $0x88,0xd8(%rsp)
     +0x114: lea     0x10(%rsp),%r14
     +0x119: mov     %r14,%rdi
     +0x11c: call    <mldsa_keccakf1600_permute>
     +0x121: lea     0xe0(%rsp),%r15
     +0x129: mov     $0x88,%edx
     +0x12e: mov     %r15,%rdi
     +0x131: mov     %r14,%rsi
     +0x134: call    <memcpy>
     +0x139: movl    $0x88,0xd8(%rsp)
     +0x144: mov     0xe0(%rsp),%r12
     +0x14c: mov     $0x400,%edx
     +0x151: mov     %rbx,%rdi
     +0x154: xor     %esi,%esi
     +0x156: call    <memset>
     +0x15b: mov     $0x8,%eax
     +0x160: mov     $0xcf,%r13d
     +0x166: jmp     <mldsa65_poly_challenge+0x181>
     +0x168: nopl    0x0(%rax,%rax,1)
     +0x170: mov     %eax,%ecx
     +0x172: inc     %eax
     +0x174: movzbl  0xe0(%rsp,%rcx,1),%ecx
     +0x17c: cmp     %r13b,%cl
     +0x17f: jbe     <mldsa65_poly_challenge+0x1af>
     +0x181: cmp     $0x88,%eax
     +0x186: jb      <mldsa65_poly_challenge+0x170>
     +0x188: mov     %r14,%rdi
     +0x18b: call    <mldsa_keccakf1600_permute>
     +0x190: mov     $0x88,%edx
     +0x195: mov     %r15,%rdi
     +0x198: mov     %r14,%rsi
     +0x19b: call    <memcpy>
     +0x1a0: movl    $0x88,0xd8(%rsp)
     +0x1ab: xor     %eax,%eax
     +0x1ad: jmp     <mldsa65_poly_challenge+0x170>
     +0x1af: mov     (%rbx,%rcx,4),%edx
     +0x1b2: mov     %edx,(%rbx,%r13,4)
     +0x1b6: lea     (%r12,%r12,1),%edx
     +0x1ba: and     $0x2,%edx
     +0x1bd: mov     $0x1,%esi
     +0x1c2: sub     %edx,%esi
     +0x1c4: mov     %esi,(%rbx,%rcx,4)
     +0x1c7: shr     $1,%r12
     +0x1ca: inc     %r13
     +0x1cd: cmp     $0x100,%r13
     +0x1d4: jne     <mldsa65_poly_challenge+0x181>
     +0x1d6: mov     %r12,0x8(%rsp)
     +0x1db: xorps   %xmm0,%xmm0
     +0x1de: movaps  %xmm0,0x10(%rsp)
     +0x1e3: movaps  %xmm0,0x20(%rsp)
     +0x1e8: movaps  %xmm0,0x30(%rsp)
     +0x1ed: movaps  %xmm0,0x40(%rsp)
     +0x1f2: movaps  %xmm0,0x50(%rsp)
     +0x1f7: movaps  %xmm0,0x60(%rsp)
     +0x1fc: movaps  %xmm0,0x70(%rsp)
     +0x201: movaps  %xmm0,0x80(%rsp)
     +0x209: movaps  %xmm0,0x90(%rsp)
     +0x211: movaps  %xmm0,0xa0(%rsp)
     +0x219: movaps  %xmm0,0xb0(%rsp)
     +0x221: movaps  %xmm0,0xc0(%rsp)
     +0x229: movaps  %xmm0,0xd0(%rsp)
     +0x231: lea     0x10(%rsp),%rax
     +0x236: movaps  %xmm0,0x150(%rsp)
     +0x23e: movaps  %xmm0,0x140(%rsp)
     +0x246: movaps  %xmm0,0x130(%rsp)
     +0x24e: movaps  %xmm0,0x120(%rsp)
     +0x256: movaps  %xmm0,0x110(%rsp)
     +0x25e: movaps  %xmm0,0x100(%rsp)
     +0x266: movaps  %xmm0,0xf0(%rsp)
     +0x26e: movaps  %xmm0,0xe0(%rsp)
     +0x276: movq    $0x0,0x160(%rsp)
     +0x282: lea     0xe0(%rsp),%rax
     +0x28a: movq    $0x0,0x8(%rsp)
     +0x293: lea     0x8(%rsp),%rax
     +0x298: lea     -0x28(%rbp),%rsp
     +0x29c: pop     %rbx
     +0x29d: pop     %r12
     +0x29f: pop     %r13
     +0x2a1: pop     %r14
     +0x2a3: pop     %r15
     +0x2a5: pop     %rbp
     +0x2a6: xor     %eax,%eax
     +0x2a8: xor     %ecx,%ecx
     +0x2aa: xor     %edi,%edi
     +0x2ac: xor     %edx,%edx
     +0x2ae: xor     %esi,%esi
     +0x2b0: ret     
 ***)

let MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa65_poly_challenge";
    layout_range "plt_memcpy";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The seed is the 48 bytes C at seed, and the polynomial at c  *)
(* becomes mld_poly_challenge 49 48 C, if mld_poly_challenge_terminates 49   *)
(* 48 C. The seed may overlap the polynomial, as it is only read before the  *)
(* polynomial is written. The function saves six registers below the return  *)
(* address, aligns the stack pointer down to a multiple of 32, which may     *)
(* lower it by up to 31 bytes, and reserves 384 bytes for the signs, the     *)
(* Keccak state and the buffer, below which mldsa_keccakf1600_permute uses   *)
(* 288 bytes and its return address 8: 759 bytes of stack below the return   *)
(* address. memset and memcpy are called through the PLT with the addresses  *)
(* from the GOT, and are assumed not to use the stack.                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !c seed C pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_poly_challenge_terminates 49 48 C /\
          ALL (nonoverlapping (c,1024))
              [(word_sub stackpointer (word 759),759); (stackpointer,8)] /\
          nonoverlapping (seed,48) (word_sub stackpointer (word 759),759) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 759),759)]
           [(word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa65_poly_challenge) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,48)) s = C)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add c (word(4 * i))))
                               s =
                             mld_poly_challenge 49 48 C i))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 759),759)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the seed C, the addresses of     *)
(* memset and memcpy and the stack, with all accesses within the seed, the   *)
(* polynomial, the stack, the slot of the return address, the GOT entries,   *)
(* the region (ea,el) of the C library, the round constants of Keccak and    *)
(* the constants of the function, and the writes within the polynomial and   *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e c seed C pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_poly_challenge_terminates 49 48 C /\
          ALL (nonoverlapping (c,1024))
              [(word_sub stackpointer (word 759),759); (stackpointer,8)] /\
          nonoverlapping (seed,48) (word_sub stackpointer (word 759),759) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 759),759)]
           [(word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa65_poly_challenge) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,48)) s = C /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add c (word(4 * i))))
                               s =
                             mld_poly_challenge 49 48 C i) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events c seed C mf mc pc
                              (word_sub stackpointer (word 759))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,48; c,1024;
                         word_sub stackpointer (word 759),759; stackpointer,8;
                       word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + mldsa65_poly_challenge_consts),48]
                        [c,1024; word_sub stackpointer (word 759),759]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 759),759)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone: the same events, which depend on   *)
(* the seed C, and the same accesses.                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e c seed C pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_poly_challenge_terminates 49 48 C /\
          ALL (nonoverlapping (c,1024))
              [(word_sub stackpointer (word 759),759); (stackpointer,8)] /\
          nonoverlapping (seed,48) (word_sub stackpointer (word 759),759) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 759),759)]
           [(word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa65_poly_challenge) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,48)) s = C /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events c seed C mf mc pc
                              (word_sub stackpointer (word 759))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,48; c,1024;
                         word_sub stackpointer (word 759),759; stackpointer,8;
                       word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192;
                         word(pc + mldsa65_poly_challenge_consts),48]
                        [c,1024; word_sub stackpointer (word 759),759]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 759),759)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_65_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
