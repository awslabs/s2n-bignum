(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The challenge polynomial (SampleInBall): the statement. This is the code  *)
(* for mldsa87_poly_challenge (mld_poly_challenge in poly_kl.c, for ML-      *)
(* DSA-87) from mldsa-native's portable C implementation compiled by clang   *)
(* 23 with -O3 as a monolithic build with MLD_CONFIG_REDUCE_RAM (see         *)
(* mldsa_native/README.md). Clang inlined the SHAKE256 functions: the        *)
(* function saves six registers, aligns its frame to 32 bytes, zeroes a      *)
(* Keccak state on its stack and copies the seed of 64 bytes into it with    *)
(* 16-byte stores and XORs in the padding, calls mldsa_keccakf1600_permute   *)
(* and copies the first block of 136 bytes of the state to a buffer with     *)
(* memcpy. It loads the sign bits from the first 8 bytes of the buffer,      *)
(* zeroes the polynomial with memset, and then for i from 256 - 60 to 255    *)
(* reads bytes j of the buffer from position 8 on, calling                   *)
(* mldsa_keccakf1600_permute and memcpy for the next block when the buffer   *)
(* is used up, until j <= i, and sets c[i] = c[j] and c[j] = 1 or -1 by the  *)
(* next sign bit, before it zeroes the signs, the state and the buffer. It   *)
(* is verified in the whole image (see libmldsa.ml) against                  *)
(* mld_poly_challenge 60 64 of common/mldsa_native_challenge.ml, using the   *)
(* theorem for mldsa_keccakf1600_permute and the contracts                   *)
(* memset_full_contract and memcpy_full_contract of                          *)
(* utils/mldsa_native_libc.ml, and assuming mld_poly_challenge_terminates 60 *)
(* 64, that the SHAKE256 output of the seed has 60 acceptable bytes after    *)
(* its first 8, without which the code does not terminate. It is also shown  *)
(* to be constant time and memory safe, with the events depending on the     *)
(* seed, which is public (c~ is declassified when signing and is part of the *)
(* signature).                                                               *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_challenge.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa87_poly_challenge:
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
      +0x1e: movups  %xmm0,0xcc(%rsp)
      +0x26: movaps  %xmm0,0xc0(%rsp)
      +0x2e: movaps  %xmm0,0xb0(%rsp)
      +0x36: movaps  %xmm0,0xa0(%rsp)
      +0x3e: movaps  %xmm0,0x90(%rsp)
      +0x46: movaps  %xmm0,0x80(%rsp)
      +0x4e: movaps  %xmm0,0x70(%rsp)
      +0x53: movaps  %xmm0,0x60(%rsp)
      +0x58: movaps  %xmm0,0x50(%rsp)
      +0x5d: movaps  %xmm0,0x40(%rsp)
      +0x62: movaps  %xmm0,0x30(%rsp)
      +0x67: movaps  %xmm0,0x20(%rsp)
      +0x6c: movaps  %xmm0,0x10(%rsp)
      +0x71: movups  (%rsi),%xmm0
      +0x74: movups  0x10(%rsi),%xmm1
      +0x78: movaps  %xmm0,0x10(%rsp)
      +0x7d: movaps  %xmm1,0x20(%rsp)
      +0x82: movups  0x20(%rsi),%xmm0
      +0x86: movups  0x30(%rsi),%xmm1
      +0x8a: movaps  %xmm0,0x30(%rsp)
      +0x8f: movaps  %xmm1,0x40(%rsp)
      +0x94: xorb    $0x1f,0x50(%rsp)
      +0x99: xorb    $0x80,0x97(%rsp)
      +0xa1: movl    $0x88,0xd8(%rsp)
      +0xac: lea     0x10(%rsp),%r14
      +0xb1: mov     %r14,%rdi
      +0xb4: call    <mldsa_keccakf1600_permute>
      +0xb9: lea     0xe0(%rsp),%r15
      +0xc1: mov     $0x88,%edx
      +0xc6: mov     %r15,%rdi
      +0xc9: mov     %r14,%rsi
      +0xcc: call    <memcpy>
      +0xd1: movl    $0x88,0xd8(%rsp)
      +0xdc: mov     0xe0(%rsp),%r12
      +0xe4: mov     $0x400,%edx
      +0xe9: mov     %rbx,%rdi
      +0xec: xor     %esi,%esi
      +0xee: call    <memset>
      +0xf3: mov     $0x8,%eax
      +0xf8: mov     $0xc4,%r13d
      +0xfe: jmp     <mldsa87_poly_challenge+0x111>
     +0x100: mov     %eax,%ecx
     +0x102: inc     %eax
     +0x104: movzbl  0xe0(%rsp,%rcx,1),%ecx
     +0x10c: cmp     %r13b,%cl
     +0x10f: jbe     <mldsa87_poly_challenge+0x13f>
     +0x111: cmp     $0x88,%eax
     +0x116: jb      <mldsa87_poly_challenge+0x100>
     +0x118: mov     %r14,%rdi
     +0x11b: call    <mldsa_keccakf1600_permute>
     +0x120: mov     $0x88,%edx
     +0x125: mov     %r15,%rdi
     +0x128: mov     %r14,%rsi
     +0x12b: call    <memcpy>
     +0x130: movl    $0x88,0xd8(%rsp)
     +0x13b: xor     %eax,%eax
     +0x13d: jmp     <mldsa87_poly_challenge+0x100>
     +0x13f: mov     (%rbx,%rcx,4),%edx
     +0x142: mov     %edx,(%rbx,%r13,4)
     +0x146: lea     (%r12,%r12,1),%edx
     +0x14a: and     $0x2,%edx
     +0x14d: mov     $0x1,%esi
     +0x152: sub     %edx,%esi
     +0x154: mov     %esi,(%rbx,%rcx,4)
     +0x157: shr     $1,%r12
     +0x15a: inc     %r13
     +0x15d: cmp     $0x100,%r13
     +0x164: jne     <mldsa87_poly_challenge+0x111>
     +0x166: mov     %r12,0x8(%rsp)
     +0x16b: xorps   %xmm0,%xmm0
     +0x16e: movaps  %xmm0,0x10(%rsp)
     +0x173: movaps  %xmm0,0x20(%rsp)
     +0x178: movaps  %xmm0,0x30(%rsp)
     +0x17d: movaps  %xmm0,0x40(%rsp)
     +0x182: movaps  %xmm0,0x50(%rsp)
     +0x187: movaps  %xmm0,0x60(%rsp)
     +0x18c: movaps  %xmm0,0x70(%rsp)
     +0x191: movaps  %xmm0,0x80(%rsp)
     +0x199: movaps  %xmm0,0x90(%rsp)
     +0x1a1: movaps  %xmm0,0xa0(%rsp)
     +0x1a9: movaps  %xmm0,0xb0(%rsp)
     +0x1b1: movaps  %xmm0,0xc0(%rsp)
     +0x1b9: movaps  %xmm0,0xd0(%rsp)
     +0x1c1: lea     0x10(%rsp),%rax
     +0x1c6: movaps  %xmm0,0x150(%rsp)
     +0x1ce: movaps  %xmm0,0x140(%rsp)
     +0x1d6: movaps  %xmm0,0x130(%rsp)
     +0x1de: movaps  %xmm0,0x120(%rsp)
     +0x1e6: movaps  %xmm0,0x110(%rsp)
     +0x1ee: movaps  %xmm0,0x100(%rsp)
     +0x1f6: movaps  %xmm0,0xf0(%rsp)
     +0x1fe: movaps  %xmm0,0xe0(%rsp)
     +0x206: movq    $0x0,0x160(%rsp)
     +0x212: lea     0xe0(%rsp),%rax
     +0x21a: movq    $0x0,0x8(%rsp)
     +0x223: lea     0x8(%rsp),%rax
     +0x228: lea     -0x28(%rbp),%rsp
     +0x22c: pop     %rbx
     +0x22d: pop     %r12
     +0x22f: pop     %r13
     +0x231: pop     %r14
     +0x233: pop     %r15
     +0x235: pop     %rbp
     +0x236: xor     %eax,%eax
     +0x238: xor     %ecx,%ecx
     +0x23a: xor     %edi,%edi
     +0x23c: xor     %edx,%edx
     +0x23e: xor     %esi,%esi
     +0x240: ret     
 ***)

let MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa87_poly_challenge";
    layout_range "plt_memcpy";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The seed is the 64 bytes C at seed, and the polynomial at c  *)
(* becomes mld_poly_challenge 60 64 C, if mld_poly_challenge_terminates 60   *)
(* 64 C. The seed may overlap the polynomial, as it is only read before the  *)
(* polynomial is written. The function saves six registers below the return  *)
(* address, aligns the stack pointer down to a multiple of 32, which may     *)
(* lower it by up to 31 bytes, and reserves 384 bytes for the signs, the     *)
(* Keccak state and the buffer, below which mldsa_keccakf1600_permute uses   *)
(* 288 bytes and its return address 8: 759 bytes of stack below the return   *)
(* address. memset and memcpy are called through the PLT with the addresses  *)
(* from the GOT, and are assumed not to use the stack.                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !c seed C pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_poly_challenge_terminates 60 64 C /\
          ALL (nonoverlapping (c,1024))
              [(word_sub stackpointer (word 759),759); (stackpointer,8)] /\
          nonoverlapping (seed,64) (word_sub stackpointer (word 759),759) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 759),759)]
           [(word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa87_poly_challenge) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,64)) s = C)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add c (word(4 * i))))
                               s =
                             mld_poly_challenge 60 64 C i))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 759),759)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the seed C, the addresses of     *)
(* memset and memcpy and the stack, with all accesses within the seed, the   *)
(* polynomial, the stack, the slot of the return address, the GOT entries,   *)
(* the region (ea,el) of the C library and the round constants of Keccak,      *)
(* and the writes within the polynomial and the stack.                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e c seed C pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_poly_challenge_terminates 60 64 C /\
          ALL (nonoverlapping (c,1024))
              [(word_sub stackpointer (word 759),759); (stackpointer,8)] /\
          nonoverlapping (seed,64) (word_sub stackpointer (word 759),759) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 759),759)]
           [(word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa87_poly_challenge) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,64)) s = C /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add c (word(4 * i))))
                               s =
                             mld_poly_challenge 60 64 C i) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events c seed C mf mc pc
                              (word_sub stackpointer (word 759))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,64; c,1024;
                         word_sub stackpointer (word 759),759; stackpointer,8;
                       word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [c,1024; word_sub stackpointer (word 759),759]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 759),759)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone: the same events, which depend on   *)
(* the seed C, and the same accesses.                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e c seed C pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          mld_poly_challenge_terminates 60 64 C /\
          ALL (nonoverlapping (c,1024))
              [(word_sub stackpointer (word 759),759); (stackpointer,8)] /\
          nonoverlapping (seed,64) (word_sub stackpointer (word 759),759) /\
          ALLPAIRS nonoverlapping
           [(c,1024); (word_sub stackpointer (word 759),759)]
           [(word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
          ==> ensures x86
               (\s. bytes_loaded s (word pc)
                      mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                    read RIP s = word (pc + mldsa87_poly_challenge) /\
                    read RSP s = stackpointer /\
                    read (memory :> bytes64 stackpointer) s = returnaddress /\
                    C_ARGUMENTS [c; seed] s /\
                    (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,64)) s = C /\
                    read events s = e)
               (\s. read RIP s = returnaddress /\
                    read RSP s = word_add stackpointer (word 8) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events c seed C mf mc pc
                              (word_sub stackpointer (word 759))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,64; c,1024;
                         word_sub stackpointer (word 759),759; stackpointer,8;
                       word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [c,1024; word_sub stackpointer (word 759),759]))
               (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
                MAYCHANGE
                 [memory :> bytes(c,1024);
                  memory :> bytes(word_sub stackpointer (word 759),759)])`;;

let MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_CHALLENGE_87_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
