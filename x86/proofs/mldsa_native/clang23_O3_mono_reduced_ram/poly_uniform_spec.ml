(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of a polynomial mod q from a seed by rejection: the      *)
(* statement. This is the code for mldsa_poly_uniform (mld_poly_uniform in   *)
(* poly.c) from mldsa-native's portable C implementation compiled by clang   *)
(* 23 with -O3 and MLD_CONFIG_REDUCE_RAM (the monolithic build, see          *)
(* mldsa_native/README.md). It absorbs the seed of 34 bytes into a SHAKE128  *)
(* state on the stack, squeezes 5 blocks of 168 bytes into a buffer with     *)
(* mldsa_keccakf1600_permute and memcpy, samples the coefficients below q    *)
(* from them in a loop that clang made of mld_rej_uniform_c, and then        *)
(* squeezes one block at a time and samples from it until the polynomial     *)
(* has 256 coefficients, before zeroing the state and calling memset for the *)
(* buffer. Clang has inlined the SHAKE128 functions. It is verified in the   *)
(* whole image (see libmldsa.ml) against mld_poly_uniform of                 *)
(* common/mldsa_native_sampling.ml, using the theorems for the callees,      *)
(* and assuming that the SHAKE128 output of the seed has 256 acceptable      *)
(* groups of 3 bytes (mld_rej_uniform_terminates), without which the code    *)
(* does not terminate. It is also shown to be constant time and memory safe, *)
(* with the events depending on the seed, which is public (rho and the       *)
(* indices of the matrix entry), and on the number of groups that the        *)
(* sampling reads.                                                           *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/utils/mldsa_native_libc.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "x86/proofs/mldsa_native/clang23_O3_mono_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_uniform:
       +0x0: push    %rbp
       +0x1: mov     %rsp,%rbp
       +0x4: push    %r15
       +0x6: push    %r14
       +0x8: push    %r13
       +0xa: push    %r12
       +0xc: push    %rbx
       +0xd: and     $0xffffffffffffffe0,%rsp
      +0x11: sub     $0x440,%rsp
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
      +0x85: movq    %rax,%xmm0
      +0x8a: movq    0x11(%rsi),%xmm1
      +0x8f: punpcklqdq %xmm0,%xmm1
      +0x93: movdqu  %xmm1,0x21(%rsp)
      +0x99: movzbl  0x21(%rsi),%eax
      +0x9d: xor     %al,0x31(%rsp)
      +0xa1: mov     %rdi,%rbx
      +0xa4: xorb    $0x1f,0x32(%rsp)
      +0xa9: xorb    $0x80,0xb7(%rsp)
      +0xb1: movl    $0xa8,0xd8(%rsp)
      +0xbc: mov     $0xa8,%r12d
      +0xc2: mov     $0x348,%r13d
      +0xc8: xor     %r14d,%r14d
      +0xcb: jmp     <mldsa_poly_uniform+0x109>
      +0xcd: nopl    (%rax)
      +0xd0: mov     $0xa8,%r15d
      +0xd6: sub     %r12d,%r15d
      +0xd9: cmp     %r15,%r13
      +0xdc: cmovb   %r13,%r15
      +0xe0: mov     %r12d,%eax
      +0xe3: lea     (%rsp,%rax,1),%rsi
      +0xe7: add     $0x10,%rsi
      +0xeb: lea     (%rsp,%r14,1),%rdi
      +0xef: add     $0xe0,%rdi
      +0xf6: mov     %r15,%rdx
      +0xf9: call    <memcpy>
      +0xfe: add     %r15d,%r12d
     +0x101: add     %r15,%r14
     +0x104: sub     %r15,%r13
     +0x107: je      <mldsa_poly_uniform+0x137>
     +0x109: cmp     $0xa8,%r12d
     +0x110: jne     <mldsa_poly_uniform+0xd0>
     +0x112: lea     0x10(%rsp),%rdi
     +0x117: call    <mldsa_keccakf1600_permute>
     +0x11c: cmp     $0xa8,%r13
     +0x123: mov     $0xa8,%r15d
     +0x129: cmovb   %r13,%r15
     +0x12d: xor     %r12d,%r12d
     +0x130: lea     0x10(%rsp),%rsi
     +0x135: jmp     <mldsa_poly_uniform+0xeb>
     +0x137: mov     %r12d,0xd8(%rsp)
     +0x13f: xor     %esi,%esi
     +0x141: mov     $0x3,%eax
     +0x146: cs      nopw 0x0(%rax,%rax,1)
     +0x150: movzwl  0xdd(%rsp,%rax,1),%edx
     +0x158: movzbl  0xdf(%rsp,%rax,1),%ecx
     +0x160: and     $0x7f,%ecx
     +0x163: shl     $0x10,%ecx
     +0x166: or      %edx,%ecx
     +0x168: cmp     $0x7fe000,%ecx
     +0x16e: ja      <mldsa_poly_uniform+0x177>
     +0x170: mov     %esi,%edx
     +0x172: inc     %esi
     +0x174: mov     %ecx,(%rbx,%rdx,4)
     +0x177: cmp     $0x345,%rax
     +0x17d: ja      <mldsa_poly_uniform+0x18b>
     +0x17f: add     $0x3,%rax
     +0x183: cmp     $0x100,%esi
     +0x189: jb      <mldsa_poly_uniform+0x150>
     +0x18b: cmp     $0xff,%esi
     +0x191: ja      <mldsa_poly_uniform+0x294>
     +0x197: mov     %rbx,0x8(%rsp)
     +0x19c: jmp     <mldsa_poly_uniform+0x1ac>
     +0x19e: xchg    %ax,%ax
     +0x1a0: cmp     $0xff,%esi
     +0x1a6: ja      <mldsa_poly_uniform+0x294>
     +0x1ac: mov     %esi,0x4(%rsp)
     +0x1b0: mov     $0xa8,%ebx
     +0x1b5: xor     %r14d,%r14d
     +0x1b8: jmp     <mldsa_poly_uniform+0x1f9>
     +0x1ba: nopw    0x0(%rax,%rax,1)
     +0x1c0: mov     $0xa8,%r15d
     +0x1c6: sub     %r12d,%r15d
     +0x1c9: cmp     %r15,%rbx
     +0x1cc: cmovb   %rbx,%r15
     +0x1d0: mov     %r12d,%eax
     +0x1d3: lea     (%rsp,%rax,1),%rsi
     +0x1d7: add     $0x10,%rsi
     +0x1db: lea     (%rsp,%r14,1),%rdi
     +0x1df: add     $0xe0,%rdi
     +0x1e6: mov     %r15,%rdx
     +0x1e9: call    <memcpy>
     +0x1ee: add     %r15d,%r12d
     +0x1f1: add     %r15,%r14
     +0x1f4: sub     %r15,%rbx
     +0x1f7: je      <mldsa_poly_uniform+0x230>
     +0x1f9: cmp     $0xa8,%r12d
     +0x200: jne     <mldsa_poly_uniform+0x1c0>
     +0x202: lea     0x10(%rsp),%r13
     +0x207: mov     %r13,%rdi
     +0x20a: call    <mldsa_keccakf1600_permute>
     +0x20f: cmp     $0xa8,%rbx
     +0x216: mov     $0xa8,%r15d
     +0x21c: cmovb   %rbx,%r15
     +0x220: xor     %r12d,%r12d
     +0x223: mov     %r13,%rsi
     +0x226: jmp     <mldsa_poly_uniform+0x1db>
     +0x228: nopl    0x0(%rax,%rax,1)
     +0x230: mov     %r12d,0xd8(%rsp)
     +0x238: mov     $0x3,%eax
     +0x23d: mov     0x8(%rsp),%rbx
     +0x242: mov     0x4(%rsp),%esi
     +0x246: cs      nopw 0x0(%rax,%rax,1)
     +0x250: movzwl  0xdd(%rsp,%rax,1),%edx
     +0x258: movzbl  0xdf(%rsp,%rax,1),%ecx
     +0x260: and     $0x7f,%ecx
     +0x263: shl     $0x10,%ecx
     +0x266: or      %edx,%ecx
     +0x268: cmp     $0x7fe000,%ecx
     +0x26e: ja      <mldsa_poly_uniform+0x277>
     +0x270: mov     %esi,%edx
     +0x272: inc     %esi
     +0x274: mov     %ecx,(%rbx,%rdx,4)
     +0x277: cmp     $0xa5,%rax
     +0x27d: ja      <mldsa_poly_uniform+0x1a0>
     +0x283: add     $0x3,%rax
     +0x287: cmp     $0x100,%esi
     +0x28d: jb      <mldsa_poly_uniform+0x250>
     +0x28f: jmp     <mldsa_poly_uniform+0x1a0>
     +0x294: pxor    %xmm0,%xmm0
     +0x298: movdqa  %xmm0,0xd0(%rsp)
     +0x2a1: movdqa  %xmm0,0xc0(%rsp)
     +0x2aa: movdqa  %xmm0,0xb0(%rsp)
     +0x2b3: movdqa  %xmm0,0xa0(%rsp)
     +0x2bc: movdqa  %xmm0,0x90(%rsp)
     +0x2c5: movdqa  %xmm0,0x80(%rsp)
     +0x2ce: movdqa  %xmm0,0x70(%rsp)
     +0x2d4: movdqa  %xmm0,0x60(%rsp)
     +0x2da: movdqa  %xmm0,0x50(%rsp)
     +0x2e0: movdqa  %xmm0,0x40(%rsp)
     +0x2e6: movdqa  %xmm0,0x30(%rsp)
     +0x2ec: movdqa  %xmm0,0x20(%rsp)
     +0x2f2: movdqa  %xmm0,0x10(%rsp)
     +0x2f8: lea     0x10(%rsp),%rax
     +0x2fd: lea     0xe0(%rsp),%rbx
     +0x305: mov     $0x348,%edx
     +0x30a: mov     %rbx,%rdi
     +0x30d: xor     %esi,%esi
     +0x30f: call    <memset>
     +0x314: lea     -0x28(%rbp),%rsp
     +0x318: pop     %rbx
     +0x319: pop     %r12
     +0x31b: pop     %r13
     +0x31d: pop     %r14
     +0x31f: pop     %r15
     +0x321: pop     %rbp
     +0x322: xor     %eax,%eax
     +0x324: xor     %ecx,%ecx
     +0x326: xor     %edi,%edi
     +0x328: xor     %edx,%edx
     +0x32a: xor     %esi,%esi
     +0x32c: ret     
 ***)

let MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc
   [layout_range "mldsa_poly_uniform";
    layout_range "plt_memcpy";
    layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The seed is the 34 bytes M at seed, and the polynomial at a  *)
(* becomes mld_poly_uniform M, if the SHAKE128 output of the seed has 256    *)
(* acceptable groups. The function saves RBP, the frame pointer, and five    *)
(* more registers below the return address, lowers RSP by up to 31 bytes to  *)
(* align it to 32 bytes, and then reserves 1088 bytes for the state and the  *)
(* buffer, below which the calls of mldsa_keccakf1600_permute (288 bytes and *)
(* a return address) and memcpy use 296 bytes: 1463 bytes of stack below the *)
(* return address in all.                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> !a seed M pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_uniform_terminates (mld_shake128_stream 34 M) /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 1463),1463); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 1463),1463)]
         [(seed,34); (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa_poly_uniform) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; seed] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(seed,34)) s = M)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                          mld_poly_uniform M i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 1463),1463)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the seed and the stack, with all  *)
(* accesses within the arguments, the stack, the return address and the      *)
(* round constants of Keccak, and the writes within the polynomial and the   *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e a seed M pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_uniform_terminates (mld_shake128_stream 34 M) /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 1463),1463); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 1463),1463)]
         [(seed,34); (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa_poly_uniform) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; seed] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(seed,34)) s = M /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = mld_poly_uniform M i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a seed M mf mc pc
                            (word_sub stackpointer (word 1463)) returnaddress /\
                     memaccess_inbounds e2
                      [seed,34; a,1024;
                       word_sub stackpointer (word 1463),1463; stackpointer,8;
                       word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [a,1024; word_sub stackpointer (word 1463),1463]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 1463),1463)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* seed as above.                                                            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `!mf mc ea el ev.
     memset_full_contract mf ea el ev /\
     memcpy_full_contract mc ea el ev
     ==> exists f_events.
     forall e a seed M pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_uniform_terminates (mld_shake128_stream 34 M) /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 1463),1463); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 1463),1463)]
         [(seed,34); (word pc,libmldsa_size); (word(pc + got_memset),8); (word(pc + got_memcpy),8); (ea,el)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_clang23_O3_mono_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa_poly_uniform) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; seed] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes64(word(pc + got_memcpy))) s = mc /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(seed,34)) s = M /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a seed M mf mc pc
                            (word_sub stackpointer (word 1463)) returnaddress /\
                     memaccess_inbounds e2
                      [seed,34; a,1024;
                       word_sub stackpointer (word 1463),1463; stackpointer,8;
                       word(pc + got_memset),8; word(pc + got_memcpy),8; ea,el;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [a,1024; word_sub stackpointer (word 1463),1463]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 1463),1463)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_CLANG23_O3_MONO_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
