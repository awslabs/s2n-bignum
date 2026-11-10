(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of one polynomial of y in [-gamma1 + 1, gamma1] for      *)
(* ML-DSA-65 (gamma1 = 2^19): the statement. This is the code for            *)
(* mldsa65_poly_uniform_gamma1 (mld_poly_uniform_gamma1 in poly_kl.c) from   *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 (see *)
(* mldsa_native/README.md), which extends the seed of 64 bytes with the      *)
(* 16-bit nonce (the low 16 bits of the third argument), absorbs it into a   *)
(* SHAKE256 context with mldsa_shake256_init, _absorb and _finalize,         *)
(* squeezes 5 blocks of 136 bytes with mldsa_shake256_squeeze, unpacks the   *)
(* polynomial from the first 640 with mldsa65_polyz_unpack and releases the  *)
(* context, before zeroing the buffer with a memset that gcc inlines with    *)
(* REP STOSQ, so the direction flag must be clear, as the ABI requires on    *)
(* entry, and the extended seed with inlined stores. It is verified in the   *)
(* whole image (see libmldsa.ml) against mld_poly_uniform_gamma1_19 of       *)
(* common/mldsa_native_sampling.ml, using the theorems for the callees, and  *)
(* shown to be constant time and memory safe, with the events depending only *)
(* on the addresses.                                                         *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_init_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_absorb_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_finalize_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_squeeze_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256_release_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyz_unpack_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_poly_uniform_gamma1:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r14
       +0x6  push    r13
       +0x8  mov     r13, rdi
       +0xb  push    r12
       +0xd  push    rbx
       +0xe  and     rsp, 0xffffffffffffffe0
      +0x12  sub     rsp, 0x3e0
      +0x19  movdqu  xmm1, XMMWORD PTR [rsi]
      +0x1d  movdqu  xmm2, XMMWORD PTR [rsi+0x10]
      +0x22  movdqu  xmm3, XMMWORD PTR [rsi+0x20]
      +0x27  movdqu  xmm4, XMMWORD PTR [rsi+0x30]
      +0x2c  lea     r12, [rsp+0x50]
      +0x31  mov     r14, rsp
      +0x34  mov     rdi, r12
      +0x37  movaps  XMMWORD PTR [rsp], xmm1
      +0x3b  lea     rbx, [rsp+0x120]
      +0x43  movaps  XMMWORD PTR [rsp+0x10], xmm2
      +0x48  movaps  XMMWORD PTR [rsp+0x20], xmm3
      +0x4d  movaps  XMMWORD PTR [rsp+0x30], xmm4
      +0x52  mov     WORD PTR [rsp+0x40], dx
      +0x57  call    mldsa_shake256_init
     after_mldsa_shake256_init:
      +0x5c  mov     rsi, r14
      +0x5f  mov     edx, 0x42
      +0x64  mov     rdi, r12
      +0x67  call    mldsa_shake256_absorb
     after_mldsa_shake256_absorb:
      +0x6c  mov     rdi, r12
      +0x6f  call    mldsa_shake256_finalize
     after_mldsa_shake256_finalize:
      +0x74  mov     rdx, r12
      +0x77  mov     rdi, rbx
      +0x7a  mov     esi, 0x2a8
      +0x7f  call    mldsa_shake256_squeeze
     after_mldsa_shake256_squeeze:
      +0x84  mov     rsi, rbx
      +0x87  mov     rdi, r13
      +0x8a  call    mldsa65_polyz_unpack
     after_mldsa65_polyz_unpack:
      +0x8f  mov     rdi, r12
      +0x92  call    mldsa_shake256_release
     after_mldsa_shake256_release:
      +0x97  xor     eax, eax
      +0x99  mov     rdi, rbx
      +0x9c  mov     ecx, 0x55
      +0xa1  rep stos QWORD PTR es:[rdi], rax
      +0xa4  pxor    xmm0, xmm0
      +0xa8  xor     eax, eax
      +0xaa  mov     WORD PTR [rsp+0x40], ax
      +0xaf  movaps  XMMWORD PTR [rsp], xmm0
      +0xb3  movaps  XMMWORD PTR [rsp+0x10], xmm0
      +0xb8  movaps  XMMWORD PTR [rsp+0x20], xmm0
      +0xbd  movaps  XMMWORD PTR [rsp+0x30], xmm0
      +0xc2  lea     rsp, [rbp-0x20]
      +0xc6  pop     rbx
      +0xc7  pop     r12
      +0xc9  pop     r13
      +0xcb  pop     r14
      +0xcd  pop     rbp
     ret:
      +0xce  ret
 ***)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_poly_uniform_gamma1"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The seed is the 64 bytes sd at seed, and the polynomial at a *)
(* becomes mld_poly_uniform_gamma1_19 sd of the nonce. The function saves    *)
(* RBP, the frame pointer, and four more registers below the return address, *)
(* lowers RSP by up to 31 bytes to align it to 32 bytes, and then reserves   *)
(* 992 bytes for the extended seed, the context and the buffer, below which  *)
(* the calls of mldsa_shake256_absorb and mldsa_shake256_squeeze use 328     *)
(* bytes, with their return addresses: 1391 bytes of stack below the return  *)
(* address in all.                                                           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a seed sd nonce pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 1391),1391); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 1391),1391)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_poly_uniform_gamma1) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; seed; nonce] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,64)) s = sd)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s =
                             mld_poly_uniform_gamma1_19 sd (word_zx nonce) i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 1391),1391)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the stack, with all accesses   *)
(* within the arguments, the stack, the return address and the round         *)
(* constants of Keccak, and the writes within the polynomial and the stack.  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a seed sd nonce pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 1391),1391); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 1391),1391)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_poly_uniform_gamma1) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; seed; nonce] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,64)) s = sd /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s =
                             mld_poly_uniform_gamma1_19 sd (word_zx nonce) i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a seed pc
                            (word_sub stackpointer (word 1391)) returnaddress /\
                     memaccess_inbounds e2
                      [seed,64; a,1024;
                       word_sub stackpointer (word 1391),1391; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [a,1024; word_sub stackpointer (word 1391),1391]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 1391),1391)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a seed sd nonce pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 1391),1391); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 1391),1391)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_poly_uniform_gamma1) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; seed; nonce] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,64)) s = sd /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a seed pc
                            (word_sub stackpointer (word 1391)) returnaddress /\
                     memaccess_inbounds e2
                      [seed,64; a,1024;
                       word_sub stackpointer (word 1391),1391; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [a,1024; word_sub stackpointer (word 1391),1391]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 1391),1391)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
