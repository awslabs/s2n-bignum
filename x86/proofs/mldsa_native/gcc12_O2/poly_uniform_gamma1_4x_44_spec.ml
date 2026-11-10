(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of the four polynomials of y in [-gamma1 + 1, gamma1]    *)
(* for ML-DSA-44 (gamma1 = 2^17): the statement. This is the code for        *)
(* mldsa44_poly_uniform_gamma1_4x (mld_poly_uniform_gamma1_4x in poly_kl.c)  *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -O2 *)
(* (see mldsa_native/README.md), which extends the seed of 64 bytes with     *)
(* each of the four 16-bit nonces, absorbs the four into a fourfold SHAKE256 *)
(* state, squeezes 5 blocks of 136 bytes of each and unpacks each polynomial *)
(* from the first 576 bytes with mldsa44_polyz_unpack, before releasing the  *)
(* state and zeroing the buffers and the extended seeds, with memsets that   *)
(* gcc inlines with REP STOSQ, so the direction flag must be clear, as the   *)
(* ABI requires on entry. It is verified in the whole image (see             *)
(* libmldsa.ml) against mld_poly_uniform_gamma1_17 of                        *)
(* common/mldsa_native_sampling.ml, using the theorems for the callees. The  *)
(* nonces are the low 16 bits of the sixth argument and of the three         *)
(* arguments that the caller puts on the stack, as the System V ABI passes   *)
(* them. It is also shown to be constant time and memory safe, with the      *)
(* events depending only on the addresses.                                   *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256x4_init_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256x4_absorb_once_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256x4_squeezeblocks_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake256x4_release_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyz_unpack_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_poly_uniform_gamma1_4x:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r15
       +0x6  push    r14
       +0x8  push    r13
       +0xa  push    r12
       +0xc  push    rbx
       +0xd  and     rsp, 0xffffffffffffffe0
      +0x11  sub     rsp, 0xfe0
      +0x18  movdqu  xmm3, XMMWORD PTR [r8]
      +0x1d  movdqu  xmm2, XMMWORD PTR [r8+0x10]
      +0x23  movdqu  xmm1, XMMWORD PTR [r8+0x20]
      +0x29  movdqu  xmm0, XMMWORD PTR [r8+0x30]
      +0x2f  mov     QWORD PTR [rsp+0x30], rsi
      +0x34  lea     r12, [rsp+0x1c0]
      +0x3c  movaps  XMMWORD PTR [rsp+0x40], xmm3
      +0x41  lea     r13, [rsp+0xa0]
      +0x49  lea     r14, [rsp+0x100]
      +0x51  movaps  XMMWORD PTR [rsp+0x50], xmm2
      +0x56  lea     r15, [rsp+0x160]
      +0x5e  lea     rbx, [rsp+0x40]
      +0x63  movaps  XMMWORD PTR [rsp+0x60], xmm1
      +0x68  movaps  XMMWORD PTR [rsp+0x70], xmm0
      +0x6d  movaps  XMMWORD PTR [rsp+0xa0], xmm3
      +0x75  movaps  XMMWORD PTR [rsp+0xb0], xmm2
      +0x7d  movaps  XMMWORD PTR [rsp+0xc0], xmm1
      +0x85  movaps  XMMWORD PTR [rsp+0xd0], xmm0
      +0x8d  movaps  XMMWORD PTR [rsp+0x100], xmm3
      +0x95  movaps  XMMWORD PTR [rsp+0x110], xmm2
      +0x9d  movaps  XMMWORD PTR [rsp+0x120], xmm1
      +0xa5  movaps  XMMWORD PTR [rsp+0x130], xmm0
      +0xad  movaps  XMMWORD PTR [rsp+0x160], xmm3
      +0xb5  movaps  XMMWORD PTR [rsp+0x170], xmm2
      +0xbd  movaps  XMMWORD PTR [rsp+0x180], xmm1
      +0xc5  movaps  XMMWORD PTR [rsp+0x190], xmm0
      +0xcd  mov     QWORD PTR [rsp+0x28], rdx
      +0xd2  mov     QWORD PTR [rsp+0x20], rcx
      +0xd7  mov     WORD PTR [rsp+0x80], r9w
      +0xe0  mov     QWORD PTR [rsp+0x38], rdi
      +0xe5  mov     eax, DWORD PTR [rbp+0x10]
      +0xe8  mov     rdi, r12
      +0xeb  mov     WORD PTR [rsp+0xe0], ax
      +0xf3  mov     eax, DWORD PTR [rbp+0x18]
      +0xf6  mov     WORD PTR [rsp+0x140], ax
      +0xfe  mov     eax, DWORD PTR [rbp+0x20]
     +0x101  mov     WORD PTR [rsp+0x1a0], ax
     +0x109  call    mldsa_shake256x4_init
     after_mldsa_shake256x4_init:
     +0x10e  mov     r8, r15
     +0x111  mov     rcx, r14
     +0x114  mov     rdx, r13
     +0x117  mov     rsi, rbx
     +0x11a  mov     rdi, r12
     +0x11d  mov     r9d, 0x42
     +0x123  call    mldsa_shake256x4_absorb_once
     after_mldsa_shake256x4_absorb_once:
     +0x128  lea     r13, [rsp+0x4e0]
     +0x130  lea     r11, [rsp+0x7a0]
     +0x138  mov     r9, r12
     +0x13b  lea     r14, [rsp+0xd20]
     +0x143  mov     rsi, r11
     +0x146  mov     r8d, 0x5
     +0x14c  mov     rdi, r13
     +0x14f  lea     r15, [rsp+0xa60]
     +0x157  mov     rcx, r14
     +0x15a  mov     QWORD PTR [rsp+0x18], r11
     +0x15f  mov     rdx, r15
     +0x162  call    mldsa_shake256x4_squeezeblocks
     after_mldsa_shake256x4_squeezeblocks:
     +0x167  mov     rdi, QWORD PTR [rsp+0x38]
     +0x16c  mov     rsi, r13
     +0x16f  call    mldsa44_polyz_unpack
     after_mldsa44_polyz_unpack_1:
     +0x174  mov     rsi, QWORD PTR [rsp+0x18]
     +0x179  mov     rdi, QWORD PTR [rsp+0x30]
     +0x17e  call    mldsa44_polyz_unpack
     after_mldsa44_polyz_unpack_2:
     +0x183  mov     rdi, QWORD PTR [rsp+0x28]
     +0x188  mov     rsi, r15
     +0x18b  call    mldsa44_polyz_unpack
     after_mldsa44_polyz_unpack_3:
     +0x190  mov     rdi, QWORD PTR [rsp+0x20]
     +0x195  mov     rsi, r14
     +0x198  call    mldsa44_polyz_unpack
     after_mldsa44_polyz_unpack_4:
     +0x19d  mov     rdi, r12
     +0x1a0  call    mldsa_shake256x4_release
     after_mldsa_shake256x4_release:
     +0x1a5  xor     eax, eax
     +0x1a7  mov     rdi, r13
     +0x1aa  mov     ecx, 0x160
     +0x1af  rep stos QWORD PTR es:[rdi], rax
     +0x1b2  mov     ecx, 0x30
     +0x1b7  mov     rdi, rbx
     +0x1ba  rep stos QWORD PTR es:[rdi], rax
     +0x1bd  lea     rsp, [rbp-0x28]
     +0x1c1  pop     rbx
     +0x1c2  pop     r12
     +0x1c4  pop     r13
     +0x1c6  pop     r14
     +0x1c8  pop     r15
     +0x1ca  pop     rbp
     ret:
     +0x1cb  ret
 ***)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_poly_uniform_gamma1_4x"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The seed is the 64 bytes sd at seed, and polynomial j        *)
(* becomes mld_poly_uniform_gamma1_17 sd of the nonce j, the low 16 bits of  *)
(* nj. The nonces n1, n2 and n3 are in the 8 bytes each above the return     *)
(* address. The function saves RBP, the frame pointer, and five more         *)
(* registers below the return address, lowers RSP by up to 31 bytes to align *)
(* it to 32 bytes, and then reserves 4064 bytes for the arguments, the       *)
(* extended seeds, the state and the buffers, below which the call of        *)
(* mldsa_shake256x4_absorb_once uses 424 bytes, with its return address:     *)
(* 4567 bytes of stack below the return address in all.                      *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r0 r1 r2 r3 seed sd n0 n1 n2 n3 pc stackpointer
   returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 4567),4567)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024)]
         [(stackpointer,32)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 4567),4567)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_poly_uniform_gamma1_4x) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r0; r1; r2; r3; seed; n0] s /\
                  read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                  n1 /\
                  read (memory :> bytes64 (word_add stackpointer (word 16))) s =
                  n2 /\
                  read (memory :> bytes64 (word_add stackpointer (word 24))) s =
                  n3 /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,64)) s = sd)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r0 (word(4 * i))))
                             s =
                             mld_poly_uniform_gamma1_17 sd (word_zx n0) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                             s =
                             mld_poly_uniform_gamma1_17 sd (word_zx n1) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                             s =
                             mld_poly_uniform_gamma1_17 sd (word_zx n2) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                             s =
                             mld_poly_uniform_gamma1_17 sd (word_zx n3) i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                memory :> bytes(word_sub stackpointer (word 4567),4567)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
 MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the stack, with all accesses   *)
(* within the arguments, the stack, the return address and the stack         *)
(* arguments and the round constants of Keccak, and the writes within the    *)
(* polynomials and the stack.                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r0 r1 r2 r3 seed sd n0 n1 n2 n3 pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 4567),4567)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024)]
         [(stackpointer,32)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 4567),4567)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_poly_uniform_gamma1_4x) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r0; r1; r2; r3; seed; n0] s /\
                  read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                  n1 /\
                  read (memory :> bytes64 (word_add stackpointer (word 16))) s =
                  n2 /\
                  read (memory :> bytes64 (word_add stackpointer (word 24))) s =
                  n3 /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,64)) s = sd /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r0 (word(4 * i))))
                             s =
                             mld_poly_uniform_gamma1_17 sd (word_zx n0) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r1 (word(4 * i))))
                             s =
                             mld_poly_uniform_gamma1_17 sd (word_zx n1) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r2 (word(4 * i))))
                             s =
                             mld_poly_uniform_gamma1_17 sd (word_zx n2) i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r3 (word(4 * i))))
                             s =
                             mld_poly_uniform_gamma1_17 sd (word_zx n3) i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r0 r1 r2 r3 seed pc
                            (word_sub stackpointer (word 4567)) returnaddress /\
                     memaccess_inbounds e2
                      [seed,64; r0,1024; r1,1024; r2,1024; r3,1024;
                       word_sub stackpointer (word 4567),4567; stackpointer,32;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [r0,1024; r1,1024; r2,1024; r3,1024;
                       word_sub stackpointer (word 4567),4567]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                memory :> bytes(word_sub stackpointer (word 4567),4567)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r0 r1 r2 r3 seed sd n0 n1 n2 n3 pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 4567),4567)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024)]
         [(stackpointer,32)] /\
        ALLPAIRS nonoverlapping
         [(r0,1024); (r1,1024); (r2,1024); (r3,1024);
          (word_sub stackpointer (word 4567),4567)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_poly_uniform_gamma1_4x) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r0; r1; r2; r3; seed; n0] s /\
                  read (memory :> bytes64 (word_add stackpointer (word 8))) s =
                  n1 /\
                  read (memory :> bytes64 (word_add stackpointer (word 16))) s =
                  n2 /\
                  read (memory :> bytes64 (word_add stackpointer (word 24))) s =
                  n3 /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,64)) s = sd /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r0 r1 r2 r3 seed pc
                            (word_sub stackpointer (word 4567)) returnaddress /\
                     memaccess_inbounds e2
                      [seed,64; r0,1024; r1,1024; r2,1024; r3,1024;
                       word_sub stackpointer (word 4567),4567; stackpointer,32;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [r0,1024; r1,1024; r2,1024; r3,1024;
                       word_sub stackpointer (word 4567),4567]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(r0,1024); memory :> bytes(r1,1024);
                memory :> bytes(r2,1024); memory :> bytes(r3,1024);
                memory :> bytes(word_sub stackpointer (word 4567),4567)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_4X_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
