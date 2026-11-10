(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of four polynomials mod q from four seeds by rejection:  *)
(* the statement. This is the code for mldsa_poly_uniform_4x                 *)
(* (mld_poly_uniform_4x in poly.c) from mldsa-native's portable C            *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which absorbs the four seeds of 34 bytes, 64 bytes apart, into a fourfold *)
(* SHAKE128 state, squeezes 5 blocks of 168 bytes of each and samples the    *)
(* coefficients below q from them with mld_rej_uniform_c, and then squeezes  *)
(* one more block of each and samples from all four until each polynomial    *)
(* has 256 coefficients, before releasing the state and zeroing the buffers, *)
(* with a memset that gcc inlines with REP STOSQ, so the direction flag must *)
(* be clear, as the ABI requires on entry. It is verified in the whole image *)
(* (see libmldsa.ml) against mld_poly_uniform of                             *)
(* common/mldsa_native_sampling.ml, using the theorems for the callees, and  *)
(* assuming that the SHAKE128 output of each seed has 256 acceptable groups  *)
(* of 3 bytes (mld_rej_uniform_terminates), without which the code does not  *)
(* terminate. It is also shown to be constant time and memory safe, with the *)
(* events depending on the seeds, which are public (rho and the indices of   *)
(* the matrix entries).                                                      *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake128x4_init_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake128x4_absorb_once_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake128x4_squeezeblocks_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake128x4_release_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/rej_uniform_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_uniform_4x:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r15
       +0x6  push    r14
       +0x8  push    r13
       +0xa  mov     r13, rdi
       +0xd  push    r12
       +0xf  push    rbx
      +0x10  mov     rbx, r8
      +0x13  and     rsp, 0xffffffffffffffe0
      +0x17  sub     rsp, 0x10e0
      +0x1e  lea     r15, [rsp+0x40]
      +0x23  mov     QWORD PTR [rsp], rdi
      +0x27  lea     r12, [rsp+0x6c0]
      +0x2f  mov     rdi, r15
      +0x32  mov     QWORD PTR [rsp+0x20], rsi
      +0x37  lea     r14, [rsp+0x360]
      +0x3f  mov     QWORD PTR [rsp+0x18], rdx
      +0x44  mov     QWORD PTR [rsp+0x10], rcx
      +0x49  mov     QWORD PTR [rsp+0x8], r15
      +0x4e  call    mldsa_shake128x4_init
     after_mldsa_shake128x4_init:
      +0x53  lea     rdx, [rbx+0x40]
      +0x57  mov     rsi, rbx
      +0x5a  mov     rdi, r15
      +0x5d  lea     rcx, [rbx+0x80]
      +0x64  lea     r8, [rbx+0xc0]
      +0x6b  mov     rbx, r15
      +0x6e  mov     r9d, 0x22
      +0x74  call    mldsa_shake128x4_absorb_once
     after_mldsa_shake128x4_absorb_once:
      +0x79  mov     r9, rbx
      +0x7c  mov     rsi, r12
      +0x7f  mov     rdi, r14
      +0x82  lea     rax, [rsp+0xa20]
      +0x8a  mov     r8d, 0x5
      +0x90  mov     QWORD PTR [rsp+0x38], r12
      +0x95  lea     r15, [rsp+0xd80]
      +0x9d  mov     rdx, rax
      +0xa0  mov     rcx, r15
      +0xa3  mov     rbx, rax
      +0xa6  mov     QWORD PTR [rsp+0x30], rax
      +0xab  call    mldsa_shake128x4_squeezeblocks
     after_mldsa_shake128x4_squeezeblocks_1:
      +0xb0  xor     esi, esi
      +0xb2  mov     rdi, r13
      +0xb5  mov     ecx, 0x348
      +0xba  mov     rdx, r14
      +0xbd  call    mld_rej_uniform_c
     after_mld_rej_uniform_c_1:
      +0xc2  mov     rdi, QWORD PTR [rsp+0x20]
      +0xc7  mov     rdx, r12
      +0xca  xor     esi, esi
      +0xcc  mov     ecx, 0x348
      +0xd1  mov     r13d, eax
      +0xd4  call    mld_rej_uniform_c
     after_mld_rej_uniform_c_2:
      +0xd9  mov     rdi, QWORD PTR [rsp+0x18]
      +0xde  mov     rdx, rbx
      +0xe1  xor     esi, esi
      +0xe3  mov     ecx, 0x348
      +0xe8  mov     r12d, eax
      +0xeb  call    mld_rej_uniform_c
     after_mld_rej_uniform_c_3:
      +0xf0  mov     rdi, QWORD PTR [rsp+0x10]
      +0xf5  xor     esi, esi
      +0xf7  mov     rdx, r15
      +0xfa  mov     ecx, 0x348
      +0xff  mov     ebx, eax
     +0x101  call    mld_rej_uniform_c
     after_mld_rej_uniform_c_4:
     +0x106  cmp     r12d, 0xff
     +0x10d  mov     r10d, eax
     +0x110  setbe   al
     +0x113  cmp     r13d, 0xff
     +0x11a  jmp     join2
     +0x11f  nop
     join1:
     +0x120  mov     r9, QWORD PTR [rsp+0x8]
     +0x125  mov     rdx, QWORD PTR [rsp+0x30]
     +0x12a  mov     rcx, r15
     +0x12d  mov     rdi, r14
     +0x130  mov     rsi, QWORD PTR [rsp+0x38]
     +0x135  mov     r8d, 0x1
     +0x13b  mov     DWORD PTR [rsp+0x2c], r10d
     +0x140  call    mldsa_shake128x4_squeezeblocks
     after_mldsa_shake128x4_squeezeblocks_2:
     +0x145  mov     rdi, QWORD PTR [rsp]
     +0x149  mov     esi, r13d
     +0x14c  mov     rdx, r14
     +0x14f  mov     ecx, 0xa8
     +0x154  call    mld_rej_uniform_c
     after_mld_rej_uniform_c_5:
     +0x159  mov     rdx, QWORD PTR [rsp+0x38]
     +0x15e  mov     rdi, QWORD PTR [rsp+0x20]
     +0x163  mov     esi, r12d
     +0x166  mov     ecx, 0xa8
     +0x16b  mov     r13d, eax
     +0x16e  call    mld_rej_uniform_c
     after_mld_rej_uniform_c_6:
     +0x173  mov     rdx, QWORD PTR [rsp+0x30]
     +0x178  mov     rdi, QWORD PTR [rsp+0x18]
     +0x17d  mov     esi, ebx
     +0x17f  mov     ecx, 0xa8
     +0x184  mov     r12d, eax
     +0x187  call    mld_rej_uniform_c
     after_mld_rej_uniform_c_7:
     +0x18c  mov     esi, DWORD PTR [rsp+0x2c]
     +0x190  mov     rdi, QWORD PTR [rsp+0x10]
     +0x195  mov     rdx, r15
     +0x198  mov     ecx, 0xa8
     +0x19d  mov     ebx, eax
     +0x19f  call    mld_rej_uniform_c
     after_mld_rej_uniform_c_8:
     +0x1a4  cmp     r13d, 0xff
     +0x1ab  mov     r10d, eax
     +0x1ae  setbe   al
     +0x1b1  cmp     r12d, 0xff
     join2:
     +0x1b8  setbe   dl
     +0x1bb  or      eax, edx
     +0x1bd  cmp     ebx, 0xff
     +0x1c3  setbe   dl
     +0x1c6  or      al, dl
     +0x1c8  jne     join1
     +0x1ce  cmp     r10d, 0xff
     +0x1d5  jbe     join1
     +0x1db  mov     rdi, QWORD PTR [rsp+0x8]
     +0x1e0  call    mldsa_shake128x4_release
     after_mldsa_shake128x4_release:
     +0x1e5  xor     eax, eax
     +0x1e7  mov     rdi, r14
     +0x1ea  mov     ecx, 0x1b0
     +0x1ef  rep stos QWORD PTR es:[rdi], rax
     +0x1f2  lea     rsp, [rbp-0x28]
     +0x1f6  pop     rbx
     +0x1f7  pop     r12
     +0x1f9  pop     r13
     +0x1fb  pop     r14
     +0x1fd  pop     r15
     +0x1ff  pop     rbp
     ret:
     +0x200  ret
 ***)

let MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_poly_uniform_4x"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The seeds are the 34 bytes M0, ..., M3 at seed, seed + 64,   *)
(* seed + 128 and seed + 192, and polynomial j becomes mld_poly_uniform Mj,  *)
(* if the SHAKE128 output of each seed has 256 acceptable groups. The        *)
(* function saves RBP, the frame pointer, and five more registers below the  *)
(* return address, lowers RSP by up to 31 bytes to align it to 32 bytes, and *)
(* then reserves 4320 bytes for the arguments, the state and the buffers,    *)
(* below which the call of mldsa_shake128x4_absorb_once uses 424 bytes, with *)
(* its return address: 4823 bytes of stack below the return address in all.  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!vec0 vec1 vec2 vec3 seed M0 M1 M2 M3 pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_uniform_terminates (mld_shake128_stream 34 M0) /\
        mld_rej_uniform_terminates (mld_shake128_stream 34 M1) /\
        mld_rej_uniform_terminates (mld_shake128_stream 34 M2) /\
        mld_rej_uniform_terminates (mld_shake128_stream 34 M3) /\
        PAIRWISE nonoverlapping
         [(vec0,1024); (vec1,1024); (vec2,1024); (vec3,1024);
          (word_sub stackpointer (word 4823),4823)] /\
        ALLPAIRS nonoverlapping
         [(vec0,1024); (vec1,1024); (vec2,1024); (vec3,1024)]
         [(stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(vec0,1024); (vec1,1024); (vec2,1024); (vec3,1024);
          (word_sub stackpointer (word 4823),4823)]
         [(seed,34); (word_add seed (word 64),34);
          (word_add seed (word 128),34); (word_add seed (word 192),34);
          (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_uniform_4x) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [vec0; vec1; vec2; vec3; seed] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,34)) s = M0 /\
                  read (memory :> bytes(word_add seed (word 64),34)) s = M1 /\
                  read (memory :> bytes(word_add seed (word 128),34)) s = M2 /\
                  read (memory :> bytes(word_add seed (word 192),34)) s = M3)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add vec0 (word(4 * i))))
                             s = mld_poly_uniform M0 i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add vec1 (word(4 * i))))
                             s = mld_poly_uniform M1 i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add vec2 (word(4 * i))))
                             s = mld_poly_uniform M2 i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add vec3 (word(4 * i))))
                             s = mld_poly_uniform M3 i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(vec0,1024); memory :> bytes(vec1,1024);
                memory :> bytes(vec2,1024); memory :> bytes(vec3,1024);
                memory :> bytes(word_sub stackpointer (word 4823),4823)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the seeds and the stack, with all *)
(* accesses within the arguments, the stack, the return address and the      *)
(* round constants of Keccak, and the writes within the polynomials and the  *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e vec0 vec1 vec2 vec3 seed M0 M1 M2 M3 pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_uniform_terminates (mld_shake128_stream 34 M0) /\
        mld_rej_uniform_terminates (mld_shake128_stream 34 M1) /\
        mld_rej_uniform_terminates (mld_shake128_stream 34 M2) /\
        mld_rej_uniform_terminates (mld_shake128_stream 34 M3) /\
        PAIRWISE nonoverlapping
         [(vec0,1024); (vec1,1024); (vec2,1024); (vec3,1024);
          (word_sub stackpointer (word 4823),4823)] /\
        ALLPAIRS nonoverlapping
         [(vec0,1024); (vec1,1024); (vec2,1024); (vec3,1024)]
         [(stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(vec0,1024); (vec1,1024); (vec2,1024); (vec3,1024);
          (word_sub stackpointer (word 4823),4823)]
         [(seed,34); (word_add seed (word 64),34);
          (word_add seed (word 128),34); (word_add seed (word 192),34);
          (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_uniform_4x) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [vec0; vec1; vec2; vec3; seed] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,34)) s = M0 /\
                  read (memory :> bytes(word_add seed (word 64),34)) s = M1 /\
                  read (memory :> bytes(word_add seed (word 128),34)) s = M2 /\
                  read (memory :> bytes(word_add seed (word 192),34)) s = M3 /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add vec0 (word(4 * i))))
                             s = mld_poly_uniform M0 i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add vec1 (word(4 * i))))
                             s = mld_poly_uniform M1 i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add vec2 (word(4 * i))))
                             s = mld_poly_uniform M2 i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add vec3 (word(4 * i))))
                             s = mld_poly_uniform M3 i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events vec0 vec1 vec2 vec3 seed M0 M1 M2 M3 pc
                            (word_sub stackpointer (word 4823)) returnaddress /\
                     memaccess_inbounds e2
                      [seed,34; word_add seed (word 64),34;
                       word_add seed (word 128),34;
                       word_add seed (word 192),34;
                       vec0,1024; vec1,1024; vec2,1024; vec3,1024;
                       word_sub stackpointer (word 4823),4823; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [vec0,1024; vec1,1024; vec2,1024; vec3,1024;
                       word_sub stackpointer (word 4823),4823]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(vec0,1024); memory :> bytes(vec1,1024);
                memory :> bytes(vec2,1024); memory :> bytes(vec3,1024);
                memory :> bytes(word_sub stackpointer (word 4823),4823)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* seeds as above.                                                           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e vec0 vec1 vec2 vec3 seed M0 M1 M2 M3 pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_uniform_terminates (mld_shake128_stream 34 M0) /\
        mld_rej_uniform_terminates (mld_shake128_stream 34 M1) /\
        mld_rej_uniform_terminates (mld_shake128_stream 34 M2) /\
        mld_rej_uniform_terminates (mld_shake128_stream 34 M3) /\
        PAIRWISE nonoverlapping
         [(vec0,1024); (vec1,1024); (vec2,1024); (vec3,1024);
          (word_sub stackpointer (word 4823),4823)] /\
        ALLPAIRS nonoverlapping
         [(vec0,1024); (vec1,1024); (vec2,1024); (vec3,1024)]
         [(stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(vec0,1024); (vec1,1024); (vec2,1024); (vec3,1024);
          (word_sub stackpointer (word 4823),4823)]
         [(seed,34); (word_add seed (word 64),34);
          (word_add seed (word 128),34); (word_add seed (word 192),34);
          (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_uniform_4x) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [vec0; vec1; vec2; vec3; seed] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,34)) s = M0 /\
                  read (memory :> bytes(word_add seed (word 64),34)) s = M1 /\
                  read (memory :> bytes(word_add seed (word 128),34)) s = M2 /\
                  read (memory :> bytes(word_add seed (word 192),34)) s = M3 /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events vec0 vec1 vec2 vec3 seed M0 M1 M2 M3 pc
                            (word_sub stackpointer (word 4823)) returnaddress /\
                     memaccess_inbounds e2
                      [seed,34; word_add seed (word 64),34;
                       word_add seed (word 128),34;
                       word_add seed (word 192),34;
                       vec0,1024; vec1,1024; vec2,1024; vec3,1024;
                       word_sub stackpointer (word 4823),4823; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [vec0,1024; vec1,1024; vec2,1024; vec3,1024;
                       word_sub stackpointer (word 4823),4823]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(vec0,1024); memory :> bytes(vec1,1024);
                memory :> bytes(vec2,1024); memory :> bytes(vec3,1024);
                memory :> bytes(word_sub stackpointer (word 4823),4823)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_4X_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
