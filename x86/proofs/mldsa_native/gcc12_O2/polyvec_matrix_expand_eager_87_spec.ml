(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Expansion of the matrix from rho: the statement. This is the code for     *)
(* mldsa87_polyvec_matrix_expand_eager (mld_polyvec_matrix_expand_eager in   *)
(* polyvec_lazy.c) from mldsa-native's portable C implementation compiled by *)
(* gcc 12 with -O2 (see mldsa_native/README.md), which copies rho into four  *)
(* seed buffers on the stack and samples the 56 entries four at a time with  *)
(* mldsa_poly_uniform_4x, appending j and i to rho for entry (i,j), before   *)
(* zeroing the buffers, with a memset that gcc inlines with REP STOSQ, so    *)
(* the direction flag must be clear, as the ABI requires on entry. It is     *)
(* verified in the whole image (see libmldsa.ml) against                     *)
(* mld_polyvec_matrix_expand of common/mldsa_native_sampling.ml, using the   *)
(* theorem for the callee, assuming that sampling terminates for each entry  *)
(* (mld_matrix_terminates), and shown to be constant time and memory safe,   *)
(* with the events depending on rho, which is public.                        *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_uniform_4x_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa87_polyvec_matrix_expand_eager:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r14
       +0x6  mov     r14, rdi
       +0x9  push    r13
       +0xb  push    r12
       +0xd  push    rbx
       +0xe  and     rsp, 0xffffffffffffffe0
      +0x12  sub     rsp, 0x100
      +0x19  movdqu  xmm1, XMMWORD PTR [rsi]
      +0x1d  movdqu  xmm0, XMMWORD PTR [rsi+0x10]
      +0x22  mov     rbx, rsp
      +0x25  lea     r13, [rsp+0x100]
      +0x2d  mov     rax, rbx
     loop1:
      +0x30  movaps  XMMWORD PTR [rax], xmm1
      +0x33  add     rax, 0x40
      +0x37  movaps  XMMWORD PTR [rax-0x30], xmm0
     loop1_test:
      +0x3b  cmp     r13, rax
     loop1_back:
      +0x3e  jne     loop1
     loop1_exit:
      +0x40  xor     r12d, r12d
      +0x43  nop     DWORD PTR [rax+rax*1+0x0]
     loop2:
      +0x48  mov     rsi, rbx
      +0x4b  mov     ecx, r12d
     loop3:
      +0x4e  mov     edx, ecx
      +0x50  mov     eax, ecx
      +0x52  mov     edi, ecx
      +0x54  add     rsi, 0x40
      +0x58  imul    rdx, rdx, 0x24924925
      +0x5f  add     ecx, 0x1
      +0x62  shr     rdx, 0x20
      +0x66  sub     eax, edx
      +0x68  shr     eax, 1
      +0x6a  add     eax, edx
      +0x6c  shr     eax, 0x2
      +0x6f  lea     edx, [rax*8+0x0]
      +0x76  mov     BYTE PTR [rsi-0x1f], al
      +0x79  sub     edx, eax
      +0x7b  sub     edi, edx
      +0x7d  mov     BYTE PTR [rsi-0x20], dil
     loop3_test:
      +0x81  cmp     r13, rsi
     loop3_back:
      +0x84  jne     loop3
     loop3_exit:
      +0x86  lea     edx, [r12+0x3]
      +0x8b  lea     esi, [r12+0x2]
      +0x90  mov     r8, rdx
      +0x93  imul    rdx, rdx, 0x24924925
      +0x9a  lea     edi, [r12+0x1]
      +0x9f  mov     eax, r8d
      +0xa2  shr     rdx, 0x20
      +0xa6  sub     eax, edx
      +0xa8  shr     eax, 1
      +0xaa  add     eax, edx
      +0xac  shr     eax, 0x2
      +0xaf  mov     edx, eax
      +0xb1  lea     rcx, [rdx*8+0x0]
      +0xb9  sub     rcx, rdx
      +0xbc  lea     edx, [rax*8+0x0]
      +0xc3  sub     edx, eax
      +0xc5  mov     eax, esi
      +0xc7  sub     r8d, edx
      +0xca  mov     edx, esi
      +0xcc  imul    rdx, rdx, 0x24924925
      +0xd3  add     rcx, r8
      +0xd6  shl     rcx, 0xa
      +0xda  add     rcx, r14
      +0xdd  shr     rdx, 0x20
      +0xe1  sub     eax, edx
      +0xe3  shr     eax, 1
      +0xe5  add     eax, edx
      +0xe7  shr     eax, 0x2
      +0xea  mov     r8d, eax
      +0xed  lea     rdx, [r8*8+0x0]
      +0xf5  sub     rdx, r8
      +0xf8  lea     r8d, [rax*8+0x0]
     +0x100  sub     r8d, eax
     +0x103  mov     eax, edi
     +0x105  sub     esi, r8d
     +0x108  add     rdx, rsi
     +0x10b  mov     esi, edi
     +0x10d  imul    rsi, rsi, 0x24924925
     +0x114  shl     rdx, 0xa
     +0x118  add     rdx, r14
     +0x11b  shr     rsi, 0x20
     +0x11f  sub     eax, esi
     +0x121  shr     eax, 1
     +0x123  add     eax, esi
     +0x125  shr     eax, 0x2
     +0x128  mov     r8d, eax
     +0x12b  lea     rsi, [r8*8+0x0]
     +0x133  sub     rsi, r8
     +0x136  lea     r8d, [rax*8+0x0]
     +0x13e  sub     r8d, eax
     +0x141  mov     eax, r12d
     +0x144  sub     edi, r8d
     +0x147  add     rsi, rdi
     +0x14a  mov     edi, r12d
     +0x14d  imul    rdi, rdi, 0x24924925
     +0x154  shl     rsi, 0xa
     +0x158  add     rsi, r14
     +0x15b  shr     rdi, 0x20
     +0x15f  sub     eax, edi
     +0x161  shr     eax, 1
     +0x163  add     eax, edi
     +0x165  shr     eax, 0x2
     +0x168  mov     r8d, eax
     +0x16b  lea     rdi, [r8*8+0x0]
     +0x173  sub     rdi, r8
     +0x176  lea     r8d, [rax*8+0x0]
     +0x17e  sub     r8d, eax
     +0x181  mov     eax, r12d
     +0x184  add     r12d, 0x4
     +0x188  sub     eax, r8d
     +0x18b  mov     r8, rbx
     +0x18e  add     rdi, rax
     +0x191  shl     rdi, 0xa
     +0x195  add     rdi, r14
     +0x198  call    mldsa_poly_uniform_4x
     loop2_test: after_mldsa_poly_uniform_4x:
     +0x19d  cmp     r12d, 0x38
     loop2_back:
     +0x1a1  jne     loop2
     loop2_exit:
     +0x1a7  xor     eax, eax
     +0x1a9  mov     rdi, rbx
     +0x1ac  mov     ecx, 0x20
     +0x1b1  rep stos QWORD PTR es:[rdi], rax
     +0x1b4  lea     rsp, [rbp-0x20]
     +0x1b8  pop     rbx
     +0x1b9  pop     r12
     +0x1bb  pop     r13
     +0x1bd  pop     r14
     +0x1bf  pop     rbp
     ret:
     +0x1c0  ret
 ***)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_polyvec_matrix_expand_eager"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The 32 bytes r of rho; the matrix at mat, 8 rows of 7        *)
(* polynomials, becomes mld_polyvec_matrix_expand 7 r if sampling terminates *)
(* for each entry. The function saves RBP, the frame pointer, and four more  *)
(* registers below the return address, lowers RSP by up to 31 bytes to align *)
(* it to 32 bytes, and then reserves 256 bytes for the four seed buffers,    *)
(* below which the calls of mldsa_poly_uniform_4x use 4831 bytes, with their *)
(* return addresses: 5158 bytes of stack below the return address in all.    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mat rho r pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 8 7 r /\
        nonoverlapping (mat,57344) (word_sub stackpointer (word 5158),5158) /\
        nonoverlapping (mat,57344) (stackpointer,8) /\
        ALLPAIRS nonoverlapping
         [(mat,57344); (word_sub stackpointer (word 5158),5158)]
         [(rho,32); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                  word (pc + mldsa87_polyvec_matrix_expand_eager) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [mat; rho] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(rho,32)) s = r)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!n. n < 14336
                       ==> read(memory :> bytes32(word_add mat (word(4 * n))))
                             s = mld_polyvec_matrix_expand 7 r n))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(mat,57344);
                memory :> bytes(word_sub stackpointer (word 5158),5158)])`;;

let
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho and the stack, with all       *)
(* accesses within rho, the matrix, the stack, the return address and the    *)
(* round constants of Keccak, and the writes within the matrix and the       *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e mat rho r pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 8 7 r /\
        nonoverlapping (mat,57344) (word_sub stackpointer (word 5158),5158) /\
        nonoverlapping (mat,57344) (stackpointer,8) /\
        ALLPAIRS nonoverlapping
         [(mat,57344); (word_sub stackpointer (word 5158),5158)]
         [(rho,32); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                  word (pc + mldsa87_polyvec_matrix_expand_eager) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [mat; rho] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(rho,32)) s = r /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!n. n < 14336
                       ==> read(memory :> bytes32(word_add mat (word(4 * n))))
                             s = mld_polyvec_matrix_expand 7 r n) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events mat rho r pc
                            (word_sub stackpointer (word 5158)) returnaddress /\
                     memaccess_inbounds e2
                      [rho,32; mat,57344;
                       word_sub stackpointer (word 5158),5158; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [mat,57344; word_sub stackpointer (word 5158),5158]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(mat,57344);
                memory :> bytes(word_sub stackpointer (word 5158),5158)])`;;

let
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e mat rho r pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 8 7 r /\
        nonoverlapping (mat,57344) (word_sub stackpointer (word 5158),5158) /\
        nonoverlapping (mat,57344) (stackpointer,8) /\
        ALLPAIRS nonoverlapping
         [(mat,57344); (word_sub stackpointer (word 5158),5158)]
         [(rho,32); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                  word (pc + mldsa87_polyvec_matrix_expand_eager) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [mat; rho] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(rho,32)) s = r /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events mat rho r pc
                            (word_sub stackpointer (word 5158)) returnaddress /\
                     memaccess_inbounds e2
                      [rho,32; mat,57344;
                       word_sub stackpointer (word 5158),5158; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [mat,57344; word_sub stackpointer (word 5158),5158]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(mat,57344);
                memory :> bytes(word_sub stackpointer (word 5158),5158)])`;;

let
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
