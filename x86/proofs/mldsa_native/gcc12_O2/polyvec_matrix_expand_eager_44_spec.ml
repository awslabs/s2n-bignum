(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Expansion of the matrix from rho: the statement. This is the code for     *)
(* mldsa44_polyvec_matrix_expand_eager (mld_polyvec_matrix_expand_eager in   *)
(* polyvec_lazy.c) from mldsa-native's portable C implementation compiled by *)
(* gcc 12 with -O2 (see mldsa_native/README.md), which copies rho into four  *)
(* seed buffers on the stack and samples the 16 entries four at a time with  *)
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

    mldsa44_polyvec_matrix_expand_eager:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r14
       +0x6  push    r13
       +0x8  mov     r13, rdi
       +0xb  push    r12
       +0xd  push    rbx
       +0xe  and     rsp, 0xffffffffffffffe0
      +0x12  sub     rsp, 0x100
      +0x19  movdqu  xmm1, XMMWORD PTR [rsi]
      +0x1d  movdqu  xmm0, XMMWORD PTR [rsi+0x10]
      +0x22  mov     r14, rsp
      +0x25  lea     r12, [rsp+0x100]
      +0x2d  mov     rax, r14
     loop1:
      +0x30  movaps  XMMWORD PTR [rax], xmm1
      +0x33  add     rax, 0x40
      +0x37  movaps  XMMWORD PTR [rax-0x30], xmm0
     loop1_test:
      +0x3b  cmp     r12, rax
     loop1_back:
      +0x3e  jne     loop1
     loop1_exit:
      +0x40  xor     ebx, ebx
     loop2:
      +0x42  mov     rax, r14
      +0x45  mov     edx, ebx
     loop3:
      +0x47  mov     ecx, edx
      +0x49  add     rax, 0x40
      +0x4d  and     ecx, 0x3
      +0x50  mov     BYTE PTR [rax-0x20], cl
      +0x53  mov     ecx, edx
      +0x55  add     edx, 0x1
      +0x58  shr     ecx, 0x2
      +0x5b  mov     BYTE PTR [rax-0x1f], cl
     loop3_test:
      +0x5e  cmp     r12, rax
     loop3_back:
      +0x61  jne     loop3
     loop3_exit:
      +0x63  lea     eax, [rbx+0x3]
      +0x66  mov     edi, ebx
      +0x68  mov     r8, r14
      +0x6b  shr     eax, 0x2
      +0x6e  shr     edi, 0x2
      +0x71  shl     rax, 0xc
      +0x75  shl     rdi, 0xc
      +0x79  lea     rcx, [r13+rax*1+0xc00]
      +0x81  lea     eax, [rbx+0x2]
      +0x84  add     rdi, r13
      +0x87  shr     eax, 0x2
      +0x8a  shl     rax, 0xc
      +0x8e  lea     rdx, [r13+rax*1+0x800]
      +0x96  lea     eax, [rbx+0x1]
      +0x99  add     ebx, 0x4
      +0x9c  shr     eax, 0x2
      +0x9f  shl     rax, 0xc
      +0xa3  lea     rsi, [r13+rax*1+0x400]
      +0xab  call    mldsa_poly_uniform_4x
     loop2_test: after_mldsa_poly_uniform_4x:
      +0xb0  cmp     ebx, 0x10
     loop2_back:
      +0xb3  jne     loop2
     loop2_exit:
      +0xb5  xor     eax, eax
      +0xb7  mov     rdi, r14
      +0xba  mov     ecx, 0x20
      +0xbf  rep stos QWORD PTR es:[rdi], rax
      +0xc2  lea     rsp, [rbp-0x20]
      +0xc6  pop     rbx
      +0xc7  pop     r12
      +0xc9  pop     r13
      +0xcb  pop     r14
      +0xcd  pop     rbp
     ret:
      +0xce  ret
 ***)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_polyvec_matrix_expand_eager"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The 32 bytes r of rho; the matrix at mat, 4 rows of 4        *)
(* polynomials, becomes mld_polyvec_matrix_expand 4 r if sampling terminates *)
(* for each entry. The function saves RBP, the frame pointer, and four more  *)
(* registers below the return address, lowers RSP by up to 31 bytes to align *)
(* it to 32 bytes, and then reserves 256 bytes for the four seed buffers,    *)
(* below which the calls of mldsa_poly_uniform_4x use 4831 bytes, with their *)
(* return addresses: 5158 bytes of stack below the return address in all.    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mat rho r pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 4 4 r /\
        nonoverlapping (mat,16384) (word_sub stackpointer (word 5158),5158) /\
        nonoverlapping (mat,16384) (stackpointer,8) /\
        ALLPAIRS nonoverlapping
         [(mat,16384); (word_sub stackpointer (word 5158),5158)]
         [(rho,32); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                  word (pc + mldsa44_polyvec_matrix_expand_eager) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [mat; rho] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(rho,32)) s = r)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!n. n < 4096
                       ==> read(memory :> bytes32(word_add mat (word(4 * n))))
                             s = mld_polyvec_matrix_expand 4 r n))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(mat,16384);
                memory :> bytes(word_sub stackpointer (word 5158),5158)])`;;

let
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho and the stack, with all       *)
(* accesses within rho, the matrix, the stack, the return address and the    *)
(* round constants of Keccak, and the writes within the matrix and the       *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e mat rho r pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 4 4 r /\
        nonoverlapping (mat,16384) (word_sub stackpointer (word 5158),5158) /\
        nonoverlapping (mat,16384) (stackpointer,8) /\
        ALLPAIRS nonoverlapping
         [(mat,16384); (word_sub stackpointer (word 5158),5158)]
         [(rho,32); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                  word (pc + mldsa44_polyvec_matrix_expand_eager) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [mat; rho] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(rho,32)) s = r /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!n. n < 4096
                       ==> read(memory :> bytes32(word_add mat (word(4 * n))))
                             s = mld_polyvec_matrix_expand 4 r n) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events mat rho r pc
                            (word_sub stackpointer (word 5158)) returnaddress /\
                     memaccess_inbounds e2
                      [rho,32; mat,16384;
                       word_sub stackpointer (word 5158),5158; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [mat,16384; word_sub stackpointer (word 5158),5158]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(mat,16384);
                memory :> bytes(word_sub stackpointer (word 5158),5158)])`;;

let
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e mat rho r pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 4 4 r /\
        nonoverlapping (mat,16384) (word_sub stackpointer (word 5158),5158) /\
        nonoverlapping (mat,16384) (stackpointer,8) /\
        ALLPAIRS nonoverlapping
         [(mat,16384); (word_sub stackpointer (word 5158),5158)]
         [(rho,32); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                  word (pc + mldsa44_polyvec_matrix_expand_eager) /\
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
                      [rho,32; mat,16384;
                       word_sub stackpointer (word 5158),5158; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [mat,16384; word_sub stackpointer (word 5158),5158]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(mat,16384);
                memory :> bytes(word_sub stackpointer (word 5158),5158)])`;;

let
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
