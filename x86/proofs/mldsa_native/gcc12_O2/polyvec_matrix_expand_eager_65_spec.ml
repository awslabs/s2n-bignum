(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Expansion of the matrix from rho: the statement. This is the code for     *)
(* mldsa65_polyvec_matrix_expand_eager (mld_polyvec_matrix_expand_eager in   *)
(* polyvec_lazy.c) from mldsa-native's portable C implementation compiled by *)
(* gcc 12 with -O2 (see mldsa_native/README.md), which copies rho into four  *)
(* seed buffers on the stack and samples 28 of the 30 entries four at a time *)
(* with mldsa_poly_uniform_4x, appending j and i to rho for entry (i,j), and *)
(* the last two with mldsa_poly_uniform, before zeroing the buffers, with a  *)
(* memset that gcc inlines with REP STOSQ, so the direction flag must be     *)
(* clear, as the ABI requires on entry. It is verified in the whole image    *)
(* (see libmldsa.ml) against mld_polyvec_matrix_expand of                    *)
(* common/mldsa_native_sampling.ml, using the theorems for the callees,      *)
(* assuming that sampling terminates for each entry (mld_matrix_terminates), *)
(* and shown to be constant time and memory safe, with the events depending  *)
(* on rho, which is public.                                                  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_uniform_4x_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_uniform_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_polyvec_matrix_expand_eager:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r15
       +0x6  push    r14
       +0x8  mov     r14, rdi
       +0xb  push    r13
       +0xd  push    r12
       +0xf  push    rbx
      +0x10  and     rsp, 0xffffffffffffffe0
      +0x14  sub     rsp, 0x100
      +0x1b  movdqu  xmm1, XMMWORD PTR [rsi]
      +0x1f  movdqu  xmm0, XMMWORD PTR [rsi+0x10]
      +0x24  mov     rbx, rsp
      +0x27  lea     r15, [rsp+0x100]
      +0x2f  mov     rax, rbx
     loop1:
      +0x32  movaps  XMMWORD PTR [rax], xmm1
      +0x35  add     rax, 0x40
      +0x39  movaps  XMMWORD PTR [rax-0x30], xmm0
     loop1_test:
      +0x3d  cmp     r15, rax
     loop1_back:
      +0x40  jne     loop1
     loop1_exit:
      +0x42  xor     r12d, r12d
      +0x45  mov     r13d, 0xcccccccd
      +0x4b  nop     DWORD PTR [rax+rax*1+0x0]
     loop2:
      +0x50  mov     rdx, rbx
      +0x53  mov     ecx, r12d
     loop3:
      +0x56  mov     eax, ecx
      +0x58  mov     esi, ecx
      +0x5a  add     rdx, 0x40
      +0x5e  add     ecx, 0x1
      +0x61  imul    rax, r13
      +0x65  shr     rax, 0x22
      +0x69  lea     edi, [rax+rax*4]
      +0x6c  mov     BYTE PTR [rdx-0x1f], al
      +0x6f  sub     esi, edi
      +0x71  mov     BYTE PTR [rdx-0x20], sil
     loop3_test:
      +0x75  cmp     r15, rdx
     loop3_back:
      +0x78  jne     loop3
     loop3_exit:
      +0x7a  lea     eax, [r12+0x3]
      +0x7f  lea     esi, [r12+0x2]
      +0x84  mov     rdx, rax
      +0x87  imul    rax, r13
      +0x8b  lea     edi, [r12+0x1]
      +0x90  shr     rax, 0x22
      +0x94  mov     ecx, eax
      +0x96  lea     eax, [rax+rax*4]
      +0x99  sub     edx, eax
      +0x9b  mov     eax, esi
      +0x9d  lea     rcx, [rcx+rcx*4]
      +0xa1  imul    rax, r13
      +0xa5  add     rcx, rdx
      +0xa8  shl     rcx, 0xa
      +0xac  add     rcx, r14
      +0xaf  shr     rax, 0x22
      +0xb3  mov     edx, eax
      +0xb5  lea     eax, [rax+rax*4]
      +0xb8  sub     esi, eax
      +0xba  mov     eax, edi
      +0xbc  lea     rdx, [rdx+rdx*4]
      +0xc0  imul    rax, r13
      +0xc4  add     rdx, rsi
      +0xc7  shl     rdx, 0xa
      +0xcb  add     rdx, r14
      +0xce  shr     rax, 0x22
      +0xd2  mov     esi, eax
      +0xd4  lea     eax, [rax+rax*4]
      +0xd7  sub     edi, eax
      +0xd9  mov     eax, r12d
      +0xdc  lea     rsi, [rsi+rsi*4]
      +0xe0  imul    rax, r13
      +0xe4  add     rsi, rdi
      +0xe7  shl     rsi, 0xa
      +0xeb  add     rsi, r14
      +0xee  shr     rax, 0x22
      +0xf2  lea     r8d, [rax+rax*4]
      +0xf6  mov     edi, eax
      +0xf8  mov     eax, r12d
      +0xfb  add     r12d, 0x4
      +0xff  sub     eax, r8d
     +0x102  lea     rdi, [rdi+rdi*4]
     +0x106  mov     r8, rbx
     +0x109  add     rdi, rax
     +0x10c  shl     rdi, 0xa
     +0x110  add     rdi, r14
     +0x113  call    mldsa_poly_uniform_4x
     loop2_test: after_mldsa_poly_uniform_4x:
     +0x118  cmp     r12d, 0x1c
     loop2_back:
     +0x11c  jne     loop2
     loop2_exit:
     +0x122  movzx   eax, WORD PTR [rip+0x5579]
                      // mldsa65_polyvec_matrix_expand_eager_const1
     +0x129  lea     rdi, [r14+0x7000]
     +0x130  mov     rsi, rbx
     +0x133  mov     WORD PTR [rsp+0x20], ax
     +0x138  call    mldsa_poly_uniform
     after_mldsa_poly_uniform_1:
     +0x13d  movzx   eax, WORD PTR [rip+0x5560]
                      // mldsa65_polyvec_matrix_expand_eager_const2
     +0x144  lea     rdi, [r14+0x7400]
     +0x14b  mov     rsi, rbx
     +0x14e  mov     WORD PTR [rsp+0x20], ax
     +0x153  call    mldsa_poly_uniform
     after_mldsa_poly_uniform_2:
     +0x158  xor     eax, eax
     +0x15a  mov     rdi, rbx
     +0x15d  mov     ecx, 0x20
     +0x162  rep stos QWORD PTR es:[rdi], rax
     +0x165  lea     rsp, [rbp-0x28]
     +0x169  pop     rbx
     +0x16a  pop     r12
     +0x16c  pop     r13
     +0x16e  pop     r14
     +0x170  pop     r15
     +0x172  pop     rbp
     ret:
     +0x173  ret
 ***)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_polyvec_matrix_expand_eager"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The 32 bytes r of rho; the matrix at mat, 6 rows of 5        *)
(* polynomials, becomes mld_polyvec_matrix_expand 5 r if sampling terminates *)
(* for each entry. The function saves RBP, the frame pointer, and five more  *)
(* registers below the return address, lowers RSP by up to 31 bytes to align *)
(* it to 32 bytes, and then reserves 256 bytes for the four seed buffers,    *)
(* below which the calls of mldsa_poly_uniform_4x use 4831 bytes, with their *)
(* return addresses (and those of mldsa_poly_uniform fewer): 5166 bytes of   *)
(* stack below the return address in all.                                    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mat rho r pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 6 5 r /\
        nonoverlapping (mat,30720) (word_sub stackpointer (word 5166),5166) /\
        nonoverlapping (mat,30720) (stackpointer,8) /\
        ALLPAIRS nonoverlapping
         [(mat,30720); (word_sub stackpointer (word 5166),5166)]
         [(rho,32); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                  word (pc + mldsa65_polyvec_matrix_expand_eager) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [mat; rho] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(rho,32)) s = r)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!n. n < 7680
                       ==> read(memory :> bytes32(word_add mat (word(4 * n))))
                             s = mld_polyvec_matrix_expand 5 r n))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(mat,30720);
                memory :> bytes(word_sub stackpointer (word 5166),5166)])`;;

let
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, rho and the stack, with all       *)
(* accesses within rho, the matrix, the stack, the return address, the round *)
(* constants of Keccak and the two 16-bit constants with the indices of the  *)
(* last two entries (which the x86 code loads from the read-only data), and  *)
(* the writes within the matrix and the stack.                               *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e mat rho r pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 6 5 r /\
        nonoverlapping (mat,30720) (word_sub stackpointer (word 5166),5166) /\
        nonoverlapping (mat,30720) (stackpointer,8) /\
        ALLPAIRS nonoverlapping
         [(mat,30720); (word_sub stackpointer (word 5166),5166)]
         [(rho,32); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                  word (pc + mldsa65_polyvec_matrix_expand_eager) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [mat; rho] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(rho,32)) s = r /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!n. n < 7680
                       ==> read(memory :> bytes32(word_add mat (word(4 * n))))
                             s = mld_polyvec_matrix_expand 5 r n) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events mat rho r pc
                            (word_sub stackpointer (word 5166)) returnaddress /\
                     memaccess_inbounds e2
                      [rho,32; mat,30720;
                       word_sub stackpointer (word 5166),5166; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + mldsa65_polyvec_matrix_expand_eager_consts),4]
                      [mat,30720; word_sub stackpointer (word 5166),5166]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(mat,30720);
                memory :> bytes(word_sub stackpointer (word 5166),5166)])`;;

let
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e mat rho r pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 6 5 r /\
        nonoverlapping (mat,30720) (word_sub stackpointer (word 5166),5166) /\
        nonoverlapping (mat,30720) (stackpointer,8) /\
        ALLPAIRS nonoverlapping
         [(mat,30720); (word_sub stackpointer (word 5166),5166)]
         [(rho,32); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                  word (pc + mldsa65_polyvec_matrix_expand_eager) /\
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
                            (word_sub stackpointer (word 5166)) returnaddress /\
                     memaccess_inbounds e2
                      [rho,32; mat,30720;
                       word_sub stackpointer (word 5166),5166; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + mldsa65_polyvec_matrix_expand_eager_consts),4]
                      [mat,30720; word_sub stackpointer (word 5166),5166]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(mat,30720);
                memory :> bytes(word_sub stackpointer (word 5166),5166)])`;;

let
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
 MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_EAGER_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
