(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Product of a row of the matrix with a vector, in the NTT domain, with the *)
(* entries sampled on demand: the statement. This is the code for            *)
(* mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy                      *)
(* (mld_polyvec_matrix_pointwise_montgomery_row_lazy in polyvec_lazy.c) from *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 and  *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md). It copies the seed    *)
(* rho from the structure mld_polymat_lazy at mat into a buffer of 64 bytes  *)
(* on the stack, samples entry (i,0) of the matrix into t with               *)
(* mldsa_poly_uniform (with the bytes 0 and i after rho) and multiplies it   *)
(* by polynomial 0 of v with mldsa_poly_pointwise_montgomery, and then for   *)
(* each column j = 1, ..., 4 samples entry (i,j) into the polynomial of      *)
(* the structure, multiplies it by polynomial j of v and adds it to t with   *)
(* mldsa_poly_add, and finally reduces t with mldsa_poly_reduce and zeroes   *)
(* the buffer. The frame is aligned to 32 bytes. It is verified in the whole *)
(* image (see libmldsa.ml) against mld_polyvec_matrix_row_lazy of            *)
(* common/mldsa_native_polyvec_lazy.ml, using the theorems for the callees,  *)
(* and shown to be constant time and memory safe, with the events depending  *)
(* on rho (from which the matrix is public) and the addresses.               *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec_lazy.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_uniform_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_pointwise_montgomery_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_add_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_reduce_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r15
       +0x6  mov     r15d, 0x1
       +0xc  push    r14
       +0xe  push    r13
      +0x10  mov     r13, rdi
      +0x13  push    r12
      +0x15  mov     r12, rsi
      +0x18  push    rbx
      +0x19  mov     rbx, rdx
      +0x1c  and     rsp, 0xffffffffffffffe0
      +0x20  sub     rsp, 0x60
      +0x24  movdqu  xmm1, XMMWORD PTR [rsi+0x400]
      +0x2c  movdqu  xmm2, XMMWORD PTR [rsi+0x410]
      +0x34  lea     r14, [rsp+0x20]
      +0x39  mov     BYTE PTR [rsp+0x1f], cl
      +0x3d  mov     rsi, r14
      +0x40  mov     BYTE PTR [rsp+0x41], cl
      +0x44  movaps  XMMWORD PTR [rsp+0x20], xmm1
      +0x49  movaps  XMMWORD PTR [rsp+0x30], xmm2
      +0x4e  mov     BYTE PTR [rsp+0x40], 0x0
      +0x53  call    mldsa_poly_uniform
     after_mldsa_poly_uniform_1:
      +0x58  mov     rsi, rbx
      +0x5b  mov     rdi, r13
      +0x5e  add     rbx, 0x400
      +0x65  call    mldsa_poly_pointwise_montgomery
     loop1:
     after_mldsa_poly_pointwise_montgomery_1:
      +0x6a  movzx   eax, BYTE PTR [rsp+0x1f]
      +0x6f  mov     rsi, r14
      +0x72  mov     rdi, r12
      +0x75  mov     BYTE PTR [rsp+0x40], r15b
      +0x7a  add     r15d, 0x1
      +0x7e  mov     BYTE PTR [rsp+0x41], al
      +0x82  call    mldsa_poly_uniform
     after_mldsa_poly_uniform_2:
      +0x87  mov     rsi, rbx
      +0x8a  mov     rdi, r12
      +0x8d  add     rbx, 0x400
      +0x94  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_2:
      +0x99  mov     rsi, r12
      +0x9c  mov     rdi, r13
      +0x9f  call    mldsa_poly_add
     loop1_test: after_mldsa_poly_add:
      +0xa4  cmp     r15d, 0x5
     loop1_back:
      +0xa8  jne     loop1
     loop1_exit:
      +0xaa  mov     rdi, r13
      +0xad  call    mldsa_poly_reduce
     after_mldsa_poly_reduce:
      +0xb2  pxor    xmm0, xmm0
      +0xb6  movaps  XMMWORD PTR [rsp+0x20], xmm0
      +0xbb  movaps  XMMWORD PTR [rsp+0x30], xmm0
      +0xc0  movaps  XMMWORD PTR [rsp+0x40], xmm0
      +0xc5  movaps  XMMWORD PTR [rsp+0x50], xmm0
      +0xca  lea     rsp, [rbp-0x28]
      +0xce  pop     rbx
      +0xcf  pop     r12
      +0xd1  pop     r13
      +0xd3  pop     r14
      +0xd5  pop     r15
      +0xd7  pop     rbp
     ret:
      +0xd8  ret
 ***)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. Row i of the matrix of 6 rows and 5 columns expanded from    *)
(* the seed rho (32 bytes at mat + 1024, after the polynomial of the         *)
(* structure) times the vector y at v (5 polynomials, in the NTT domain): t  *)
(* becomes mld_polyvec_matrix_row_lazy 5 rho y i, and the polynomial of the  *)
(* structure is overwritten. The sampling of the entries of the matrix must  *)
(* terminate, t and the structure be aligned to 16 bytes (as for             *)
(* mldsa_poly_add and mldsa_poly_reduce) and the direction flag be clear (as *)
(* for mldsa_poly_uniform). The stack is the 1670 bytes below the return     *)
(* address, including the up to 31 bytes by which the code aligns RSP.       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!t mat v rho y i pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        i < 6 /\ mld_matrix_terminates 6 5 rho /\
        aligned 16 t /\ aligned 16 mat /\
        PAIRWISE nonoverlapping
         [(t,1024); (mat,1024); (word_sub stackpointer (word 1670),1670)] /\
        ALLPAIRS nonoverlapping
         [(t,1024); (mat,1024); (word_sub stackpointer (word 1670),1670)]
         [(word pc,libmldsa_size); (word_add mat (word 1024),32); (v,5120)] /\
        ALL (nonoverlapping (stackpointer,8)) [(t,1024); (mat,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s =
                  word(pc +
                   mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [t; mat; v; word i] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(word_add mat (word 1024),32)) s =
                  rho /\
                  (!j. j < 1280
                       ==> read(memory :> bytes32(word_add v (word(4 * j))))
                             s = y j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!k. k < 256
                       ==> read(memory :> bytes32(word_add t (word(4 * k))))
                             s =
                           mld_polyvec_matrix_row_lazy 5 rho y i k))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(t,1024); memory :> bytes(mat,1024);
                memory :> bytes(word_sub stackpointer (word 1670),1670)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of rho, i and the addresses, with all accesses      *)
(* within the arguments, the stack, the return address and the constants of  *)
(* the callees, and the writes within t, the polynomial of the structure and *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e t mat v rho y i pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        i < 6 /\ mld_matrix_terminates 6 5 rho /\
        aligned 16 t /\ aligned 16 mat /\
        PAIRWISE nonoverlapping
         [(t,1024); (mat,1024); (word_sub stackpointer (word 1670),1670)] /\
        ALLPAIRS nonoverlapping
         [(t,1024); (mat,1024); (word_sub stackpointer (word 1670),1670)]
         [(word pc,libmldsa_size); (word_add mat (word 1024),32); (v,5120)] /\
        ALL (nonoverlapping (stackpointer,8)) [(t,1024); (mat,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s =
                  word(pc +
                   mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [t; mat; v; word i] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(word_add mat (word 1024),32)) s =
                  rho /\
                  (!j. j < 1280
                       ==> read(memory :> bytes32(word_add v (word(4 * j))))
                             s = y j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!k. k < 256
                       ==> read(memory :> bytes32(word_add t (word(4 * k))))
                             s =
                           mld_polyvec_matrix_row_lazy 5 rho y i k) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events t mat v rho i pc
                                   (word_sub stackpointer (word 1670))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [t,1024; mat,1024; word_add mat (word 1024),32; v,5120;
                       word_sub stackpointer (word 1670),1670; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + mldsa_poly_reduce_consts),16]
                      [t,1024; mat,1024;
                       word_sub stackpointer (word 1670),1670]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(t,1024); memory :> bytes(mat,1024);
                memory :> bytes(word_sub stackpointer (word 1670),1670)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e t mat v rho i pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        i < 6 /\ mld_matrix_terminates 6 5 rho /\
        aligned 16 t /\ aligned 16 mat /\
        PAIRWISE nonoverlapping
         [(t,1024); (mat,1024); (word_sub stackpointer (word 1670),1670)] /\
        ALLPAIRS nonoverlapping
         [(t,1024); (mat,1024); (word_sub stackpointer (word 1670),1670)]
         [(word pc,libmldsa_size); (word_add mat (word 1024),32); (v,5120)] /\
        ALL (nonoverlapping (stackpointer,8)) [(t,1024); (mat,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s =
                  word(pc +
                   mldsa65_polyvec_matrix_pointwise_montgomery_row_lazy) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [t; mat; v; word i] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(word_add mat (word 1024),32)) s =
                  rho /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events t mat v rho i pc
                                   (word_sub stackpointer (word 1670))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [t,1024; mat,1024; word_add mat (word 1024),32; v,5120;
                       word_sub stackpointer (word 1670),1670; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + mldsa_poly_reduce_consts),16]
                      [t,1024; mat,1024;
                       word_sub stackpointer (word 1670),1670]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(t,1024); memory :> bytes(mat,1024);
                memory :> bytes(word_sub stackpointer (word 1670),1670)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_ROW_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
