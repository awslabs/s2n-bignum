(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The product w = invNTT(A * NTT(y)) of signing, with the entries of A and  *)
(* the polynomials of y sampled on demand: the statement. This is the code   *)
(* for mldsa65_polyvec_matrix_pointwise_montgomery_yvec_lazy                 *)
(* (mld_polyvec_matrix_pointwise_montgomery_yvec_lazy in polyvec_lazy.c)     *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -O2 *)
(* and MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md). It copies the     *)
(* seed rho from the structure mld_polymat_lazy at mat into a buffer of 64   *)
(* bytes on the stack, and then, column by column, for j = 0, ..., 4,        *)
(* samples polynomial j of y into scratch with mldsa65_poly_uniform_gamma1   *)
(* (from the seed rho'' and the nonce kappa + j of the structure             *)
(* mld_yvec_lazy at y) and transforms it with mldsa_poly_ntt, and for each   *)
(* row k = 0, ..., 5 samples entry (k,j) of the matrix with                  *)
(* mldsa_poly_uniform, into polynomial k of w for j = 0 and otherwise into   *)
(* the polynomial of the structure, multiplies it by scratch with            *)
(* mldsa_poly_pointwise_montgomery and, for j > 0, adds it to polynomial k   *)
(* of w with mldsa_poly_add. It then zeroes the buffer, reduces w with       *)
(* mldsa65_polyveck_reduce and transforms it back with                       *)
(* mldsa65_polyveck_invntt_tomont. The frame is aligned to 32 bytes. It is   *)
(* verified in the whole image (see libmldsa.ml) against                     *)
(* mld_polyvec_matrix_yvec_lazy of common/mldsa_native_lazy.ml and           *)
(* mld_sign_y of common/mldsa_native_sign.ml, using the theorems for the     *)
(* callees, and shown to be constant time and memory safe, with the events   *)
(* depending on rho (from which the matrix is public) and the addresses.     *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_lazy.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_uniform_gamma1_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_uniform_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_pointwise_montgomery_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_add_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyveck_reduce_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyveck_invntt_tomont_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa65_polyvec_matrix_pointwise_montgomery_yvec_lazy:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r15
       +0x6  push    r14
       +0x8  mov     r14, rcx
       +0xb  push    r13
       +0xd  mov     r13, rsi
      +0x10  push    r12
      +0x12  xor     r12d, r12d
      +0x15  push    rbx
      +0x16  and     rsp, 0xffffffffffffffe0
      +0x1a  sub     rsp, 0x60
      +0x1e  movdqu  xmm1, XMMWORD PTR [rsi+0x400]
      +0x26  movdqu  xmm2, XMMWORD PTR [rsi+0x410]
      +0x2e  lea     rax, [rsp+0x20]
      +0x33  mov     QWORD PTR [rsp+0x10], rdi
      +0x38  mov     QWORD PTR [rsp+0x8], rdx
      +0x3d  mov     QWORD PTR [rsp+0x18], rax
      +0x42  movaps  XMMWORD PTR [rsp+0x20], xmm1
      +0x47  movaps  XMMWORD PTR [rsp+0x30], xmm2
      +0x4c  nop     DWORD PTR [rax+0x0]
     join1:
      +0x50  mov     rax, QWORD PTR [rsp+0x8]
      +0x55  mov     rdi, r14
      +0x58  xor     r15d, r15d
      +0x5b  movzx   edx, WORD PTR [rax+0x8]
      +0x5f  mov     rsi, QWORD PTR [rax]
      +0x62  add     edx, r12d
      +0x65  movzx   edx, dx
      +0x68  call    mldsa65_poly_uniform_gamma1
     after_mldsa65_poly_uniform_gamma1:
      +0x6d  mov     rdi, r14
      +0x70  call    mldsa_poly_ntt
     after_mldsa_poly_ntt:
      +0x75  mov     rbx, QWORD PTR [rsp+0x10]
      +0x7a  jmp     join4
      +0x7c  nop     DWORD PTR [rax+0x0]
     join2:
      +0x80  mov     rsi, QWORD PTR [rsp+0x18]
      +0x85  mov     rdi, r13
      +0x88  mov     BYTE PTR [rsp+0x40], r12b
      +0x8d  mov     BYTE PTR [rsp+0x41], r15b
      +0x92  call    mldsa_poly_uniform
     after_mldsa_poly_uniform_1:
      +0x97  mov     rsi, r14
      +0x9a  mov     rdi, r13
      +0x9d  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_1:
      +0xa2  mov     rsi, r13
      +0xa5  mov     rdi, rbx
      +0xa8  call    mldsa_poly_add
     join3: after_mldsa_poly_add:
      +0xad  add     r15d, 0x1
      +0xb1  add     rbx, 0x400
      +0xb8  cmp     r15d, 0x6
      +0xbc  je      join5
     join4:
      +0xbe  test    r12d, r12d
      +0xc1  jne     join2
      +0xc3  mov     rsi, QWORD PTR [rsp+0x18]
      +0xc8  mov     rdi, rbx
      +0xcb  mov     BYTE PTR [rsp+0x40], 0x0
      +0xd0  mov     BYTE PTR [rsp+0x41], r15b
      +0xd5  call    mldsa_poly_uniform
     after_mldsa_poly_uniform_2:
      +0xda  mov     rsi, r14
      +0xdd  mov     rdi, rbx
      +0xe0  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_2:
      +0xe5  jmp     join3
      +0xe7  nop     WORD PTR [rax+rax*1+0x0]
     join5:
      +0xf0  add     r12d, 0x1
      +0xf4  cmp     r12d, 0x5
      +0xf8  jne     join1
      +0xfe  pxor    xmm0, xmm0
     +0x102  mov     rax, QWORD PTR [rsp+0x18]
     +0x107  movaps  XMMWORD PTR [rsp+0x20], xmm0
     +0x10c  movaps  XMMWORD PTR [rsp+0x30], xmm0
     +0x111  movaps  XMMWORD PTR [rsp+0x40], xmm0
     +0x116  movaps  XMMWORD PTR [rsp+0x50], xmm0
     +0x11b  mov     rbx, QWORD PTR [rsp+0x10]
     +0x120  mov     rdi, rbx
     +0x123  call    mldsa65_polyveck_reduce
     after_mldsa65_polyveck_reduce:
     +0x128  mov     rdi, rbx
     +0x12b  call    mldsa65_polyveck_invntt_tomont
     after_mldsa65_polyveck_invntt_tomont:
     +0x130  lea     rsp, [rbp-0x28]
     +0x134  pop     rbx
     +0x135  pop     r12
     +0x137  pop     r13
     +0x139  pop     r14
     +0x13b  pop     r15
     +0x13d  pop     rbp
     ret:
     +0x13e  ret
 ***)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_65_GCC12_O2_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa65_polyvec_matrix_pointwise_montgomery_yvec_lazy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The structure mld_yvec_lazy at y holds the address rp of the *)
(* 64 bytes rhoprime and the 16-bit counter kappa, and the structure         *)
(* mld_polymat_lazy at mat the seed rho (32 bytes at mat + 1024, after its   *)
(* polynomial). The vector w (6 polynomials) becomes                         *)
(* mld_polyvec_matrix_yvec_lazy 5 rho (mld_sign_y mld_poly_uniform_gamma1_19 *)
(* rhoprime kappa), while the polynomial of the structure and scratch are    *)
(* overwritten. The sampling of the entries of the matrix must terminate, w  *)
(* and the structure be aligned to 16 bytes and the direction flag be clear. *)
(* The stack is the 1670 bytes below the return address, including the up to *)
(* 31 bytes by which the code aligns RSP.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!w mat y scratch rp rho rhoprime kappa pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 6 5 rho /\
        aligned 16 w /\ aligned 16 mat /\
        PAIRWISE nonoverlapping
         [(w,6144); (mat,1024); (scratch,1024);
          (word_sub stackpointer (word 1670),1670)] /\
        ALLPAIRS nonoverlapping
         [(w,6144); (mat,1024); (scratch,1024);
          (word_sub stackpointer (word 1670),1670)]
         [(word pc,libmldsa_size); (word_add mat (word 1024),32); (y,16);
          (rp,64)] /\
        ALL (nonoverlapping (stackpointer,8))
            [(w,6144); (mat,1024); (scratch,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s =
                  word(pc +
                   mldsa65_polyvec_matrix_pointwise_montgomery_yvec_lazy) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [w; mat; y; scratch] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(word_add mat (word 1024),32)) s =
                  rho /\
                  read (memory :> bytes64 y) s = rp /\
                  read (memory :> bytes16(word_add y (word 8))) s =
                  word kappa /\
                  read (memory :> bytes(rp,64)) s = rhoprime)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 1536
                       ==> read(memory :> bytes32(word_add w (word(4 * i))))
                             s =
                           mld_polyvec_matrix_yvec_lazy 5 rho
                            (mld_sign_y mld_poly_uniform_gamma1_19
                              rhoprime kappa) i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(w,6144); memory :> bytes(mat,1024);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 1670),1670)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of rho and the addresses (the sampling of y is      *)
(* constant time), with all accesses within the arguments, the structures,   *)
(* rhoprime, the stack, the return address and the constants of the callees, *)
(* and the writes within w, the polynomial of the structure, scratch and the *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e w mat y scratch rp rho rhoprime kappa pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 6 5 rho /\
        aligned 16 w /\ aligned 16 mat /\
        PAIRWISE nonoverlapping
         [(w,6144); (mat,1024); (scratch,1024);
          (word_sub stackpointer (word 1670),1670)] /\
        ALLPAIRS nonoverlapping
         [(w,6144); (mat,1024); (scratch,1024);
          (word_sub stackpointer (word 1670),1670)]
         [(word pc,libmldsa_size); (word_add mat (word 1024),32); (y,16);
          (rp,64)] /\
        ALL (nonoverlapping (stackpointer,8))
            [(w,6144); (mat,1024); (scratch,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s =
                  word(pc +
                   mldsa65_polyvec_matrix_pointwise_montgomery_yvec_lazy) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [w; mat; y; scratch] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(word_add mat (word 1024),32)) s =
                  rho /\
                  read (memory :> bytes64 y) s = rp /\
                  read (memory :> bytes16(word_add y (word 8))) s =
                  word kappa /\
                  read (memory :> bytes(rp,64)) s = rhoprime /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 1536
                       ==> read(memory :> bytes32(word_add w (word(4 * i))))
                             s =
                           mld_polyvec_matrix_yvec_lazy 5 rho
                            (mld_sign_y mld_poly_uniform_gamma1_19
                              rhoprime kappa) i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events w mat y scratch rp rho pc
                                   (word_sub stackpointer (word 1670))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [w,6144; mat,1024; word_add mat (word 1024),32; y,16;
                       scratch,1024; rp,64;
                       word_sub stackpointer (word 1670),1670; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_reduce_consts),16]
                      [w,6144; mat,1024; scratch,1024;
                       word_sub stackpointer (word 1670),1670]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(w,6144); memory :> bytes(mat,1024);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 1670),1670)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e w mat y scratch rp rho kappa pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 6 5 rho /\
        aligned 16 w /\ aligned 16 mat /\
        PAIRWISE nonoverlapping
         [(w,6144); (mat,1024); (scratch,1024);
          (word_sub stackpointer (word 1670),1670)] /\
        ALLPAIRS nonoverlapping
         [(w,6144); (mat,1024); (scratch,1024);
          (word_sub stackpointer (word 1670),1670)]
         [(word pc,libmldsa_size); (word_add mat (word 1024),32); (y,16);
          (rp,64)] /\
        ALL (nonoverlapping (stackpointer,8))
            [(w,6144); (mat,1024); (scratch,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s =
                  word(pc +
                   mldsa65_polyvec_matrix_pointwise_montgomery_yvec_lazy) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [w; mat; y; scratch] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(word_add mat (word 1024),32)) s =
                  rho /\
                  read (memory :> bytes64 y) s = rp /\
                  read (memory :> bytes16(word_add y (word 8))) s =
                  word kappa /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events w mat y scratch rp rho pc
                                   (word_sub stackpointer (word 1670))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [w,6144; mat,1024; word_add mat (word 1024),32; y,16;
                       scratch,1024; rp,64;
                       word_sub stackpointer (word 1670),1670; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_reduce_consts),16]
                      [w,6144; mat,1024; scratch,1024;
                       word_sub stackpointer (word 1670),1670]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(w,6144); memory :> bytes(mat,1024);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 1670),1670)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
