(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The product w = invNTT(A * NTT(y)) of signing, with the entries of A and  *)
(* the polynomials of y sampled on demand: the statement. This is the code   *)
(* for mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy                 *)
(* (mld_polyvec_matrix_pointwise_montgomery_yvec_lazy in polyvec_lazy.c)     *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -O2 *)
(* and MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md). It copies the     *)
(* seed rho from the structure mld_polymat_lazy at mat into a buffer of 64   *)
(* bytes on the stack, and then, column by column, for j = 0, ..., 3,        *)
(* samples polynomial j of y into scratch with mldsa44_poly_uniform_gamma1   *)
(* (from the seed rho'' and the nonce kappa + j of the structure             *)
(* mld_yvec_lazy at y) and transforms it with mldsa_poly_ntt, and for each   *)
(* row k = 0, ..., 3 samples entry (k,j) of the matrix with                  *)
(* mldsa_poly_uniform, into polynomial k of w for j = 0 and otherwise into   *)
(* the polynomial of the structure, multiplies it by scratch with            *)
(* mldsa_poly_pointwise_montgomery and, for j > 0, adds it to polynomial k   *)
(* of w with mldsa_poly_add. It then zeroes the buffer, reduces w with       *)
(* mldsa44_polyveck_reduce and transforms it back with                       *)
(* mldsa44_polyveck_invntt_tomont. The frame is aligned to 32 bytes. It is   *)
(* verified in the whole image (see libmldsa.ml) against mld_yvec_lazy_w of  *)
(* common/mldsa_native_polyvec_lazy.ml, using the theorems for the callees,  *)
(* and shown to be constant time and memory safe, with the events depending  *)
(* on rho (from which the matrix is public) and the addresses.               *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec_lazy.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_uniform_gamma1_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_ntt_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_uniform_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_pointwise_montgomery_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_add_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyveck_reduce_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/polyveck_invntt_tomont_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r15
       +0x6  push    r14
       +0x8  xor     r14d, r14d
       +0xb  push    r13
       +0xd  mov     r13, rcx
      +0x10  push    r12
      +0x12  mov     r12, rsi
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
     join1:
      +0x4c  mov     rax, QWORD PTR [rsp+0x8]
      +0x51  mov     rdi, r13
      +0x54  xor     r15d, r15d
      +0x57  movzx   edx, WORD PTR [rax+0x8]
      +0x5b  mov     rsi, QWORD PTR [rax]
      +0x5e  add     edx, r14d
      +0x61  movzx   edx, dx
      +0x64  call    mldsa44_poly_uniform_gamma1
     after_mldsa44_poly_uniform_gamma1:
      +0x69  mov     rdi, r13
      +0x6c  call    mldsa_poly_ntt
     after_mldsa_poly_ntt:
      +0x71  mov     rbx, QWORD PTR [rsp+0x10]
     join2:
      +0x76  test    r14d, r14d
      +0x79  je      join4
      +0x7f  mov     rsi, QWORD PTR [rsp+0x18]
      +0x84  mov     rdi, r12
      +0x87  mov     BYTE PTR [rsp+0x40], r14b
      +0x8c  mov     BYTE PTR [rsp+0x41], r15b
      +0x91  call    mldsa_poly_uniform
     after_mldsa_poly_uniform_1:
      +0x96  mov     rsi, r13
      +0x99  mov     rdi, r12
      +0x9c  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_1:
      +0xa1  mov     rsi, r12
      +0xa4  mov     rdi, rbx
      +0xa7  call    mldsa_poly_add
     join3: after_mldsa_poly_add:
      +0xac  add     r15d, 0x1
      +0xb0  add     rbx, 0x400
      +0xb7  cmp     r15d, 0x4
      +0xbb  jne     join2
      +0xbd  add     r14d, 0x1
      +0xc1  cmp     r14d, 0x4
      +0xc5  jne     join1
      +0xc7  pxor    xmm0, xmm0
      +0xcb  mov     rax, QWORD PTR [rsp+0x18]
      +0xd0  movaps  XMMWORD PTR [rsp+0x20], xmm0
      +0xd5  movaps  XMMWORD PTR [rsp+0x30], xmm0
      +0xda  movaps  XMMWORD PTR [rsp+0x40], xmm0
      +0xdf  movaps  XMMWORD PTR [rsp+0x50], xmm0
      +0xe4  mov     rbx, QWORD PTR [rsp+0x10]
      +0xe9  mov     rdi, rbx
      +0xec  call    mldsa44_polyveck_reduce
     after_mldsa44_polyveck_reduce:
      +0xf1  mov     rdi, rbx
      +0xf4  call    mldsa44_polyveck_invntt_tomont
     after_mldsa44_polyveck_invntt_tomont:
      +0xf9  lea     rsp, [rbp-0x28]
      +0xfd  pop     rbx
      +0xfe  pop     r12
     +0x100  pop     r13
     +0x102  pop     r14
     +0x104  pop     r15
     +0x106  pop     rbp
     ret:
     +0x107  ret
     +0x108  nop     DWORD PTR [rax+rax*1+0x0]
     join4:
     +0x110  mov     rsi, QWORD PTR [rsp+0x18]
     +0x115  mov     rdi, rbx
     +0x118  mov     BYTE PTR [rsp+0x40], 0x0
     +0x11d  mov     BYTE PTR [rsp+0x41], r15b
     +0x122  call    mldsa_poly_uniform
     after_mldsa_poly_uniform_2:
     +0x127  mov     rsi, r13
     +0x12a  mov     rdi, rbx
     +0x12d  call    mldsa_poly_pointwise_montgomery
     after_mldsa_poly_pointwise_montgomery_2:
     +0x132  jmp     join3
 ***)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The structure mld_yvec_lazy at y holds the address rp of the *)
(* 64 bytes rhoprime and the 16-bit counter kappa, and the structure         *)
(* mld_polymat_lazy at mat the seed rho (32 bytes at mat + 1024, after its   *)
(* polynomial). The vector w (4 polynomials) becomes                         *)
(* mld_yvec_lazy_w 4 mld_poly_uniform_gamma1_17 rho rhoprime kappa, while    *)
(* the polynomial of the structure and scratch are overwritten. The sampling *)
(* of the entries of the matrix must terminate, w and the structure be       *)
(* aligned to 16 bytes and the direction flag be clear. The stack is the     *)
(* 1670 bytes below the return address, including the up to 31 bytes by      *)
(* which the code aligns RSP.                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!w mat y scratch rp rho rhoprime kappa pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 4 4 rho /\
        aligned 16 w /\ aligned 16 mat /\
        PAIRWISE nonoverlapping
         [(w,4096); (mat,1024); (scratch,1024);
          (word_sub stackpointer (word 1670),1670)] /\
        ALLPAIRS nonoverlapping
         [(w,4096); (mat,1024); (scratch,1024);
          (word_sub stackpointer (word 1670),1670)]
         [(word pc,libmldsa_size); (word_add mat (word 1024),32); (y,16);
          (rp,64)] /\
        ALL (nonoverlapping (stackpointer,8))
            [(w,4096); (mat,1024); (scratch,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s =
                  word(pc +
                   mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy) /\
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
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add w (word(4 * i))))
                             s =
                           mld_yvec_lazy_w 4 mld_poly_uniform_gamma1_17
                            rho rhoprime kappa i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(w,4096); memory :> bytes(mat,1024);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 1670),1670)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of rho and the addresses (the sampling of y is      *)
(* constant time), with all accesses within the arguments, the structures,   *)
(* rhoprime, the stack, the return address and the constants of the callees, *)
(* and the writes within w, the polynomial of the structure, scratch and the *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e w mat y scratch rp rho rhoprime kappa pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 4 4 rho /\
        aligned 16 w /\ aligned 16 mat /\
        PAIRWISE nonoverlapping
         [(w,4096); (mat,1024); (scratch,1024);
          (word_sub stackpointer (word 1670),1670)] /\
        ALLPAIRS nonoverlapping
         [(w,4096); (mat,1024); (scratch,1024);
          (word_sub stackpointer (word 1670),1670)]
         [(word pc,libmldsa_size); (word_add mat (word 1024),32); (y,16);
          (rp,64)] /\
        ALL (nonoverlapping (stackpointer,8))
            [(w,4096); (mat,1024); (scratch,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s =
                  word(pc +
                   mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy) /\
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
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add w (word(4 * i))))
                             s =
                           mld_yvec_lazy_w 4 mld_poly_uniform_gamma1_17
                            rho rhoprime kappa i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events w mat y scratch rp rho pc
                                   (word_sub stackpointer (word 1670))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [w,4096; mat,1024; word_add mat (word 1024),32; y,16;
                       scratch,1024; rp,64;
                       word_sub stackpointer (word 1670),1670; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_reduce_consts),16]
                      [w,4096; mat,1024; scratch,1024;
                       word_sub stackpointer (word 1670),1670]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(w,4096); memory :> bytes(mat,1024);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 1670),1670)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e w mat y scratch rp rho kappa pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_matrix_terminates 4 4 rho /\
        aligned 16 w /\ aligned 16 mat /\
        PAIRWISE nonoverlapping
         [(w,4096); (mat,1024); (scratch,1024);
          (word_sub stackpointer (word 1670),1670)] /\
        ALLPAIRS nonoverlapping
         [(w,4096); (mat,1024); (scratch,1024);
          (word_sub stackpointer (word 1670),1670)]
         [(word pc,libmldsa_size); (word_add mat (word 1024),32); (y,16);
          (rp,64)] /\
        ALL (nonoverlapping (stackpointer,8))
            [(w,4096); (mat,1024); (scratch,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s =
                  word(pc +
                   mldsa44_polyvec_matrix_pointwise_montgomery_yvec_lazy) /\
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
                      [w,4096; mat,1024; word_add mat (word 1024),32; y,16;
                       scratch,1024; rp,64;
                       word_sub stackpointer (word 1670),1670; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192;
                       word(pc + rodata_mld_zetas),1024;
                       word(pc + mldsa_poly_reduce_consts),16]
                      [w,4096; mat,1024; scratch,1024;
                       word_sub stackpointer (word 1670),1670]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(w,4096); memory :> bytes(mat,1024);
                memory :> bytes(scratch,1024);
                memory :> bytes(word_sub stackpointer (word 1670),1670)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
