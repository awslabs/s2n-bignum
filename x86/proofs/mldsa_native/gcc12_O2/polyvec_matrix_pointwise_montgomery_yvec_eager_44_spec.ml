(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Product of the matrix with a vector, out of the NTT domain: the           *)
(* statement. This is the code for                                           *)
(* mldsa44_polyvec_matrix_pointwise_montgomery_yvec_eager                    *)
(* (mld_polyvec_matrix_pointwise_montgomery_yvec_eager in polyvec_lazy.c)    *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -O2 *)
(* (see mldsa_native/README.md), which copies the vector y to the scratch    *)
(* vector with a REP MOVSQ (the memcpy that gcc inlines), transforms it with *)
(* mldsa44_polyvecl_ntt, computes each polynomial of the product with        *)
(* mldsa44_polyvec_matrix_pointwise_montgomery_row_eager in a loop, and      *)
(* transforms the product back with mldsa44_polyveck_invntt_tomont as a tail *)
(* call. It is verified in the whole image (see libmldsa.ml) against         *)
(* mld_polyvec_matrix_pointwise_montgomery of                                *)
(* common/mldsa_native_polyvec.ml, using the theorems for the callees, and   *)
(* shown to be constant time and memory safe.                                *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvecl_ntt_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyvec_matrix_pointwise_montgomery_row_eager_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/polyveck_invntt_tomont_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyvec_matrix_pointwise_montgomery_yvec_eager:
       +0x0  push    r14
       +0x2  mov     r14, rdi
       +0x5  push    r13
       +0x7  mov     r13, rsi
       +0xa  mov     rsi, rdx
       +0xd  push    r12
       +0xf  mov     r12, rcx
      +0x12  mov     ecx, 0x200
      +0x17  push    rbp
      +0x18  mov     rdi, r12
      +0x1b  mov     rbp, r14
      +0x1e  push    rbx
      +0x1f  xor     ebx, ebx
      +0x21  rep movs QWORD PTR es:[rdi], QWORD PTR ds:[rsi]
      +0x24  mov     rdi, r12
      +0x27  call    mldsa44_polyvecl_ntt
     loop1: after_mldsa44_polyvecl_ntt:
      +0x2c  mov     ecx, ebx
      +0x2e  mov     rdi, rbp
      +0x31  mov     rdx, r12
      +0x34  mov     rsi, r13
      +0x37  call    mldsa44_polyvec_matrix_pointwise_montgomery_row_eager
     after_mldsa44_polyvec_matrix_pointwise_montgomery_row_eager:
      +0x3c  add     ebx, 0x1
      +0x3f  add     rbp, 0x400
     loop1_test:
      +0x46  cmp     ebx, 0x4
     loop1_back:
      +0x49  jne     loop1
     loop1_exit:
      +0x4b  pop     rbx
      +0x4c  mov     rdi, r14
      +0x4f  pop     rbp
      +0x50  pop     r12
      +0x52  pop     r13
      +0x54  pop     r14
      +0x56  jmp     mldsa44_polyveck_invntt_tomont
 ***)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_polyvec_matrix_pointwise_montgomery_yvec_eager"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The matrix A at mat, 4 rows of 4 polynomials of 256          *)
(* coefficients of 32 bits each, and the vector z at y, 4 polynomials (see   *)
(* common/mldsa_native_polyvec.ml): the vector at w becomes the inverse NTT  *)
(* of the product of A with the NTT of z, mld_polyvec_map                    *)
(* mld_poly_invntt_tomont (mld_polyvec_matrix_pointwise_montgomery 4 A       *)
(* (mld_polyvec_map mld_poly_ntt z)). The scratch vector at scratch is       *)
(* overwritten. The REP MOVSQ needs the direction flag clear, as the ABI     *)
(* guarantees. The stack is the 40 bytes where the function saves RBX, RBP   *)
(* and R12-R14 below the return address, the slot below them for the return  *)
(* address of a call, and the 72 bytes below that of mldsa44_polyvecl_ntt    *)
(* (120 bytes in all).                                                       *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!w mat y scratch A z pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(w,4096); (scratch,4096); (word_sub stackpointer (word 120),120)] /\
        ALLPAIRS nonoverlapping
         [(w,4096); (scratch,4096); (word_sub stackpointer (word 120),120)]
         [(word pc,libmldsa_size); (mat,16384); (y,4096)] /\
        ALL (nonoverlapping (stackpointer,8)) [(w,4096); (scratch,4096)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                  word(pc +
                   mldsa44_polyvec_matrix_pointwise_montgomery_yvec_eager) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [w; mat; y; scratch] s /\
                  (read DF s <=> false) /\
                  (!j. j < 4096
                       ==> read(memory :> bytes32(word_add mat (word(4 * j))))
                             s = A j) /\
                  (!j. j < 1024
                       ==> read(memory :> bytes32(word_add y (word(4 * j))))
                             s = z j))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add w (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_invntt_tomont
                              (mld_polyvec_matrix_pointwise_montgomery 4 A
                                (mld_polyvec_map mld_poly_ntt z)) i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(w,4096);
                memory :> bytes(scratch,4096);
                memory :> bytes(word_sub stackpointer (word 120),120)])`;;

let
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* arguments, the table of zetas in the image, the stack frame and the slot  *)
(* of the return address, and the writes within the outputs and the stack    *)
(* frame.                                                                    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e w mat y scratch A z pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(w,4096); (scratch,4096); (word_sub stackpointer (word 120),120)] /\
        ALLPAIRS nonoverlapping
         [(w,4096); (scratch,4096); (word_sub stackpointer (word 120),120)]
         [(word pc,libmldsa_size); (mat,16384); (y,4096)] /\
        ALL (nonoverlapping (stackpointer,8)) [(w,4096); (scratch,4096)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                  word(pc +
                   mldsa44_polyvec_matrix_pointwise_montgomery_yvec_eager) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [w; mat; y; scratch] s /\
                  (read DF s <=> false) /\
                  (!j. j < 4096
                       ==> read(memory :> bytes32(word_add mat (word(4 * j))))
                             s = A j) /\
                  (!j. j < 1024
                       ==> read(memory :> bytes32(word_add y (word(4 * j))))
                             s = z j) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add w (word(4 * i))))
                             s =
                           mld_polyvec_map mld_poly_invntt_tomont
                              (mld_polyvec_matrix_pointwise_montgomery 4 A
                                (mld_polyvec_map mld_poly_ntt z)) i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events w mat y scratch pc
                            (word_sub stackpointer (word 120)) returnaddress /\
                     memaccess_inbounds e2
                      [w,4096; mat,16384; y,4096; scratch,4096;
                       word(pc + rodata_mld_zetas),1024;
                       word_sub stackpointer (word 120),120; stackpointer,8]
                      [w,4096; scratch,4096;
                       word_sub stackpointer (word 120),120]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(w,4096);
                memory :> bytes(scratch,4096);
                memory :> bytes(word_sub stackpointer (word 120),120)])`;;

let
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e w mat y scratch pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        PAIRWISE nonoverlapping
         [(w,4096); (scratch,4096); (word_sub stackpointer (word 120),120)] /\
        ALLPAIRS nonoverlapping
         [(w,4096); (scratch,4096); (word_sub stackpointer (word 120),120)]
         [(word pc,libmldsa_size); (mat,16384); (y,4096)] /\
        ALL (nonoverlapping (stackpointer,8)) [(w,4096); (scratch,4096)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                  word(pc +
                   mldsa44_polyvec_matrix_pointwise_montgomery_yvec_eager) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [w; mat; y; scratch] s /\
                  (read DF s <=> false) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events w mat y scratch pc
                            (word_sub stackpointer (word 120)) returnaddress /\
                     memaccess_inbounds e2
                      [w,4096; mat,16384; y,4096; scratch,4096;
                       word(pc + rodata_mld_zetas),1024;
                       word_sub stackpointer (word 120),120; stackpointer,8]
                      [w,4096; scratch,4096;
                       word_sub stackpointer (word 120),120]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(w,4096);
                memory :> bytes(scratch,4096);
                memory :> bytes(word_sub stackpointer (word 120),120)])`;;

let
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
 MLDSA_NATIVE_POLYVEC_MATRIX_POINTWISE_MONTGOMERY_YVEC_EAGER_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
