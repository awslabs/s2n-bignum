(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise products of two vectors of 7 polynomials, accumulated and       *)
(* reduced: the statement. This is the code for                              *)
(* mldsa87_polyvecl_pointwise_acc_montgomery                                 *)
(* (mld_polyvecl_pointwise_acc_montgomery in polyvec.c, which calls the _c   *)
(* version) from mldsa-native's portable C implementation compiled by gcc 12 *)
(* with -O2 (see mldsa_native/README.md), which computes one coefficient at  *)
(* a time: for each coefficient, a loop over the 7 polynomials accumulates   *)
(* the 64-bit products, whose sum is then reduced, with the multiplication   *)
(* by q done with shifts. It is verified in the whole image (see             *)
(* libmldsa.ml) against                                                      *)
(* mld_polyvec_pointwise_acc_montgomery 7 of common/mldsa_native_polyvec.ml, *)
(* and shown to be constant time and memory safe.                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa87_polyvecl_pointwise_acc_montgomery:
       +0x0  push    rbx
       +0x1  mov     r9, rdx
       +0x4  mov     r8, rsi
       +0x7  xor     edx, edx
       +0x9  nop     DWORD PTR [rax+0x0]
     loop1:
      +0x10  xor     eax, eax
      +0x12  lea     r11, [r8+rdx*1]
      +0x16  lea     r10, [r9+rdx*1]
      +0x1a  xor     esi, esi
      +0x1c  nop     DWORD PTR [rax+0x0]
     loop2:
      +0x20  movsxd  rcx, DWORD PTR [r11+rax*1]
      +0x24  movsxd  rbx, DWORD PTR [r10+rax*1]
      +0x28  add     rax, 0x400
      +0x2e  imul    rcx, rbx
      +0x32  add     rsi, rcx
     loop2_test:
      +0x35  cmp     rax, 0x1c00
     loop2_back:
      +0x3b  jne     loop2
     loop2_exit:
      +0x3d  imul    ecx, esi, 0x3802001
      +0x43  movsxd  rcx, ecx
      +0x46  mov     r10, rcx
      +0x49  mov     rax, rcx
      +0x4c  shl     r10, 0xa
      +0x50  sub     rax, r10
      +0x53  shl     rax, 0xd
      +0x57  sub     rax, rcx
      +0x5a  add     rax, rsi
      +0x5d  sar     rax, 0x20
      +0x61  mov     DWORD PTR [rdi+rdx*1], eax
      +0x64  add     rdx, 0x4
     loop1_test:
      +0x68  cmp     rdx, 0x400
     loop1_back:
      +0x6f  jne     loop1
     loop1_exit:
      +0x71  pop     rbx
     ret:
      +0x72  ret
 ***)

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_polyvecl_pointwise_acc_montgomery"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The vectors x at u and y at v, 7 polynomials of 256          *)
(* coefficients of 32 bits each (see common/mldsa_native_polyvec.ml), may    *)
(* overlap each other but not the polynomial at w, which becomes             *)
(* mld_polyvec_pointwise_acc_montgomery 7 x y. The function saves RBX below  *)
(* the return address.                                                       *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!w u v x y pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (w,1024))
            [(word pc,libmldsa_size); (u,7168); (v,7168);
             (word_sub stackpointer (word 8),8); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 8),8))
            [(word pc,libmldsa_size); (u,7168); (v,7168)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                    word (pc + mldsa87_polyvecl_pointwise_acc_montgomery) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [w; u; v] s /\
                  (!i. i < 1792
                       ==> read(memory :> bytes32(word_add u (word(4 * i))))
                             s = x i) /\
                  (!i. i < 1792
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = y i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add w (word(4 * i))))
                            s = mld_polyvec_pointwise_acc_montgomery 7 x y i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(w,1024);
                         memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with the reads within the    *)
(* two vectors, the stack frame and the slot of the return address, and the  *)
(* writes within the polynomial at w and the stack frame.                    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e w u v x y pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (w,1024))
            [(word pc,libmldsa_size); (u,7168); (v,7168);
             (word_sub stackpointer (word 8),8); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 8),8))
            [(word pc,libmldsa_size); (u,7168); (v,7168)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                    word (pc + mldsa87_polyvecl_pointwise_acc_montgomery) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [w; u; v] s /\
                  (!i. i < 1792
                       ==> read(memory :> bytes32(word_add u (word(4 * i))))
                             s = x i) /\
                  (!i. i < 1792
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = y i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add w (word(4 * i))))
                             s =
                           mld_polyvec_pointwise_acc_montgomery 7 x y i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events w u v pc (word_sub stackpointer (word 8))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [u,7168; v,7168; word_sub stackpointer (word 8),8;
                       stackpointer,8]
                      [w,1024; word_sub stackpointer (word 8),8]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(w,1024);
                         memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e w u v pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (w,1024))
            [(word pc,libmldsa_size); (u,7168); (v,7168);
             (word_sub stackpointer (word 8),8); (stackpointer,8)] /\
        ALL (nonoverlapping (word_sub stackpointer (word 8),8))
            [(word pc,libmldsa_size); (u,7168); (v,7168)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                    word (pc + mldsa87_polyvecl_pointwise_acc_montgomery) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [w; u; v] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events w u v pc (word_sub stackpointer (word 8))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [u,7168; v,7168; word_sub stackpointer (word 8),8;
                       stackpointer,8]
                      [w,1024; word_sub stackpointer (word 8),8]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(w,1024);
                         memory :> bytes(word_sub stackpointer (word 8),8)])`;;

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
