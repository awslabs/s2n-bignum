(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise products of two vectors of 5 polynomials, accumulated and       *)
(* reduced: the statement. This is the code for                              *)
(* mldsa65_polyvecl_pointwise_acc_montgomery                                 *)
(* (mld_polyvecl_pointwise_acc_montgomery in polyvec.c, which calls the _c   *)
(* version) from mldsa-native's portable C implementation compiled by gcc 12 *)
(* with -O2 (see mldsa_native/README.md), which computes one coefficient at  *)
(* a time: for each coefficient, a loop over the 5 polynomials accumulates   *)
(* the 64-bit products, whose sum is then reduced, with the multiplication   *)
(* by q done with shifts. It is verified in the whole image (see             *)
(* libmldsa.ml) against                                                      *)
(* mld_polyvec_pointwise_acc_montgomery 5 of common/mldsa_native_polyvec.ml, *)
(* and shown to be constant time and memory safe.                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_polyvecl_pointwise_acc_montgomery:
       +0x0  mov     r9, rdx
       +0x3  mov     r8, rsi
       +0x6  xor     edx, edx
       +0x8  nop     DWORD PTR [rax+rax*1+0x0]
     loop1:
      +0x10  mov     rax, rdx
      +0x13  xor     esi, esi
      +0x15  lea     r11, [rdx+0x1400]
      +0x1c  nop     DWORD PTR [rax+0x0]
     loop2:
      +0x20  movsxd  rcx, DWORD PTR [r8+rax*1]
      +0x24  movsxd  r10, DWORD PTR [r9+rax*1]
      +0x28  add     rax, 0x400
      +0x2e  imul    rcx, r10
      +0x32  add     rsi, rcx
     loop2_test:
      +0x35  cmp     r11, rax
     loop2_back:
      +0x38  jne     loop2
     loop2_exit:
      +0x3a  imul    ecx, esi, 0x3802001
      +0x40  movsxd  rcx, ecx
      +0x43  mov     r10, rcx
      +0x46  mov     rax, rcx
      +0x49  shl     r10, 0xa
      +0x4d  sub     rax, r10
      +0x50  shl     rax, 0xd
      +0x54  sub     rax, rcx
      +0x57  add     rax, rsi
      +0x5a  sar     rax, 0x20
      +0x5e  mov     DWORD PTR [rdi+rdx*1], eax
      +0x61  add     rdx, 0x4
     loop1_test:
      +0x65  cmp     rdx, 0x400
     loop1_back:
      +0x6c  jne     loop1
     loop1_exit: ret:
      +0x6e  ret
 ***)

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_polyvecl_pointwise_acc_montgomery"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The vectors x at u and y at v, 5 polynomials of 256          *)
(* coefficients of 32 bits each (see common/mldsa_native_polyvec.ml), may    *)
(* overlap each other but not the polynomial at w, which becomes             *)
(* mld_polyvec_pointwise_acc_montgomery 5 x y.                               *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!w u v x y pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (w,1024))
            [(word pc,libmldsa_size); (u,5120); (v,5120); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                    word (pc + mldsa65_polyvecl_pointwise_acc_montgomery) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [w; u; v] s /\
                  (!i. i < 1280
                       ==> read(memory :> bytes32(word_add u (word(4 * i))))
                             s = x i) /\
                  (!i. i < 1280
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = y i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add w (word(4 * i))))
                            s = mld_polyvec_pointwise_acc_montgomery 5 x y i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(w,1024)])`;;

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with the reads within the    *)
(* two vectors and the slot of the return address, and the writes within the *)
(* polynomial at w.                                                          *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e w u v x y pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (w,1024))
            [(word pc,libmldsa_size); (u,5120); (v,5120); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                    word (pc + mldsa65_polyvecl_pointwise_acc_montgomery) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [w; u; v] s /\
                  (!i. i < 1280
                       ==> read(memory :> bytes32(word_add u (word(4 * i))))
                             s = x i) /\
                  (!i. i < 1280
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = y i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add w (word(4 * i))))
                             s =
                           mld_polyvec_pointwise_acc_montgomery 5 x y i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events w u v pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                      [u,5120; v,5120; stackpointer,8] [w,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(w,1024)])`;;

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e w u v pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (w,1024))
            [(word pc,libmldsa_size); (u,5120); (v,5120); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                    word (pc + mldsa65_polyvecl_pointwise_acc_montgomery) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [w; u; v] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events w u v pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                      [u,5120; v,5120; stackpointer,8] [w,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(w,1024)])`;;

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
