(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise products of two vectors of 4 polynomials, accumulated and       *)
(* reduced: the statement. This is the code for                              *)
(* mldsa44_polyvecl_pointwise_acc_montgomery                                 *)
(* (mld_polyvecl_pointwise_acc_montgomery in polyvec.c, which calls the _c   *)
(* version) from mldsa-native's portable C implementation compiled by gcc 12 *)
(* with -O2 (see mldsa_native/README.md), which computes one coefficient at  *)
(* a time: for each coefficient, a loop over the 4 polynomials accumulates   *)
(* the 64-bit products, whose sum is then reduced, with the multiplication   *)
(* by q done with shifts. It is verified in the whole image (see             *)
(* libmldsa.ml) against                                                      *)
(* mld_polyvec_pointwise_acc_montgomery 4 of common/mldsa_native_polyvec.ml, *)
(* and shown to be constant time and memory safe.                            *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyvecl_pointwise_acc_montgomery:
       +0x0  mov     r10, rdx
       +0x3  mov     r8, rdi
       +0x6  mov     r9, rsi
       +0x9  xor     edx, edx
       +0xb  nop     DWORD PTR [rax+rax*1+0x0]
     loop1:
      +0x10  mov     rax, rdx
      +0x13  xor     esi, esi
      +0x15  lea     rcx, [rdx+0x1000]
     loop2:
      +0x1c  movsxd  rdi, DWORD PTR [r9+rax*1]
      +0x20  movsxd  r11, DWORD PTR [r10+rax*1]
      +0x24  add     rax, 0x400
      +0x2a  imul    rdi, r11
      +0x2e  add     rsi, rdi
     loop2_test:
      +0x31  cmp     rcx, rax
     loop2_back:
      +0x34  jne     loop2
     loop2_exit:
      +0x36  imul    ecx, esi, 0x3802001
      +0x3c  movsxd  rcx, ecx
      +0x3f  mov     rdi, rcx
      +0x42  mov     rax, rcx
      +0x45  shl     rdi, 0xa
      +0x49  sub     rax, rdi
      +0x4c  shl     rax, 0xd
      +0x50  sub     rax, rcx
      +0x53  add     rax, rsi
      +0x56  sar     rax, 0x20
      +0x5a  mov     DWORD PTR [r8+rdx*1], eax
      +0x5e  add     rdx, 0x4
     loop1_test:
      +0x62  cmp     rdx, 0x400
     loop1_back:
      +0x69  jne     loop1
     loop1_exit: ret:
      +0x6b  ret
 ***)

let MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_polyvecl_pointwise_acc_montgomery"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The vectors x at u and y at v, 4 polynomials of 256          *)
(* coefficients of 32 bits each (see common/mldsa_native_polyvec.ml), may    *)
(* overlap each other but not the polynomial at w, which becomes             *)
(* mld_polyvec_pointwise_acc_montgomery 4 x y.                               *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!w u v x y pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (w,1024))
            [(word pc,libmldsa_size); (u,4096); (v,4096); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                    word (pc + mldsa44_polyvecl_pointwise_acc_montgomery) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [w; u; v] s /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add u (word(4 * i))))
                             s = x i) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = y i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add w (word(4 * i))))
                            s = mld_polyvec_pointwise_acc_montgomery 4 x y i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(w,1024)])`;;

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with the reads within the    *)
(* two vectors and the slot of the return address, and the writes within the *)
(* polynomial at w.                                                          *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e w u v x y pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (w,1024))
            [(word pc,libmldsa_size); (u,4096); (v,4096); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                    word (pc + mldsa44_polyvecl_pointwise_acc_montgomery) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [w; u; v] s /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add u (word(4 * i))))
                             s = x i) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = y i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add w (word(4 * i))))
                             s =
                           mld_polyvec_pointwise_acc_montgomery 4 x y i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events w u v pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                      [u,4096; v,4096; stackpointer,8] [w,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(w,1024)])`;;

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e w u v pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (w,1024))
            [(word pc,libmldsa_size); (u,4096); (v,4096); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s =
                    word (pc + mldsa44_polyvecl_pointwise_acc_montgomery) /\
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
                      [u,4096; v,4096; stackpointer,8] [w,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(w,1024)])`;;

let
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
 MLDSA_NATIVE_POLYVECL_POINTWISE_ACC_MONTGOMERY_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
