(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Pointwise Montgomery multiplication of polynomials: the statement. This   *)
(* is the code for mldsa_poly_pointwise_montgomery                           *)
(* (mld_poly_pointwise_montgomery in poly.c, which calls the _c version)     *)
(* from mldsa-native's portable C implementation compiled by gcc 12 with -O2 *)
(* (see mldsa_native/README.md), which computes one coefficient at a time,   *)
(* with the multiplication by q done with shifts. It is verified in the      *)
(* whole image (see libmldsa.ml) against mld_poly_pointwise_montgomery of    *)
(* common/mldsa_native_poly.ml, and shown to be constant time and memory     *)
(* safe.                                                                     *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_poly.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_pointwise_montgomery:
       +0x0  mov     r8, rdi
       +0x3  xor     edx, edx
       +0x5  nop     DWORD PTR [rax]
     loop1:
       +0x8  movsxd  rax, DWORD PTR [rsi+rdx*1]
       +0xc  movsxd  rdi, DWORD PTR [r8+rdx*1]
      +0x10  imul    rdi, rax
      +0x14  imul    ecx, edi, 0x3802001
      +0x1a  movsxd  rcx, ecx
      +0x1d  mov     r9, rcx
      +0x20  mov     rax, rcx
      +0x23  shl     r9, 0xa
      +0x27  sub     rax, r9
      +0x2a  shl     rax, 0xd
      +0x2e  sub     rax, rcx
      +0x31  add     rax, rdi
      +0x34  sar     rax, 0x20
      +0x38  mov     DWORD PTR [r8+rdx*1], eax
      +0x3c  add     rdx, 0x4
     loop1_test:
      +0x40  cmp     rdx, 0x400
     loop1_back:
      +0x47  jne     loop1
     loop1_exit: ret:
      +0x49  ret
 ***)

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_poly_pointwise_montgomery"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomials x at r and y at b, 256 coefficients of 32    *)
(* bits each, may not overlap; r becomes                                     *)
(* mld_poly_pointwise_montgomery x y.                                        *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r b x y pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (b,1024); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_pointwise_montgomery) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; b] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i))))
                             s = x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add b (word(4 * i))))
                             s = y i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add r (word(4 * i))))
                            s = mld_poly_pointwise_montgomery x y i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
 MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the slot of the return address, and the writes     *)
(* within the outputs.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r b x y pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (b,1024); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_pointwise_montgomery) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; b] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i))))
                             s = x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add b (word(4 * i))))
                             s = y i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add r (word(4 * i))))
                             s = mld_poly_pointwise_montgomery x y i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r b pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [r,1024; b,1024; stackpointer,8] [r,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (b,1024); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_pointwise_montgomery) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [r; b] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r b pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [r,1024; b,1024; stackpointer,8] [r,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_POINTWISE_MONTGOMERY_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
