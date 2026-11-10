(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Splitting of the coefficients of a polynomial at 2^13: the statement.     *)
(* This is the code for mldsa_poly_power2round (mld_poly_power2round in      *)
(* poly.c, with mld_power2round of rounding.h) from mldsa-native's portable  *)
(* C implementation compiled by gcc 12 with -O2 (see                         *)
(* mldsa_native/README.md), which the compiler has vectorized, with two      *)
(* vectors of constants from the read-only data. It is verified in the whole *)
(* image (see libmldsa.ml) against mld_poly_power2round_hi and               *)
(* mld_poly_power2round_lo of common/mldsa_native_poly.ml, and shown to be   *)
(* constant time and memory safe. Since the code uses aligned SSE loads and  *)
(* stores, the polynomials must be aligned, as they are in mldsa-native.     *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_poly.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_power2round:
       +0x0  movdqa  xmm4, XMMWORD PTR [rip+0x9a48]
                     // mldsa_poly_power2round_const1
       +0x8  movdqa  xmm3, XMMWORD PTR [rip+0x9a50]
                     // mldsa_poly_power2round_const2
      +0x10  xor     eax, eax
      +0x12  nop     WORD PTR [rax+rax*1+0x0]
     loop1:
      +0x18  movdqa  xmm0, XMMWORD PTR [rdx+rax*1]
      +0x1d  movdqa  xmm1, xmm0
      +0x21  paddd   xmm1, xmm4
      +0x25  movdqa  xmm2, xmm1
      +0x29  pand    xmm1, xmm3
      +0x2d  psrad   xmm2, 0xd
      +0x32  psubd   xmm0, xmm1
      +0x36  movaps  XMMWORD PTR [rdi+rax*1], xmm2
      +0x3a  movaps  XMMWORD PTR [rsi+rax*1], xmm0
      +0x3e  add     rax, 0x10
     loop1_test:
      +0x42  cmp     rax, 0x400
     loop1_back:
      +0x48  jne     loop1
     loop1_exit: ret:
      +0x4a  ret
 ***)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_poly_power2round"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. For the polynomial x at a, the high parts are written to a1  *)
(* and the low parts to a0, three regions of 1024 bytes that may not         *)
(* overlap, and the outputs may not overlap the slot of the return address.  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a1 a0 a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 a1 /\ aligned 16 a0 /\ aligned 16 a /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (a,1024); (word pc,libmldsa_size)] /\
        ALL (nonoverlapping (stackpointer,8)) [(a1,1024); (a0,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_power2round) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a1; a0; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a1 (word(4 * i))))
                             s = mld_poly_power2round_hi x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a0 (word(4 * i))))
                             s = mld_poly_power2round_lo x i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a1,1024); memory :> bytes(a0,1024)])`;;

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs, the vectors of constants and the slot of the return   *)
(* address, and the writes within the outputs.                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a1 a0 a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 a1 /\ aligned 16 a0 /\ aligned 16 a /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (a,1024); (word pc,libmldsa_size)] /\
        ALL (nonoverlapping (stackpointer,8)) [(a1,1024); (a0,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_power2round) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a1; a0; a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a1 (word(4 * i))))
                             s = mld_poly_power2round_hi x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a0 (word(4 * i))))
                             s = mld_poly_power2round_lo x i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a1 a0 a pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; word(pc + mldsa_poly_power2round_consts),32;
                       stackpointer,8]
                      [a1,1024; a0,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a1,1024); memory :> bytes(a0,1024)])`;;

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a1 a0 a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 a1 /\ aligned 16 a0 /\ aligned 16 a /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (a,1024); (word pc,libmldsa_size)] /\
        ALL (nonoverlapping (stackpointer,8)) [(a1,1024); (a0,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_power2round) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a1; a0; a] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a1 a0 a pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; word(pc + mldsa_poly_power2round_consts),32;
                       stackpointer,8]
                      [a1,1024; a0,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a1,1024); memory :> bytes(a0,1024)])`;;

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* The same in place, with the low part written over the input (a0 = a), as  *)
(* mld_compute_pack_t0_t1 calls it: each iteration loads its four input      *)
(* coefficients before it stores the results.                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_FULL_INPLACE_STMT =
 `exists f_events.
     forall e a1 a0 x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 a1 /\ aligned 16 a0 /\
        PAIRWISE nonoverlapping
         [(a1,1024); (a0,1024); (word pc,libmldsa_size)] /\
        ALL (nonoverlapping (stackpointer,8)) [(a1,1024); (a0,1024)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_power2round) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a1; a0; a0] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a0 (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a1 (word(4 * i))))
                             s = mld_poly_power2round_hi x i) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a0 (word(4 * i))))
                             s = mld_poly_power2round_lo x i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a1 a0 pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                      [a0,1024; word(pc + mldsa_poly_power2round_consts),32;
                       stackpointer,8]
                      [a1,1024; a0,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a1,1024); memory :> bytes(a0,1024)])`;;

let MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_FULL_INPLACE =
  assume_spec
   MLDSA_NATIVE_POLY_POWER2ROUND_GCC12_O2_IMAGE_SUBROUTINE_FULL_INPLACE_STMT;;
