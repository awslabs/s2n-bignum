(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Check of the norm of a polynomial against a bound B: the statement. This  *)
(* is the code for mldsa_poly_chknorm (mld_poly_chknorm in poly.c, which     *)
(* calls mld_poly_chknorm_c) from mldsa-native's portable C implementation   *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md). It is verified  *)
(* in the whole image (see libmldsa.ml) against mld_poly_chknorm of          *)
(* common/mldsa_native_poly.ml: the result is all ones if some coefficient a *)
(* has B - 1 - |a| < 0, and zero otherwise. It is also shown to be constant  *)
(* time and memory safe.                                                     *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_poly.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_chknorm:
       +0x0  mov     rcx, rdi
       +0x3  lea     edi, [rsi-0x1]
       +0x6  xor     esi, esi
       +0x8  lea     r8, [rcx+0x400]
       +0xf  nop
     loop1:
      +0x10  movsxd  rax, DWORD PTR [rcx]
      +0x13  mov     r9, rax
      +0x16  sar     rax, 0x1f
      +0x1a  mov     edx, r9d
      +0x1d  neg     edx
      +0x1f  xor     edx, r9d
      +0x22  and     edx, eax
      +0x24  mov     eax, edi
      +0x26  xor     edx, r9d
      +0x29  sub     eax, edx
      +0x2b  cdqe
      +0x2d  sar     rax, 0x1f
      +0x31  add     rcx, 0x4
      +0x35  or      esi, eax
     loop1_test:
      +0x37  cmp     rcx, r8
     loop1_back:
      +0x3a  jne     loop1
     loop1_exit:
      +0x3c  mov     eax, esi
     ret:
      +0x3e  ret
 ***)

let MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_poly_chknorm"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomial x is at a and the bound B is the low 32 bits  *)
(* of the second argument; the result is a 32-bit value, zero-extended.      *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a x bnd pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_chknorm) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; bnd] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = word_zx(mld_poly_chknorm x (word_zx bnd)))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`;;

let MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs and the slot of the return address, and the writes     *)
(* within the outputs.                                                       *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a x bnd pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_chknorm) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; bnd] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  C_RETURN s = word_zx(mld_poly_chknorm x (word_zx bnd)) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a bnd pc stackpointer returnaddress /\
                     memaccess_inbounds e2 [a,1024; stackpointer,8] []))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`;;

let MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a bnd pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_chknorm) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; bnd] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a bnd pc stackpointer returnaddress /\
                     memaccess_inbounds e2 [a,1024; stackpointer,8] []))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`;;

let MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_CHKNORM_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
