(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition of polynomials, coefficientwise with wraparound: the statement.  *)
(* This is the code for mldsa_poly_add (mld_poly_add in poly.c) from         *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2      *)
(* (see mldsa_native/README.md), which the compiler has vectorized. It is    *)
(* verified in the whole image (see libmldsa.ml) against mld_poly_add of     *)
(* common/mldsa_native_poly.ml, and shown to be constant time and memory     *)
(* safe. Since the code uses aligned SSE loads and stores, the polynomials   *)
(* must be aligned, as they are in mldsa-native.                             *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_poly.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_add:
       +0x0  xor     eax, eax
       +0x2  nop     WORD PTR [rax+rax*1+0x0]
     loop1:
       +0x8  movdqa  xmm0, XMMWORD PTR [rdi+rax*1]
       +0xd  paddd   xmm0, XMMWORD PTR [rsi+rax*1]
      +0x12  movaps  XMMWORD PTR [rdi+rax*1], xmm0
      +0x16  add     rax, 0x10
     loop1_test:
      +0x1a  cmp     rax, 0x400
     loop1_back:
      +0x20  jne     loop1
     loop1_exit: ret:
      +0x22  ret
 ***)

let MLDSA_NATIVE_POLY_ADD_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_poly_add"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomials x at r and y at b, 256 coefficients of 32    *)
(* bits each, may not overlap; r becomes mld_poly_add x y.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!r b x y pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 r /\ aligned 16 b /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (b,1024); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_add) /\
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
                            s = mld_poly_add x y i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* two polynomials and the slot of the return address, and the writes within *)
(* r.                                                                        *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e r b x y pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 r /\ aligned 16 b /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (b,1024); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_add) /\
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
                             s = mld_poly_add x y i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events r b pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                       [r,1024; b,1024; stackpointer,8] [r,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(r,1024)])`;;

let MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e r b pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 r /\ aligned 16 b /\
        ALL (nonoverlapping (r,1024))
            [(word pc,libmldsa_size); (b,1024); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_add) /\
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

let MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_ADD_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
