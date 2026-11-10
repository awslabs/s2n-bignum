(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction of the coefficients of a polynomial with mld_reduce32: the      *)
(* statement. This is the code for mldsa_poly_reduce (mld_poly_reduce in     *)
(* poly.c) from mldsa-native's portable C implementation compiled by gcc 12  *)
(* with -O2 (see mldsa_native/README.md), which the compiler has vectorized, *)
(* with a vector of 2^22 from the read-only data and the multiplication by q *)
(* done with shifts. It is verified in the whole image (see libmldsa.ml)     *)
(* against mld_poly_reduce of common/mldsa_native_poly.ml, and shown to be   *)
(* constant time and memory safe. Since the code uses aligned SSE loads and  *)
(* stores, the polynomial must be aligned, as it is in mldsa-native.         *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_poly.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_reduce:
       +0x0  movdqa  xmm2, XMMWORD PTR [rip+0x9e08]
                     // mldsa_poly_reduce_consts
       +0x8  lea     rax, [rdi+0x400]
       +0xf  nop
     loop1:
      +0x10  movdqa  xmm1, XMMWORD PTR [rdi]
      +0x14  add     rdi, 0x10
      +0x18  paddd   xmm1, xmm2
      +0x1c  psrad   xmm1, 0x17
      +0x21  movdqa  xmm0, xmm1
      +0x25  pslld   xmm0, 0xa
      +0x2a  psubd   xmm0, xmm1
      +0x2e  pslld   xmm0, 0xd
      +0x33  paddd   xmm0, xmm1
      +0x37  movdqa  xmm1, XMMWORD PTR [rdi-0x10]
      +0x3c  psubd   xmm1, xmm0
      +0x40  movaps  XMMWORD PTR [rdi-0x10], xmm1
     loop1_test:
      +0x44  cmp     rax, rdi
     loop1_back:
      +0x47  jne     loop1
     loop1_exit: ret:
      +0x49  ret
 ***)

let MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_poly_reduce"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The polynomial x at a, 256 coefficients of 32 bits each,     *)
(* becomes mld_poly_reduce x.                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 a /\
        ALL (nonoverlapping (a,1024))
            [(word pc,libmldsa_size); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_reduce) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i))))
                            s = mld_poly_reduce x i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`;;

let MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* inputs and outputs, the vector of constants and the slot of the return    *)
(* address, and the writes within the outputs.                               *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 a /\
        ALL (nonoverlapping (a,1024))
            [(word pc,libmldsa_size); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_reduce) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = mld_poly_reduce x i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; word(pc + mldsa_poly_reduce_consts),16;
                       stackpointer,8]
                      [a,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`;;

let MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 a /\
        ALL (nonoverlapping (a,1024))
            [(word pc,libmldsa_size); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_reduce) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                      [a,1024; word(pc + mldsa_poly_reduce_consts),16;
                       stackpointer,8]
                      [a,1024]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(a,1024)])`;;

let MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_REDUCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
