(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition of q to the negative coefficients of a vector of 8 polynomials:  *)
(* the statement. This is the code for mldsa87_polyveck_caddq                *)
(* (mld_polyveck_caddq in polyvec.c) from mldsa-native's portable C          *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which calls mldsa_poly_caddq for each polynomial in a loop. It is         *)
(* verified in the whole image (see libmldsa.ml) against mld_polyvec_map     *)
(* mld_poly_caddq of common/mldsa_native_polyvec.ml, using the theorems for  *)
(* mldsa_poly_caddq, and shown to be constant time and memory safe.          *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_caddq_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa87_polyveck_caddq:
       +0x0  push    rbp
       +0x1  lea     rbp, [rdi+0x2000]
       +0x8  push    rbx
       +0x9  mov     rbx, rdi
       +0xc  sub     rsp, 0x8
     loop1:
      +0x10  mov     rdi, rbx
      +0x13  add     rbx, 0x400
      +0x1a  call    mldsa_poly_caddq
     loop1_test: after_mldsa_poly_caddq:
      +0x1f  cmp     rbx, rbp
     loop1_back:
      +0x22  jne     loop1
     loop1_exit:
      +0x24  add     rsp, 0x8
      +0x28  pop     rbx
      +0x29  pop     rbp
     ret:
      +0x2a  ret
 ***)

let MLDSA_NATIVE_POLYVECK_CADDQ_87_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_polyveck_caddq"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The vector x at v, 8 polynomials of 256 coefficients of 32   *)
(* bits each (see common/mldsa_native_polyvec.ml), becomes mld_polyvec_map   *)
(* mld_poly_caddq x. The function saves RBP and RBX below the return address *)
(* and keeps 8 more bytes there, and each call of mldsa_poly_caddq puts its  *)
(* return address below them (32 bytes in all).                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_CADDQ_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!v x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (v,8192))
            [(word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(v,8192); (word_sub stackpointer (word 32),32)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa87_polyveck_caddq) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [v] s /\
                  (!i. i < 2048
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 2048
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = mld_polyvec_map mld_poly_caddq x i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,8192);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYVECK_CADDQ_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYVECK_CADDQ_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* vector, the stack frame and the slot of the return address, and the       *)
(* writes within the vector and the stack frame.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_CADDQ_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e v x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (v,8192))
            [(word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(v,8192); (word_sub stackpointer (word 32),32)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa87_polyveck_caddq) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [v] s /\
                  (!i. i < 2048
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 2048
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = mld_polyvec_map mld_poly_caddq x i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events v pc (word_sub stackpointer (word 32))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [v,8192; word_sub stackpointer (word 32),32;
                       stackpointer,8]
                      [v,8192; word_sub stackpointer (word 32),32]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,8192);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYVECK_CADDQ_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVECK_CADDQ_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_CADDQ_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e v pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (v,8192))
            [(word_sub stackpointer (word 32),32); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(v,8192); (word_sub stackpointer (word 32),32)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa87_polyveck_caddq) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [v] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events v pc (word_sub stackpointer (word 32))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [v,8192; word_sub stackpointer (word 32),32;
                       stackpointer,8]
                      [v,8192; word_sub stackpointer (word 32),32]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,8192);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYVECK_CADDQ_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVECK_CADDQ_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
