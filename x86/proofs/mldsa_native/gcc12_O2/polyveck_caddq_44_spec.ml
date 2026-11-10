(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Addition of q to the negative coefficients of a vector of 4 polynomials:  *)
(* the statement. This is the code for mldsa44_polyveck_caddq                *)
(* (mld_polyveck_caddq in polyvec.c) from mldsa-native's portable C          *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which calls mldsa_poly_caddq for each polynomial, the last time as a tail *)
(* call. It is verified in the whole image (see libmldsa.ml) against         *)
(* mld_polyvec_map mld_poly_caddq of common/mldsa_native_polyvec.ml, using   *)
(* the theorems for mldsa_poly_caddq, and shown to be constant time and      *)
(* memory safe.                                                              *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_caddq_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyveck_caddq:
       +0x0  push    rbx
       +0x1  mov     rbx, rdi
       +0x4  call    mldsa_poly_caddq
     after_mldsa_poly_caddq_1:
       +0x9  lea     rdi, [rbx+0x400]
      +0x10  call    mldsa_poly_caddq
     after_mldsa_poly_caddq_2:
      +0x15  lea     rdi, [rbx+0x800]
      +0x1c  call    mldsa_poly_caddq
     after_mldsa_poly_caddq_3:
      +0x21  lea     rdi, [rbx+0xc00]
      +0x28  pop     rbx
      +0x29  jmp     mldsa_poly_caddq
 ***)

let MLDSA_NATIVE_POLYVECK_CADDQ_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_polyveck_caddq"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The vector x at v, 4 polynomials of 256 coefficients of 32   *)
(* bits each (see common/mldsa_native_polyvec.ml), becomes mld_polyvec_map   *)
(* mld_poly_caddq x. The function saves RBX below the return address, and    *)
(* each call of mldsa_poly_caddq but the last, which is a tail call, puts    *)
(* its return address below that.                                            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_CADDQ_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!v x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (v,4096))
            [(word_sub stackpointer (word 16),16); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(v,4096); (word_sub stackpointer (word 16),16)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyveck_caddq) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [v] s /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = x i))
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 1024
                      ==> read(memory :> bytes32(word_add v (word(4 * i))))
                            s = mld_polyvec_map mld_poly_caddq x i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,4096);
                memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_POLYVECK_CADDQ_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYVECK_CADDQ_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* vector, the stack frame and the slot of the return address, and the       *)
(* writes within the vector and the stack frame.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_CADDQ_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e v x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (v,4096))
            [(word_sub stackpointer (word 16),16); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(v,4096); (word_sub stackpointer (word 16),16)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyveck_caddq) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [v] s /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = mld_polyvec_map mld_poly_caddq x i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events v pc (word_sub stackpointer (word 16))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [v,4096; word_sub stackpointer (word 16),16;
                       stackpointer,8]
                      [v,4096; word_sub stackpointer (word 16),16]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,4096);
                memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_POLYVECK_CADDQ_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVECK_CADDQ_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_CADDQ_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e v pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (v,4096))
            [(word_sub stackpointer (word 16),16); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(v,4096); (word_sub stackpointer (word 16),16)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyveck_caddq) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [v] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events v pc (word_sub stackpointer (word 16))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [v,4096; word_sub stackpointer (word 16),16;
                       stackpointer,8]
                      [v,4096; word_sub stackpointer (word 16),16]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,4096);
                memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_POLYVECK_CADDQ_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVECK_CADDQ_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
