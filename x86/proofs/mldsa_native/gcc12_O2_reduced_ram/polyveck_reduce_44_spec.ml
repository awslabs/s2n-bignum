(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction of the coefficients of a vector of 4 polynomials: the           *)
(* statement. This is the code for mldsa44_polyveck_reduce                   *)
(* (mld_polyveck_reduce in polyvec.c) from mldsa-native's portable C         *)
(* implementation compiled by gcc 12 with -O2 and MLD_CONFIG_REDUCE_RAM (see *)
(* mldsa_native/README.md), which calls mldsa_poly_reduce for each           *)
(* polynomial, the last time as a tail call. It is verified in the whole     *)
(* image (see libmldsa.ml) against mld_polyvec_map mld_poly_reduce of        *)
(* common/mldsa_native_polyvec.ml, using the theorems for mldsa_poly_reduce, *)
(* and shown to be constant time and memory safe. Since mldsa_poly_reduce    *)
(* uses aligned SSE loads and stores, the vector must be aligned, as it is   *)
(* in mldsa-native.                                                          *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_reduce_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyveck_reduce:
       +0x0  push    rbx
       +0x1  mov     rbx, rdi
       +0x4  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_1:
       +0x9  lea     rdi, [rbx+0x400]
      +0x10  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_2:
      +0x15  lea     rdi, [rbx+0x800]
      +0x1c  call    mldsa_poly_reduce
     after_mldsa_poly_reduce_3:
      +0x21  lea     rdi, [rbx+0xc00]
      +0x28  pop     rbx
      +0x29  jmp     mldsa_poly_reduce
 ***)

let MLDSA_NATIVE_POLYVECK_REDUCE_44_GCC12_O2_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa44_polyveck_reduce"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The vector x at v, aligned to 16 bytes, 4 polynomials of 256 *)
(* coefficients of 32 bits each (see common/mldsa_native_polyvec.ml),        *)
(* becomes mld_polyvec_map mld_poly_reduce x. The function saves RBX below   *)
(* the return address, and each call of mldsa_poly_reduce but the last,      *)
(* which is a tail call, puts its return address below that.                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_REDUCE_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!v x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 v /\
        ALL (nonoverlapping (v,4096))
            [(word_sub stackpointer (word 16),16); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(v,4096); (word_sub stackpointer (word 16),16)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa44_polyveck_reduce) /\
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
                            s = mld_polyvec_map mld_poly_reduce x i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,4096);
                memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_POLYVECK_REDUCE_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYVECK_REDUCE_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* vector, the constants of mldsa_poly_reduce, the stack frame and the slot  *)
(* of the return address, and the writes within the vector and the stack    *)
(* frame.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_REDUCE_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e v x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 v /\
        ALL (nonoverlapping (v,4096))
            [(word_sub stackpointer (word 16),16); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(v,4096); (word_sub stackpointer (word 16),16)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa44_polyveck_reduce) /\
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
                             s = mld_polyvec_map mld_poly_reduce x i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events v pc (word_sub stackpointer (word 16))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [v,4096; word(pc + mldsa_poly_reduce_consts),16;
                       word_sub stackpointer (word 16),16; stackpointer,8]
                      [v,4096; word_sub stackpointer (word 16),16]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,4096);
                memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_POLYVECK_REDUCE_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVECK_REDUCE_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_REDUCE_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e v pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 v /\
        ALL (nonoverlapping (v,4096))
            [(word_sub stackpointer (word 16),16); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(v,4096); (word_sub stackpointer (word 16),16)]
         [(word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s = word (pc + mldsa44_polyveck_reduce) /\
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
                      [v,4096; word(pc + mldsa_poly_reduce_consts),16;
                       word_sub stackpointer (word 16),16; stackpointer,8]
                      [v,4096; word_sub stackpointer (word 16),16]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,4096);
                memory :> bytes(word_sub stackpointer (word 16),16)])`;;

let MLDSA_NATIVE_POLYVECK_REDUCE_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVECK_REDUCE_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
