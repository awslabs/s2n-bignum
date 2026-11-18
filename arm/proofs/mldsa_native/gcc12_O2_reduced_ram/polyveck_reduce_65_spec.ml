(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Reduction of the coefficients of a vector of 6 polynomials to small       *)
(* representatives: the statement. This is the code for                      *)
(* mldsa65_polyveck_reduce (mld_polyveck_reduce in polyvec.c) from           *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -O2 and  *)
(* MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md), which calls           *)
(* mldsa_poly_reduce for each polynomial, the last time as a tail call. The  *)
(* code is that of mldsa65_polyveck_invntt_tomont with mldsa_poly_reduce in  *)
(* place of mldsa_poly_invntt_tomont. It is verified in the whole image (see *)
(* libmldsa.ml) against mld_polyvec_map mld_poly_reduce of                   *)
(* common/mldsa_native_polyvec.ml, using the theorems for mldsa_poly_reduce, *)
(* and shown to be constant time and memory safe.                            *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/poly_reduce_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa65_polyveck_reduce:
       +0x0: stp     x19, x20, [sp, #-32]!
       +0x4: mov     x19, x0
       +0x8: mov     x0, #0x1800
       +0xc: add     x20, x19, x0
      +0x10: str     x30, [sp, #16]
      +0x14: nop
      +0x18: mov     x0, x19
      +0x1c: add     x19, x19, #0x400
      +0x20: bl      <mldsa_poly_reduce>
      +0x24: cmp     x19, x20
      +0x28: b.ne    <mldsa65_polyveck_reduce+0x18>
      +0x2c: ldr     x30, [sp, #16]
      +0x30: ldp     x19, x20, [sp], #32
      +0x34: ret
 ***)

let MLDSA_NATIVE_POLYVECK_REDUCE_65_GCC12_O2_REDUCED_RAM_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa65_polyveck_reduce"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The vector x at v, 6 polynomials of 256 coefficients of 32   *)
(* bits each (see common/mldsa_native_polyvec.ml), becomes mld_polyvec_map   *)
(* mld_poly_reduce x.                                                 *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_REDUCE_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!v x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (v,6144) (word_sub stackpointer (word 32),32) /\
        ALLPAIRS nonoverlapping
         [(v,6144); (word_sub stackpointer (word 32),32)]
         [(word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read PC s = word (pc + mldsa65_polyveck_reduce) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [v] s /\
                  (!i. i < 1536
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = x i))
             (\s. read PC s = returnaddress /\
                  !i. i < 1536
                      ==> read(memory :> bytes32(word_add v (word(4 * i))))
                            s = mld_polyvec_map mld_poly_reduce x i)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,6144);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYVECK_REDUCE_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLYVECK_REDUCE_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* vector, the constants of mldsa_poly_reduce and the stack frame, and the   *)
(* writes within the vector and the stack frame.                             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_REDUCE_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e v x pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (v,6144) (word_sub stackpointer (word 32),32) /\
        ALLPAIRS nonoverlapping
         [(v,6144); (word_sub stackpointer (word 32),32)]
         [(word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read PC s = word (pc + mldsa65_polyveck_reduce) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [v] s /\
                  (!i. i < 1536
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = x i) /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (!i. i < 1536
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s = mld_polyvec_map mld_poly_reduce x i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events v pc (word_sub stackpointer (word 32))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [v,6144; word_sub stackpointer (word 32),32;
                       word(pc + mldsa_poly_reduce_consts),16]
                      [v,6144; word_sub stackpointer (word 32),32]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,6144);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYVECK_REDUCE_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYVECK_REDUCE_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECK_REDUCE_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e v pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (v,6144) (word_sub stackpointer (word 32),32) /\
        ALLPAIRS nonoverlapping
         [(v,6144); (word_sub stackpointer (word 32),32)]
         [(word pc,libmldsa_size)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read PC s = word (pc + mldsa65_polyveck_reduce) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [v] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events v pc (word_sub stackpointer (word 32))
                                   returnaddress /\
                     memaccess_inbounds e2
                      [v,6144; word_sub stackpointer (word 32),32;
                       word(pc + mldsa_poly_reduce_consts),16]
                      [v,6144; word_sub stackpointer (word 32),32]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,6144);
                memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_POLYVECK_REDUCE_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYVECK_REDUCE_65_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
