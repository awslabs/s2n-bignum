(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The lazy expansion of the matrix: the statement. This is the code for     *)
(* mldsa44_polyvec_matrix_expand_lazy (mld_polyvec_matrix_expand_lazy in     *)
(* polyvec_lazy.c) from mldsa-native's portable C implementation compiled by *)
(* gcc 12 with -O2 and MLD_CONFIG_REDUCE_RAM (see mldsa_native/README.md),   *)
(* which does not expand the matrix: it only copies the 32 bytes of the seed *)
(* rho into the structure mld_polymat_lazy at mat, after the polynomial      *)
(* (1024 bytes) that the lazy products use for the entries that they sample, *)
(* with two 128-bit loads and stores. It is verified in the whole image (see *)
(* libmldsa.ml) and shown to be constant time and memory safe.               *)
(* ========================================================================= *)

needs "x86/proofs/mlkem_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2_reduced_ram/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyvec_matrix_expand_lazy:
       +0x0  movdqu  xmm0, XMMWORD PTR [rsi]
       +0x4  movups  XMMWORD PTR [rdi+0x400], xmm0
       +0xb  movdqu  xmm1, XMMWORD PTR [rsi+0x10]
      +0x10  movups  XMMWORD PTR [rdi+0x410], xmm1
     ret:
      +0x17  ret
 ***)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc
   [layout_range "mldsa44_polyvec_matrix_expand_lazy"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The 32 bytes r at rho are copied to mat + 1024, the seed of  *)
(* the structure; the function is a leaf and uses no stack.                  *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!mat rho r pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (word_add mat (word 1024),32))
            [(word pc,libmldsa_size); (rho,32); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s =
                  word (pc + mldsa44_polyvec_matrix_expand_lazy) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [mat; rho] s /\
                  read (memory :> bytes(rho,32)) s = r)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(word_add mat (word 1024),32)) s = r)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_add mat (word 1024),32)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses only, with all accesses within the *)
(* seed, the slot of the return address and the seed of the structure, and   *)
(* the writes within the seed of the structure.                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e mat rho r pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (word_add mat (word 1024),32))
            [(word pc,libmldsa_size); (rho,32); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s =
                  word (pc + mldsa44_polyvec_matrix_expand_lazy) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [mat; rho] s /\
                  read (memory :> bytes(rho,32)) s = r /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  read (memory :> bytes(word_add mat (word 1024),32)) s = r /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events mat rho pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                      [rho,32; stackpointer,8; word_add mat (word 1024),32]
                      [word_add mat (word 1024),32]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_add mat (word 1024),32)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e mat rho pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (word_add mat (word 1024),32))
            [(word pc,libmldsa_size); (rho,32); (stackpointer,8)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_reduced_ram_mc /\
                  read RIP s =
                  word (pc + mldsa44_polyvec_matrix_expand_lazy) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [mat; rho] s /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events mat rho pc stackpointer returnaddress /\
                     memaccess_inbounds e2
                      [rho,32; stackpointer,8; word_add mat (word 1024),32]
                      [word_add mat (word 1024),32]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(word_add mat (word 1024),32)])`;;

let MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVEC_MATRIX_EXPAND_LAZY_44_GCC12_O2_REDUCED_RAM_IMAGE_SUBROUTINE_SAFE_STMT;;
