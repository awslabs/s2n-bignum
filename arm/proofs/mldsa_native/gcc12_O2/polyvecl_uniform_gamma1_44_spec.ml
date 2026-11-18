(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of the vector y of signing: the statement. This is the code for  *)
(* mldsa44_polyvecl_uniform_gamma1 (mld_polyvecl_uniform_gamma1 in           *)
(* polyvec.c) from mldsa-native's portable C implementation compiled by gcc  *)
(* 12 with -O2 (see mldsa_native/README.md), which samples its four          *)
(* polynomials with one call of mldsa44_poly_uniform_gamma1_4x, with the     *)
(* nonces kappa to kappa + 3 (all modulo 2^16, kappa being the low 16 bits   *)
(* of the third argument). It is verified in the whole image (see            *)
(* libmldsa.ml) against mld_poly_uniform_gamma1_17 of                        *)
(* common/mldsa_native_sampling.ml, using the theorems for the callees and   *)
(* the contract memset_full_contract of utils/mlkem_native_libc_full.ml for  *)
(* memset, and shown to be constant time and memory safe, with the events    *)
(* depending only on the addresses.                                          *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/poly_uniform_gamma1_4x_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyvecl_uniform_gamma1:
       +0x0: sub     sp, sp, #0x20
       +0x4: sxth    w6, w2
       +0x8: add     w3, w6, #0x3
       +0xc: add     w7, w6, #0x2
      +0x10: mov     x4, x1
      +0x14: mov     w5, w2
      +0x18: strh    w3, [sp]
      +0x1c: add     w6, w6, #0x1
      +0x20: add     x3, x0, #0xc00
      +0x24: add     x2, x0, #0x800
      +0x28: add     x1, x0, #0x400
      +0x2c: str     x30, [sp, #16]
      +0x30: bl      <mldsa44_poly_uniform_gamma1_4x>
      +0x34: ldr     x30, [sp, #16]
      +0x38: add     sp, sp, #0x20
      +0x3c: ret
 ***)

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_polyvecl_uniform_gamma1"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The seed sd is the 64      *)
(* bytes at seed, and polynomial j of the 4 at v becomes                     *)
(* mld_poly_uniform_gamma1_17 of sd and the nonce kappa + j. The stack is    *)
(* the 32 bytes of the function and those of the callees below them.         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !v seed sd kappa guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          nonoverlapping (v,4096) (word_sub stackpointer (word 4496),4496) /\
          ALLPAIRS nonoverlapping
           [(v,4096); (word_sub stackpointer (word 4496),4496)]
           [(seed,64); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa44_polyvecl_uniform_gamma1) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [v; seed; kappa] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,64)) s = sd)
               (\s. read PC s = returnaddress /\
                    (!i. i < 1024
                         ==> read(memory :> bytes32(word_add v (word(4 * i))))
                               s =
                             mld_polyvec
                              (\j. mld_poly_uniform_gamma1_17 sd
                                     (word_add (word_zx kappa) (word j)))
                              i))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(v,4096);
                  memory :> bytes(word_sub stackpointer (word 4496),4496)])`;;

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the address of memset and the     *)
(* stack, with all accesses within the arguments, the stack, the GOT entries *)
(* and the stack guard, the region (ea,el) that memset may read and the      *)
(* round constants of Keccak, and the writes within the vector and the       *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e v seed sd kappa guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          nonoverlapping (v,4096) (word_sub stackpointer (word 4496),4496) /\
          ALLPAIRS nonoverlapping
           [(v,4096); (word_sub stackpointer (word 4496),4496)]
           [(seed,64); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa44_polyvecl_uniform_gamma1) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [v; seed; kappa] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,64)) s = sd /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!i. i < 1024
                         ==> read(memory :> bytes32(word_add v (word(4 * i))))
                               s =
                             mld_polyvec
                              (\j. mld_poly_uniform_gamma1_17 sd
                                     (word_add (word_zx kappa) (word j)))
                              i) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events v seed guard mf pc
                              (word_sub stackpointer (word 4496))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,64; v,4096;
                         word_sub stackpointer (word 4496),4496;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [v,4096;
                         word_sub stackpointer (word 4496),4496]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(v,4096);
                  memory :> bytes(word_sub stackpointer (word 4496),4496)])`;;

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e v seed sd kappa guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          nonoverlapping (v,4096) (word_sub stackpointer (word 4496),4496) /\
          ALLPAIRS nonoverlapping
           [(v,4096); (word_sub stackpointer (word 4496),4496)]
           [(seed,64); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
                    read PC s = word (pc + mldsa44_polyvecl_uniform_gamma1) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [v; seed; kappa] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,64)) s = sd /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events v seed guard mf pc
                              (word_sub stackpointer (word 4496))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,64; v,4096;
                         word_sub stackpointer (word 4496),4496;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [v,4096;
                         word_sub stackpointer (word 4496),4496]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(v,4096);
                  memory :> bytes(word_sub stackpointer (word 4496),4496)])`;;

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
