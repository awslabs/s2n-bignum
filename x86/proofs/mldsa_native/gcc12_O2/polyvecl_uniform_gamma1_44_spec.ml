(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of the vector y of signing: the statement. This is the code for  *)
(* mldsa44_polyvecl_uniform_gamma1 (mld_polyvecl_uniform_gamma1 in           *)
(* polyvec.c) from mldsa-native's portable C implementation compiled by gcc  *)
(* 12 with -O2 (see mldsa_native/README.md), which samples the four          *)
(* polynomials with one call of mldsa44_poly_uniform_gamma1_4x, with the     *)
(* nonces kappa to kappa + 3 (modulo 2^16, kappa being the low 16 bits of    *)
(* the third argument). It is verified in the whole image (see libmldsa.ml)  *)
(* against mld_poly_uniform_gamma1_17 of common/mldsa_native_sampling.ml,    *)
(* using the theorems for the callee, and shown to be constant time and      *)
(* memory safe, with the events depending only on the addresses. As the      *)
(* callees zero their buffers with memsets that gcc inlines with REP STOSQ,  *)
(* the direction flag must be clear, as the ABI requires on entry.           *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_uniform_gamma1_4x_44_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa44_polyvecl_uniform_gamma1:
       +0x0  lea     eax, [rdx+0x3]
       +0x3  sub     rsp, 0x10
       +0x7  mov     r8, rsi
       +0xa  movzx   r9d, dx
       +0xe  movzx   eax, ax
      +0x11  lea     r10, [rdi+0x800]
      +0x18  lea     rcx, [rdi+0xc00]
      +0x1f  push    rax
      +0x20  lea     eax, [rdx+0x2]
      +0x23  lea     rsi, [rdi+0x400]
      +0x2a  movzx   eax, ax
      +0x2d  push    rax
      +0x2e  lea     eax, [rdx+0x1]
      +0x31  mov     rdx, r10
      +0x34  movzx   eax, ax
      +0x37  push    rax
      +0x38  call    mldsa44_poly_uniform_gamma1_4x
     after_mldsa44_poly_uniform_gamma1_4x:
      +0x3d  add     rsp, 0x28
     ret:
      +0x41  ret
 ***)

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa44_polyvecl_uniform_gamma1"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The seed is the 64 bytes sd at seed, and polynomial j of the *)
(* vector at v becomes mld_poly_uniform_gamma1_17 sd of the nonce kappa + j, *)
(* for j < 4. The function reserves 40 bytes, for alignment and for the      *)
(* three nonces that it passes to mldsa44_poly_uniform_gamma1_4x on the      *)
(* stack, below which the callee uses 4575 bytes, with its return address:   *)
(* 4615 bytes of stack below the return address in all.                      *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!v seed sd kappa pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (v,4096))
            [(word_sub stackpointer (word 4615),4615); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(v,4096); (word_sub stackpointer (word 4615),4615)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyvecl_uniform_gamma1) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [v; seed; kappa] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,64)) s = sd)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s =
                           mld_polyvec
                            (\j. mld_poly_uniform_gamma1_17 sd
                                   (word_add (word_zx kappa) (word j)))
                            i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,4096);
                memory :> bytes(word_sub stackpointer (word 4615),4615)])`;;

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
 MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the stack, with all accesses   *)
(* within the arguments, the stack, the return address and the round         *)
(* constants of Keccak, and the writes within the vector and the stack.      *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e v seed sd kappa pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (v,4096))
            [(word_sub stackpointer (word 4615),4615); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(v,4096); (word_sub stackpointer (word 4615),4615)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyvecl_uniform_gamma1) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [v; seed; kappa] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,64)) s = sd /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 1024
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s =
                           mld_polyvec
                            (\j. mld_poly_uniform_gamma1_17 sd
                                   (word_add (word_zx kappa) (word j)))
                            i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events v seed pc
                            (word_sub stackpointer (word 4615)) returnaddress /\
                     memaccess_inbounds e2
                      [seed,64; v,4096;
                       word_sub stackpointer (word 4615),4615; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [v,4096; word_sub stackpointer (word 4615),4615]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,4096);
                memory :> bytes(word_sub stackpointer (word 4615),4615)])`;;

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e v seed sd kappa pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (v,4096))
            [(word_sub stackpointer (word 4615),4615); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(v,4096); (word_sub stackpointer (word 4615),4615)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa44_polyvecl_uniform_gamma1) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [v; seed; kappa] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,64)) s = sd /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events v seed pc
                            (word_sub stackpointer (word 4615)) returnaddress /\
                     memaccess_inbounds e2
                      [seed,64; v,4096;
                       word_sub stackpointer (word 4615),4615; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [v,4096; word_sub stackpointer (word 4615),4615]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,4096);
                memory :> bytes(word_sub stackpointer (word 4615),4615)])`;;

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_44_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
