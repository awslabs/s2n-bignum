(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of the vector y of signing: the statement. This is the code for  *)
(* mldsa65_polyvecl_uniform_gamma1 (mld_polyvecl_uniform_gamma1 in           *)
(* polyvec.c) from mldsa-native's portable C implementation compiled by gcc  *)
(* 12 with -O2 (see mldsa_native/README.md), which samples the first four    *)
(* polynomials with mldsa65_poly_uniform_gamma1_4x, with the nonces kappa to *)
(* kappa + 3, and the fifth with mldsa65_poly_uniform_gamma1, in a tail      *)
(* call, with kappa + 4 (all modulo 2^16, kappa being the low 16 bits of the *)
(* third argument). It is verified in the whole image (see libmldsa.ml)      *)
(* against mld_poly_uniform_gamma1_19 of common/mldsa_native_sampling.ml,    *)
(* using the theorems for the callees, and shown to be constant time and     *)
(* memory safe, with the events depending only on the addresses. As the      *)
(* callees zero their buffers with memsets that gcc inlines with REP STOSQ,  *)
(* the direction flag must be clear, as the ABI requires on entry.           *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_uniform_gamma1_4x_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_uniform_gamma1_65_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa65_polyvecl_uniform_gamma1:
       +0x0  push    r12
       +0x2  mov     r12, rsi
       +0x5  lea     rcx, [rdi+0xc00]
       +0xc  lea     rsi, [rdi+0x400]
      +0x13  push    rbp
      +0x14  mov     r8, r12
      +0x17  mov     rbp, rdi
      +0x1a  push    rbx
      +0x1b  mov     ebx, edx
      +0x1d  lea     rdx, [rdi+0x800]
      +0x24  lea     eax, [rbx+0x3]
      +0x27  movzx   r9d, bx
      +0x2b  movzx   eax, ax
      +0x2e  sub     rsp, 0x8
      +0x32  push    rax
      +0x33  lea     eax, [rbx+0x2]
      +0x36  movzx   eax, ax
      +0x39  push    rax
      +0x3a  lea     eax, [rbx+0x1]
      +0x3d  movzx   eax, ax
      +0x40  push    rax
      +0x41  call    mldsa65_poly_uniform_gamma1_4x
     after_mldsa65_poly_uniform_gamma1_4x:
      +0x46  add     rsp, 0x20
      +0x4a  lea     edx, [rbx+0x4]
      +0x4d  mov     rsi, r12
      +0x50  pop     rbx
      +0x51  lea     rdi, [rbp+0x1000]
      +0x58  movzx   edx, dx
      +0x5b  pop     rbp
      +0x5c  pop     r12
      +0x5e  jmp     mldsa65_poly_uniform_gamma1
 ***)

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa65_polyvecl_uniform_gamma1"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The seed is the 64 bytes sd at seed, and polynomial j of the *)
(* vector at v becomes mld_poly_uniform_gamma1_19 sd of the nonce kappa + j, *)
(* for j < 5. The function saves three registers and reserves 32 bytes, for  *)
(* alignment and for the three nonces that it passes to                      *)
(* mldsa65_poly_uniform_gamma1_4x on the stack, below which the callee uses  *)
(* 4575 bytes, with its return address: 4631 bytes of stack below the return *)
(* address in all (the tail call of mldsa65_poly_uniform_gamma1 uses less).  *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!v seed sd kappa pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (v,5120))
            [(word_sub stackpointer (word 4631),4631); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(v,5120); (word_sub stackpointer (word 4631),4631)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_polyvecl_uniform_gamma1) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [v; seed; kappa] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,64)) s = sd)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 1280
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s =
                           mld_polyvec
                            (\j. mld_poly_uniform_gamma1_19 sd
                                   (word_add (word_zx kappa) (word j)))
                            i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,5120);
                memory :> bytes(word_sub stackpointer (word 4631),4631)])`;;

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
 MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the stack, with all accesses   *)
(* within the arguments, the stack, the return address and the round         *)
(* constants of Keccak, and the writes within the vector and the stack.      *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e v seed sd kappa pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (v,5120))
            [(word_sub stackpointer (word 4631),4631); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(v,5120); (word_sub stackpointer (word 4631),4631)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_polyvecl_uniform_gamma1) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [v; seed; kappa] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,64)) s = sd /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 1280
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s =
                           mld_polyvec
                            (\j. mld_poly_uniform_gamma1_19 sd
                                   (word_add (word_zx kappa) (word j)))
                            i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events v seed pc
                            (word_sub stackpointer (word 4631)) returnaddress /\
                     memaccess_inbounds e2
                      [seed,64; v,5120;
                       word_sub stackpointer (word 4631),4631; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [v,5120; word_sub stackpointer (word 4631),4631]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,5120);
                memory :> bytes(word_sub stackpointer (word 4631),4631)])`;;

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e v seed sd kappa pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (v,5120))
            [(word_sub stackpointer (word 4631),4631); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(v,5120); (word_sub stackpointer (word 4631),4631)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa65_polyvecl_uniform_gamma1) /\
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
                            (word_sub stackpointer (word 4631)) returnaddress /\
                     memaccess_inbounds e2
                      [seed,64; v,5120;
                       word_sub stackpointer (word 4631),4631; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [v,5120; word_sub stackpointer (word 4631),4631]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,5120);
                memory :> bytes(word_sub stackpointer (word 4631),4631)])`;;

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_65_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
