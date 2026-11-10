(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Sampling of the vector y of signing: the statement. This is the code for  *)
(* mldsa87_polyvecl_uniform_gamma1 (mld_polyvecl_uniform_gamma1 in           *)
(* polyvec.c) from mldsa-native's portable C implementation compiled by gcc  *)
(* 12 with -O2 (see mldsa_native/README.md), which samples the first three   *)
(* polynomials with mldsa87_poly_uniform_gamma1_4x, with the nonces kappa to *)
(* kappa + 2 and a fourth polynomial with nonce 255 at the address of the    *)
(* fourth, and then the last four with a second call, with kappa + 3 to      *)
(* kappa + 6, overwriting the fourth (all modulo 2^16, kappa being the low   *)
(* 16 bits of the third argument). It is verified in the whole image (see    *)
(* libmldsa.ml) against mld_poly_uniform_gamma1_19 of                        *)
(* common/mldsa_native_sampling.ml, using the theorems for the callee, and   *)
(* shown to be constant time and memory safe, with the events depending only *)
(* on the addresses. As the callees zero their buffers with memsets that gcc *)
(* inlines with REP STOSQ, the direction flag must be clear, as the ABI      *)
(* requires on entry.                                                        *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "common/mldsa_native_polyvec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/poly_uniform_gamma1_4x_87_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa87_polyvecl_uniform_gamma1:
       +0x0  push    r13
       +0x2  lea     r13, [rdi+0xc00]
       +0x9  push    r12
       +0xb  mov     r12, rsi
       +0xe  mov     rcx, r13
      +0x11  lea     rsi, [rdi+0x400]
      +0x18  push    rbp
      +0x19  mov     r8, r12
      +0x1c  mov     rbp, rdi
      +0x1f  push    rbx
      +0x20  mov     ebx, edx
      +0x22  lea     rdx, [rdi+0x800]
      +0x29  lea     eax, [rbx+0x2]
      +0x2c  movzx   r9d, bx
      +0x30  movzx   eax, ax
      +0x33  sub     rsp, 0x10
      +0x37  push    0xff
      +0x3c  push    rax
      +0x3d  lea     eax, [rbx+0x1]
      +0x40  movzx   eax, ax
      +0x43  push    rax
      +0x44  call    mldsa87_poly_uniform_gamma1_4x
     after_mldsa87_poly_uniform_gamma1_4x_1:
      +0x49  lea     eax, [rbx+0x6]
      +0x4c  add     rsp, 0x18
      +0x50  lea     r9d, [rbx+0x3]
      +0x54  movzx   eax, ax
      +0x57  lea     rcx, [rbp+0x1800]
      +0x5e  mov     r8, r12
      +0x61  mov     rdi, r13
      +0x64  push    rax
      +0x65  lea     eax, [rbx+0x5]
      +0x68  add     ebx, 0x4
      +0x6b  movzx   r9d, r9w
      +0x6f  movzx   eax, ax
      +0x72  movzx   ebx, bx
      +0x75  lea     rdx, [rbp+0x1400]
      +0x7c  push    rax
      +0x7d  lea     rsi, [rbp+0x1000]
      +0x84  push    rbx
      +0x85  call    mldsa87_poly_uniform_gamma1_4x
     after_mldsa87_poly_uniform_gamma1_4x_2:
      +0x8a  add     rsp, 0x28
      +0x8e  pop     rbx
      +0x8f  pop     rbp
      +0x90  pop     r12
      +0x92  pop     r13
     ret:
      +0x94  ret
 ***)

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_87_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa87_polyvecl_uniform_gamma1"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The seed is the 64 bytes sd at seed, and polynomial j of the *)
(* vector at v becomes mld_poly_uniform_gamma1_19 sd of the nonce kappa + j, *)
(* for j < 7. The function saves four registers and reserves 40 bytes, for   *)
(* alignment and for the three nonces that it passes to                      *)
(* mldsa87_poly_uniform_gamma1_4x on the stack, below which the callee uses  *)
(* 4575 bytes, with its return address: 4647 bytes of stack below the return *)
(* address in all.                                                           *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!v seed sd kappa pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (v,7168))
            [(word_sub stackpointer (word 4647),4647); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(v,7168); (word_sub stackpointer (word 4647),4647)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa87_polyvecl_uniform_gamma1) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [v; seed; kappa] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,64)) s = sd)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 1792
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s =
                           mld_polyvec
                            (\j. mld_poly_uniform_gamma1_19 sd
                                   (word_add (word_zx kappa) (word j)))
                            i))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,7168);
                memory :> bytes(word_sub stackpointer (word 4647),4647)])`;;

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
 MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_87_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses and the stack, with all accesses   *)
(* within the arguments, the stack, the return address and the round         *)
(* constants of Keccak, and the writes within the vector and the stack.      *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e v seed sd kappa pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (v,7168))
            [(word_sub stackpointer (word 4647),4647); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(v,7168); (word_sub stackpointer (word 4647),4647)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa87_polyvecl_uniform_gamma1) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [v; seed; kappa] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,64)) s = sd /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 1792
                       ==> read(memory :> bytes32(word_add v (word(4 * i))))
                             s =
                           mld_polyvec
                            (\j. mld_poly_uniform_gamma1_19 sd
                                   (word_add (word_zx kappa) (word j)))
                            i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events v seed pc
                            (word_sub stackpointer (word 4647)) returnaddress /\
                     memaccess_inbounds e2
                      [seed,64; v,7168;
                       word_sub stackpointer (word 4647),4647; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [v,7168; word_sub stackpointer (word 4647),4647]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,7168);
                memory :> bytes(word_sub stackpointer (word 4647),4647)])`;;

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_87_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec
   MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_87_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let
 MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e v seed sd kappa pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        ALL (nonoverlapping (v,7168))
            [(word_sub stackpointer (word 4647),4647); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(v,7168); (word_sub stackpointer (word 4647),4647)]
         [(seed,64); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa87_polyvecl_uniform_gamma1) /\
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
                            (word_sub stackpointer (word 4647)) returnaddress /\
                     memaccess_inbounds e2
                      [seed,64; v,7168;
                       word_sub stackpointer (word 4647),4647; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [v,7168; word_sub stackpointer (word 4647),4647]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(v,7168);
                memory :> bytes(word_sub stackpointer (word 4647),4647)])`;;

let MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec
   MLDSA_NATIVE_POLYVECL_UNIFORM_GAMMA1_87_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
