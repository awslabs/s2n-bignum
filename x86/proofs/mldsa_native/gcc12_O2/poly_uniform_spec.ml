(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of a polynomial mod q from a seed by rejection: the      *)
(* statement. This is the code for mldsa_poly_uniform (mld_poly_uniform in   *)
(* poly.c) from mldsa-native's portable C implementation compiled by gcc 12  *)
(* with -O2 (see mldsa_native/README.md), which absorbs the seed of 34 bytes *)
(* into a SHAKE128 state, squeezes 5 blocks of 168 bytes and samples the     *)
(* coefficients below q from them with mld_rej_uniform_c, and then squeezes  *)
(* one more block at a time until the polynomial has 256 coefficients,       *)
(* before releasing the state and zeroing the buffer, with a memset that gcc *)
(* inlines with REP STOSQ, so the direction flag must be clear, as the ABI   *)
(* requires on entry. It is verified in the whole image (see libmldsa.ml)    *)
(* against mld_poly_uniform of common/mldsa_native_sampling.ml, using the    *)
(* theorems for the callees, and assuming that the SHAKE128 output of the    *)
(* seed has 256 acceptable groups of 3 bytes (mld_rej_uniform_terminates),   *)
(* without which the code does not terminate. It is also shown to be         *)
(* constant time and memory safe, with the events depending on the seed,     *)
(* which is public (rho and the indices of the matrix entry).                *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/relative.ml";;
needs "x86/proofs/utils/mldsa_native_image.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake128_init_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake128_absorb_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake128_finalize_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake128_squeeze_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/shake128_release_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/rej_uniform_spec.ml";;
needs "x86/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_poly_uniform:
       +0x0  push    rbp
       +0x1  mov     rbp, rsp
       +0x4  push    r14
       +0x6  mov     r14, rdi
       +0x9  push    r13
       +0xb  push    r12
       +0xd  push    rbx
       +0xe  mov     rbx, rsi
      +0x11  and     rsp, 0xffffffffffffffe0
      +0x15  sub     rsp, 0x440
      +0x1c  lea     r13, [rsp+0x10]
      +0x21  lea     r12, [rsp+0xe0]
      +0x29  mov     rdi, r13
      +0x2c  call    mldsa_shake128_init
     after_mldsa_shake128_init:
      +0x31  mov     edx, 0x22
      +0x36  mov     rsi, rbx
      +0x39  mov     rdi, r13
      +0x3c  call    mldsa_shake128_absorb
     after_mldsa_shake128_absorb:
      +0x41  mov     rdi, r13
      +0x44  call    mldsa_shake128_finalize
     after_mldsa_shake128_finalize:
      +0x49  mov     rdx, r13
      +0x4c  mov     esi, 0x348
      +0x51  mov     rdi, r12
      +0x54  call    mldsa_shake128_squeeze
     after_mldsa_shake128_squeeze_1:
      +0x59  xor     esi, esi
      +0x5b  mov     ecx, 0x348
      +0x60  mov     rdx, r12
      +0x63  mov     rdi, r14
      +0x66  call    mld_rej_uniform_c
     after_mld_rej_uniform_c_1:
      +0x6b  cmp     eax, 0xff
      +0x70  ja      join1
      +0x72  mov     ebx, eax
      +0x74  nop     DWORD PTR [rax+0x0]
     loop1:
      +0x78  mov     rdx, r13
      +0x7b  mov     esi, 0xa8
      +0x80  mov     rdi, r12
      +0x83  call    mldsa_shake128_squeeze
     after_mldsa_shake128_squeeze_2:
      +0x88  mov     esi, ebx
      +0x8a  mov     ecx, 0xa8
      +0x8f  mov     rdx, r12
      +0x92  mov     rdi, r14
      +0x95  call    mld_rej_uniform_c
     after_mld_rej_uniform_c_2:
      +0x9a  mov     ebx, eax
     loop1_test:
      +0x9c  cmp     eax, 0xff
     loop1_back:
      +0xa1  jbe     loop1
     join1: loop1_exit:
      +0xa3  mov     rdi, r13
      +0xa6  call    mldsa_shake128_release
     after_mldsa_shake128_release:
      +0xab  xor     eax, eax
      +0xad  mov     rdi, r12
      +0xb0  mov     ecx, 0x69
      +0xb5  rep stos QWORD PTR es:[rdi], rax
      +0xb8  lea     rsp, [rbp-0x20]
      +0xbc  pop     rbx
      +0xbd  pop     r12
      +0xbf  pop     r13
      +0xc1  pop     r14
      +0xc3  pop     rbp
     ret:
      +0xc4  ret
 ***)

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_EXEC =
  X86_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_poly_uniform"];;

(* ------------------------------------------------------------------------- *)
(* Correctness. The seed is the 34 bytes M at seed, and the polynomial at a  *)
(* becomes mld_poly_uniform M, if the SHAKE128 output of the seed has 256    *)
(* acceptable groups. The function saves RBP, the frame pointer, and four    *)
(* more registers below the return address, lowers RSP by up to 31 bytes to  *)
(* align it to 32 bytes, and then reserves 1088 bytes for the context and    *)
(* the buffer, below which the calls of mldsa_shake128_absorb and            *)
(* mldsa_shake128_squeeze use 328 bytes, with their return addresses: 1487   *)
(* bytes of stack below the return address in all.                           *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a seed M pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_uniform_terminates (mld_shake128_stream 34 M) /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 1487),1487); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 1487),1487)]
         [(seed,34); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_uniform) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; seed] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,34)) s = M)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  !i. i < 256
                      ==> read(memory :> bytes32(word_add a (word(4 * i)))) s =
                          mld_poly_uniform M i)
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 1487),1487)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the seed and the stack, with all  *)
(* accesses within the arguments, the stack, the return address and the      *)
(* round constants of Keccak, and the writes within the polynomial and the   *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e a seed M pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_uniform_terminates (mld_shake128_stream 34 M) /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 1487),1487); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 1487),1487)]
         [(seed,34); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_uniform) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; seed] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,34)) s = M /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (!i. i < 256
                       ==> read(memory :> bytes32(word_add a (word(4 * i))))
                             s = mld_poly_uniform M i) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a seed M pc
                            (word_sub stackpointer (word 1487)) returnaddress /\
                     memaccess_inbounds e2
                      [seed,34; a,1024;
                       word_sub stackpointer (word 1487),1487; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [a,1024; word_sub stackpointer (word 1487),1487]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 1487),1487)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* seed as above.                                                            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e a seed M pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        mld_rej_uniform_terminates (mld_shake128_stream 34 M) /\
        ALL (nonoverlapping (a,1024))
            [(word_sub stackpointer (word 1487),1487); (stackpointer,8)] /\
        ALLPAIRS nonoverlapping
         [(a,1024); (word_sub stackpointer (word 1487),1487)]
         [(seed,34); (word pc,libmldsa_size)]
        ==> ensures x86
             (\s. bytes_loaded s (word pc) mldsa_native_libmldsa_gcc12_O2_mc /\
                  read RIP s = word (pc + mldsa_poly_uniform) /\
                  read RSP s = stackpointer /\
                  read (memory :> bytes64 stackpointer) s = returnaddress /\
                  C_ARGUMENTS [a; seed] s /\
                  (read DF s <=> false) /\
                  read (memory :> bytes(seed,34)) s = M /\
                  read events s = e)
             (\s. read RIP s = returnaddress /\
                  read RSP s = word_add stackpointer (word 8) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events a seed M pc
                            (word_sub stackpointer (word 1487)) returnaddress /\
                     memaccess_inbounds e2
                      [seed,34; a,1024;
                       word_sub stackpointer (word 1487),1487; stackpointer,8;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [a,1024; word_sub stackpointer (word 1487),1487]))
             (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE
               [memory :> bytes(a,1024);
                memory :> bytes(word_sub stackpointer (word 1487),1487)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
