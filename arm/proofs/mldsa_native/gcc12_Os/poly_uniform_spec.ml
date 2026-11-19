(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of a polynomial mod q from a seed by rejection: the      *)
(* statement. This is the code for mldsa_poly_uniform (mld_poly_uniform in   *)
(* poly.c) from mldsa-native's portable C implementation compiled by gcc 12  *)
(* with -Os (see mldsa_native/README.md), which absorbs the seed of 34 bytes *)
(* into a SHAKE128 state, squeezes 5 blocks of 168 bytes and samples the     *)
(* coefficients below q from them with mld_rej_uniform_c, and then squeezes  *)
(* one more block at a time until the polynomial has 256 coefficients,       *)
(* before releasing the state and zeroing the buffer with memset. It is      *)
(* verified in the whole image (see libmldsa.ml) against mld_poly_uniform of *)
(* common/mldsa_native_sampling.ml, using the theorems for the callees and   *)
(* the contract memset_full_contract of utils/mlkem_native_libc_full.ml for  *)
(* memset, and assuming that the SHAKE128 output of the seed has 256         *)
(* acceptable groups of 3 bytes (mld_rej_uniform_terminates), without which  *)
(* the code does not terminate. It is also shown to be constant time and     *)
(* memory safe, with the events depending on the seed, which is public (rho  *)
(* and the indices of the matrix entry).                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake128_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake128_absorb_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake128_finalize_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake128_squeeze_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake128_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/rej_uniform_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa_poly_uniform:
       +0x0: sub     sp, sp, #0x470
       +0x4: stp     x21, x22, [sp, #16]
       +0x8: mov     x22, x0
       +0xc: add     x21, sp, #0x398
      +0x10: adrp    x0, <page>
      +0x14: ldr     x0, [x0, #4088]
      +0x18: stp     x19, x20, [sp]
      +0x1c: mov     x20, x1
      +0x20: str     x30, [sp, #32]
      +0x24: add     x19, sp, #0x4f
      +0x28: and     x19, x19, #0xffffffffffffffe0
      +0x2c: ldr     x1, [x0]
      +0x30: str     x1, [sp, #1128]
      +0x34: mov     x1, #0x0
      +0x38: mov     x0, x21
      +0x3c: bl      <mldsa_shake128_init>
      +0x40: mov     x1, x20
      +0x44: mov     x2, #0x22
      +0x48: mov     x0, x21
      +0x4c: bl      <mldsa_shake128_absorb>
      +0x50: mov     x0, x21
      +0x54: bl      <mldsa_shake128_finalize>
      +0x58: mov     x2, x21
      +0x5c: mov     x1, #0x348
      +0x60: mov     x0, x19
      +0x64: bl      <mldsa_shake128_squeeze>
      +0x68: mov     x2, x19
      +0x6c: mov     w3, #0x348
      +0x70: mov     w1, #0x0
      +0x74: mov     x0, x22
      +0x78: bl      <mld_rej_uniform_c>
      +0x7c: mov     w20, w0
      +0x80: cmp     w0, #0xff
      +0x84: b.ls    <mldsa_poly_uniform+0xc0>
      +0x88: mov     x0, x21
      +0x8c: bl      <mldsa_shake128_release>
      +0x90: mov     x0, x19
      +0x94: mov     x2, #0x348
      +0x98: mov     w1, #0x0
      +0x9c: bl      <memset>
      +0xa0: adrp    x0, <page>
      +0xa4: ldr     x0, [x0, #4088]
      +0xa8: ldr     x2, [sp, #1128]
      +0xac: ldr     x1, [x0]
      +0xb0: subs    x2, x2, x1
      +0xb4: mov     x1, #0x0
      +0xb8: b.eq    <mldsa_poly_uniform+0xe0>
      +0xbc: bl      <stack_chk_fail>
      +0xc0: mov     x2, x21
      +0xc4: mov     x1, #0xa8
      +0xc8: mov     x0, x19
      +0xcc: bl      <mldsa_shake128_squeeze>
      +0xd0: mov     x2, x19
      +0xd4: mov     w1, w20
      +0xd8: mov     w3, #0xa8
      +0xdc: b       <mldsa_poly_uniform+0x74>
      +0xe0: ldp     x19, x20, [sp]
      +0xe4: ldp     x21, x22, [sp, #16]
      +0xe8: ldr     x30, [sp, #32]
      +0xec: add     sp, sp, #0x470
      +0xf0: ret
    plt_memset:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa_poly_uniform"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The seed is the 34 bytes M *)
(* at seed, and the polynomial at a becomes mld_poly_uniform M, if the       *)
(* SHAKE128 output of the seed has 256 acceptable groups. The stack is the   *)
(* 1136 bytes of the function and the 304 below them of                      *)
(* mldsa_shake128_absorb and mldsa_shake128_squeeze.                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !a seed M guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M) /\
          nonoverlapping (a,1024) (word_sub stackpointer (word 1440),1440) /\
          ALLPAIRS nonoverlapping
           [(a,1024); (word_sub stackpointer (word 1440),1440)]
           [(seed,34); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa_poly_uniform) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,34)) s = M)
               (\s. read PC s = returnaddress /\
                    !i. i < 256
                        ==> read(memory :> bytes32(word_add a (word(4 * i))))
                              s = mld_poly_uniform M i)
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(a,1024);
                  memory :> bytes(word_sub stackpointer (word 1440),1440)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the seed, the address of memset   *)
(* and the stack, with all accesses within the arguments, the stack, the GOT *)
(* entries and the stack guard, the region (ea,el) that memset may read and  *)
(* the round constants of Keccak, and the writes within the polynomial and   *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e a seed M guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M) /\
          nonoverlapping (a,1024) (word_sub stackpointer (word 1440),1440) /\
          ALLPAIRS nonoverlapping
           [(a,1024); (word_sub stackpointer (word 1440),1440)]
           [(seed,34); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa_poly_uniform) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,34)) s = M /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add a (word(4 * i))))
                               s = mld_poly_uniform M i) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events a seed M guard mf pc
                              (word_sub stackpointer (word 1440))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,34; a,1024;
                         word_sub stackpointer (word 1440),1440;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [a,1024; word_sub stackpointer (word 1440),1440]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(a,1024);
                  memory :> bytes(word_sub stackpointer (word 1440),1440)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* seed as above.                                                            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e a seed M guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M) /\
          nonoverlapping (a,1024) (word_sub stackpointer (word 1440),1440) /\
          ALLPAIRS nonoverlapping
           [(a,1024); (word_sub stackpointer (word 1440),1440)]
           [(seed,34); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa_poly_uniform) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; seed] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,34)) s = M /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events a seed M guard mf pc
                              (word_sub stackpointer (word 1440))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,34; a,1024;
                         word_sub stackpointer (word 1440),1440;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [a,1024; word_sub stackpointer (word 1440),1440]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(a,1024);
                  memory :> bytes(word_sub stackpointer (word 1440),1440)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
