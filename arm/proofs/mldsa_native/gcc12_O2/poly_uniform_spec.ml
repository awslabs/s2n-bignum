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
needs "arm/proofs/mldsa_native/gcc12_O2/shake128_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake128_absorb_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake128_finalize_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake128_squeeze_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/shake128_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/rej_uniform_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa_poly_uniform:
       +0x0: sub     sp, sp, #0x470
       +0x4: adrp    x2, <page>
       +0x8: ldr     x2, [x2, #4088]
       +0xc: stp     x19, x20, [sp]
      +0x10: mov     x19, x1
      +0x14: add     x20, sp, #0x4f
      +0x18: stp     x21, x22, [sp, #16]
      +0x1c: add     x21, sp, #0x398
      +0x20: mov     x22, x0
      +0x24: str     x30, [sp, #32]
      +0x28: and     x20, x20, #0xffffffffffffffe0
      +0x2c: ldr     x0, [x2]
      +0x30: str     x0, [sp, #1128]
      +0x34: mov     x0, #0x0
      +0x38: mov     x0, x21
      +0x3c: bl      <mldsa_shake128_init>
      +0x40: mov     x1, x19
      +0x44: mov     x2, #0x22
      +0x48: mov     x0, x21
      +0x4c: bl      <mldsa_shake128_absorb>
      +0x50: mov     x0, x21
      +0x54: bl      <mldsa_shake128_finalize>
      +0x58: mov     x2, x21
      +0x5c: mov     x0, x20
      +0x60: mov     x1, #0x348
      +0x64: bl      <mldsa_shake128_squeeze>
      +0x68: mov     x2, x20
      +0x6c: mov     x0, x22
      +0x70: mov     w3, #0x348
      +0x74: mov     w1, #0x0
      +0x78: bl      <mld_rej_uniform_c>
      +0x7c: cmp     w0, #0xff
      +0x80: b.hi    <+0xb8>
      +0x84: mov     w19, w0
      +0x88: mov     x2, x21
      +0x8c: mov     x0, x20
      +0x90: mov     x1, #0xa8
      +0x94: bl      <mldsa_shake128_squeeze>
      +0x98: mov     w1, w19
      +0x9c: mov     x2, x20
      +0xa0: mov     x0, x22
      +0xa4: mov     w3, #0xa8
      +0xa8: bl      <mld_rej_uniform_c>
      +0xac: mov     w19, w0
      +0xb0: cmp     w0, #0xff
      +0xb4: b.ls    <+0x88>
      +0xb8: mov     x0, x21
      +0xbc: bl      <mldsa_shake128_release>
      +0xc0: mov     x0, x20
      +0xc4: mov     x2, #0x348
      +0xc8: mov     w1, #0x0
      +0xcc: bl      <memset@plt>
      +0xd0: adrp    x0, <page>
      +0xd4: ldr     x0, [x0, #4088]
      +0xd8: ldr     x2, [sp, #1128]
      +0xdc: ldr     x1, [x0]
      +0xe0: subs    x2, x2, x1
      +0xe4: mov     x1, #0x0
      +0xe8: b.ne    <+0x100>
      +0xec: ldp     x19, x20, [sp]
      +0xf0: ldp     x21, x22, [sp, #16]
      +0xf4: ldr     x30, [sp, #32]
      +0xf8: add     sp, sp, #0x470
      +0xfc: ret
     +0x100: bl      <__stack_chk_fail@plt>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_poly_uniform"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The seed is the 34 bytes M *)
(* at seed, and the polynomial at a becomes mld_poly_uniform M, if the       *)
(* SHAKE128 output of the seed has 256 acceptable groups. The stack is the   *)
(* 1136 bytes of the function and the 256 below them of                      *)
(* mldsa_shake128_absorb and mldsa_shake128_squeeze.                         *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !a seed M guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M) /\
          nonoverlapping (a,1024) (word_sub stackpointer (word 1392),1392) /\
          ALLPAIRS nonoverlapping
           [(a,1024); (word_sub stackpointer (word 1392),1392)]
           [(seed,34); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
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
                  memory :> bytes(word_sub stackpointer (word 1392),1392)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the seed, the address of memset   *)
(* and the stack, with all accesses within the arguments, the stack, the GOT *)
(* entries and the stack guard, the region (ea,el) that memset may read and  *)
(* the round constants of Keccak, and the writes within the polynomial and   *)
(* the stack.                                                                *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e a seed M guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M) /\
          nonoverlapping (a,1024) (word_sub stackpointer (word 1392),1392) /\
          ALLPAIRS nonoverlapping
           [(a,1024); (word_sub stackpointer (word 1392),1392)]
           [(seed,34); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
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
                              (word_sub stackpointer (word 1392))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,34; a,1024;
                         word_sub stackpointer (word 1392),1392;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [a,1024; word_sub stackpointer (word 1392),1392]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(a,1024);
                  memory :> bytes(word_sub stackpointer (word 1392),1392)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone, with the events depending on the   *)
(* seed as above.                                                            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e a seed M guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          mld_rej_uniform_terminates (mld_shake128_stream 34 M) /\
          nonoverlapping (a,1024) (word_sub stackpointer (word 1392),1392) /\
          ALLPAIRS nonoverlapping
           [(a,1024); (word_sub stackpointer (word 1392),1392)]
           [(seed,34); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_O2_mc /\
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
                              (word_sub stackpointer (word 1392))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,34; a,1024;
                         word_sub stackpointer (word 1392),1392;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [a,1024; word_sub stackpointer (word 1392),1392]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(a,1024);
                  memory :> bytes(word_sub stackpointer (word 1392),1392)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;
