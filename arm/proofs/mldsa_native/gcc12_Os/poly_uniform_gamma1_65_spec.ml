(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Uniform sampling of one polynomial of y in [-gamma1 + 1, gamma1] for      *)
(* ML-DSA-65 (gamma1 = 2^19): the statement. This is the code for            *)
(* mldsa65_poly_uniform_gamma1 (mld_poly_uniform_gamma1 in poly_kl.c) from   *)
(* mldsa-native's portable C implementation compiled by gcc 12 with -Os (see *)
(* mldsa_native/README.md), which extends the seed of 64 bytes with the      *)
(* 16-bit nonce (the low 16 bits of the third argument), absorbs it into a   *)
(* SHAKE256 context with mldsa_shake256_init, _absorb and _finalize,         *)
(* squeezes 5 blocks of 136 bytes with mldsa_shake256_squeeze, unpacks the   *)
(* polynomial from the first 640 with mldsa65_polyz_unpack and releases the  *)
(* context, before zeroing the buffer and the extended seed with             *)
(* mld_zeroize. It is verified in the whole image (see libmldsa.ml)          *)
(* against mld_poly_uniform_gamma1_19 of common/mldsa_native_sampling.ml,    *)
(* using the theorems for the callees and the contract memset_full_contract  *)
(* of utils/mlkem_native_libc_full.ml for memset, and shown to be constant   *)
(* time and memory safe, with the events depending only on the addresses.    *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc_full.ml";;
needs "common/mldsa_native_sampling.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256_init_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256_absorb_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256_finalize_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256_squeeze_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/shake256_release_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/polyz_unpack_65_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/zeroize_3_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    mldsa65_poly_uniform_gamma1:
       +0x0: sub     sp, sp, #0x430
       +0x4: stp     x19, x20, [sp]
       +0x8: add     x19, sp, #0x4f
       +0xc: and     x19, x19, #0xffffffffffffffe0
      +0x10: stp     x21, x22, [sp, #16]
      +0x14: add     x20, x19, #0x2c0
      +0x18: mov     x22, x0
      +0x1c: str     x30, [sp, #32]
      +0x20: add     x21, sp, #0x358
      +0x24: adrp    x0, <page>
      +0x28: ldr     x0, [x0, #4088]
      +0x2c: ldp     q0, q1, [x1]
      +0x30: ldr     x3, [x0]
      +0x34: str     x3, [sp, #1064]
      +0x38: mov     x3, #0x0
      +0x3c: mov     x0, x21
      +0x40: stp     q0, q1, [x20]
      +0x44: ldp     q0, q1, [x1, #32]
      +0x48: stp     q0, q1, [x20, #32]
      +0x4c: strh    w2, [x19, #768]
      +0x50: bl      <mldsa_shake256_init>
      +0x54: mov     x1, x20
      +0x58: mov     x2, #0x42
      +0x5c: mov     x0, x21
      +0x60: bl      <mldsa_shake256_absorb>
      +0x64: mov     x0, x21
      +0x68: bl      <mldsa_shake256_finalize>
      +0x6c: mov     x2, x21
      +0x70: mov     x0, x19
      +0x74: mov     x1, #0x2a8
      +0x78: bl      <mldsa_shake256_squeeze>
      +0x7c: mov     x1, x19
      +0x80: mov     x0, x22
      +0x84: bl      <mldsa65_polyz_unpack>
      +0x88: mov     x0, x21
      +0x8c: bl      <mldsa_shake256_release>
      +0x90: mov     x0, x19
      +0x94: mov     x1, #0x2a8
      +0x98: bl      <mld_zeroize_3>
      +0x9c: mov     x0, x20
      +0xa0: mov     x1, #0x42
      +0xa4: bl      <mld_zeroize_3>
      +0xa8: adrp    x0, <page>
      +0xac: ldr     x0, [x0, #4088]
      +0xb0: ldr     x2, [sp, #1064]
      +0xb4: ldr     x1, [x0]
      +0xb8: subs    x2, x2, x1
      +0xbc: mov     x1, #0x0
      +0xc0: b.eq    <mldsa65_poly_uniform_gamma1+0xc8>
      +0xc4: bl      <stack_chk_fail>
      +0xc8: ldp     x19, x20, [sp]
      +0xcc: ldp     x21, x22, [sp, #16]
      +0xd0: ldr     x30, [sp, #32]
      +0xd4: add     sp, sp, #0x430
      +0xd8: ret
 ***)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "mldsa65_poly_uniform_gamma1"];;

(* ------------------------------------------------------------------------- *)
(* Correctness, assuming the contract for memset. The seed sd is the 64      *)
(* bytes at seed, and the polynomial at a becomes mld_poly_uniform_gamma1_19 *)
(* of sd and the nonce. The stack is the 1072 bytes of the function and the  *)
(* 304 used by absorbing or squeezing below them.                            *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> !a seed sd nonce guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          nonoverlapping (a,1024) (word_sub stackpointer (word 1376),1376) /\
          ALLPAIRS nonoverlapping
           [(a,1024); (word_sub stackpointer (word 1376),1376)]
           [(seed,64); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa65_poly_uniform_gamma1) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; seed; nonce] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,64)) s = sd)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add a (word(4 * i))))
                               s =
                             mld_poly_uniform_gamma1_19 sd (word_zx nonce) i))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(a,1024);
                  memory :> bytes(word_sub stackpointer (word 1376),1376)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the address of memset and the     *)
(* stack, with all accesses within the arguments, the stack, the GOT entries *)
(* and the stack guard, the region (ea,el) that memset may read and the      *)
(* round constants of Keccak, and the writes within the polynomial and the   *)
(* stack.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e a seed sd nonce guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          nonoverlapping (a,1024) (word_sub stackpointer (word 1376),1376) /\
          ALLPAIRS nonoverlapping
           [(a,1024); (word_sub stackpointer (word 1376),1376)]
           [(seed,64); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa65_poly_uniform_gamma1) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; seed; nonce] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,64)) s = sd /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (!i. i < 256
                         ==> read(memory :> bytes32(word_add a (word(4 * i))))
                               s =
                             mld_poly_uniform_gamma1_19 sd (word_zx nonce) i) /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events a seed guard mf pc
                              (word_sub stackpointer (word 1376))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,64; a,1024;
                         word_sub stackpointer (word 1376),1376;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [a,1024; word_sub stackpointer (word 1376),1376]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(a,1024);
                  memory :> bytes(word_sub stackpointer (word 1376),1376)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
  `!mf ea el ev.
     memset_full_contract mf ea el ev
     ==> exists f_events.
          forall e a seed sd nonce guard pc stackpointer returnaddress.
          aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
          aligned 16 stackpointer /\
          nonoverlapping (a,1024) (word_sub stackpointer (word 1376),1376) /\
          ALLPAIRS nonoverlapping
           [(a,1024); (word_sub stackpointer (word 1376),1376)]
           [(seed,64); (word pc,libmldsa_size);
            (word(pc + got_stack_chk_guard),8); (guard,8);
            (word(pc + got_memset),8); (ea,el)]
          ==> ensures arm
               (\s. aligned_bytes_loaded s (word pc)
                      mldsa_native_libmldsa_gcc12_Os_mc /\
                    read PC s = word (pc + mldsa65_poly_uniform_gamma1) /\
                    read SP s = stackpointer /\
                    read X30 s = returnaddress /\
                    C_ARGUMENTS [a; seed; nonce] s /\
                    read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                      guard /\
                    read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                    read (memory :> bytes(ea,el)) s = ev /\
                    read (memory :> bytes(seed,64)) s = sd /\
                    read events s = e)
               (\s. read PC s = returnaddress /\
                    (exists e2.
                       read events s = APPEND e2 e /\
                       e2 = f_events a seed guard mf pc
                              (word_sub stackpointer (word 1376))
                              returnaddress /\
                       memaccess_inbounds e2
                        [seed,64; a,1024;
                         word_sub stackpointer (word 1376),1376;
                         word(pc + got_stack_chk_guard),8; guard,8;
                         word(pc + got_memset),8; ea,el;
                         word(pc + rodata_mld_KeccakF_RoundConstants),192]
                        [a,1024; word_sub stackpointer (word 1376),1376]))
               (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
                MAYCHANGE
                 [memory :> bytes(a,1024);
                  memory :> bytes(word_sub stackpointer (word 1376),1376)])`;;

let MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_POLY_UNIFORM_GAMMA1_65_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
