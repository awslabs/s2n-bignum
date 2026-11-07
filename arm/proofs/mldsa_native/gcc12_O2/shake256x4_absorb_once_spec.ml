(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing four messages of the same length into four SHAKE256 states.     *)
(* This is the code for mldsa_shake256x4_absorb_once from mldsa-native's     *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mldsa_native/README.md), which zeroes the 800 bytes of the context with   *)
(* memset from the C library, called through the PLT of the image, and then  *)
(* calls mld_keccak_absorb_once_x4 with the rate 136 of SHAKE256, as a tail  *)
(* call. It is verified in the whole image (see                              *)
(* libmldsa.ml), using the theorems for                                      *)
(* mld_keccak_absorb_once_x4 in the image and assuming the contracts for     *)
(* memset in utils/mlkem_native_libc.ml.                                     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/utils/mlkem_native_libc.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/keccak_absorb_once_x4_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image, and the PLT stub for memset:

    mldsa_shake256x4_absorb_once:
       +0x0: stp     x19, x20, [sp, #-64]!
       +0x4: mov     x20, x1
       +0x8: mov     x19, x0
       +0xc: mov     w1, #0x0
      +0x10: stp     x21, x22, [sp, #16]
      +0x14: mov     x22, x3
      +0x18: mov     x21, x2
      +0x1c: mov     x2, #0x320
      +0x20: stp     x23, x24, [sp, #32]
      +0x24: mov     x23, x4
      +0x28: mov     x24, x5
      +0x2c: str     x30, [sp, #48]
      +0x30: bl      <memset@plt>
      +0x34: ldr     x30, [sp, #48]
      +0x38: mov     x6, x24
      +0x3c: mov     x5, x23
      +0x40: mov     x4, x22
      +0x44: ldp     x23, x24, [sp, #32]
      +0x48: mov     x3, x21
      +0x4c: ldp     x21, x22, [sp, #16]
      +0x50: mov     x2, x20
      +0x54: mov     x0, x19
      +0x58: mov     w1, #0x88
      +0x5c: ldp     x19, x20, [sp], #64
      +0x60: b       <mld_keccak_absorb_once_x4.constprop.0>

    memset@plt:
       +0x0: adrp    x16, <page>
       +0x4: ldr     x17, [x16, #4072]
       +0x8: add     x16, x16, #0xfe8
       +0xc: br      x17
 ***)

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_shake256x4_absorb_once"; layout_range "plt_memset"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!st m0 m1 m2 m3 mlen M0 M1 M2 M3 guard mf ea el ev pc stackpointer
    returnaddress.
        memset_contract mf ea el ev /\
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        nonoverlapping (st,800) (word_sub stackpointer (word 304),304) /\
        ALLPAIRS nonoverlapping
         [(st,800); (word_sub stackpointer (word 304),304)]
         [(m0,mlen); (m1,mlen); (m2,mlen); (m3,mlen);
          (word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
          (guard,8);
          (word(pc + got_memset),8); (ea,el)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_shake256x4_absorb_once) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [st; m0; m1; m2; m3; word mlen] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes64(word(pc + got_memset))) s = mf /\
                  read (memory :> bytes(ea,el)) s = ev /\
                  read (memory :> bytes(m0,mlen)) s = M0 /\
                  read (memory :> bytes(m1,mlen)) s = M1 /\
                  read (memory :> bytes(m2,mlen)) s = M2 /\
                  read (memory :> bytes(m3,mlen)) s = M3)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes st) s =
                  word_xor
                   (keccak_absorb 136
                     (M0 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 136 0x1F mlen))
                     (mlen DIV 136))
                   (word((M0 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad 136 0x1F mlen)) DIV
                         2 EXP (8 * 136 * mlen DIV 136) MOD
                         2 EXP (8 * 136))) /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  word_xor
                   (keccak_absorb 136
                     (M1 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 136 0x1F mlen))
                     (mlen DIV 136))
                   (word((M1 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad 136 0x1F mlen)) DIV
                         2 EXP (8 * 136 * mlen DIV 136) MOD
                         2 EXP (8 * 136))) /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  word_xor
                   (keccak_absorb 136
                     (M2 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 136 0x1F mlen))
                     (mlen DIV 136))
                   (word((M2 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad 136 0x1F mlen)) DIV
                         2 EXP (8 * 136 * mlen DIV 136) MOD
                         2 EXP (8 * 136))) /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  word_xor
                   (keccak_absorb 136
                     (M3 + 2 EXP (8 * mlen) *
                           num_of_bytelist(keccak_pad 136 0x1F mlen))
                     (mlen DIV 136))
                   (word((M3 + 2 EXP (8 * mlen) *
                               num_of_bytelist(keccak_pad 136 0x1F mlen)) DIV
                         2 EXP (8 * 136 * mlen DIV 136) MOD 2 EXP (8 * 136))))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 304),304)])`;;

let MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SHAKE256X4_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
