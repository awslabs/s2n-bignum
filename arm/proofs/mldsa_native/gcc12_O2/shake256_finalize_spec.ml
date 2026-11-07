(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Finalizing the absorbing into a SHAKE256 context: the statement. This is  *)
(* the code for mldsa_shake256_finalize (mld_shake256_finalize in fips202.c, *)
(* with keccak_finalize inlined) from mldsa-native's portable C              *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which XORs the domain separation byte 0x1F at the position and the byte   *)
(* 0x80 at the end 135 of the block into the state, by two calls of          *)
(* mldsa_keccakf1600_xor_bytes with the bytes on its stack, and sets the     *)
(* position to the rate 136. It is verified in the whole image (see          *)
(* libmldsa.ml) against mld_keccak_finalize of                               *)
(* common/mldsa_native_fips202.ml, for a position up to the rate, as the C   *)
(* code requires; the address of the stack guard is read from the GOT.       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_absorb.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/keccakf1600_xor_bytes_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_shake256_finalize:
       +0x0: stp     x19, x30, [sp, #-32]!
       +0x4: mov     w5, #0x1f
       +0x8: mov     w6, #0xffffff80
       +0xc: adrp    x4, 1f000 <page>
      +0x10: ldr     x4, [x4, #4088]
      +0x14: mov     x19, x0
      +0x18: ldr     w2, [x0, #200]
      +0x1c: add     x1, sp, #0x17
      +0x20: ldr     x7, [x4]
      +0x24: str     x7, [sp, #24]
      +0x28: mov     x7, #0x0
      +0x2c: mov     w3, #0x1
      +0x30: strb    w6, [sp, #22]
      +0x34: strb    w5, [sp, #23]
      +0x38: bl      <mldsa_keccakf1600_xor_bytes>
      +0x3c: mov     x0, x19
      +0x40: add     x1, sp, #0x16
      +0x44: mov     w2, #0x87
      +0x48: mov     w3, #0x1
      +0x4c: bl      <mldsa_keccakf1600_xor_bytes>
      +0x50: adrp    x0, 1f000 <page>
      +0x54: ldr     x0, [x0, #4088]
      +0x58: mov     w1, #0x88
      +0x5c: str     w1, [x19, #200]
      +0x60: ldr     x2, [sp, #24]
      +0x64: ldr     x1, [x0]
      +0x68: subs    x2, x2, x1
      +0x6c: mov     x1, #0x0
      +0x70: b.ne    <mldsa_shake256_finalize+0x7c>
      +0x74: ldp     x19, x30, [sp], #32
      +0x78: ret
      +0x7c: bl      <__stack_chk_fail@plt>
 ***)

let MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_shake256_finalize"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!ctx (S:1600 word) pos guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ pos <= 136 /\
        nonoverlapping (ctx,204) (word_sub stackpointer (word 32),32) /\
        ALLPAIRS nonoverlapping
         [(ctx,204); (word_sub stackpointer (word 32),32)]
         [(word pc,libmldsa_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_shake256_finalize) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ctx] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> wbytes ctx) s = S /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word pos)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes ctx) s =
                  mld_keccak_finalize 136 0x1F S pos /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word 136)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(ctx,204);
                         memory :> bytes(word_sub stackpointer (word 32),32)])`;;

let MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SHAKE256_FINALIZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
