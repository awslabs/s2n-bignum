(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing a message into a SHAKE128 context: the statement. This is the   *)
(* code for mldsa_shake128_absorb (mld_shake128_absorb in fips202.c, with    *)
(* keccak_absorb inlined) from mldsa-native's portable C implementation      *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), which XORs the  *)
(* message into the state from the position on, with                         *)
(* mldsa_keccakf1600_xor_bytes, permuting it with mldsa_keccakf1600_permute  *)
(* after each full block of 168 bytes, and stores the new position. It is    *)
(* verified in the whole image (see libmldsa.ml) against mld_keccak_absorb   *)
(* of common/mldsa_native_fips202.ml, for a position up to the rate, as the  *)
(* C code requires. The stack is the 64 bytes of the function and the 192    *)
(* used by the permutation below them.                                       *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_absorb.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/keccakf1600_xor_bytes_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/keccakf1600_permute_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_shake128_absorb:
       +0x0: stp     x19, x20, [sp, #-64]!
       +0x4: mov     x19, x2
       +0x8: mov     w3, #0xa8
       +0xc: ldr     w2, [x0, #200]
      +0x10: mov     x20, x1
      +0x14: stp     x21, x22, [sp, #16]
      +0x18: mov     x22, x0
      +0x1c: sub     w21, w3, w2
      +0x20: str     x30, [sp, #32]
      +0x24: sub     w3, w3, w2
      +0x28: cmp     x21, x19
      +0x2c: b.hi    <mldsa_shake128_absorb+0x60>
      +0x30: mov     x1, x20
      +0x34: mov     x0, x22
      +0x38: bl      <mldsa_keccakf1600_xor_bytes>
      +0x3c: sub     x19, x19, x21
      +0x40: mov     x0, x22
      +0x44: add     x20, x20, x21
      +0x48: bl      <mldsa_keccakf1600_permute>
      +0x4c: mov     x21, #0xa8
      +0x50: mov     w2, #0x0
      +0x54: mov     w3, #0xa8
      +0x58: cmp     x19, #0xa7
      +0x5c: b.hi    <mldsa_shake128_absorb+0x30>
      +0x60: mov     x1, x20
      +0x64: mov     w3, w19
      +0x68: mov     x0, x22
      +0x6c: str     w2, [sp, #60]
      +0x70: bl      <mldsa_keccakf1600_xor_bytes>
      +0x74: ldr     w2, [sp, #60]
      +0x78: ldr     x30, [sp, #32]
      +0x7c: add     w2, w2, w19
      +0x80: str     w2, [x22, #200]
      +0x84: ldp     x21, x22, [sp, #16]
      +0x88: ldp     x19, x20, [sp], #64
      +0x8c: ret
 ***)

let MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_shake128_absorb"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!ctx src inlen (S:1600 word) pos M pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ pos <= 168 /\
        PAIRWISE nonoverlapping
         [(ctx,204); (src,inlen); (word_sub stackpointer (word 256),256)] /\
        ALL (nonoverlapping (word pc,libmldsa_size))
         [(ctx,204); (word_sub stackpointer (word 256),256)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_shake128_absorb) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ctx; src; word inlen] s /\
                  read (memory :> wbytes ctx) s = S /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word pos /\
                  read (memory :> bytes(src,inlen)) s = M)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes ctx) s =
                  FST(mld_keccak_absorb 168 S pos inlen M) /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word(SND(mld_keccak_absorb 168 S pos inlen M)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE [memory :> bytes(ctx,204);
                         memory :> bytes(word_sub stackpointer (word 256),256)])`;;

let MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SHAKE128_ABSORB_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
