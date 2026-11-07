(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squeezing bytes from a SHAKE256 context: the statement. This is the code  *)
(* for mldsa_shake256_squeeze (mld_shake256_squeeze in fips202.c, with       *)
(* keccak_squeeze inlined) from mldsa-native's portable C implementation     *)
(* compiled by gcc 12 with -O2 (see mldsa_native/README.md), which copies    *)
(* the bytes of the state from the position on with                          *)
(* mldsa_keccakf1600_extract_bytes, permuting it with                        *)
(* mldsa_keccakf1600_permute whenever the position reaches the rate 136 and  *)
(* more bytes are wanted, and stores the new position. It is verified in the *)
(* whole image (see libmldsa.ml) against mld_keccak_squeeze_byte and         *)
(* mld_keccak_squeeze_state of common/mldsa_native_fips202.ml, for a         *)
(* position up to the rate, as the C code requires. The stack is the 64      *)
(* bytes of the function and the 192 used by the permutation below them.     *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_absorb.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/keccakf1600_extract_bytes_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/keccakf1600_permute_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_shake256_squeeze:
       +0x0: stp     x19, x20, [sp, #-64]!
       +0x4: stp     x21, x22, [sp, #16]
       +0x8: ldr     w21, [x2, #200]
       +0xc: stp     x23, x24, [sp, #32]
      +0x10: mov     x23, x2
      +0x14: str     x30, [sp, #56]
      +0x18: cbz     x1, <mldsa_shake256_squeeze+0x98>
      +0x1c: mov     x19, x1
      +0x20: mov     x22, #0x0
      +0x24: mov     w24, #0x88
      +0x28: str     x25, [sp, #48]
      +0x2c: mov     x25, x0
      +0x30: b       <mldsa_shake256_squeeze+0x74>
      +0x34: sub     w3, w24, w21
      +0x38: sub     w20, w24, w21
      +0x3c: mov     w4, w21
      +0x40: add     x1, x25, x22
      +0x44: mov     w2, w4
      +0x48: mov     x0, x23
      +0x4c: mov     w21, #0x88
      +0x50: cmp     x20, x19
      +0x54: b.ls    <mldsa_shake256_squeeze+0x64>
      +0x58: add     w21, w4, w19
      +0x5c: mov     w3, w19
      +0x60: mov     x20, x19
      +0x64: bl      <mldsa_keccakf1600_extract_bytes>
      +0x68: add     x22, x22, x20
      +0x6c: subs    x19, x19, x20
      +0x70: b.eq    <mldsa_shake256_squeeze+0x94>
      +0x74: cmp     w21, #0x88
      +0x78: b.ne    <mldsa_shake256_squeeze+0x34>
      +0x7c: mov     x0, x23
      +0x80: bl      <mldsa_keccakf1600_permute>
      +0x84: mov     w3, w21
      +0x88: mov     x20, #0x88
      +0x8c: mov     w4, #0x0
      +0x90: b       <mldsa_shake256_squeeze+0x40>
      +0x94: ldr     x25, [sp, #48]
      +0x98: ldr     x30, [sp, #56]
      +0x9c: str     w21, [x23, #200]
      +0xa0: ldp     x21, x22, [sp, #16]
      +0xa4: ldp     x23, x24, [sp, #32]
      +0xa8: ldp     x19, x20, [sp], #64
      +0xac: ret
 ***)

let MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_shake256_squeeze"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!out outlen ctx (S:1600 word) pos pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ pos <= 136 /\
        PAIRWISE nonoverlapping
         [(ctx,204); (out,outlen); (word_sub stackpointer (word 256),256)] /\
        ALL (nonoverlapping (word pc,libmldsa_size))
         [(ctx,204); (out,outlen); (word_sub stackpointer (word 256),256)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_shake256_squeeze) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; ctx] s /\
                  read (memory :> wbytes ctx) s = S /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word pos)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist
                   (list_of_seq (mld_keccak_squeeze_byte 136 S pos) outlen) /\
                  read (memory :> wbytes ctx) s =
                  FST(mld_keccak_squeeze_state 136 S pos outlen) /\
                  read (memory :> bytes32(word_add ctx (word 200))) s =
                  word(SND(mld_keccak_squeeze_state 136 S pos outlen)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE [memory :> bytes(ctx,204); memory :> bytes(out,outlen);
                         memory :> bytes(word_sub stackpointer (word 256),256)])`;;

let MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_SHAKE256_SQUEEZE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
