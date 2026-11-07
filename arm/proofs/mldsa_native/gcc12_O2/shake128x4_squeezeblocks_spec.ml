(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squeezing whole blocks from four SHAKE128 states. This is the code for    *)
(* mldsa_shake128x4_squeezeblocks from mldsa-native's portable C             *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which for each of nblocks blocks permutes the four states with            *)
(* mldsa_keccakf1600x4_permute and then extracts the first 168 bytes of each *)
(* with mldsa_keccakf1600x4_extract_bytes. It is verified in the whole image *)
(* (see libmldsa.ml), using the theorems for those                           *)
(* functions.                                                                *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/keccakf1600x4_permute_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/keccakf1600x4_extract_bytes_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_shake128x4_squeezeblocks:
       +0x0: cbz     x4, <mldsa_shake128x4_squeezeblocks+0x80>
       +0x4: stp     x19, x20, [sp, #-64]!
       +0x8: mov     x20, x2
       +0xc: mov     x19, x3
      +0x10: stp     x21, x22, [sp, #16]
      +0x14: mov     x22, x0
      +0x18: mov     x21, x1
      +0x1c: stp     x23, x24, [sp, #32]
      +0x20: mov     x23, x4
      +0x24: mov     x24, x5
      +0x28: str     x30, [sp, #48]
      +0x2c: mov     x0, x24
      +0x30: bl      <mldsa_keccakf1600x4_permute>
      +0x34: mov     x4, x19
      +0x38: mov     x3, x20
      +0x3c: mov     x2, x21
      +0x40: mov     x1, x22
      +0x44: mov     x0, x24
      +0x48: mov     w6, #0xa8
      +0x4c: mov     w5, #0x0
      +0x50: bl      <mldsa_keccakf1600x4_extract_bytes>
      +0x54: add     x19, x19, #0xa8
      +0x58: add     x20, x20, #0xa8
      +0x5c: add     x21, x21, #0xa8
      +0x60: add     x22, x22, #0xa8
      +0x64: subs    x23, x23, #0x1
      +0x68: b.ne    <mldsa_shake128x4_squeezeblocks+0x2c>
      +0x6c: ldp     x21, x22, [sp, #16]
      +0x70: ldp     x23, x24, [sp, #32]
      +0x74: ldr     x30, [sp, #48]
      +0x78: ldp     x19, x20, [sp], #64
      +0x7c: ret
      +0x80: ret
 ***)

let MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_shake128x4_squeezeblocks"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!out0 out1 out2 out3 nblocks st
    (S0:1600 word) (S1:1600 word) (S2:1600 word) (S3:1600 word)
    pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(out0,168 * nblocks); (out1,168 * nblocks); (out2,168 * nblocks);
          (out3,168 * nblocks); (st,800);
          (word_sub stackpointer (word 272),272)] /\
        ALL (nonoverlapping (word pc,libmldsa_size))
         [(out0,168 * nblocks); (out1,168 * nblocks); (out2,168 * nblocks);
          (out3,168 * nblocks); (st,800);
          (word_sub stackpointer (word 272),272)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_shake128x4_squeezeblocks) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out0; out1; out2; out3; word nblocks; st] s /\
                  read (memory :> wbytes st) s = S0 /\
                  read (memory :> wbytes (word_add st (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add st (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add st (word 600))) s = S3)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out0,168 * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * 168 * i) *
                        val(keccak_squeeze (i + 1) S0) MOD 2 EXP (8 * 168)) /\
                  read (memory :> bytes(out1,168 * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * 168 * i) *
                        val(keccak_squeeze (i + 1) S1) MOD 2 EXP (8 * 168)) /\
                  read (memory :> bytes(out2,168 * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * 168 * i) *
                        val(keccak_squeeze (i + 1) S2) MOD 2 EXP (8 * 168)) /\
                  read (memory :> bytes(out3,168 * nblocks)) s =
                  nsum {i | i < nblocks}
                   (\i. 2 EXP (8 * 168 * i) *
                        val(keccak_squeeze (i + 1) S3) MOD 2 EXP (8 * 168)) /\
                  read (memory :> wbytes st) s = keccak_squeeze nblocks S0 /\
                  read (memory :> wbytes (word_add st (word 200))) s =
                  keccak_squeeze nblocks S1 /\
                  read (memory :> wbytes (word_add st (word 400))) s =
                  keccak_squeeze nblocks S2 /\
                  read (memory :> wbytes (word_add st (word 600))) s =
                  keccak_squeeze nblocks S3)
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out0,168 * nblocks);
                memory :> bytes(out1,168 * nblocks);
                memory :> bytes(out2,168 * nblocks);
                memory :> bytes(out3,168 * nblocks);
                memory :> bytes(st,800);
                memory :> bytes(word_sub stackpointer (word 272),272)])`;;

let MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
