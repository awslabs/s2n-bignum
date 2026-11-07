(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Extraction of bytes from four Keccak states. This is the code for         *)
(* mldsa_keccakf1600x4_extract_bytes from mldsa-native's portable C          *)
(* implementation compiled by gcc 12 with -O2 (see mldsa_native/README.md),  *)
(* which calls mldsa_keccakf1600_extract_bytes for each of the states, the   *)
(* last time as a tail call. It is verified in the whole image (see          *)
(* libmldsa.ml), using the theorems for                                      *)
(* mldsa_keccakf1600_extract_bytes in the image.                             *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_keccak.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/keccakf1600_extract_bytes_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_O2/libmldsa.ml";;

(*** The code in the image:

    mldsa_keccakf1600x4_extract_bytes:
       +0x0: stp     x19, x20, [sp, #-64]!
       +0x4: mov     w19, w5
       +0x8: mov     w20, w6
       +0xc: stp     x21, x22, [sp, #16]
      +0x10: mov     x22, x4
      +0x14: mov     x21, x0
      +0x18: stp     x23, x24, [sp, #32]
      +0x1c: mov     x24, x2
      +0x20: mov     x23, x3
      +0x24: mov     w2, w5
      +0x28: mov     w3, w6
      +0x2c: str     x30, [sp, #48]
      +0x30: bl      <mldsa_keccakf1600_extract_bytes>
      +0x34: mov     w3, w20
      +0x38: mov     w2, w19
      +0x3c: mov     x1, x24
      +0x40: add     x0, x21, #0xc8
      +0x44: bl      <mldsa_keccakf1600_extract_bytes>
      +0x48: mov     w3, w20
      +0x4c: mov     w2, w19
      +0x50: mov     x1, x23
      +0x54: add     x0, x21, #0x190
      +0x58: bl      <mldsa_keccakf1600_extract_bytes>
      +0x5c: ldp     x23, x24, [sp, #32]
      +0x60: mov     w3, w20
      +0x64: ldr     x30, [sp, #48]
      +0x68: mov     w2, w19
      +0x6c: mov     x1, x22
      +0x70: add     x0, x21, #0x258
      +0x74: ldp     x21, x22, [sp, #16]
      +0x78: ldp     x19, x20, [sp], #64
      +0x7c: b       <mldsa_keccakf1600_extract_bytes>
 ***)

let MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_O2_mc
   [layout_range "mldsa_keccakf1600x4_extract_bytes"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!a d0 d1 d2 d3 off len (S0:1600 word) (S1:1600 word) (S2:1600 word)
    (S3:1600 word) pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ off + len <= 200 /\
        PAIRWISE nonoverlapping
         [(d0,len); (d1,len); (d2,len); (d3,len);
          (word_sub stackpointer (word 64),64)] /\
        ALLPAIRS nonoverlapping
         [(d0,len); (d1,len); (d2,len); (d3,len);
          (word_sub stackpointer (word 64),64)]
         [(word pc,libmldsa_size); (a,800)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_O2_mc /\
                  read PC s = word (pc + mldsa_keccakf1600x4_extract_bytes) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [a; d0; d1; d2; d3; word off; word len] s /\
                  read (memory :> wbytes a) s = S0 /\
                  read (memory :> wbytes (word_add a (word 200))) s = S1 /\
                  read (memory :> wbytes (word_add a (word 400))) s = S2 /\
                  read (memory :> wbytes (word_add a (word 600))) s = S3)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(d0,len)) s =
                  (val S0 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                  read (memory :> bytes(d1,len)) s =
                  (val S1 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                  read (memory :> bytes(d2,len)) s =
                  (val S2 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len) /\
                  read (memory :> bytes(d3,len)) s =
                  (val S3 DIV 2 EXP (8 * off)) MOD 2 EXP (8 * len))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
              MAYCHANGE [memory :> bytes(d0,len); memory :> bytes(d1,len);
                         memory :> bytes(d2,len); memory :> bytes(d3,len);
                         memory :> bytes(word_sub stackpointer
                                                  (word 64),64)])`;;

let MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;
