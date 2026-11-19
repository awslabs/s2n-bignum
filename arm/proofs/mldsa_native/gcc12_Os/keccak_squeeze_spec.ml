(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Squeezing bytes from a Keccak state at a position, for a rate r. This is  *)
(* the code for the static function keccak_squeeze in mldsa-native's         *)
(* fips202.c (named keccak_squeeze_fn in layout.ml), from its portable C     *)
(* implementation compiled by gcc 12 with -Os (see mldsa_native/README.md),  *)
(* which gcc 12 with -O2 inlines into mldsa_shake128_squeeze and             *)
(* mldsa_shake256_squeeze. It copies the output bytes from the position on   *)
(* with mldsa_keccakf1600_extract_bytes, permutes the state with             *)
(* mldsa_keccakf1600_permute whenever the position has reached the rate r    *)
(* and more bytes are wanted, and returns the new position. The rate r is    *)
(* an argument: 168 for SHAKE128 and 136 for SHAKE256. It is verified in     *)
(* the whole image (see libmldsa.ml) against mld_keccak_squeeze_byte and     *)
(* mld_keccak_squeeze_state of common/mldsa_native_fips202.ml, for a         *)
(* position up to the rate, as the C code requires. The stack is the 64      *)
(* bytes of the function and the 224 used by the permutation below them. It  *)
(* is also shown to be constant time and memory safe.                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_absorb.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/keccakf1600_extract_bytes_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/keccakf1600_permute_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    keccak_squeeze_fn:
       +0x0: stp     x19, x20, [sp, #-64]!
       +0x4: mov     x20, x1
       +0x8: mov     w19, w3
       +0xc: stp     x21, x22, [sp, #16]
      +0x10: mov     w22, w4
      +0x14: stp     x23, x24, [sp, #32]
      +0x18: mov     x24, x0
      +0x1c: mov     x23, x2
      +0x20: stp     x25, x30, [sp, #48]
      +0x24: mov     x25, #0x0
      +0x28: cbnz    x20, <keccak_squeeze_fn+0x44>
      +0x2c: ldp     x21, x22, [sp, #16]
      +0x30: mov     w0, w19
      +0x34: ldp     x23, x24, [sp, #32]
      +0x38: ldp     x25, x30, [sp, #48]
      +0x3c: ldp     x19, x20, [sp], #64
      +0x40: ret
      +0x44: cmp     w19, w22
      +0x48: b.ne    <keccak_squeeze_fn+0x58>
      +0x4c: mov     w19, #0x0
      +0x50: mov     x0, x23
      +0x54: bl      <mldsa_keccakf1600_permute>
      +0x58: sub     w0, w22, w19
      +0x5c: sub     w21, w22, w19
      +0x60: cmp     x0, x20
      +0x64: mov     w2, w19
      +0x68: csel    w21, w20, w21, hi
      +0x6c: add     x1, x24, x25
      +0x70: mov     w3, w21
      +0x74: mov     x0, x23
      +0x78: sub     x20, x20, w21, uxtw
      +0x7c: add     w19, w19, w21
      +0x80: add     x25, x25, w21, uxtw
      +0x84: bl      <mldsa_keccakf1600_extract_bytes>
      +0x88: b       <keccak_squeeze_fn+0x28>
 ***)

let MLDSA_NATIVE_KECCAK_SQUEEZE_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "keccak_squeeze_fn"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAK_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!out outlen ctx pos r (S:1600 word) pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\ pos <= r /\
        PAIRWISE nonoverlapping
         [(ctx,200); (out,outlen); (word_sub stackpointer (word 288),288)] /\
        ALL (nonoverlapping (word pc,libmldsa_size))
         [(ctx,200); (out,outlen); (word_sub stackpointer (word 288),288)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + keccak_squeeze_fn) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; ctx; word pos; word r] s /\
                  read (memory :> wbytes ctx) s = S)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist
                   (list_of_seq (mld_keccak_squeeze_byte r S pos) outlen) /\
                  read (memory :> wbytes ctx) s =
                  FST(mld_keccak_squeeze_state r S pos outlen) /\
                  read X0 s =
                  word(SND(mld_keccak_squeeze_state r S pos outlen)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE [memory :> bytes(ctx,200); memory :> bytes(out,outlen);
                         memory :> bytes(word_sub stackpointer (word 288),288)])`;;

let MLDSA_NATIVE_KECCAK_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_KECCAK_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the length, the position and the  *)
(* rate only (which give the number of blocks), with all accesses within the *)
(* output, the context, the stack and the round constants of the             *)
(* permutation, and the writes within the context, the output and the stack. *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAK_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e out outlen ctx pos r (S:1600 word) pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\ pos <= r /\
        PAIRWISE nonoverlapping
         [(ctx,200); (out,outlen); (word_sub stackpointer (word 288),288)] /\
        ALL (nonoverlapping (word pc,libmldsa_size))
         [(ctx,200); (out,outlen); (word_sub stackpointer (word 288),288)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + keccak_squeeze_fn) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; ctx; word pos; word r] s /\
                  read (memory :> wbytes ctx) s = S /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist
                   (list_of_seq (mld_keccak_squeeze_byte r S pos) outlen) /\
                  read (memory :> wbytes ctx) s =
                  FST(mld_keccak_squeeze_state r S pos outlen) /\
                  read X0 s =
                  word(SND(mld_keccak_squeeze_state r S pos outlen)) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out outlen ctx pos r pc
                                 (word_sub stackpointer (word 288))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,outlen; ctx,200;
                       word_sub stackpointer (word 288),288;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [ctx,200; out,outlen;
                       word_sub stackpointer (word 288),288]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ctx,200); memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 288),288)])`;;

let MLDSA_NATIVE_KECCAK_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_KECCAK_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAK_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e out outlen ctx pos r pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\ pos <= r /\
        PAIRWISE nonoverlapping
         [(ctx,200); (out,outlen); (word_sub stackpointer (word 288),288)] /\
        ALL (nonoverlapping (word pc,libmldsa_size))
         [(ctx,200); (out,outlen); (word_sub stackpointer (word 288),288)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + keccak_squeeze_fn) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; ctx; word pos; word r] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events out outlen ctx pos r pc
                                 (word_sub stackpointer (word 288))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [out,outlen; ctx,200;
                       word_sub stackpointer (word 288),288;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [ctx,200; out,outlen;
                       word_sub stackpointer (word 288),288]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ctx,200); memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 288),288)])`;;

let MLDSA_NATIVE_KECCAK_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_KECCAK_SQUEEZE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
