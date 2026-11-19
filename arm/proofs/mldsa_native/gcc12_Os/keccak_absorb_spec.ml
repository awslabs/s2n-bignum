(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Absorbing a message into a Keccak state at a position, for a rate r. This *)
(* is the code for the static function keccak_absorb in mldsa-native's       *)
(* fips202.c (named keccak_absorb_fn in layout.ml), from its portable C      *)
(* implementation compiled by gcc 12 with -Os (see mldsa_native/README.md),  *)
(* which gcc 12 with -O2 inlines into mldsa_shake128_absorb and              *)
(* mldsa_shake256_absorb. It XORs the message into the state from the        *)
(* position on, with mldsa_keccakf1600_xor_bytes, permutes the state with    *)
(* mldsa_keccakf1600_permute after each full block of r bytes, and returns   *)
(* the new position. The rate r is an argument: 168 for SHAKE128 and 136 for *)
(* SHAKE256. It is verified in the whole image (see libmldsa.ml) against     *)
(* mld_keccak_absorb of common/mldsa_native_fips202.ml, for a position up to *)
(* the rate, as the C code requires. The stack is the 64 bytes of the        *)
(* function and the 224 used by the permutation below them. It is also shown *)
(* to be constant time and memory safe.                                      *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/utils/mldsa_native_absorb.ml";;
needs "common/mldsa_native_fips202.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/keccakf1600_xor_bytes_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/keccakf1600_permute_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/libmldsa.ml";;

(*** The code in the image:

    keccak_absorb_fn:
       +0x0: stp     x19, x20, [sp, #-64]!
       +0x4: mov     w19, w1
       +0x8: mov     x20, x4
       +0xc: stp     x21, x22, [sp, #16]
      +0x10: mov     x22, x0
      +0x14: mov     x21, x3
      +0x18: stp     x23, x24, [sp, #32]
      +0x1c: mov     w23, w2
      +0x20: str     x30, [sp, #48]
      +0x24: sub     w24, w23, w19
      +0x28: sub     w3, w23, w19
      +0x2c: cmp     x24, x20
      +0x30: b.ls    <keccak_absorb_fn+0x60>
      +0x34: mov     w3, w20
      +0x38: mov     w2, w19
      +0x3c: mov     x1, x21
      +0x40: mov     x0, x22
      +0x44: bl      <mldsa_keccakf1600_xor_bytes>
      +0x48: ldp     x21, x22, [sp, #16]
      +0x4c: add     w0, w19, w20
      +0x50: ldp     x23, x24, [sp, #32]
      +0x54: ldr     x30, [sp, #48]
      +0x58: ldp     x19, x20, [sp], #64
      +0x5c: ret
      +0x60: mov     w2, w19
      +0x64: mov     x1, x21
      +0x68: mov     x0, x22
      +0x6c: bl      <mldsa_keccakf1600_xor_bytes>
      +0x70: mov     x0, x22
      +0x74: sub     x20, x20, x24
      +0x78: add     x21, x21, x24
      +0x7c: mov     w19, #0x0
      +0x80: bl      <mldsa_keccakf1600_permute>
      +0x84: b       <keccak_absorb_fn+0x24>
 ***)

let MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_EXEC =
  ARM_MK_EXEC_RANGES_RULE mldsa_native_libmldsa_gcc12_Os_mc
   [layout_range "keccak_absorb_fn"];;

(* ------------------------------------------------------------------------- *)
(* Correctness.                                                              *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT =
 `!ctx pos r src inlen (S:1600 word) M pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\ pos <= r /\
        PAIRWISE nonoverlapping
         [(ctx,200); (src,inlen); (word_sub stackpointer (word 288),288)] /\
        ALL (nonoverlapping (word pc,libmldsa_size))
         [(ctx,200); (word_sub stackpointer (word 288),288)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + keccak_absorb_fn) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ctx; word pos; word r; src; word inlen] s /\
                  read (memory :> wbytes ctx) s = S /\
                  read (memory :> bytes(src,inlen)) s = M)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes ctx) s =
                  FST(mld_keccak_absorb r S pos inlen M) /\
                  read X0 s = word(SND(mld_keccak_absorb r S pos inlen M)))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE [memory :> bytes(ctx,200);
                         memory :> bytes(word_sub stackpointer (word 288),288)])`;;

let MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_CORRECT =
  assume_spec
   MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety together: the same, and the  *)
(* events are a function of the addresses, the length, the position and the  *)
(* rate only (which give the number of blocks), with all accesses within the *)
(* context, the message, the stack and the round constants of the            *)
(* permutation, and the writes within the context and the stack.             *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT =
 `exists f_events.
     forall e ctx pos r src inlen (S:1600 word) M pc stackpointer
            returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\ pos <= r /\
        PAIRWISE nonoverlapping
         [(ctx,200); (src,inlen); (word_sub stackpointer (word 288),288)] /\
        ALL (nonoverlapping (word pc,libmldsa_size))
         [(ctx,200); (word_sub stackpointer (word 288),288)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + keccak_absorb_fn) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ctx; word pos; word r; src; word inlen] s /\
                  read (memory :> wbytes ctx) s = S /\
                  read (memory :> bytes(src,inlen)) s = M /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  read (memory :> wbytes ctx) s =
                  FST(mld_keccak_absorb r S pos inlen M) /\
                  read X0 s = word(SND(mld_keccak_absorb r S pos inlen M)) /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events ctx pos r src inlen pc
                                 (word_sub stackpointer (word 288))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [ctx,200; src,inlen;
                       word_sub stackpointer (word 288),288;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [ctx,200; word_sub stackpointer (word 288),288]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ctx,200);
                memory :> bytes(word_sub stackpointer (word 288),288)])`;;

let MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_FULL =
  assume_spec MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant time and memory safety alone.                                    *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT =
 `exists f_events.
     forall e ctx pos r src inlen pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmldsa_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\ 0 < r /\ r <= 200 /\ pos <= r /\
        PAIRWISE nonoverlapping
         [(ctx,200); (src,inlen); (word_sub stackpointer (word 288),288)] /\
        ALL (nonoverlapping (word pc,libmldsa_size))
         [(ctx,200); (word_sub stackpointer (word 288),288)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mldsa_native_libmldsa_gcc12_Os_mc /\
                  read PC s = word (pc + keccak_absorb_fn) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [ctx; word pos; word r; src; word inlen] s /\
                  read events s = e)
             (\s. read PC s = returnaddress /\
                  (exists e2.
                     read events s = APPEND e2 e /\
                     e2 = f_events ctx pos r src inlen pc
                                 (word_sub stackpointer (word 288))
                                 returnaddress /\
                     memaccess_inbounds e2
                      [ctx,200; src,inlen;
                       word_sub stackpointer (word 288),288;
                       word(pc + rodata_mld_KeccakF_RoundConstants),192]
                      [ctx,200; word_sub stackpointer (word 288),288]))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(ctx,200);
                memory :> bytes(word_sub stackpointer (word 288),288)])`;;

let MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLDSA_NATIVE_KECCAK_ABSORB_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT;;
