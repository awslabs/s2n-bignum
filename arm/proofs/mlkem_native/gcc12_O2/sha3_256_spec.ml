(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA3-256. This is the code for mlkem_sha3_256 from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O2 (see                *)
(* mlkem_native/README.md), which absorbs the input into a state on the      *)
(* stack with mlk_keccak_absorb_once, permutes it and extracts the 32 bytes  *)
(* of the hash, and then zeroes the state. It is verified in the whole image *)
(* (see libmlkem.ml), using the theorems for                                 *)
(* mlk_keccak_absorb_once, mlkem_keccakf1600_permute and                     *)
(* mlkem_keccakf1600_extract_bytes in the image. The result is sha3_256 of   *)
(* common/fips202.ml.                                                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/relative.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/keccak_absorb_once_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/keccakf1600_extract_bytes_spec.ml";;
needs "arm/proofs/mlkem_native/gcc12_O2/libmlkem.ml";;

(*** The code in the image:

    mlkem_sha3_256:
       +0x0: stp     x19, x20, [sp, #-240]!
       +0x4: mov     x3, x2
       +0x8: mov     x2, x1
       +0xc: adrp    x5, <page>
      +0x10: ldr     x5, [x5, #4088]  // got_stack_chk_guard
      +0x14: str     x30, [sp, #16]
      +0x18: add     x19, sp, #0x20
      +0x1c: mov     w4, #0x6
      +0x20: mov     x20, x0
      +0x24: mov     w1, #0x88
      +0x28: ldr     x0, [x5]
      +0x2c: str     x0, [sp, #232]
      +0x30: mov     x0, #0x0
      +0x34: mov     x0, x19
      +0x38: bl      <mlk_keccak_absorb_once>
      +0x3c: mov     x0, x19
      +0x40: bl      <mlkem_keccakf1600_permute>
      +0x44: mov     x1, x20
      +0x48: mov     x0, x19
      +0x4c: mov     w3, #0x20
      +0x50: mov     w2, #0x0
      +0x54: bl      <mlkem_keccakf1600_extract_bytes>
      +0x58: str     xzr, [x19, #192]
      +0x5c: movi    v0.4s, #0x0
      +0x60: stp     q0, q0, [x19]
      +0x64: stp     q0, q0, [x19, #32]
      +0x68: stp     q0, q0, [x19, #64]
      +0x6c: stp     q0, q0, [x19, #96]
      +0x70: stp     q0, q0, [x19, #128]
      +0x74: stp     q0, q0, [x19, #160]
      +0x78: adrp    x0, <page>
      +0x7c: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x80: ldr     x2, [sp, #232]
      +0x84: ldr     x1, [x0]
      +0x88: subs    x2, x2, x1
      +0x8c: mov     x1, #0x0
      +0x90: b.ne    <mlkem_sha3_256+0xa0>
      +0x94: ldr     x30, [sp, #16]
      +0x98: ldp     x19, x20, [sp], #240
      +0x9c: ret
      +0xa0: bl      <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc
   [layout_range "mlkem_sha3_256"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The input is a list of bytes, and the 32 bytes of the  *)
(* output, as a number, are those of sha3_256 in common/fips202.ml. As for   *)
(* mlkem_poly_compress_d4, the address of the stack guard is read from the   *)
(* GOT, and the stack is the 240 bytes of the function and the 256 used by   *)
(* mlk_keccak_absorb_once below them.                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT =
  `!out m (inp:byte list) guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(out,32); (m,LENGTH inp); (word_sub stackpointer (word 496),496)] /\
        ALLPAIRS nonoverlapping
         [(out,32); (word_sub stackpointer (word 496),496)]
         [(word pc,libmlkem_size); (word(pc + got_stack_chk_guard),8);
          (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + mlkem_sha3_256) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; m; word(LENGTH inp)] s /\
                  read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                    guard /\
                  read (memory :> bytes(m,LENGTH inp)) s =
                  num_of_bytelist inp)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,32)) s =
                  num_of_bytelist(sha3_256 inp))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,32);
                memory :> bytes(word_sub stackpointer (word 496),496)])`;;

let MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  assume_spec MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT;;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. As for mlkem_poly_compress_d4, it  *)
(* is stated directly, since the events depend on the address of the stack   *)
(* guard, read from the GOT.                                                 *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let SHA3_256_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `m:int64`; `out:int64`; `inlen:num`;
                          `guard:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC name safety_th]);;

let MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT =
  `exists f_events.
     forall e out m inlen guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [out,32; m,inlen; word_sub stackpointer (word 496),496] /\
       ALLPAIRS nonoverlapping
        [out,32; word_sub stackpointer (word 496),496]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + mlkem_sha3_256) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out; m; word inlen] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m out inlen guard pc
                           (word_sub stackpointer (word 496)) returnaddress /\
                    memaccess_inbounds e2
                     [m,inlen; out,32; word_sub stackpointer (word 496),496;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out,32; word_sub stackpointer (word 496),496]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out,32);
               memory :> bytes(word_sub stackpointer (word 496),496)])`;;

let MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  assume_spec MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT;;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using those  *)
(* of mlk_keccak_absorb_once, mlkem_keccakf1600_permute and                  *)
(* mlkem_keccakf1600_extract_bytes, for the hash check of the decapsulation  *)
(* key, whose result the decapsulation branches on.                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT =
  `exists f_events.
     forall e out m (inp:byte list) inlen guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + libmlkem_size <= 2 EXP 64 /\
       aligned 16 stackpointer /\ LENGTH inp = inlen /\
       PAIRWISE nonoverlapping
        [out,32; m,inlen; word_sub stackpointer (word 496),496] /\
       ALLPAIRS nonoverlapping
        [out,32; word_sub stackpointer (word 496),496]
        [word pc,libmlkem_size; word(pc + got_stack_chk_guard),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + mlkem_sha3_256) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out; m; word inlen] s /\
                 read (memory :> bytes64(word(pc + got_stack_chk_guard))) s =
                   guard /\
                 read (memory :> bytes(m,inlen)) s = num_of_bytelist inp /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 read (memory :> bytes(out,32)) s =
                 num_of_bytelist(sha3_256 inp) /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m out inlen guard pc
                           (word_sub stackpointer (word 496)) returnaddress /\
                    memaccess_inbounds e2
                     [m,inlen; out,32; word_sub stackpointer (word 496),496;
                      word(pc + got_stack_chk_guard),8; guard,8;
                      word(pc + rodata_mlk_KeccakF_RoundConstants),192]
                     [out,32; word_sub stackpointer (word 496),496]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out,32);
               memory :> bytes(word_sub stackpointer (word 496),496)])`;;

let MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_FULL =
  assume_spec MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT;;
