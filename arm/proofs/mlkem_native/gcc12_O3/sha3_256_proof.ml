(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHA3-256. This is the code for mlkem_sha3_256 from mlkem-native's         *)
(* portable C implementation compiled by gcc 12 with -O3 (see                *)
(* mlkem_native/README.md), which absorbs the input into a state on the      *)
(* stack with mlk_keccak_absorb_once, permutes it and extracts the 32 bytes  *)
(* of the hash, and then zeroes the state. It is verified in the whole image *)
(* (see libmlkem.ml), using the theorems for                                 *)
(* mlk_keccak_absorb_once, mlkem_keccakf1600_permute and                     *)
(* mlkem_keccakf1600_extract_bytes in the image. The result is sha3_256 of   *)
(* common/fips202.ml.                                                        *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native/gcc12_O3/keccak_absorb_once_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/keccakf1600_extract_bytes_proof.ml";;
needs "arm/proofs/mlkem_native/gcc12_O3/libmlkem.ml";;

(*** The code in the image:

    mlkem_sha3_256:
       +0x0: stp     x19, x20, [sp, #-240]!
       +0x4: mov     w3, #0x6
       +0x8: mov     x20, x0
       +0xc: adrp    x4, <page>
      +0x10: ldr     x4, [x4, #4088]  // got_stack_chk_guard
      +0x14: str     x30, [sp, #16]
      +0x18: add     x19, sp, #0x20
      +0x1c: ldr     x0, [x4]
      +0x20: str     x0, [sp, #232]
      +0x24: mov     x0, #0x0
      +0x28: mov     x0, x19
      +0x2c: bl      <mlk_keccak_absorb_once>
      +0x30: mov     x0, x19
      +0x34: bl      <mlkem_keccakf1600_permute>
      +0x38: mov     x1, x20
      +0x3c: mov     x0, x19
      +0x40: mov     w3, #0x20
      +0x44: mov     w2, #0x0
      +0x48: bl      <mlkem_keccakf1600_extract_bytes>
      +0x4c: str     xzr, [x19, #192]
      +0x50: movi    v0.4s, #0x0
      +0x54: stp     q0, q0, [x19]
      +0x58: stp     q0, q0, [x19, #32]
      +0x5c: stp     q0, q0, [x19, #64]
      +0x60: stp     q0, q0, [x19, #96]
      +0x64: stp     q0, q0, [x19, #128]
      +0x68: stp     q0, q0, [x19, #160]
      +0x6c: adrp    x0, <page>
      +0x70: ldr     x0, [x0, #4088]  // got_stack_chk_guard
      +0x74: ldr     x2, [sp, #232]
      +0x78: ldr     x1, [x0]
      +0x7c: subs    x2, x2, x1
      +0x80: mov     x1, #0x0
      +0x84: b.ne    <mlkem_sha3_256+0x94>
      +0x88: ldr     x30, [sp, #16]
      +0x8c: ldp     x19, x20, [sp], #240
      +0x90: ret
      +0x94: bl      <__stack_chk_fail@plt>
      +0x98: nop
      +0x9c: nop
 ***)

let MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O3_mc
   [layout_range "mlkem_sha3_256"];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The input is a list of bytes, and the 32 bytes of the  *)
(* output, as a number, are those of sha3_256 in common/fips202.ml. As for   *)
(* mlkem_poly_compress_d4, the address of the stack guard is read from the   *)
(* GOT, and the stack is the 240 bytes of the function and the 256 used by   *)
(* mlk_keccak_absorb_once below them.                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHA3_256_GCC12_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (`!out m (inp:byte list) guard pc stackpointer returnaddress.
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
                    mlkem_native_libmlkem_gcc12_O3_mc /\
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
                memory :> bytes(word_sub stackpointer (word 496),496)])`,
  MAP_EVERY X_GEN_TAC
   [`out:int64`; `m:int64`; `inp:byte list`; `guard:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 496 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Saving the registers and the stack guard, and the absorption ***)

  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC (1--4) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC (5--12) THEN
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O3_mc,MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O3_mc,
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT)
   [`read X0 s`; `read X1 s`; `LENGTH(inp:byte list)`; `6`;
    `num_of_bytelist(inp:byte list)`; `pc:num`; `read SP s`; `read X30 s`]
   13 THEN

  (*** The permutation and the extraction of the hash ***)

  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC (14--15) THEN
  KECCAK_STATE_THEN `word_add (stackpointer:int64) (word 288)` (fun v ->
    ARM_SUBROUTINE_SIM_TAC
     (mlkem_native_libmlkem_gcc12_O3_mc,MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC,
      0x0,mlkem_native_libmlkem_gcc12_O3_mc,
      MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_CORRECT_F1600)
     [`read X0 s`; v; `pc:num`; `read SP s`; `read X30 s`] 16) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC (17--21) THEN
  KECCAK_STATE_THEN `word_add (stackpointer:int64) (word 288)` (fun v ->
    ARM_SUBROUTINE_SIM_TAC
     (mlkem_native_libmlkem_gcc12_O3_mc,MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC,
      0x0,mlkem_native_libmlkem_gcc12_O3_mc,
      MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_IMAGE_SUBROUTINE_CORRECT)
     [`read X0 s`; `read X1 s`; `0`; `32`; v; `pc:num`; `read X30 s`] 22) THEN

  (*** Zeroing the state, the check of the stack guard and the return ***)

  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC (23--31) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC (32--40) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN

  (*** The first 32 bytes of the state after absorbing, as in sha3_256 ***)

  REWRITE_TAC[sha3_256] THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
  MATCH_MP_TAC KECCAK_SPONGE_BYTES THEN
  REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

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
      (mlkem_native_libmlkem_gcc12_O3_mc,MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O3_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `m:int64`; `out:int64`; `inlen:num`;
                          `guard:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC name safety_th]);;

let MLKEM_NATIVE_SHA3_256_GCC12_O3_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
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
                   mlkem_native_libmlkem_gcc12_O3_mc /\
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
               memory :> bytes(word_sub stackpointer (word 496),496)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_SAFE
    "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_SAFE
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_IMAGE_SUBROUTINE_SAFE
    "H_EXTRACT" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC (1--4) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC (5--12) THEN
  SHA3_256_SAFE_CALL_TAC "H_ABSORB"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `inlen:num`;
    `6`; `pc:num`; `read SP s`; `read X30 s`] 13 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC (14--15) THEN
  SHA3_256_SAFE_CALL_TAC "H_PERMUTE"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
    `read X30 s`] 16 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC (17--21) THEN
  SHA3_256_SAFE_CALL_TAC "H_EXTRACT"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `0`; `32`;
    `pc:num`; `read X30 s`] 22 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC (23--31) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC (32--40) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

(* ------------------------------------------------------------------------- *)
(* Combined correctness, constant-time and memory safety proof, using those  *)
(* of mlk_keccak_absorb_once, mlkem_keccakf1600_permute and                  *)
(* mlkem_keccakf1600_extract_bytes, for the hash check of the decapsulation  *)
(* key, whose result the decapsulation branches on.                          *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHA3_256_GCC12_O3_IMAGE_SUBROUTINE_FULL =
  prove
 (`exists f_events.
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
                   mlkem_native_libmlkem_gcc12_O3_mc /\
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
               memory :> bytes(word_sub stackpointer (word 496),496)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O3_IMAGE_SUBROUTINE_FULL
    "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O3_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O3_IMAGE_SUBROUTINE_FULL
    "H_EXTRACT" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`;
                                     `got_stack_chk_guard:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC (1--4) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC (5--12) THEN
  SHA3_256_SAFE_CALL_TAC "H_ABSORB"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `inlen:num`;
    `6`; `num_of_bytelist(inp:byte list)`; `pc:num`; `read SP s`;
    `read X30 s`] 13 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC (14--15) THEN
  KECCAK_STATE_THEN `word_add (stackpointer:int64) (word 288)` (fun v ->
    SHA3_256_SAFE_CALL_TAC "H_PERMUTE"
     [`e:(uarch_event)list`; `read X0 s`; v; `pc:num`; `read SP s`;
      `read X30 s`] 16) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC (17--21) THEN
  KECCAK_STATE_THEN `word_add (stackpointer:int64) (word 288)` (fun v ->
    SHA3_256_SAFE_CALL_TAC "H_EXTRACT"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `0`; `32`; v;
      `pc:num`; `read X30 s`] 22) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC (23--31) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O3_EXEC (32--40) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [UNDISCH_THEN `LENGTH(inp:byte list) = inlen` (SUBST_ALL_TAC o SYM) THEN
    REWRITE_TAC[sha3_256] THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
    MATCH_MP_TAC KECCAK_SPONGE_BYTES THEN
    REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCHARGE_SAFETY_PROPERTY_TAC]);;
