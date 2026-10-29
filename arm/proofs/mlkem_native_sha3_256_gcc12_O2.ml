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
(* (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at address 0x2650,   *)
(* using the theorems for mlk_keccak_absorb_once at 0x23b0,                  *)
(* mlkem_keccakf1600_permute at 0x2dd0 and mlkem_keccakf1600_extract_bytes   *)
(* at 0x2c60 in the image. The result is sha3_256 of common/fips202.ml.      *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_keccak_absorb_once_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_keccakf1600_extract_bytes_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    2650: stp     x19, x20, [sp, #-240]!
    2654: mov     x3, x2
    2658: mov     x2, x1
    265c: adrp    x5, 1f000 <mlk_zetas+0x18c80>
    2660: ldr     x5, [x5, #4088]
    2664: str     x30, [sp, #16]
    2668: add     x19, sp, #0x20
    266c: mov     w4, #0x6
    2670: mov     x20, x0
    2674: mov     w1, #0x88
    2678: ldr     x0, [x5]
    267c: str     x0, [sp, #232]
    2680: mov     x0, #0x0
    2684: mov     x0, x19
    2688: bl      23b0 <mlk_keccak_absorb_once>
    268c: mov     x0, x19
    2690: bl      2dd0 <mlkem_keccakf1600_permute>
    2694: mov     x1, x20
    2698: mov     x0, x19
    269c: mov     w3, #0x20
    26a0: mov     w2, #0x0
    26a4: bl      2c60 <mlkem_keccakf1600_extract_bytes>
    26a8: str     xzr, [x19, #192]
    26ac: movi    v0.4s, #0x0
    26b0: stp     q0, q0, [x19]
    26b4: stp     q0, q0, [x19, #32]
    26b8: stp     q0, q0, [x19, #64]
    26bc: stp     q0, q0, [x19, #96]
    26c0: stp     q0, q0, [x19, #128]
    26c4: stp     q0, q0, [x19, #160]
    26c8: adrp    x0, 1f000 <mlk_zetas+0x18c80>
    26cc: ldr     x0, [x0, #4088]
    26d0: ldr     x2, [sp, #232]
    26d4: ldr     x1, [x0]
    26d8: subs    x2, x2, x1
    26dc: mov     x1, #0x0
    26e0: b.ne    26f0 <mlkem_sha3_256+0xa0>
    26e4: ldr     x30, [sp, #16]
    26e8: ldp     x19, x20, [sp], #240
    26ec: ret
    26f0: bl      830 <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x2650,0x26f4];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The input is a list of bytes, and the 32 bytes of the  *)
(* output, as a number, are those of sha3_256 in common/fips202.ml. As for   *)
(* mlkem_poly_compress_d4, the address of the stack guard is read from the   *)
(* GOT, and the stack is the 240 bytes of the function and the 256 used by   *)
(* mlk_keccak_absorb_once below them.                                        *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!out m (inp:byte list) guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(out,32); (m,LENGTH inp); (word_sub stackpointer (word 496),496)] /\
        ALLPAIRS nonoverlapping
         [(out,32); (word_sub stackpointer (word 496),496)]
         [(word pc,0x6480); (word(pc + 0x1fff8),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x2650) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; m; word(LENGTH inp)] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
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
  REWRITE_TAC[SPECL [`pc:num`; `0x1fff8`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1fff8`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** Saving the registers and the stack guard, and the absorption ***)

  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC (1--4) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC (5--15) THEN
  ARM_SUBROUTINE_SIM_TAC
   (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC,
    0x0,mlkem_native_libmlkem_gcc12_O2_mc,
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT)
   [`read X0 s`; `136`; `read X2 s`; `LENGTH(inp:byte list)`; `6`;
    `num_of_bytelist(inp:byte list)`; `pc:num`; `read SP s`; `read X30 s`]
   16 THEN

  (*** The permutation and the extraction of the hash ***)

  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC (17--18) THEN
  KECCAK_STATE_THEN `word_add (stackpointer:int64) (word 288)` (fun v ->
    ARM_SUBROUTINE_SIM_TAC
     (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC,
      0x0,mlkem_native_libmlkem_gcc12_O2_mc,
      MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600)
     [`read X0 s`; v; `pc:num`; `read SP s`; `read X30 s`] 19) THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC (20--24) THEN
  KECCAK_STATE_THEN `word_add (stackpointer:int64) (word 288)` (fun v ->
    ARM_SUBROUTINE_SIM_TAC
     (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC,
      0x0,mlkem_native_libmlkem_gcc12_O2_mc,
      MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT)
     [`read X0 s`; `read X1 s`; `0`; `32`; v; `pc:num`; `read X30 s`] 25) THEN

  (*** Zeroing the state, the check of the stack guard and the return ***)

  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC (26--34) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC (35--43) THEN
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
      (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref [`pc:num`; `m:int64`; `out:int64`; `inlen:num`;
                          `guard:int64`; `stackpointer:int64`;
                          `returnaddress:int64`]);
      LABEL_TAC name safety_th]);;

let MLKEM_NATIVE_SHA3_256_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e out m inlen guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [out,32; m,inlen; word_sub stackpointer (word 496),496] /\
       ALLPAIRS nonoverlapping
        [out,32; word_sub stackpointer (word 496),496]
        [word pc,0x6480; word(pc + 0x1fff8),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + 0x2650) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out; m; word inlen] s /\
                 read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m out inlen guard pc
                           (word_sub stackpointer (word 496)) returnaddress /\
                    memaccess_inbounds e2
                     [m,inlen; out,32; word_sub stackpointer (word 496),496;
                      word(pc + 0x1fff8),8; guard,8; word(pc + 0x62b0),192]
                     [out,32; word_sub stackpointer (word 496),496]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out,32);
               memory :> bytes(word_sub stackpointer (word 496),496)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_EXTRACT" THEN
  META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1fff8`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1fff8`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC (1--4) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC (5--15) THEN
  SHA3_256_SAFE_CALL_TAC "H_ABSORB"
   [`e:(uarch_event)list`; `read X0 s`; `136`; `read X2 s`; `inlen:num`;
    `6`; `pc:num`; `read SP s`; `read X30 s`] 16 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC (17--18) THEN
  SHA3_256_SAFE_CALL_TAC "H_PERMUTE"
   [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
    `read X30 s`] 19 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC (20--24) THEN
  SHA3_256_SAFE_CALL_TAC "H_EXTRACT"
   [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `0`; `32`;
    `pc:num`; `read X30 s`] 25 THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC (26--34) THEN
  MLKEM_NATIVE_ADRP_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_SHA3_256_GCC12_O2_EXEC (35--43) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
