(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* SHAKE256 with an output of any length. This is the code for               *)
(* mlkem_shake256 from mlkem-native's portable C implementation compiled by  *)
(* gcc 12 with -O2 (see mlkem_native/README.md), which absorbs the input     *)
(* into a state on the stack with mlk_keccak_absorb_once, and then for each  *)
(* block of the output permutes the state and extracts up to 136 bytes of    *)
(* it, the rate of SHAKE256, before zeroing the state. It is verified in     *)
(* the whole image (see mlkem_native_libmlkem_gcc12_O2.ml), where it is at   *)
(* address 0x2570, using the theorems for mlk_keccak_absorb_once at 0x23b0,  *)
(* mlkem_keccakf1600_permute at 0x2dd0 and mlkem_keccakf1600_extract_bytes   *)
(* at 0x2c60 in the image. The result is shake256 of common/fips202.ml.      *)
(* ========================================================================= *)

needs "arm/proofs/mlkem_native_keccak_absorb_once_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_keccakf1600_extract_bytes_gcc12_O2.ml";;
needs "arm/proofs/mlkem_native_libmlkem_gcc12_O2.ml";;

(*** The code in the image:

    2570: stp     x19, x20, [sp, #-304]!
    2574: mov     x19, x1
    2578: adrp    x4, 1f000 <mlk_zetas+0x18c80>
    257c: ldr     x4, [x4, #4088]
    2580: stp     x21, x22, [sp, #16]
    2584: add     x21, sp, #0x4f
    2588: str     x30, [sp, #40]
    258c: and     x21, x21, #0xffffffffffffffe0
    2590: mov     x22, x0
    2594: mov     x0, x21
    2598: ldr     x1, [x4]
    259c: str     x1, [sp, #296]
    25a0: mov     x1, #0x0
    25a4: mov     w4, #0x1f
    25a8: mov     w1, #0x88
    25ac: bl      23b0 <mlk_keccak_absorb_once>
    25b0: cbz     x19, 25f4 <mlkem_shake256+0x84>
    25b4: str     x23, [sp, #32]
    25b8: mov     x23, #0x88
    25bc: nop
    25c0: mov     x0, x21
    25c4: bl      2dd0 <mlkem_keccakf1600_permute>
    25c8: cmp     x19, #0x88
    25cc: mov     x1, x22
    25d0: csel    x20, x19, x23, ls
    25d4: mov     x0, x21
    25d8: mov     w3, w20
    25dc: mov     w2, #0x0
    25e0: bl      2c60 <mlkem_keccakf1600_extract_bytes>
    25e4: add     x22, x22, x20
    25e8: subs    x19, x19, x20
    25ec: b.ne    25c0 <mlkem_shake256+0x50>
    25f0: ldr     x23, [sp, #32]
    25f4: movi    v0.4s, #0x0
    25f8: stp     q0, q0, [x21]
    25fc: stp     q0, q0, [x21, #32]
    2600: stp     q0, q0, [x21, #64]
    2604: stp     q0, q0, [x21, #96]
    2608: stp     q0, q0, [x21, #128]
    260c: stp     q0, q0, [x21, #160]
    2610: stp     q0, q0, [x21, #192]
    2614: adrp    x0, 1f000 <mlk_zetas+0x18c80>
    2618: ldr     x0, [x0, #4088]
    261c: ldr     x2, [sp, #296]
    2620: ldr     x1, [x0]
    2624: subs    x2, x2, x1
    2628: mov     x1, #0x0
    262c: b.ne    2640 <mlkem_shake256+0xd0>
    2630: ldp     x21, x22, [sp, #16]
    2634: ldr     x30, [sp, #40]
    2638: ldp     x19, x20, [sp], #304
    263c: ret
    2640: str     x23, [sp, #32]
    2644: bl      830 <__stack_chk_fail@plt>
 ***)

let MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC =
  ARM_MK_EXEC_RANGES_RULE mlkem_native_libmlkem_gcc12_O2_mc [0x2570,0x2648];;

(* ------------------------------------------------------------------------- *)
(* The state is aligned to 32 bytes within the stack frame, so its address   *)
(* depends on whether the stack pointer is a multiple of 32 or just of 16.   *)
(* ------------------------------------------------------------------------- *)

let ALIGNED_16_32_WORD_AND = prove
 (`(!x:int64. aligned 16 x <=> word_and x (word 15) = word 0) /\
   (!x:int64. aligned 32 x <=> word_and x (word 31) = word 0)`,
  CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[aligned; DIMINDEX_64] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV DIVIDES_CONV) THEN REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`x:int64`; `4`] (CONJUNCT1 WORD_AND_MASK_WORD));
    MP_TAC(ISPECL [`x:int64`; `5`] (CONJUNCT1 WORD_AND_MASK_WORD))] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIVIDES_MOD; GSYM VAL_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `x MOD 16 < 16`; ARITH_RULE `x MOD 32 < 32`;
           ARITH_RULE `x < 16 ==> x < 2 EXP 64`;
           ARITH_RULE `x < 32 ==> x < 2 EXP 64`]);;

let SHAKE256_STATE_ADDRESS = prove
 (`!sp:int64.
        aligned 16 sp
        ==> word_and (word_add sp (word 335)) (word 18446744073709551584) =
            word_add sp (word(if aligned 32 sp then 320 else 304))`,
  REWRITE_TAC[ALIGNED_16_32_WORD_AND] THEN GEN_TAC THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN
  W(fun (_,w) -> ACCEPT_TAC(BITBLAST_RULE w)));;

let SHAKE256_STATE_TAC =
  SUBGOAL_THEN
   `word_and (word_add stackpointer (word 335))
             (word 18446744073709551584):int64 =
    word_add stackpointer (word(if aligned 32 stackpointer then 320 else 304))`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC SHAKE256_STATE_ADDRESS THEN ASM_REWRITE_TAC[]; ALL_TAC];;

let SHAKE256_ST = `word_add (stackpointer:int64)
                    (word(if aligned 32 stackpointer then 320 else 304))`;;

(*** The setup for both proofs, with the bounds on the offset of the state ***)

let SHAKE256_SETUP_TAC =
  SUBGOAL_THEN `aligned 16 (stackpointer:int64)` ASSUME_TAC THENL
   [UNDISCH_TAC `aligned 16 (word_add stackpointer (word 560):int64)` THEN
    CONV_TAC(LAND_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `304 <= (if aligned 32 (stackpointer:int64) then 320 else 304) /\
    (if aligned 32 (stackpointer:int64) then 320 else 304) <= 320`
  STRIP_ASSUME_TAC THENL [COND_CASES_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SPECL [`pc:num`; `0x1fff8`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SPECL [`pc:num`; `0x1fff8`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_PRESERVED_TAC "x20_init" `X20` THEN
  ENSURES_PRESERVED_TAC "x21_init" `X21` THEN
  ENSURES_PRESERVED_TAC "x22_init" `X22` THEN
  ENSURES_PRESERVED_TAC "x23_init" `X23`;;

(*** The bound on outlen from the nonoverlapping, and its 64-bit word ***)

let SHAKE256_BOUND_TAC =
  SUBGOAL_THEN `560 + outlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(stackpointer:int64)`; `val(out:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word outlen:int64) = outlen` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC];;

(*** The test of outlen = 0 at the start, when it is known to be false ***)

let SHAKE256_NONZERO_TAC =
  let t1 = `val(word outlen:int64) = outlen` and t2 = `~(outlen = 0)` in
  RULE_ASSUM_TAC(fun th ->
    if concl th = t1 || concl th = t2 then th
    else REWRITE_RULE[ASSUME t1; ASSUME t2] th);;

(*** The number of bytes extracted in each iteration, MIN x 136 ***)

let SHAKE256_CSEL_LEMMA = prove
 (`!x. x < 2 EXP 64
       ==> (if ~(136 <= val (word x:int64) /\
                 ~(val (word_sub (word x) (word 136):int64) = 0))
            then word x else word 136):int64 = word(MIN x 136)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN
  SUBGOAL_THEN `val(word x:int64) = x /\ val(word 136:int64) = 136`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `x < 2 EXP 64` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ARITH_TAC;
    COND_CASES_TAC THEN AP_TERM_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC]);;

(*** Iteration i of the loop, with 136 * i bytes done ***)

let SHAKE256_ITERATION_TAC tac =
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN tac THEN
  SUBGOAL_THEN `136 * i < outlen` ASSUME_TAC THENL
   [UNDISCH_TAC `i < (outlen + 135) DIV 136` THEN
    REWRITE_TAC[ARITH_RULE `i < q <=> i + 1 <= q`] THEN
    SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `MIN outlen (136 * i) = 136 * i` SUBST1_TAC THENL
   [UNDISCH_TAC `136 * i < outlen` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `0 < MIN (outlen - 136 * i) 136 /\ MIN (outlen - 136 * i) 136 <= 136 /\
    0 + MIN (outlen - 136 * i) 136 <= 200 /\
    136 * i + MIN (outlen - 136 * i) 136 <= outlen /\
    MIN outlen (136 * (i + 1)) = 136 * i + MIN (outlen - 136 * i) 136 /\
    (outlen - 136 * i - MIN (outlen - 136 * i) 136 = 0 <=>
     ~(i + 1 < (outlen + 135) DIV 136))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `i + 1 < q <=> i + 2 <= q`] THEN
    SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN
    UNDISCH_TAC `136 * i < outlen` THEN ARITH_TAC;
    ALL_TAC];;

(*** The block length after the csel, and the counter after the subs ***)

let SHAKE256_LENGTH_TAC =
  MP_TAC(SPEC `outlen - 136 * i` SHAKE256_CSEL_LEMMA) THEN
  ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  ARGS_32_TAC [`MIN (outlen - 136 * i) 136`];;

let SHAKE256_COUNTER_TAC =
  SUBGOAL_THEN
   `word_sub (word (outlen - 136 * i))
             (word(MIN (outlen - 136 * i) 136)):int64 =
    word(outlen - 136 * i - MIN (outlen - 136 * i) 136)` SUBST_ALL_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `val(word(outlen - 136 * i - MIN (outlen - 136 * i) 136):int64) =
    outlen - 136 * i - MIN (outlen - 136 * i) 136`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ASSUME
   `outlen - 136 * i - MIN (outlen - 136 * i) 136 = 0 <=>
    ~(i + 1 < (outlen + 135) DIV 136)`]);;

(*** The done count at the end of the loop ***)

let SHAKE256_EXIT_TAC =
  SUBGOAL_THEN `MIN outlen (136 * (outlen + 135) DIV 136) = outlen`
   SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `MIN a b = a <=> a <= b`] THEN
    MP_TAC(SPECL [`outlen + 135`; `136`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUB_REFL];;

(* ------------------------------------------------------------------------- *)
(* Correctness proof. The input is a list of bytes, and the outlen bytes of  *)
(* the output, as a number, are the first outlen bytes of shake256 in        *)
(* common/fips202.ml. Each iteration of the loop extracts                    *)
(* MIN (outlen - 136 * i) 136 bytes. As for mlkem_poly_compress_d4, the      *)
(* address of the stack guard is read from the GOT, and the stack is the 304 *)
(* bytes of the function and the 256 used by mlk_keccak_absorb_once below    *)
(* them.                                                                     *)
(* ------------------------------------------------------------------------- *)

let MLKEM_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (`!out outlen m (inp:byte list) guard pc stackpointer returnaddress.
        aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
        aligned 16 stackpointer /\
        PAIRWISE nonoverlapping
         [(out,outlen); (m,LENGTH inp);
          (word_sub stackpointer (word 560),560)] /\
        ALLPAIRS nonoverlapping
         [(out,outlen); (word_sub stackpointer (word 560),560)]
         [(word pc,0x6480); (word(pc + 0x1fff8),8); (guard,8)]
        ==> ensures arm
             (\s. aligned_bytes_loaded s (word pc)
                    mlkem_native_libmlkem_gcc12_O2_mc /\
                  read PC s = word (pc + 0x2570) /\
                  read SP s = stackpointer /\
                  read X30 s = returnaddress /\
                  C_ARGUMENTS [out; word outlen; m; word(LENGTH inp)] s /\
                  read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                  read (memory :> bytes(m,LENGTH inp)) s =
                  num_of_bytelist inp)
             (\s. read PC s = returnaddress /\
                  read (memory :> bytes(out,outlen)) s =
                  num_of_bytelist(list_of_seq (shake256 inp) outlen))
             (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
              MAYCHANGE
               [memory :> bytes(out,outlen);
                memory :> bytes(word_sub stackpointer (word 560),560)])`,
  MAP_EVERY X_GEN_TAC
   [`out:int64`; `outlen:num`; `m:int64`; `inp:byte list`; `guard:int64`;
    `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 560 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SHAKE256_SETUP_TAC THEN

  (*** The absorption, up to the test of outlen ***)

  ENSURES_SEQUENCE_TAC `pc + 0x25b0`
   `\s. read X19 s = word outlen /\
        read X21 s =
        word_add stackpointer
         (word(if aligned 32 stackpointer then 320 else 304)) /\
        read X22 s = out /\ read X23 s = x23_init /\
        read SP s = word_add stackpointer (word 256) /\
        read (memory :> bytes64 (word_add stackpointer (word 256))) s =
        x19_init /\
        read (memory :> bytes64 (word_add stackpointer (word 264))) s =
        x20_init /\
        read (memory :> bytes64 (word_add stackpointer (word 272))) s =
        x21_init /\
        read (memory :> bytes64 (word_add stackpointer (word 280))) s =
        x22_init /\
        read (memory :> bytes64 (word_add stackpointer (word 296))) s =
        returnaddress /\
        read (memory :> bytes64 (word_add stackpointer (word 552))) s =
        canary /\
        read (memory :> bytes64 (word_add (word pc) (word 131064))) s =
        guard /\
        read (memory :> bytes64 guard) s = canary /\
        read (memory :> bytes(word_add stackpointer
                (word(if aligned 32 stackpointer then 320 else 304)),200)) s =
        val(word_xor
         (keccak_absorb 136
           (num_of_bytelist inp +
            2 EXP (8 * LENGTH inp) *
            num_of_bytelist(keccak_pad 136 31 (LENGTH inp)))
           (LENGTH(inp:byte list) DIV 136))
         (word((num_of_bytelist inp +
                2 EXP (8 * LENGTH inp) *
                num_of_bytelist(keccak_pad 136 31 (LENGTH inp))) DIV
               2 EXP (8 * 136 * LENGTH inp DIV 136) MOD
               2 EXP (8 * 136))):1600 word)` THEN
  CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (1--3) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (4--8) THEN
    SHAKE256_STATE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (9--16) THEN
    ARM_SUBROUTINE_SIM_TAC
     (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC,
      0x0,mlkem_native_libmlkem_gcc12_O2_mc,
      MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT)
     [`read X0 s`; `136`; `read X2 s`; `LENGTH(inp:byte list)`; `31`;
      `num_of_bytelist(inp:byte list)`; `pc:num`; `read SP s`; `read X30 s`]
     17 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN

  (*** The case outlen = 0, with no output ***)

  ASM_CASES_TAC `outlen = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (1--10) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (11--20) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[list_of_seq; num_of_bytelist; READ_MEMORY_BYTES_TRIVIAL];
    ALL_TAC] THEN

  (*** Otherwise the loop, with MIN outlen (136 * i) bytes done ***)

  SHAKE256_BOUND_TAC THEN
  ENSURES_WHILE_UP2_TAC `(outlen + 135) DIV 136` `pc + 0x25c0` `pc + 0x25f0`
   `\i s. read X19 s = word(outlen - MIN outlen (136 * i)) /\
          read X21 s =
          word_add stackpointer
           (word(if aligned 32 stackpointer then 320 else 304)) /\
          read X22 s = word_add out (word(MIN outlen (136 * i))) /\
          read X23 s = word 136 /\
          read SP s = word_add stackpointer (word 256) /\
          read (memory :> bytes64 (word_add stackpointer (word 256))) s =
          x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 264))) s =
          x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 272))) s =
          x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 280))) s =
          x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 288))) s =
          x23_init /\
          read (memory :> bytes64 (word_add stackpointer (word 296))) s =
          returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 552))) s =
          canary /\
          read (memory :> bytes64 (word_add (word pc) (word 131064))) s =
          guard /\
          read (memory :> bytes64 guard) s = canary /\
          read (memory :> bytes(out,MIN outlen (136 * i))) s =
          num_of_bytelist
           (list_of_seq (shake256 inp) (MIN outlen (136 * i))) /\
          read (memory :> bytes(word_add stackpointer
                (word(if aligned 32 stackpointer then 320 else 304)),200)) s =
          val(keccak_squeeze i
           (word_xor
             (keccak_absorb 136
               (num_of_bytelist inp +
                2 EXP (8 * LENGTH inp) *
                num_of_bytelist(keccak_pad 136 31 (LENGTH inp)))
               (LENGTH(inp:byte list) DIV 136))
             (word((num_of_bytelist inp +
                    2 EXP (8 * LENGTH inp) *
                    num_of_bytelist(keccak_pad 136 31 (LENGTH inp))) DIV
                   2 EXP (8 * 136 * LENGTH inp DIV 136) MOD
                   2 EXP (8 * 136))):1600 word))` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[DIV_EQ_0; ARITH_EQ] THEN UNDISCH_TAC `~(outlen = 0)` THEN
    ARITH_TAC;

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (1--1) THEN
    SHAKE256_NONZERO_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (2--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `MIN n 0 = 0`; SUB_0; WORD_ADD_0;
                READ_MEMORY_BYTES_TRIVIAL; list_of_seq; num_of_bytelist;
                keccak_squeeze];

    (*** The loop body: permute and extract the next block ***)

    SHAKE256_ITERATION_TAC ALL_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (1--2) THEN
    KECCAK_STATE_AT_TAC SHAKE256_ST THEN
    KECCAK_STATE_THEN SHAKE256_ST (fun v ->
      ARM_SUBROUTINE_SIM_TAC
       (mlkem_native_libmlkem_gcc12_O2_mc,
        MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC,
        0x0,mlkem_native_libmlkem_gcc12_O2_mc,
      MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_F1600)
       [`read X0 s`; v; `pc:num`; `read SP s`; `read X30 s`] 3) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (4--10) THEN
    SHAKE256_LENGTH_TAC THEN
    KECCAK_STATE_AT_TAC SHAKE256_ST THEN
    KECCAK_STATE_THEN SHAKE256_ST (fun v ->
      ARM_SUBROUTINE_SIM_TAC
       (mlkem_native_libmlkem_gcc12_O2_mc,
        MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC,
        0x0,mlkem_native_libmlkem_gcc12_O2_mc,
      MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_CORRECT)
       [`read X0 s`; `read X1 s`; `0`; `MIN (outlen - 136 * i) 136`; v;
        `pc:num`; `read X30 s`] 11) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (12--14) THEN
    SHAKE256_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [COND_CASES_TAC THEN REWRITE_TAC[];
      AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD];
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[shake256] THEN CONV_TAC SYM_CONV THEN
      REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1] THEN
      REWRITE_TAC[GSYM(CONJUNCT2 keccak_squeeze); ADD1] THEN
      MATCH_MP_TAC KECCAK_SPONGE_BLOCK THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      REWRITE_TAC[GSYM ADD1; keccak_squeeze]];

    (*** Zeroing the state, the check of the stack guard and the return ***)

    SHAKE256_EXIT_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (1--10) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (11--20) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof. As for mlkem_poly_compress_d4, it  *)
(* is stated directly, since the events depend on the address of the stack   *)
(* guard, read from the GOT.                                                 *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let SHAKE256_SAFE_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    ARM_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mlkem_native_libmlkem_gcc12_O2_mc,MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC,
       0x0,mlkem_native_libmlkem_gcc12_O2_mc,safety_th)
      ilist n THENL
     [ABSORB_EXISTS_E2_TAC (ref
       [`pc:num`; `m:int64`; `out:int64`; `outlen:num`; `inlen:num`;
        `guard:int64`; `stackpointer:int64`; `returnaddress:int64`;
        `i:num`]);
      LABEL_TAC name safety_th]);;

let MLKEM_NATIVE_SHAKE256_GCC12_O2_IMAGE_SUBROUTINE_SAFE =
  time prove
 (`exists f_events.
     forall e out outlen m inlen guard pc stackpointer returnaddress.
       aligned 4096 (word pc:int64) /\ pc + 0x6480 <= 2 EXP 64 /\
       aligned 16 stackpointer /\
       PAIRWISE nonoverlapping
        [out,outlen; m,inlen; word_sub stackpointer (word 560),560] /\
       ALLPAIRS nonoverlapping
        [out,outlen; word_sub stackpointer (word 560),560]
        [word pc,0x6480; word(pc + 0x1fff8),8; guard,8]
       ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc)
                   mlkem_native_libmlkem_gcc12_O2_mc /\
                 read PC s = word (pc + 0x2570) /\
                 read SP s = stackpointer /\
                 read X30 s = returnaddress /\
                 C_ARGUMENTS [out; word outlen; m; word inlen] s /\
                 read (memory :> bytes64(word(pc + 0x1fff8))) s = guard /\
                 read events s = e)
            (\s. read PC s = returnaddress /\
                 (exists e2.
                    read events s = APPEND e2 e /\
                    e2 = f_events m out outlen inlen guard pc
                           (word_sub stackpointer (word 560)) returnaddress /\
                    memaccess_inbounds e2
                     [m,inlen; out,outlen;
                      word_sub stackpointer (word 560),560;
                      word(pc + 0x1fff8),8; guard,8; word(pc + 0x62b0),192]
                     [out,outlen; word_sub stackpointer (word 560),560]))
            (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,, MAYCHANGE [X18] ,,
             MAYCHANGE
              [memory :> bytes(out,outlen);
               memory :> bytes(word_sub stackpointer (word 560),560)])`,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAK_ABSORB_ONCE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_ABSORB" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_EXTRACT" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(m:int64) (out:int64) (outlen:num) (inlen:num) (guard:int64) (pc:num)
      (stackpointer:int64) (returnaddress:int64).
      APPEND
       (if outlen = 0
        then f_ev_zero m out outlen inlen guard pc stackpointer returnaddress
        else APPEND
              (f_ev_epil m out outlen inlen guard pc stackpointer
                         returnaddress)
              (APPEND
                (ENUMERATEL ((outlen + 135) DIV 136)
                  (\i. f_ev_loop m out outlen inlen guard pc stackpointer
                                 returnaddress i))
                (f_ev_prol m out outlen inlen guard pc stackpointer
                           returnaddress)))
       (f_ev_absorb m out outlen inlen guard pc stackpointer returnaddress)
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SHAKE256_SETUP_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + 0x25b0`
   `\s. read X19 s = word outlen /\
        read X21 s =
        word_add stackpointer
         (word(if aligned 32 stackpointer then 320 else 304)) /\
        read X22 s = out /\ read X23 s = x23_init /\
        read SP s = word_add stackpointer (word 256) /\
        read (memory :> bytes64 (word_add stackpointer (word 256))) s =
        x19_init /\
        read (memory :> bytes64 (word_add stackpointer (word 264))) s =
        x20_init /\
        read (memory :> bytes64 (word_add stackpointer (word 272))) s =
        x21_init /\
        read (memory :> bytes64 (word_add stackpointer (word 280))) s =
        x22_init /\
        read (memory :> bytes64 (word_add stackpointer (word 296))) s =
        returnaddress /\
        read (memory :> bytes64 (word_add stackpointer (word 552))) s =
        canary /\
        read (memory :> bytes64 (word_add (word pc) (word 131064))) s =
        guard /\
        read (memory :> bytes64 guard) s = canary` THEN
  CONJ_TAC THENL
   [REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (1--3) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (4--8) THEN
    SHAKE256_STATE_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (9--16) THEN
    SHAKE256_SAFE_CALL_TAC "H_ABSORB"
     [`e:(uarch_event)list`; `read X0 s`; `136`; `read X2 s`; `inlen:num`;
      `31`; `pc:num`; `read SP s`; `read X30 s`] 17 THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `outlen = 0` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (1--10) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (11--20) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  SHAKE256_BOUND_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `(outlen + 135) DIV 136`
    `pc + 0x25c0` `pc + 0x25f0`
   `\i s. read X19 s = word(outlen - MIN outlen (136 * i)) /\
          read X21 s =
          word_add stackpointer
           (word(if aligned 32 stackpointer then 320 else 304)) /\
          read X22 s = word_add out (word(MIN outlen (136 * i))) /\
          read X23 s = word 136 /\
          read SP s = word_add stackpointer (word 256) /\
          read (memory :> bytes64 (word_add stackpointer (word 256))) s =
          x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 264))) s =
          x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 272))) s =
          x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 280))) s =
          x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 288))) s =
          x23_init /\
          read (memory :> bytes64 (word_add stackpointer (word 296))) s =
          returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 552))) s =
          canary /\
          read (memory :> bytes64 (word_add (word pc) (word 131064))) s =
          guard /\
          read (memory :> bytes64 guard) s = canary` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[DIV_EQ_0; ARITH_EQ] THEN UNDISCH_TAC `~(outlen = 0)` THEN
    ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (1--1) THEN
    SHAKE256_NONZERO_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (2--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `MIN n 0 = 0`; SUB_0; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    SHAKE256_ITERATION_TAC (REWRITE_TAC[]) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (1--2) THEN
    SHAKE256_SAFE_CALL_TAC "H_PERMUTE"
     [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
      `read X30 s`] 3 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (4--10) THEN
    SHAKE256_LENGTH_TAC THEN
    SHAKE256_SAFE_CALL_TAC "H_EXTRACT"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `0`;
      `MIN (outlen - 136 * i) 136`; `pc:num`; `read X30 s`] 11 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (12--14) THEN
    SHAKE256_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    SHAKE256_EXIT_TAC THEN
    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (1--10) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE256_GCC12_O2_EXEC (11--20) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;
