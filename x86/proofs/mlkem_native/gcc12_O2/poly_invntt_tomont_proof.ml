(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/gcc12_O2/poly_invntt_tomont_spec.ml";;


let INVNTT_CONSTANTS_LOADED = prove
 (INVNTT_CONSTANTS_LOADED_STMT,
  let dth = find
   (fun th -> name_of(lhs(concl th)) =
              "mlkem_native_poly_invntt_tomont_gcc12_O2_data")
   mlkem_native_poly_invntt_tomont_gcc12_O2_data in
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[MESON[WORD_ADD_0]
   `word c:int64 = word_add (word c) (word 0)`] THEN
  REWRITE_TAC[WORD_ADD; GSYM WORD_ADD_ASSOC; WORD_ADD_0] THEN
  MAP_EVERY (fun k ->
     MP_TAC(SPECL [`word c:int64`;
                   `mlkem_native_poly_invntt_tomont_gcc12_O2_data`;
                   k; `s:x86state`] BYTES_LOADED_BYTES128))
   [`0`; `16`; `32`] THEN
  ASM_REWRITE_TAC[CONV_RULE(RAND_CONV LENGTH_CONV)
               (AP_TERM `LENGTH:byte list->num` dth)] THEN
  REWRITE_TAC[dth; num_of_bytelist] THEN
  CONV_TAC(DEPTH_CONV WORD_RED_CONV THENC NUM_REDUCE_CONV) THEN
  REWRITE_TAC[WORD_ADD_0] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  CONV_TAC WORD_REDUCE_CONV);;

let INVNTT_LANE_FORM = prove
 (INVNTT_LANE_FORM_STMT,
  GEN_TAC THEN
  MP_TAC(ISPECL
   [`word_mul (word_mul (x:int16) (word 1441)) (word 62209):int16`;
    `word 62207:int16`] WORD_JOIN_MULHI_MULLO) THEN
  MP_TAC(ISPECL [`x:int16`; `word 1441:int16`] WORD_JOIN_MULHI_MULLO) THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM MONTRED_X86_SCALAR; montred_x86] THEN
  SIMP_TAC[WORD_ZX_MUL; DIMINDEX_16; DIMINDEX_32; ARITH] THEN
  REWRITE_TAC[WORD_BLAST `word_zx(word_sx (x:int16):int32) = x`] THEN
  CONV_TAC(ONCE_DEPTH_CONV WORD_RED_CONV) THEN
  REWRITE_TAC[WORD_BLAST `word_subword (y:int32) (0,16):int16 = word_zx y`]);;

let INVNTT_BARRETT_GCC12_O2 = prove
 (INVNTT_BARRETT_GCC12_O2_STMT,
  REPEAT GEN_TAC THEN
  SIMP_TAC[WORD_ZX_ADD; WORD_ZX_ZX_GEN; DIMINDEX_16; DIMINDEX_32; DIMINDEX_64;
           ARITH] THEN
  REWRITE_TAC[WORD_ZX_JOIN_48_16; WORD_ADD_SYM]);;

let WORD_ZX_ADD_ZX_ZX_16 = prove
 (WORD_ZX_ADD_ZX_ZX_16_STMT,
  SIMP_TAC[WORD_ZX_ADD; WORD_ZX_ZX; WORD_ZX_TRIVIAL; DIMINDEX_16; DIMINDEX_32;
           ARITH]);;

let WORD_ZX_SUB_ZX_ZX_16 = prove
 (WORD_ZX_SUB_ZX_ZX_16_STMT,
  SIMP_TAC[WORD_ZX_SUB; WORD_ZX_ZX; WORD_ZX_TRIVIAL; DIMINDEX_16; DIMINDEX_32;
           ARITH]);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_BLOCK = prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_BLOCK_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The inner loop, RCX and RDX pointing at the lower and upper ***)
  (*** coefficients and RSI at the end of the upper ones           ***)

  ENSURES_WHILE_UP_TAC `len:num` `pc + poly_invntt_tomont_loop3` `pc + poly_invntt_tomont_loop3_test`
   `\jj s. bytes_loaded s (word pc)
             (mlkem_native_poly_invntt_tomont_gcc12_O2_mc pc consts zetas) /\
           read RCX s = word_add a (word(2 * (start + jj))) /\
           read RDX s = word_add a (word(2 * (start + len + jj))) /\
           read RSI s = word_add a (word(2 * (start + len))) /\
           read RDI s = word(start + len) /\
           read R10 s = word(k - 1) /\
           read R8 s = word_zx(word_sx z:int32) /\
           read RBX s = word(2 * len) /\
           read R12 s = a /\ read R14 s = word_add a (word 2) /\
           read R13 s = word zetas /\
           read R11 s = w11 /\ read R15 s = w15 /\
           read RSP s = word_add sbase (word 12) /\
           read (memory :> bytes32 sbase) s = word start /\
           (!k. k < 128
                ==> read(memory :> bytes16(word_add (word zetas)
                                                    (word(2 * k)))) s =
                    iword(EL k mlk_zetas)) /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    if start <= i /\ i < start + jj \/
                       start + len <= i /\ i < start + len + jj
                    then invntt_block_c z start len m i else m i)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** Setting up the pointers for the inner loop ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--2) THEN
    W32_DECIDE_FLAGS_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (3--15) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `~(a <= i /\ i < a:num)`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN WORD_SMALL_TAC;

    (*** The inner loop body, one butterfly ***)

    X_GEN_TAC `jj:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && free_in `m:num->int16` (concl th)
      then MP_TAC(SPEC `start + jj:num` th) THEN
           MP_TAC(SPEC `start + len + jj:num` th) THEN
           ASSUME_TAC(BETA_RULE(MATCH_MP (SPEC
             `\i. ~(i = start + jj) /\ ~(i = start + len + jj)`
             (MESON[] `!R P Q. (!i:num. P i ==> Q i)
                               ==> (!i. P i /\ R i ==> Q i)`)) th))
      else failwith "") THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LT_REFL; ARITH_RULE
     `jj < len
      ==> ~(start <= start + len + jj /\ start + len + jj < start + jj) /\
          ~(start + len <= start + len + jj /\
            start + len + jj < start + len + jj)`] THEN
    DISCH_TAC THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LT_REFL; ARITH_RULE
     `jj < len
      ==> ~(start <= start + jj /\ start + jj < start + jj) /\
          ~(start + len <= start + jj /\ start + jj < start + len + jj)`] THEN
    DISCH_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--22) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC]) THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i = start + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LE_ADD; ARITH_RULE `start + jj < start + jj + 1`] THEN
      MLKEM_NATIVE_WORD_SIMP_TAC THEN
      REWRITE_TAC[INVNTT_BARRETT_GCC12_O2; WORD_ZX_ADD_ZX_ZX_16] THEN
      REWRITE_TAC[BARRED_GCC12_O2] THEN
      REWRITE_TAC[invntt_block_c; LE_ADD; LT_ADD_LCANCEL] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[ADD_AC; WORD_ADD_SYM];
      ALL_TAC] THEN
    ASM_CASES_TAC `i = start + len + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `start + len + jj < start + len + jj + 1`;
                  ARITH_RULE `start + len <= start + len + jj`] THEN
      MLKEM_NATIVE_WORD_SIMP_TAC THEN
      REWRITE_TAC[MONTRED_X86_FOLD; WORD_ZX_SUB_ZX_ZX_16] THEN
      REWRITE_TAC[invntt_block_c; invntt_fqmul_c] THEN
      SUBGOAL_THEN
       `~(start <= start + len + jj /\ start + len + jj < start + len) /\
        start + len <= start + len + jj /\
        start + len + jj < start + 2 * len`
       (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `jj < len` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `(start + len + jj) - len = start + jj`];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `m:num->int16` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MAP_EVERY UNDISCH_TAC [`~(i = start + jj)`; `~(i = start + len + jj)`] THEN
    ARITH_TAC;

    (*** The inner loop back-edge ***)

    X_GEN_TAC `jj:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The inner loop exit and the end of the block, restoring RSI ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (2--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC]) THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `m:num->int16` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[invntt_block_c] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC]);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_LAYER = prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_LAYER_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) MP_TAC) THEN
  SPEC_TAC(`l:num`,`l:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
  (map INVNTT_LAYER_TAC (1--7)));;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_LAYERS = prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_LAYERS_STMT,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `consts:num`; `zetas:num`; `x:num->int16`; `pc:num`;
    `sbase:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Initialization, including the address of the table ***)

  ENSURES_SEQUENCE_TAC `pc + poly_invntt_tomont_join1` (invntt_layerhead_tm 7) THEN CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--5) THEN
    MP_TAC(CONJUNCT1(SPECL [`pc:num`; `236`; `0`; `zetas:num`]
      RIP_REL_ADDR_FOLD)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (6--6) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[CONJUNCT1 invntt_layers_c] THEN
    REWRITE_TAC[mlk_zetas] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_IWORD_CONV) THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV);
    ALL_TAC] THEN

  (*** The layers, with the loop back to the head between them ***)

  MAP_EVERY (fun l ->
    ENSURES_SEQUENCE_TAC `pc + poly_invntt_tomont_loop2_exit` (invntt_layerend_tm l) THEN
    CONJ_TAC THENL [INVNTT_LAYER_APPLY_TAC l; ALL_TAC] THEN
    if l = 1 then ALL_TAC else
    ENSURES_SEQUENCE_TAC `pc + poly_invntt_tomont_join1` (invntt_layerhead_tm (l - 1)) THEN
    CONJ_TAC THENL [INVNTT_LAYERBACK_TAC l; ALL_TAC]) (rev(1--7)) THEN

  (*** The exit after the last layer ***)

  ENSURES_INIT_TAC "s0" THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--3) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let INVNTT_BLOCKS_C_CLOSED = prove
 (INVNTT_BLOCKS_C_CLOSED_STMT,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[invntt_blocks_c; MULT_CLAUSES; CONJUNCT1 LT] THEN
  REWRITE_TAC[invntt_block_c] THEN
  SUBGOAL_THEN `1 <= 2 EXP (8 - l)` MP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `n = 2 EXP (8 - l)` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[MULT_CLAUSES; LEFT_ADD_DISTRIB] THEN
  ASM_CASES_TAC `2 * n * b <= i /\ i < 2 * n * b + 2 * n` THENL
   [SUBGOAL_THEN `i DIV (2 * n) = b /\ i MOD (2 * n) = i - 2 * n * b`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC DIVMOD_UNIQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `2 * n * b <= i /\ i < 2 * n * b + 2 * n
      ==> ~(i < 2 * n * b) /\ ~(i + n < 2 * n * b) /\
          i < 2 * n * b + 2 * n`] THEN
    ASM_CASES_TAC `i < 2 * n * b + n` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `2 * n * b <= i /\ i < 2 * n * b + n ==> i - 2 * n * b < n`;
     ARITH_RULE `~(i < 2 * n * b + n) ==> ~(i - 2 * n * b < n)`;
     ARITH_RULE `~(i < 2 * n * b + n) ==> ~(i - n < 2 * n * b)`] THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[ARITH_RULE
     `~(p <= i /\ i < p + 2 * n)
      ==> ~(p <= i /\ i < p + n) /\ ~(p + n <= i /\ i < p + 2 * n)`] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]);;

let INVNTT_LAYERS_C_STEP = prove
 (INVNTT_LAYERS_C_STEP_STMT,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[invntt_layers_c; INVNTT_BLOCKS_C_CLOSED] THEN
  SUBGOAL_THEN `2 * 2 EXP (8 - (7 - n)) * 2 EXP (6 - n) = 256`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM MULT_ASSOC; GSYM EXP_ADD] THEN
  ASM_SIMP_TAC[ARITH_RULE `n < 7 ==> 8 - (7 - n) + 6 - n = 7`] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let INVNTT_LAYERS_C_CORRECT = prove
 (INVNTT_LAYERS_C_CORRECT_STMT,
  GEN_TAC THEN CONV_TAC EXPAND_CASES_CONV THEN
  REPEAT CONJ_TAC THEN INVNTT_FINAL_TAC);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SCALE = prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SCALE_STMT,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `consts:num`; `zetas:num`; `x:num->int16`; `pc:num`;
    `sbase:int64`; `w15:int64`; `w14:int64`; `w13:int64`; `w12:int64`;
    `wbp:int64`; `wbx:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `32` `pc + poly_invntt_tomont_loop1` `pc + poly_invntt_tomont_loop1_test`
   `\i s. read RAX s = word_add a (word(16 * i)) /\
          read RDX s = word_add a (word 512) /\
          read R12 s = a /\ read RSP s = word_add sbase (word 12) /\
          read(memory :> bytes64(word_add sbase (word 52))) s = w15 /\
          read(memory :> bytes64(word_add sbase (word 44))) s = w14 /\
          read(memory :> bytes64(word_add sbase (word 36))) s = w13 /\
          read(memory :> bytes64(word_add sbase (word 28))) s = w12 /\
          read(memory :> bytes64(word_add sbase (word 20))) s = wbp /\
          read(memory :> bytes64(word_add sbase (word 12))) s = wbx /\
          read XMM5 s = word 0x05a105a105a105a105a105a105a105a1 /\
          read XMM6 s = word 0xf301f301f301f301f301f301f301f301 /\
          read XMM4 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
          (!j. 8 * i <= j /\ j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   invntt_scale_c x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, loading the constants and saving registers ***)

    RIPREL_FOLD_TAC `consts:num` `10` `-- &22:int` `32` THEN
    RIPREL_FOLD_TAC `consts:num` `30` `&30:int` `0` THEN
    RIPREL_FOLD_TAC `consts:num` `40` `&24:int` `16` THEN
    SUBGOAL_THEN `aligned 16 (word(consts + 16):int64) /\
                  aligned 16 (word(consts + 32):int64)` STRIP_ASSUME_TAC
    THENL
     [REWRITE_TAC[WORD_ADD] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
    GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
    GHOST_INTRO_TAC `ymm6_init:int256` `read YMM6` THEN
    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[XMM4; XMM5; XMM6; READ_ZEROTOP_128] THEN
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC]) THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[];

    (*** The loop body, for 8 coefficients loaded as one 128-bit word ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
    GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
    GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
    GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
    GHOST_INTRO_TAC `ymm7_init:int256` `read YMM7` THEN
    ENSURES_INIT_TAC "s0" THEN
    XMM_EXISTSTOP_TAC "top4" `YMM4` THEN
    XMM_EXISTSTOP_TAC "top5" `YMM5` THEN
    XMM_EXISTSTOP_TAC "top6" `YMM6` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
      [MATCH_MP CHUNK8_INPUT_SPLIT (ASSUME `i < 32`)]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
    REWRITE_TAC[CHUNK8_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN STRIP_TAC THEN
    MP_TAC(READ_MEMORY_MERGE_CONV 3
      `read(memory :> bytes128(word_add a (word(16 * i)))) s0`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    DISCARD_MATCHING_ASSUMPTIONS [`read (memory :> bytes16 a) s = x`] THEN
    MAP_EVERY (fun n ->
      X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC [n] THEN
      SIMD_SIMPLIFY_TAC[]) (1--37) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE (SIMD_SIMPLIFY_CONV []) o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
      check (can (term_match [] `read (memory :> bytes128 a) s = x`) o
             concl)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[XMM4; XMM5; XMM6; READ_ZEROTOP_128] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC]) THEN
    REWRITE_TAC[CHUNK8_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[CHUNK8_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN
    ASM_REWRITE_TAC[invntt_scale_c; INVNTT_LANE_FORM];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add a (word (16 * i)))
                     (word_add a (word 512)):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y) = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 32 ==> 16 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 32` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `invntt_scale_c` (concl th)))]);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `consts:num`; `zetas:num`; `x:num->int16`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 60 THEN
  MAP_EVERY X_GEN_TAC [`sbase:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY (fun (n,c) -> ENSURES_PRESERVED_TAC n c)
   [("rbx_init",`RBX`); ("rbp_init",`RBP`); ("r12_init",`R12`);
    ("r13_init",`R13`); ("r14_init",`R14`); ("r15_init",`R15`)] THEN
  ENSURES_INIT_TAC "s0" THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INVNTT_CONSTANTS_LOADED) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLK_ZETAS_LOADED) THEN

  (*** The scaling, which also saves the registers ***)

  MP_TAC(SPECL [`a:int64`; `consts:num`; `zetas:num`; `x:num->int16`;
                `pc:num`; `sbase:int64`; `r15_init:int64`; `r14_init:int64`;
                `r13_init:int64`; `r12_init:int64`; `rbp_init:int64`;
                `rbx_init:int64`]
         MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SCALE) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  X86_BIGSTEP_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC "s1" THEN

  (*** The layers ***)

  MP_TAC(SPECL [`a:int64`; `consts:num`; `zetas:num`; `invntt_scale_c x`;
                `pc:num`; `sbase:int64`]
         MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_LAYERS) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  X86_BIGSTEP_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC "s2" THEN

  (*** Restoring the registers and returning ***)

  X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (3--9) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC]) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[INVNTT_LAYERS_C_CORRECT]);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_BLOCK_SAFE = prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_BLOCK_SAFE_STMT,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (consts:num) (zetas:num) (pc:num) (sbase:int64) (start:num)
     (len:num).
      APPEND (f_ev_blkend a consts zetas pc sbase start len)
        (APPEND (ENUMERATEL len
                   (\j. f_ev_bfly a consts zetas pc sbase start len j))
                (f_ev_blkhead a consts zetas pc sbase start len))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `len:num` `pc + poly_invntt_tomont_loop3` `pc + poly_invntt_tomont_loop3_exit`
   `\j s. read RCX s = word_add a (word(2 * (start + j))) /\
          read RDX s = word_add a (word(2 * (start + len + j))) /\
          read RSI s = word_add a (word(2 * (start + len))) /\
          read RDI s = word(start + len) /\
          read R10 s = word(k - 1) /\ read RBX s = word(2 * len) /\
          read R12 s = a /\ read R14 s = word_add a (word 2) /\
          read R13 s = word zetas /\
          read R11 s = w11 /\ read R15 s = rs /\
          read RSP s = word_add sbase (word 12) /\
          read(memory :> bytes64(word_add sbase (word 60))) s = retaddr /\
          read(memory :> bytes64(word_add sbase (word 52))) s = w15 /\
          read(memory :> bytes64(word_add sbase (word 44))) s = w14 /\
          read(memory :> bytes64(word_add sbase (word 36))) s = w13 /\
          read(memory :> bytes64(word_add sbase (word 28))) s = w12 /\
          read(memory :> bytes64(word_add sbase (word 20))) s = wbp /\
          read(memory :> bytes64(word_add sbase (word 12))) s = wbx /\
          read (memory :> bytes32 sbase) s = word start` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** Setting up the pointers for the inner loop ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--2) THEN
    W32_DECIDE_FLAGS_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (3--15) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
    REPEAT(CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The inner loop body, one butterfly, and the loop test ***)

    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--22) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_add (word_add a (word x)) (word y):int64 =
      word_add a (word(x + y))`]) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (23--23) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (24--24) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(2 * (start + j) + 2 = 2 * (start + len)) <=> j + 1 < len`
     SUBST_ALL_TAC THENL
     [UNDISCH_TAC `j < len` THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The end of the block, restoring RSI ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--1) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let INVNTT_GCC12_O2_LAYER_EVENTS =
  map (fun l ->
        new_specification
         ["x86_invntt_gcc12_O2_layer_events_" ^ string_of_int l]
         (prove(lsafe_goal l,INVNTT_LAYER_SAFE_TAC l)))
      (1--7);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SCALE_SAFE = prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SCALE_SAFE_STMT,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (consts:num) (zetas:num) (pc:num) (sbase:int64).
      APPEND (f_ev_sexit a consts zetas pc sbase)
        (APPEND (ENUMERATEL 32 (\i. f_ev_sloop a consts zetas pc sbase i))
                (f_ev_sprol a consts zetas pc sbase))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  RIPREL_FOLD_TAC `consts:num` `10` `-- &22:int` `32` THEN
  RIPREL_FOLD_TAC `consts:num` `30` `&30:int` `0` THEN
  RIPREL_FOLD_TAC `consts:num` `40` `&24:int` `16` THEN
  SUBGOAL_THEN `aligned 16 (word(consts + 16):int64) /\
                aligned 16 (word(consts + 32):int64)` STRIP_ASSUME_TAC
  THENL
   [REWRITE_TAC[WORD_ADD] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + poly_invntt_tomont_loop1` `pc + poly_invntt_tomont_loop1_exit`
   `\i s. read RAX s = word_add a (word(16 * i)) /\
          read RDX s = word_add a (word 512) /\
          read R12 s = a /\ read RSP s = word_add sbase (word 12) /\
          read(memory :> bytes64(word_add sbase (word 52))) s = w15 /\
          read(memory :> bytes64(word_add sbase (word 44))) s = w14 /\
          read(memory :> bytes64(word_add sbase (word 36))) s = w13 /\
          read(memory :> bytes64(word_add sbase (word 28))) s = w12 /\
          read(memory :> bytes64(word_add sbase (word 20))) s = wbp /\
          read(memory :> bytes64(word_add sbase (word 12))) s = wbx /\
          read(memory :> bytes64(word_add sbase (word 60))) s = retaddr` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--13) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    LSAFE_SIM_TAC `1` ALL_TAC 0] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_EXEC (1--39) THEN
  SUBGOAL_THEN
   `~(val (word_add (word_add a (word (16 * i))) (word 16):int64) =
      val (word_add a (word 512):int64)) <=> i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_EQ; GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_EQ; DIMINDEX_64; CONG] THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 32 ==> 16 * i + 16 < 2 EXP 64`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 32` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SUBROUTINE_SAFE_STMT,
  INVNTT_SAFE_TOP_TAC);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLKEM_NATIVE_IMAGE_TAC
   (INST [`pc + mlkem_poly_invntt_tomont`,`pc:num`; `pc + mlkem_poly_invntt_tomont_consts`,`consts:num`;
    `pc + rodata_mlk_zetas`,`zetas:num`]
     (SPEC_ALL MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SUBROUTINE_CORRECT))
   [MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IN_IMAGE;
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_CONSTANTS_IN_IMAGE;
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_ZETAS_IN_IMAGE]);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  MLKEM_NATIVE_IMAGE_SAFE_TAC
   MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_SUBROUTINE_SAFE
   [`pc + mlkem_poly_invntt_tomont`,`pc:num`; `pc + mlkem_poly_invntt_tomont_consts`,`consts:num`;
    `pc + rodata_mlk_zetas`,`zetas:num`]
   [MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_IN_IMAGE;
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_CONSTANTS_IN_IMAGE;
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_ZETAS_IN_IMAGE]);;
