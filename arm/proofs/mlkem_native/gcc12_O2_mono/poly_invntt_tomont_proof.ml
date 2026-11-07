(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_invntt_tomont_spec.ml";;


let WORD_2_VAL = prove
 (WORD_2_VAL_STMT,
  REWRITE_TAC[WORD_MUL; WORD_VAL]);;

let WORD_SXFROM_ADD_16 = prove
 (WORD_SXFROM_ADD_16_STMT,
  BITBLAST_TAC);;

let WORD_SXFROM_SUB_16 = prove
 (WORD_SXFROM_SUB_16_STMT,
  BITBLAST_TAC);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_BLOCK = prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_BLOCK_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The inner loop, X2 pointing at the upper coefficient and X3 = -len ***)

  ENSURES_WHILE_UP_TAC `len:num` `pc + mlk_poly_invntt_tomont_c_loop4`
   `pc + mlk_poly_invntt_tomont_c_loop4_test`
   `\jj s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O2_mono_mc /\
           read X2 s = word_add a (word(2 * (start + len + jj))) /\
           read X5 s = word_add a (word(2 * (start + 2 * len))) /\
           read X3 s = word_neg(word len) /\
           read X10 s = word(start + len) /\ read X11 s = word start /\
           read X12 s = word(k - 1) /\
           read X4 s = word 4294963967 /\
           read X6 s = word_zx(word_sx z:int32) /\
           read X13 s = word(2 * len) /\
           read X7 s = word 4294963969 /\
           read X8 s = word 33554432 /\ read X9 s = word 20159 /\
           read X14 s = word zetas /\ read X15 s = a /\
           read X16 s = word_add a (word 2) /\
           read X17 s = w17 /\ read X18 s = w18 /\ read X30 s = w30 /\
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
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (1--2) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (3--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `~(a <= i /\ i < a:num)`] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_RULE `word_neg x = word_sub (word 0) x`] THEN
    REPEAT CONJ_TAC THEN WORD_SMALL_TAC;

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
    ASM_SIMP_TAC[ARITH_RULE
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
    SUBGOAL_THEN
     `word_add (word_add a (word(2 * (start + len + jj))))
               (word(2 * val(word_neg(word len):int64))):int64 =
      word_add a (word(2 * (start + jj)))`
    ASSUME_TAC THENL
     [REWRITE_TAC[WORD_2_VAL] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (1--17) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i = start + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LE_ADD; ARITH_RULE `start + jj < start + jj + 1`] THEN
      MLKEM_NATIVE_W_SIMP_TAC THEN REWRITE_TAC[WORD_ADD_0] THEN
      REWRITE_TAC[WORD_SXFROM_ADD_16; BARRED_SCALAR] THEN
      REWRITE_TAC[invntt_block_c; LE_ADD; LT_ADD_LCANCEL] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[ADD_AC];
      ALL_TAC] THEN
    ASM_CASES_TAC `i = start + len + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `start + len + jj < start + len + jj + 1`;
                  ARITH_RULE `start + len <= start + len + jj`] THEN
      MLKEM_NATIVE_W_SIMP_TAC THEN REWRITE_TAC[WORD_ADD_0] THEN
      REWRITE_TAC[WORD_SXFROM_SUB_16; GSYM montred_scalar] THEN
      REWRITE_TAC[invntt_block_c; invntt_fqmul_c] THEN
      ASM_SIMP_TAC[ARITH_RULE
       `jj < len ==> ~(start <= start + len + jj /\
                       start + len + jj < start + len) /\
                     start + len <= start + len + jj /\
                     start + len + jj < start + 2 * len`] THEN
      REWRITE_TAC[ARITH_RULE `(start + len + jj) - len = start + jj`];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `m:num->int16` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;

    (*** The inner loop back-edge ***)

    X_GEN_TAC `jj:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The inner loop exit and the end of the block ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (2--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [WORD_SMALL_TAC; WORD_SMALL_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `m:num->int16` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[invntt_block_c] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC]);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_LAYER = prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_LAYER_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) MP_TAC) THEN
  SPEC_TAC(`l:num`,`l:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
  (map INVNTT_LAYER_TAC (1--7)));;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_LAYERS = prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_LAYERS_STMT,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `consts:num`; `zetas:num`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun eq ->
    if is_eq(concl eq) && lhand(concl eq) = `zetas:num`
    then (zeta_eq := eq; ALL_TAC) else failwith "") THEN

  (*** Initialization, including the address of the table ***)

  ENSURES_SEQUENCE_TAC
   `pc + mlk_poly_invntt_tomont_c_loop2` (invntt_layerhead_tm 7) THEN CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    (fun g -> ASSUME_TAC !zeta_eq g) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLK_ZETAS_LOADED o
                MATCH_MP MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_ZETAS_IN_IMAGE) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (2--11) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[CONJUNCT1 invntt_layers_c] THEN
    REWRITE_TAC[mlk_zetas] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_IWORD_CONV) THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    TRY(CONV_TAC WORD_RULE);
    ALL_TAC] THEN

  (*** The layers, with the loop back to the head between them ***)

  MAP_EVERY (fun l ->
    ENSURES_SEQUENCE_TAC
     `pc + mlk_poly_invntt_tomont_c_loop3_exit` (invntt_layerend_tm l) THEN
    CONJ_TAC THENL [INVNTT_LAYER_APPLY_TAC l; ALL_TAC] THEN
    if l = 1 then ALL_TAC else
    ENSURES_SEQUENCE_TAC
     `pc + mlk_poly_invntt_tomont_c_loop2` (invntt_layerhead_tm (l - 1)) THEN
    CONJ_TAC THENL [INVNTT_LAYERBACK_TAC l; ALL_TAC]) (rev(1--7)) THEN

  (*** The exit after the last layer ***)

  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (2--2) THEN
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

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_SCALE = prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_SCALE_STMT,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `x:num->int16`; `pc:num`;
    `stackpointer:int64`; `x19:int64`; `x30:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `32` `pc + mlk_poly_invntt_tomont_c_loop1`
   `pc + mlk_poly_invntt_tomont_c_loop1_test`
   `\i s. read X0 s = word_add a (word(16 * i)) /\
          read X1 s = word_add a (word 512) /\
          read X15 s = a /\
          read SP s = word_sub stackpointer (word 16) /\
          read(memory :> bytes64(word_sub stackpointer (word 16))) s = x19 /\
          read(memory :> bytes64(word_add (word_sub stackpointer (word 16))
                                 (word 8))) s = x30 /\
          read Q3 s = word 0xf2fff2fff2fff2fff2fff2fff2fff2ff /\
          read Q4 s = word 0x05a105a105a105a105a105a105a105a1 /\
          read Q5 s = word 0xf301f301f301f301f301f301f301f301 /\
          (!j. 8 * i <= j /\ j < 256
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   x j) /\
          (!j. j < 8 * i
               ==> read(memory :> bytes16(word_add a (word(2 * j)))) s =
                   invntt_scale_c x j)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, loading the constants and saving registers ***)

    ENSURES_INIT_TAC "s0" THEN
    MAP_EVERY (fun th -> FIRST_ASSUM(ASSUME_TAC o MATCH_MP th))
      MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_CONSTANTS THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (1--2) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (3--6) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (7--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[];

    (*** The loop body, for 8 coefficients loaded as one 128-bit word ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
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
      ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC [n] THEN
      SIMD_SIMPLIFY_TAC[montred_neon]) (1--9) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o CONV_RULE (SIMD_SIMPLIFY_CONV []) o
      CONV_RULE(READ_MEMORY_SPLIT_CONV 3) o
      check (can (term_match [] `read (memory :> bytes128 a) s = x`) o
             concl)) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN
    REWRITE_TAC[CHUNK8_OUTPUT_SPLIT] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC[CHUNK8_ADDR; ADD_CLAUSES] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
    REWRITE_TAC[WORD_ADD_0] THEN ASM_REWRITE_TAC[invntt_scale_c];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `invntt_scale_c` (concl th)))]);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_Z = prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_Z_STMT,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `zetas:num`; `x:num->int16`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[SOME_FLAGS; C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun eq ->
    if is_eq(concl eq) && lhand(concl eq) = `zetas:num`
    then RULE_ASSUM_TAC(REWRITE_RULE[eq]) THEN ASSUME_TAC eq
    else failwith "") THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_INIT_TAC "s0" THEN

  (*** The scaling, which also saves X19 and X30 ***)

  MP_TAC(SPECL [`a:int64`; `x:num->int16`; `pc:num`; `stackpointer:int64`;
                `x19_init:int64`; `returnaddress:int64`]
         MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_SCALE) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC "s1" THEN

  (*** The layers ***)

  MP_TAC(SPECL [`a:int64`; `0`; `zetas:num`; `invntt_scale_c x`; `pc:num`]
         MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_LAYERS) THEN
  ASM_REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  ARM_BIGSTEP_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC "s2" THEN

  (*** Restoring X19 and X30 and returning ***)

  ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (3--4) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_RULE] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[INVNTT_LAYERS_C_CORRECT]);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`a:int64`; `x:num->int16`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `nonoverlapping (a:int64,512)
                  (word(pc + rodata_mlk_zetas),256)` MP_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:int64`; `pc + rodata_mlk_zetas`; `x:num->int16`; `pc:num`;
                `stackpointer:int64`; `returnaddress:int64`] MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_Z) THEN
  ASM_REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES]);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_BLOCK_SAFE = prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_BLOCK_SAFE_STMT,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (consts:num) (zetas:num) (pc:num) (start:num) (len:num).
      APPEND (f_ev_blkend a consts zetas pc start len)
        (APPEND (ENUMERATEL len
                   (\j. f_ev_bfly a consts zetas pc start len j))
                (f_ev_blkhead a consts zetas pc start len))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL;
              SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `len:num` `pc + mlk_poly_invntt_tomont_c_loop4`
   `pc + mlk_poly_invntt_tomont_c_loop4_exit`
   `\j s. read X2 s = word_add a (word(2 * (start + len + j))) /\
          read X5 s = word_add a (word(2 * (start + 2 * len))) /\
          read X3 s = word_neg(word len) /\
          read X10 s = word(start + len) /\ read X11 s = word start /\
          read X12 s = word(k - 1) /\ read X13 s = word(2 * len) /\
          read X14 s = word zetas /\ read X15 s = a /\
          read X16 s = word_add a (word 2) /\
          read X17 s = w17 /\ read X18 s = w18 /\ read X30 s = w30 /\
          read SP s = sp /\
          read(memory :> bytes64(word_add sp (word 8))) s = returnaddress /\
          read(memory :> bytes64 sp) s = x19v` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** Setting up the pointers for the inner loop ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (1--2) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (3--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[WORD_RULE `word_neg x = word_sub (word 0) x`] THEN
    REPEAT(CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The inner loop body, one butterfly, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN
     `word_add (word_add a (word(2 * (start + len + i))))
               (word(2 * val(word_neg(word len):int64))):int64 =
      word_add a (word(2 * (start + i)))`
    ASSUME_TAC THENL
     [REWRITE_TAC[WORD_2_VAL] THEN CONV_TAC WORD_RULE; ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (1--17) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_add (word_add a (word x)) (word y):int64 =
      word_add a (word(x + y))`]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (18--18) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (19--19) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(2 * (start + len + i) + 2 = 2 * (start + 2 * len)) <=> i + 1 < len`
    SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The end of the block ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let INVNTT_GCC12_O2_MONO_LAYER_EVENTS =
  map (fun l ->
        new_specification ["invntt_gcc12_O2_mono_layer_events_" ^ string_of_int l]
                          (prove(lsafe_goal l,INVNTT_LAYER_SAFE_TAC l)))
      (1--7);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_SCALE_SAFE = prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_SCALE_SAFE_STMT,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (consts:num) (zetas:num) (pc:num) (sp:int64).
      APPEND (f_ev_sexit a consts zetas pc sp)
        (APPEND (ENUMERATEL 32 (\i. f_ev_sloop a consts zetas pc sp i))
                (f_ev_sprol a consts zetas pc sp))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL;
              SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhand(concl th) = `consts:num`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhand(concl th) = `zetas:num`)) THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlk_poly_invntt_tomont_c_loop1`
   `pc + mlk_poly_invntt_tomont_c_loop1_exit`
   `\i s. read X0 s = word_add a (word(16 * i)) /\
          read X1 s = word_add a (word 512) /\
          read X15 s = a /\
          read SP s = sp /\
          read(memory :> bytes64(word_add sp (word 8))) s = returnaddress /\
          read(memory :> bytes64 sp) s = x19v` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (1--2) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (3--6) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (7--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    REPEAT CONJ_TAC THEN TRY(CONV_TAC WORD_RULE) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    LSAFE_SIM_TAC ALL_TAC 0] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  ARM_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_EXEC (1--11) THEN
  SUBGOAL_THEN
   `~(val(word_sub (word_add a (word 512))
                   (word_add (word_add a (word (16 * i))) (word 16)):int64) =
      0) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[WORD_RULE
     `word_sub (word_add a x) (word_add (word_add a y) z):int64 =
      word_sub x (word_add y z)`] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 32 ==> 16 * i + 16 < 18446744073709551616`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `16 * (i + 1) = 16 * i + 16`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_SAFE_Z = prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_SAFE_Z_STMT,
  INVNTT_SAFE_TOP_TAC);;

let MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT,
  X_CHOOSE_THEN `g:int64->num->num->num->int64->int64->(uarch_event)list`
    ASSUME_TAC MLKEM_NATIVE_POLY_INVNTT_TOMONT_GCC12_O2_MONO_SAFE_Z THEN
  EXISTS_TAC `\(a:int64) (pc:num) (sp:int64) (returnaddress:int64).
                (g:int64->num->num->num->int64->int64->(uarch_event)list)
                  a (pc + mlk_poly_invntt_tomont_c_consts)
                  (pc + rodata_mlk_zetas) pc sp returnaddress` THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `pc:num`; `stackpointer:int64`;
    `returnaddress:int64`] THEN
  REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `nonoverlapping (a:int64,512)
                  (word(pc + rodata_mlk_zetas),256)` MP_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`;
    `pc + mlk_poly_invntt_tomont_c_consts`; `pc + rodata_mlk_zetas`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[]);;
