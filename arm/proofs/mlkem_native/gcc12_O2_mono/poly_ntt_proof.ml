(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_O2_mono/poly_ntt_spec.ml";;


let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_BLOCK = prove
 (MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_BLOCK_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_WHILE_UP_TAC `len:num` `pc + mlk_poly_ntt_c_loop3`
   `pc + mlk_poly_ntt_c_loop3_test`
   `\jj s. aligned_bytes_loaded s (word pc)
             mlkem_native_libmlkem_gcc12_O2_mono_mc /\
           read X1 s = word_add a (word(2 * (start + jj))) /\
           read X5 s = word_add a (word(2 * (start + len))) /\
           read X4 s = word len /\
           read X9 s = word start /\ read X10 s = word(start + len) /\
           read X11 s = word(k + 1) /\
           read X6 s = word_zx(word_sx z:int32) /\
           read X12 s = word(2 * len) /\
           read X7 s = word 4294963967 /\ read X8 s = word 4294963969 /\
           read X13 s = word zetas /\ read X14 s = a /\
           read X15 s = word_add a (word 2) /\
           read X16 s = w15 /\ read X17 s = w16 /\ read X18 s = w17 /\
           (!k. k < 128
                ==> read(memory :> bytes16(word_add (word zetas)
                                                    (word(2 * k)))) s =
                    iword(EL k mlk_zetas)) /\
           (!i. i < 256
                ==> read(memory :> bytes16(word_add a (word(2 * i)))) s =
                    if start <= i /\ i < start + jj \/
                       start + len <= i /\ i < start + len + jj
                    then ntt_block_c z start len m i else m i)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** Setting up the pointers for the inner loop ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (1--2) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (3--12) THEN
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
    ASM_SIMP_TAC[ARITH_RULE
     `jj < len
      ==> ~(start <= start + len + jj /\ start + len + jj < start + jj) /\
          ~(start + len <= start + len + jj /\
            start + len + jj < start + len + jj)`] THEN
    REWRITE_TAC[ARITH_RULE
     `2 * (start + len + jj) = 2 * (start + jj) + 2 * len`] THEN
    DISCH_TAC THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `jj < len
      ==> ~(start <= start + jj /\ start + jj < start + jj) /\
          ~(start + len <= start + jj /\ start + jj < start + len + jj)`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `val(word len:int64) = len` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (1--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i = start + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LE_ADD; ARITH_RULE `start + jj < start + jj + 1`] THEN
      MLKEM_NATIVE_W_SIMP_TAC THEN REWRITE_TAC[WORD_ADD_0] THEN
      REWRITE_TAC[GSYM montred_scalar; WORD_ZX_ADD_ZX_16] THEN
      REWRITE_TAC[ntt_block_c; ntt_fqmul_c; LE_ADD] THEN
      ASM_REWRITE_TAC[LT_ADD_LCANCEL] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN REWRITE_TAC[ADD_AC; WORD_ADD_SYM];
      ALL_TAC] THEN
    ASM_CASES_TAC `i = start + len + jj` THENL
     [FIRST_X_ASSUM SUBST1_TAC THEN
      REWRITE_TAC[ARITH_RULE
       `2 * (start + len + jj) = 2 * (start + jj) + 2 * len`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `start + len + jj < start + len + jj + 1`;
                  ARITH_RULE `start + len <= start + len + jj`] THEN
      MLKEM_NATIVE_W_SIMP_TAC THEN REWRITE_TAC[WORD_ADD_0] THEN
      REWRITE_TAC[GSYM montred_scalar; WORD_ZX_SUB_ZX_16] THEN
      REWRITE_TAC[ntt_block_c; ntt_fqmul_c] THEN
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
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (2--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];

    (*** The inner loop exit and the end of the block ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (1--1) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (2--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [WORD_SMALL_TAC; WORD_SMALL_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && free_in `m:num->int16` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ntt_block_c] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC]);;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_LAYER = prove
 (MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_LAYER_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL; SOME_FLAGS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) MP_TAC) THEN
  SPEC_TAC(`l:num`,`l:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC NUM_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
  (map NTT_LAYER_TAC (0--6)));;

let NTT_BLOCKS_C_CLOSED = prove
 (NTT_BLOCKS_C_CLOSED_STMT,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ntt_blocks_c; MULT_CLAUSES; CONJUNCT1 LT] THEN
  REWRITE_TAC[ntt_block_c] THEN
  SUBGOAL_THEN `1 <= 2 EXP (7 - l)` MP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `n = 2 EXP (7 - l)` THEN DISCH_TAC THEN
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

let NTT_LAYERS_C_STEP = prove
 (NTT_LAYERS_C_STEP_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ntt_layers_c; NTT_BLOCKS_C_CLOSED] THEN
  SUBGOAL_THEN `i < 2 * 2 EXP (7 - l) * 2 EXP l`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM MULT_ASSOC; GSYM EXP_ADD] THEN
  ASM_SIMP_TAC[ARITH_RULE `l < 7 ==> 7 - l + l = 7`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

let NTT_LAYERS_C_CORRECT = prove
 (NTT_LAYERS_C_CORRECT_STMT,
  GEN_TAC THEN CONV_TAC(LAND_CONV EXPAND_CASES_CONV) THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  CONV_TAC EXPAND_CASES_CONV THEN
  W(fun (asl,w) ->
    let lfn = MLKEM_NATIVE_LOCAL_CONGBOUND_RULE
                (PROCESS_BOUND_ASSUMPTIONS (map snd asl))
                NTT_LAYER_EQUATIONS in
    REPEAT CONJ_TAC THEN NTT_FINAL_TAC lfn));;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_LAYERS = prove
 (MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_LAYERS_STMT,
  MAP_EVERY X_GEN_TAC [`a:int64`; `zetas:num`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[SOME_FLAGS; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun eq ->
    if is_eq(concl eq) && lhand(concl eq) = `zetas:num`
    then (zeta_eq := eq; ALL_TAC) else failwith "") THEN

  (*** Initialization, including the address of the table ***)

  ENSURES_SEQUENCE_TAC
   `pc + mlk_poly_ntt_c_loop1` (ntt_layerhead_tm 0) THEN CONJ_TAC THENL
   [ENSURES_INIT_TAC "s0" THEN
    (fun g -> ASSUME_TAC !zeta_eq g) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLK_ZETAS_LOADED o
                MATCH_MP MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_ZETAS_IN_IMAGE) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (2--10) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[CONJUNCT1 ntt_layers_c] THEN
    REWRITE_TAC[mlk_zetas] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV WORD_IWORD_CONV) THEN
    CONV_TAC(DEPTH_CONV WORD_RED_CONV) THEN
    TRY(CONV_TAC WORD_RULE);
    ALL_TAC] THEN

  (*** The layers, with the loop back to the head between them ***)

  MAP_EVERY (fun l ->
    ENSURES_SEQUENCE_TAC `pc + mlk_poly_ntt_c_loop2_exit` (ntt_layerend_tm l) THEN
    CONJ_TAC THENL [NTT_LAYER_APPLY_TAC l; ALL_TAC] THEN
    if l = 6 then ALL_TAC else
    ENSURES_SEQUENCE_TAC `pc + mlk_poly_ntt_c_loop1` (ntt_layerhead_tm (l + 1)) THEN
    CONJ_TAC THENL [NTT_LAYERBACK_TAC l; ALL_TAC]) (0--6) THEN

  (*** The exit after the last layer ***)

  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (1--1) THEN
  W32_DECIDE_FLAGS_TAC THEN
  ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (2--2) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]);;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_CORRECT = prove
 (MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC [`a:int64`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The output is disjoint from the table of zetas in the image ***)

  SUBGOAL_THEN `nonoverlapping (a:int64,512)
                  (word(pc + rodata_mlk_zetas),256)` MP_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:int64`; `pc + rodata_mlk_zetas`; `x:num->int16`;
                `pc:num`] MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_LAYERS) THEN
  ASM_REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ_ALT] ENSURES_POSTCONDITION_THM)) THEN
  GEN_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN DISCH_TAC THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  MP_TAC(SPEC `x:num->int16` NTT_LAYERS_C_CORRECT) THEN
  ASM_SIMP_TAC[]);;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT,
  ARM_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC
    MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_CORRECT);;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_BLOCK_SAFE = prove
 (MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_BLOCK_SAFE_STMT,
  CONCRETIZE_F_EVENTS_TAC
   `\(a:int64) (zetas:num) (pc:num) (returnaddress:int64) (start:num)
     (len:num).
      APPEND (f_ev_blkend a zetas pc returnaddress start len)
        (APPEND (ENUMERATEL len
                   (\j. f_ev_bfly a zetas pc returnaddress start len j))
                (f_ev_blkhead a zetas pc returnaddress start len))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALL;
              SOME_FLAGS] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `len:num` `pc + mlk_poly_ntt_c_loop3`
   `pc + mlk_poly_ntt_c_loop3_exit`
   `\j s. read X1 s = word_add a (word(2 * (start + j))) /\
          read X5 s = word_add a (word(2 * (start + len))) /\
          read X4 s = word len /\
          read X9 s = word start /\ read X10 s = word(start + len) /\
          read X11 s = word(k + 1) /\ read X12 s = word(2 * len) /\
          read X13 s = word zetas /\ read X14 s = a /\
          read X15 s = word_add a (word 2) /\
          read X16 s = w15 /\ read X17 s = w16 /\ read X18 s = w17 /\
          read X30 s = returnaddress` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;

    (*** Setting up the pointers for the inner loop ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (1--2) THEN
    W32_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (3--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The inner loop body, one butterfly, and the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `val(word len:int64) = len` ASSUME_TAC THENL
     [REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN MATCH_MP_TAC MOD_LT THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (1--12) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[WORD_RULE
     `word_add (word_add a (word x)) (word y):int64 =
      word_add a (word(x + y))`]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (13--13) THEN
    PTR_DECIDE_FLAGS_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (14--14) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(2 * (start + len) = 2 * (start + i) + 2) <=> i + 1 < len`
     SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The end of the block ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [WORD_SMALL_TAC; ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let NTT_GCC12_O2_MONO_LAYER_EVENTS =
  map (fun l ->
        new_specification ["ntt_gcc12_O2_mono_layer_events_" ^ string_of_int l]
                          (prove(lsafe_goal l,NTT_LAYER_SAFE_TAC l)))
      (0--6);;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_SAFE = prove
 (MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_SAFE_STMT,
  NTT_SAFE_TOP_TAC);;

let MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT,
  X_CHOOSE_THEN `g:int64->num->num->int64->(uarch_event)list` ASSUME_TAC
    MLKEM_NATIVE_POLY_NTT_GCC12_O2_MONO_SAFE THEN
  EXISTS_TAC `\(a:int64) (pc:num) (returnaddress:int64).
                (g:int64->num->num->int64->(uarch_event)list) a
                  (pc + rodata_mlk_zetas) pc returnaddress` THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `a:int64`; `pc:num`; `returnaddress:int64`] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `nonoverlapping (a:int64,512)
                  (word(pc + rodata_mlk_zetas),256)` MP_TAC THENL
   [REWRITE_TAC[WORD_ADD] THEN NONOVERLAPPING_TAC; ALL_TAC] THEN
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `a:int64`; `pc + rodata_mlk_zetas`; `pc:num`;
    `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[ALL; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[]);;
