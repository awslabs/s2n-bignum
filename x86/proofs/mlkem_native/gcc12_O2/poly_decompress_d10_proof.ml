(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/gcc12_O2/poly_decompress_d10_spec.ml";;


let D10_BYTES = prove
 (D10_BYTES_STMT,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `320`; `n:num`; `5 * i + j`; `s:x86state`]
                READ_MEMORY_BYTES8_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 8 = 256`] THEN
  REWRITE_TAC[ARITH_RULE `8 * (5 * i + j) = 40 * i + 8 * j`]);;

let D10_HALF = prove
 (D10_HALF_STMT,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o rand o snd) THEN
  ANTS_TAC THENL
   [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a:int64`; `320`; `n:num`; `5 * i`; `s:x86state`]
                READ_MEMORY_BYTES16_OF_NUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[EXP; DIV_1; ARITH_RULE `2 EXP 16 = 65536`] THEN
  REWRITE_TAC[ARITH_RULE `8 * 5 * i = 40 * i`]);;

let D10_LANE = prove
 (D10_LANE_STMT,
  GEN_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_SUBWORD; VAL_WORD_USHR; VAL_WORD_ADD;
              VAL_WORD_SHL; VAL_WORD_ZX_GEN; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[DIV_1] THEN
  MP_TAC(ISPEC `f:10 word` VAL_BOUND) THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`val(f:10 word)`,`v:num`) THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MOD_LT; ARITH_RULE `v < 1024 ==> v < 4294967296`;
   ARITH_RULE `v < 1024 ==> 2 * v < 4294967296`;
   ARITH_RULE `v < 1024 ==> 2 * v + v < 4294967296`;
   ARITH_RULE `v < 1024 ==> 4 * (2 * v + v) < 4294967296`;
   ARITH_RULE `v < 1024 ==> 4 * (2 * v + v) + v < 4294967296`;
   ARITH_RULE `v < 1024 ==> 256 * (4 * (2 * v + v) + v) < 4294967296`;
   ARITH_RULE `v < 1024 ==> v + 512 < 4294967296`;
   ARITH_RULE `v < 1024 ==>
                256 * (4 * (2 * v + v) + v) + v + 512 < 4294967296`] THEN
  SUBGOAL_THEN `(256 * (4 * (2 * v + v) + v) + v + 512) DIV 1024 < 65536 /\
                (3329 * v + 512) DIV 1024 < 65536`
   (fun th -> SIMP_TAC[th; MOD_LT]) THENL
   [REWRITE_TAC[RDIV_LT_EQ; ARITH_EQ] THEN ASM_ARITH_TAC;
    AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC]);;

let D10_FIELD = prove
 (D10_FIELD_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VAL_WORD_SUBWORD; VAL_WORD] THEN
  CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN
  REWRITE_TAC[ARITH_RULE `MIN 10 10 = 10`] THEN
  ASM_SIMP_TAC[DIV_MOD_EXP_LOW; ARITH_RULE `k < 4 ==> 10 * k + 10 <= 40`] THEN
  REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `1024 = 2 EXP 10`] THEN
  REWRITE_TAC[ARITH_RULE `40 * i + 10 * k = 10 * (4 * i + k)`]);;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_CORRECT = prove
 (MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `64` `pc + mlkem_poly_decompress_d10_loop1` `pc + mlkem_poly_decompress_d10_loop1_test`
   `\i s. read RDX s = word_add a (word(5 * i)) /\
          read RCX s = word_add r (word(8 * i)) /\
          read RSI s = word_add a (word 320) /\
          read XMM4 s = word 0x00000000000000000000020000000200 /\
          read XMM3 s = word 0 /\
          read (memory :> bytes(a,320)) s = n /\
          (!j. j < 4 * i
               ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                   word((3329 * (n DIV 2 EXP (10 * j)) MOD 2 EXP 10 + 512)
                        DIV 1024))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, with the vector of constants from the image ***)

    GHOST_INTRO_TAC `ymm3_init:int256` `read YMM3` THEN
    GHOST_INTRO_TAC `ymm4_init:int256` `read YMM4` THEN
    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP
      (MLKEM_NATIVE_IMAGE_RIPREL_CONST_RULE (layout "mlkem_poly_decompress_d10" + 0x8) (layout "mlkem_poly_decompress_d10_consts") 64)) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_EXEC (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[XMM3; XMM4; READ_ZEROTOP_128] THEN
    REPEAT(CONJ_TAC THENL [CONV_TAC WORD_BLAST; ALL_TAC]) THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; LE_0; WORD_ADD_0] THEN
    ASM_REWRITE_TAC[];

    (*** The loop body, for five bytes and four coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    GHOST_INTRO_TAC `ymm0_init:int256` `read YMM0` THEN
    GHOST_INTRO_TAC `ymm1_init:int256` `read YMM1` THEN
    GHOST_INTRO_TAC `ymm2_init:int256` `read YMM2` THEN
    GHOST_INTRO_TAC `ymm5_init:int256` `read YMM5` THEN
    ENSURES_INIT_TAC "s0" THEN
    XMM_EXISTSTOP_TAC "top3" `YMM3` THEN
    XMM_EXISTSTOP_TAC "top4" `YMM4` THEN
    MAP_EVERY (fun j ->
      MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV)
       (SPECL [`a:int64`; `n:num`; `i:num`; `s0:x86state`;
               mk_small_numeral j] D10_BYTES)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC) (1--4) THEN
    MP_TAC(SPECL [`a:int64`; `n:num`; `i:num`; `s0:x86state`] D10_HALF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    D10_ADDR_TAC THEN
    ABBREV_TAC `w:40 word = word(n DIV 2 EXP (40 * i))` THEN
    MAP_EVERY (fun k ->
      X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_EXEC [k] THEN
      SIMD_SIMPLIFY_TAC[]) (1--60) THEN
    FIRST_X_ASSUM(MP_TAC o CONV_RULE(READ_MEMORY_SPLIT_CONV 2) o
      check (can (term_match [] `read (memory :> bytes64 a) s = x`) o
             concl)) THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC
      (map2 D10_LANE_RULE (0--3) (CONJUNCTS th))) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[XMM3; XMM4; READ_ZEROTOP_128] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`] THEN
      CONV_TAC WORD_RULE;
      REWRITE_TAC[ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN
      CONV_TAC WORD_RULE;
      CONV_TAC WORD_BLAST;
      CONV_TAC WORD_BLAST;
      ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE
     `j < 4 * (i + 1) <=>
      j < 4 * i \/ j = 4 * i \/ j = 4 * i + 1 \/ j = 4 * i + 2 \/
      j = 4 * i + 3`] THEN
    REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
                FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `2 * 4 * i = 8 * i`;
                ARITH_RULE `2 * (4 * i + 1) = 8 * i + 2`;
                ARITH_RULE `2 * (4 * i + 2) = 8 * i + 4`;
                ARITH_RULE `2 * (4 * i + 3) = 8 * i + 6`] THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "w" THEN
    MAP_EVERY (fun k ->
      MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV)
       (MP (SPECL [`n:num`; `i:num`; mk_small_numeral k] D10_FIELD)
           (EQT_ELIM(NUM_LT_CONV(mk_binop `(<):num->num->bool`
                          (mk_small_numeral k) `4`))))) THEN
      DISCH_THEN SUBST1_TAC) (0--3) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word_add a (word (5 * i)))
                     (word_add a (word 320)):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[WORD_RULE
       `word_sub (word_add a x) (word_add a y):int64 = word_sub x y`] THEN
      REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 64 ==> 5 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 64` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_EXEC (1--2) THEN
    PTR_DECIDE_RIP_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `bytes16` (concl th)))]);;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_CORRECT);;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_SAFE = time prove
 (MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_SAFE_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num).
      APPEND
        (f_ev_epil a r pc)
        (APPEND
          (ENUMERATEL 64 (\i. f_ev_loop a r pc i))
          (f_ev_prol a r pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `64` `pc + mlkem_poly_decompress_d10_loop1` `pc + mlkem_poly_decompress_d10_loop1_exit`
    `\i s. read RDX s = word_add a (word(5 * i)) /\
           read RCX s = word_add r (word(8 * i)) /\
           read RSI s = word_add a (word 320)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_EXEC (1--6) THEN
    REWRITE_TAC[MULT_0; WORD_ADD_0; WORD_VAL_ADD_64] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_ADD_CONV) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_EXEC (1--0) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_EXEC (1--62) THEN
  SUBGOAL_THEN
   `~(val(word_add (word_add a (word (5 * i))) (word 5):int64) =
      val(word_add a (word 320):int64)) <=> i + 1 < 64`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_EQ; GSYM WORD_ADD_ASSOC; WORD_ADD_LCANCEL_EQ] THEN
    REWRITE_TAC[GSYM WORD_ADD; WORD_EQ; DIMINDEX_64; CONG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 64 ==> 5 * i + 5 < 18446744073709551616`] THEN
    UNDISCH_TAC `i < 64` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `5 * (i + 1) = 5 * i + 5`;
                ARITH_RULE `8 * (i + 1) = 8 * i + 8`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_DECOMPRESS_D10_GCC12_O2_IMAGE_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
