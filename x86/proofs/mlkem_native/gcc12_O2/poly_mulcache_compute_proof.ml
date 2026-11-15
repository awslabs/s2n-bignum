(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/gcc12_O2/poly_mulcache_compute_spec.ml";;


let MLK_ZETAS_MULCACHE = prove
 (MLK_ZETAS_MULCACHE_STMT,
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[mlk_zetas] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN
  REWRITE_TAC[BITREVERSE7_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

let MLK_ZETAS_MULCACHE_IVAL = prove
 (MLK_ZETAS_MULCACHE_IVAL_STMT,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MLK_ZETAS_MULCACHE) THEN
  SUBGOAL_THEN
   `ival(iword(EL (64 + i) mlk_zetas):int16) = EL (64 + i) mlk_zetas`
  SUBST1_TAC THENL [MATCH_MP_TAC IVAL_IWORD; ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_16] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;

let WORD_ZX_NEG_SX = prove
 (WORD_ZX_NEG_SX_STMT,
  BITBLAST_TAC);;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_CORRECT = prove
 (MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`dst:int64`; `src:int64`; `zetas:num`; `x:num->int16`; `pc:num`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The loop invariant, with the loop test as a separate step ***)

  ENSURES_WHILE_UP_TAC `64` `pc + poly_mulcache_compute_loop1` `pc + poly_mulcache_compute_loop1_test`
   `\i s. read RCX s = word(2 * i) /\
          read R8 s = word(zetas + 128) /\
          read RSI s = src /\ read RDI s = dst /\
          (!k. k < 128
               ==> read(memory :> bytes16(word_add (word zetas)
                                                   (word(2 * k)))) s =
                   iword(EL k mlk_zetas)) /\
          (!i. i < 256
                ==> read(memory :> bytes16(word_add src (word (2 * i)))) s =
                    x i) /\
          (!j. j < 2 * i
               ==> let z_j = read(memory :> bytes16
                                (word_add dst (word (2 * j)))) s in
                   (ival z_j == (mulcache (ival o x)) j) (mod &3329) /\
                   abs(ival z_j) <= &3328)` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, including the address of the table ***)

    ENSURES_INIT_TAC "s0" THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP MLK_ZETAS_LOADED) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--3) THEN
    MP_TAC(CONJUNCT1(CONJUNCT2(SPECL [`pc:num`; `9`; `119`; `zetas:num`]
      RIP_REL_ADDR_FOLD))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; CONJUNCT1 LT; WORD_ADD_0];

    (*** The loop body, computing two output coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    VAL_INT64_TAC `2 * i` THEN
    READ_INSTANCE_TAC
     `read (memory :> bytes16
             (word_add (word (zetas + 128)) (word (1 * 2 * i)))) s0 =
      iword(EL (64 + i) mlk_zetas)` THEN
    READ_INSTANCE_TAC
     `read (memory :> bytes16 (word_add src (word (4 * 2 * i + 2)))) s0 =
      x(4 * i + 1)` THEN
    READ_INSTANCE_TAC
     `read (memory :> bytes16 (word_add src (word (4 * 2 * i + 6)))) s0 =
      x(4 * i + 3)` THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--21) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC]) THEN
    X_GEN_TAC `j:num` THEN
    REWRITE_TAC[ARITH_RULE
     `j < 2 * (i + 1) <=> j < 2 * i \/ j = 2 * i \/ j = 2 * i + 1`] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check
       (fun th -> is_forall(concl th) &&
                  can (find_term (fun t -> try fst(dest_const t) = "mulcache"
                                           with _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC; ALL_TAC] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `2 * (2 * i + 1) = 2 * 2 * i + 2`] THEN
    ASM_REWRITE_TAC[] THEN MLKEM_NATIVE_WORD_SIMP_TAC THEN
    REWRITE_TAC[WORD_ZX_NEG_SX] THEN
    REWRITE_TAC[GSYM montred_x86; MONTRED_X86_SCALAR] THEN
    MULCACHE_OUTPUT_TAC;

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN
     `~(val(word_sub (word(2 * i)) (word 128):int64) = 0)`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 64 ==> 2 * i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 64` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                can (find_term (fun t -> try fst(dest_const t) = "mulcache"
                                         with _ -> false)) (concl th)))]);;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_CORRECT_STMT,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_CORRECT);;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SAFE = time prove
 (MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SAFE_STMT,
  ASSERT_CONCL_TAC full_spec THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(src:int64) (dst:int64) (zetas:num) (pc:num).
      APPEND
        (f_ev_epil src dst zetas pc)
        (APPEND
          (ENUMERATEL 64 (\i. f_ev_loop src dst zetas pc i))
          (f_ev_prol src dst zetas pc))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; ALL;
              fst MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `64` `pc + poly_mulcache_compute_loop1` `pc + poly_mulcache_compute_loop1_exit`
    `\i s. read RCX s = word(2 * i) /\
           read R8 s = word(zetas + 128) /\
           read RSI s = src /\ read RDI s = dst` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_INIT_TAC "s0" THEN
    TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--3) THEN
    MP_TAC(CONJUNCT1(CONJUNCT2(SPECL [`pc:num`; `9`; `119`; `zetas:num`]
      RIP_REL_ADDR_FOLD))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--0) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN VAL_INT64_TAC `2 * i` THEN
  X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
    ~canonicalize_pc_diff:false
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC (1--23) THEN
  SUBGOAL_THEN
   `~(val(word_add (word(2 * i)) (word 18446744073709551490):int64) = 0) <=>
    i + 1 < 64`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOD_LT; ARITH_RULE
     `i < 64 ==> 2 * i < 18446744073709551616`] THEN
    ASM_CASES_TAC `i = 63` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOD_LT o
      lhand o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `i < 64` THEN UNDISCH_TAC `~(i = 63)` THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    UNDISCH_TAC `i < 64` THEN UNDISCH_TAC `~(i = 63)` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 * (i + 1) = 2 * i + 2`] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC]) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_SAFE_STMT,
  X86_ADD_RETURN_NOSTACK_TAC MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_EXEC
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SAFE THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MLKEM_NATIVE_IMAGE_TAC
   (INST [`pc + mlkem_poly_mulcache_compute`,`pc:num`; `pc + rodata_mlk_zetas`,`zetas:num`]
     (SPEC_ALL MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_CORRECT))
   [MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IN_IMAGE;
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_ZETAS_IN_IMAGE]);;

let MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  MLKEM_NATIVE_IMAGE_SAFE_TAC
   MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_SUBROUTINE_SAFE
   [`pc + mlkem_poly_mulcache_compute`,`pc:num`; `pc + rodata_mlk_zetas`,`zetas:num`]
   [MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_IN_IMAGE;
    MLKEM_NATIVE_POLY_MULCACHE_COMPUTE_GCC12_O2_ZETAS_IN_IMAGE]);;
