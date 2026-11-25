(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The start of CompressFragmentDoubleHash: the prologue (x29, x30, x19 and  *)
(* x20 saved in the 48-byte frame, x29 = sp), ip_end, and for 15 bytes or    *)
(* more the constants of the main loop (mask, ip_limit, the two multipliers) *)
(* up to loop1; for less, join2 with ip = 0. Both with the initial state of  *)
(* the model: no output, the tables zero.                                    *)
(* ========================================================================= *)

needs "arm/proofs/snappy/gcc12_O2/compress_fragment_double_hash_init_spec.ml";;

(* The mask 2 * (ts - 1), as sub w4, w4, #1; lsl w9, w4, #1 computes it.  *)

let SNAPPY_CF2_ZX32 = prove
 (`!k. k < 2 EXP 32 ==> word_zx (word k:int64):int32 = word k /\
                        word_zx (word k:int32):int64 = word k`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_ZX_GEN; VAL_WORD; DIMINDEX_32;
              DIMINDEX_64] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[MOD_LT; ARITH_RULE `k < 4294967296 ==> k < 18446744073709551616`]);;

let SNAPPY_CF2_MASK_WORD = prove
 (`!t. 1 <= t /\ t <= 16384
       ==> word_zx (word_shl (word_sub (word_zx (word t:int64):int32)
                                       (word 1)) 1):int64 =
           word (2 * (t - 1))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SNAPPY_CF2_ZX32; ARITH_RULE `t <= 16384 ==> t < 2 EXP 32`] THEN
  SUBGOAL_THEN `word_sub (word t) (word 1):int32 = word(t - 1)` SUBST1_TAC
  THENL [ASM_SIMP_TAC[WORD_SUB]; ALL_TAC] THEN
  REWRITE_TAC[WORD_SHL_WORD; EXP_1] THEN
  MP_TAC(SPEC `2 * (t - 1)` SNAPPY_CF2_ZX32) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]);;

(* The target: the initial state of the model at a point.                    *)

let CF2_INIT_TARGET_TAC (pt:term) (st:term) =
  MAP_EVERY EXISTS_TAC [pt; st] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(SPEC `src:byte list` SNAPPY_CF2_REACH_INIT) THEN
    REWRITE_TAC[snappy_cf2_init] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    REWRITE_TAC[snappy_cf2_point] THEN CONV_TAC NUM_REDUCE_CONV;
    REWRITE_TAC[snappy_cf2_at; snappy_cf2_regs; snappy_phase; snappy_ip;
                snappy_ne; snappy_skip; snappy_cand; snappy_aux; snappy_t1;
                snappy_t2; snappy_out; LENGTH; SNAPPY_TVAL_ZERO;
                num_of_bytelist] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_COMPONENT_COMPOSE]) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN
    REPEAT CONJ_TAC THEN
    TRY(REWRITE_TAC[snappy_cf2_events] THEN MEMSAFE_EVENTS_TAC THEN NO_TAC) THEN
    TRY CF2_ARITH_TAC THEN TRY CF2_WORD_EQ_TAC THEN
    MATCH_MP_TAC SNAPPY_CF2_MASK_WORD THEN
    MP_TAC(SPEC `LENGTH(src:byte list)` SNAPPY_POW2_TABLE_SIZE) THEN ARITH_TAC];;

let SNAPPY_CF2_GCC12_O2_INIT = prove
 (SNAPPY_CF2_GCC12_O2_INIT_STMT,
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALLPAIRS; ALL; NONOVERLAPPING_CLAUSES] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  CF2_TS_TAC THEN ENSURES_INIT_TAC "s0" THEN
  ARM_BSTEP_TAC SNAPPY_CF2_GCC12_O2_EXEC (1--6) THEN
  CF2_BRANCH_TAC `LENGTH(src:byte list) < 15` THENL
   [ARM_BSTEP_TAC SNAPPY_CF2_GCC12_O2_EXEC (7--9) THEN BSTEP_FINAL_TAC THEN
    CF2_INIT_TARGET_TAC `CompressFragmentDoubleHash_join2:num`
     `SnappyCState 5 0 0 0 0 0 (\j. 0) (\j. 0) []`;
    ARM_BSTEP_TAC SNAPPY_CF2_GCC12_O2_EXEC (7--17) THEN BSTEP_FINAL_TAC THEN
    CF2_INIT_TARGET_TAC `CompressFragmentDoubleHash_loop1:num`
     `SnappyCState 1 0 0 0 0 0 (\j. 0) (\j. 0) []`]);;
