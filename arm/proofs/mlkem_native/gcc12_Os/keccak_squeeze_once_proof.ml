(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_Os/keccak_squeeze_once_spec.ml";;


let SQUEEZE_ONCE_BLOCK = prove
 (SQUEEZE_ONCE_BLOCK_STMT,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n <= 200` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `num_of_bytelist(list_of_seq
    (\j. word_subword (keccak_squeeze (k + 1) (S:1600 word)) (8 * j,8):byte)
    n)` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC LIST_OF_SEQ_EQ THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(r * k + j) DIV r = k /\ (r * k + j) MOD r = j`
     (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `j:num` THEN ASM_ARITH_TAC;
        MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `k:num` THEN ASM_ARITH_TAC];
      REFL_TAC];
    MATCH_MP_TAC NUM_OF_BYTELIST_STATE_BYTES THEN ASM_REWRITE_TAC[]]);;

let SQUEEZE_ONCE_CSEL = prove
 (SQUEEZE_ONCE_CSEL_STMT,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
  ASM_SIMP_TAC[MOD_LT] THEN REWRITE_TAC[MIN] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let SQUEEZE_ONCE_LT = prove
 (`!outlen r i.
        0 < r ==> (i < (outlen + r - 1) DIV r <=> r * i < outlen)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `i < q <=> i + 1 <= q`] THEN
  ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_ARITH_TAC);;

let SQUEEZE_ONCE_ITER = prove
 (SQUEEZE_ONCE_ITER_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `r * i < outlen` ASSUME_TAC THENL
   [ASM_MESON_TAC[SQUEEZE_ONCE_LT]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  REWRITE_TAC[MIN] THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let SQUEEZE_ONCE_END = prove
 (SQUEEZE_ONCE_END_STMT,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`outlen + r - 1`; `r:num`] DIVISION) THEN
  ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`] THEN
  REWRITE_TAC[MIN] THEN STRIP_TAC THEN COND_CASES_TAC THEN ASM_ARITH_TAC);;

let SQUEEZE_ONCE_TEST = prove
 (SQUEEZE_ONCE_TEST_STMT,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SQUEEZE_ONCE_LT] THEN REWRITE_TAC[MIN] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

let MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600_EXTRACT_BYTES_GCC12_OS_IMAGE_SUBROUTINE_FULL
    "H_EXTRACT" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(out:int64) (outlen:num) (st:int64) (r:num) (pc:num)
      (stackpointer:int64) (returnaddress:int64).
      if outlen = 0
      then f_ev_zero out outlen st r pc stackpointer returnaddress
      else APPEND (f_ev_epil out outlen st r pc stackpointer returnaddress)
            (APPEND
              (ENUMERATEL ((outlen + r - 1) DIV r)
                (\i. f_ev_loop out outlen st r pc stackpointer
                               returnaddress i))
              (f_ev_prol out outlen st r pc stackpointer returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600;
              fst MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SQONCE_BOUND_TAC THEN SQONCE_PRESERVED_TAC THEN
  ASM_CASES_TAC `outlen = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_EXEC (1--12) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(0 + r - 1) DIV r = 0` SUBST1_TAC THENL
     [MATCH_MP_TAC DIV_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[list_of_seq; num_of_bytelist; READ_MEMORY_BYTES_TRIVIAL;
                keccak_squeeze] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `(outlen + r - 1) DIV r`
   `pc + 8996` `pc + mlk_keccak_squeeze_once_loop1_exit`
   `\i s. read X19 s = word(outlen - MIN outlen (r * i)) /\
          read X20 s = word_add out (word(MIN outlen (r * i))) /\
          read X21 s = st /\ read X22 s = word r /\
          read SP s = word_add stackpointer (word 224) /\
          read (memory :> bytes64 (word_add stackpointer (word 224))) s =
          x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 232))) s =
          x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 240))) s =
          x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 248))) s =
          x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 256))) s =
          x23_init /\
          read (memory :> bytes64 (word_add stackpointer (word 264))) s =
          returnaddress /\
          read (memory :> bytes(out,MIN outlen (r * i))) s =
          num_of_bytelist
           (list_of_seq
             (\j. word_subword (keccak_squeeze (j DIV r + 1) (S:1600 word))
                               (8 * (j MOD r),8):byte)
             (MIN outlen (r * i))) /\
          read (memory :> bytes(st,200)) s = val(keccak_squeeze i S)` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`outlen:num`; `r:num`; `0`] SQUEEZE_ONCE_LT) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC;

    (*** The start of the function up to the loop ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_EXEC (1--7) THEN
    ARGS_32_TAC [`r:num`] THEN SQONCE_NONZERO_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_EXEC (8--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `MIN outlen 0 = 0`; SUB_0;
                WORD_ADD_0; list_of_seq; num_of_bytelist;
                READ_MEMORY_BYTES_TRIVIAL; keccak_squeeze] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body: permute and extract the first min(r, left) bytes ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    MP_TAC(SPECL [`outlen:num`; `r:num`; `i:num`] SQUEEZE_ONCE_ITER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `MIN outlen (r * i) = r * i`]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_EXEC (1--2) THEN
    KECCAK_STATE_AT_TAC `st:int64` THEN
    SQONCE_CS_CALL_TAC "H_PERMUTE"
     [`e:(uarch_event)list`; `read X0 s`; `keccak_squeeze i (S:1600 word)`;
      `pc:num`; `read SP s`; `read X30 s`] 3 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_EXEC (4--6) THEN
    MP_TAC(SPECL [`r:num`; `outlen - r * i`] SQUEEZE_ONCE_CSEL) THEN
    ANTS_TAC THENL [CONJ_TAC THEN SIMPLE_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    SUBGOAL_THEN `0 + MIN r (outlen - r * i) <= 200` ASSUME_TAC THENL
     [REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_EXEC (7--12) THEN
    ARGS_32_TAC [`MIN r (outlen - r * i)`] THEN
    KECCAK_STATE_AT_TAC `st:int64` THEN
    SQONCE_CS_CALL_TAC "H_EXTRACT"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `0`;
      `MIN r (outlen - r * i)`;
      `keccak_f1600(keccak_squeeze i (S:1600 word))`;
      `pc:num`; `read X30 s`] 13 THEN
    SUBGOAL_THEN `word_sub (word (outlen - r * i))
                    (word (MIN r (outlen - r * i))):int64 =
                  word(outlen - r * i - MIN r (outlen - r * i))`
    SUBST_ALL_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
      ANTS_TAC THENL [REWRITE_TAC[MIN] THEN COND_CASES_TAC THEN
                      SIMPLE_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      REFL_TAC;
      ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_EXEC (14--15) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `val(word(outlen - (r * i + MIN r (outlen - r * i))):int64) =
                  outlen - (r * i + MIN r (outlen - r * i))` ASSUME_TAC THENL
     [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
      CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(outlen - (r * i + MIN r (outlen - r * i)) = 0) <=>
                  ~(i + 1 < (outlen + r - 1) DIV r)` ASSUME_TAC THENL
     [MP_TAC(SPECL [`outlen:num`; `r:num`; `i:num`] SQUEEZE_ONCE_TEST) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[NUM_OF_BYTELIST_LIST_OF_SEQ_ADD] THEN BETA_TAC THEN
      MP_TAC(SPECL [`S:1600 word`; `r:num`; `i:num`;
                    `MIN r (outlen - r * i)`] SQUEEZE_ONCE_BLOCK) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL [REWRITE_TAC[ARITH_RULE `MIN r x <= r`]; ALL_TAC] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
      REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM ADD1; keccak_squeeze; MULT_CLAUSES; EXP; DIV_1];
      ALL_TAC] THEN
    CONJ_TAC THENL [REWRITE_TAC[GSYM ADD1; keccak_squeeze]; ALL_TAC] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop exit ***)

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_EXEC (1--4) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MP (SPECL [`outlen:num`; `r:num`]
                                     SQUEEZE_ONCE_END) (ASSUME `0 < r`)]) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let ENSURES_PREPOST_WEAKEN = MESON[ENSURES_PREPOSTCONDITION_THM]
 `ensures step P Q C
  ==> (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x)
      ==> ensures step P' Q' C`;;

let MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  X_CHOOSE_TAC
   `f:int64->num->int64->num->num->int64->int64->(uarch_event)list`
   MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_IMAGE_SUBROUTINE_FULL THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `out:int64`; `outlen:num`; `st:int64`; `r:num`;
    `S:1600 word`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  MP_TAC MLKEM_NATIVE_KECCAK_SQUEEZE_ONCE_GCC12_OS_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `S:1600 word`
   `read (memory :> wbytes st):armstate->1600 word` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `out:int64`; `outlen:num`; `st:int64`; `r:num`;
    `S:1600 word`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;
