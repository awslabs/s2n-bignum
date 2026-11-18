(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/gcc12_O2/keccak_absorb_once_x4_spec.ml";;


let READ_MEMORY_BYTES_ZERO_SPLIT = prove
 (READ_MEMORY_BYTES_ZERO_SPLIT_STMT,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ]);;

let BYTES800_ZERO = prove
 (BYTES800_ZERO_STMT,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `800 = 200 + 600`; READ_MEMORY_BYTES_ZERO_SPLIT] THEN
  REWRITE_TAC[ARITH_RULE `600 = 200 + 400`; READ_MEMORY_BYTES_ZERO_SPLIT] THEN
  REWRITE_TAC[ARITH_RULE `400 = 200 + 200`; READ_MEMORY_BYTES_ZERO_SPLIT] THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_FULL = time prove
 (MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  ABSX4_CS_INTRO_TAC THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlk_keccak_absorb_once_x4_loop1_exit` ABSX4_CS_MID THEN CONJ_TAC THENL
   [ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THENL
     [ABSX4_CS_SHORT_TAC; ABSX4_CS_LOOP_TAC];
    ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THEN
    ABSX4_CS_TAIL_TAC]);;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  MP_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_FULL THEN
  DISCH_THEN(CHOOSE_THEN (MP_TAC o SPECL
   [`e:(uarch_event)list`; `st:int64`; `r:num`; `m0:int64`; `m1:int64`;
    `m2:int64`; `m3:int64`; `mlen:num`; `M0:num`; `M1:num`; `M2:num`;
    `M3:num`; `pc:num`; `stackpointer:int64`; `returnaddress:int64`])) THEN
  ANTS_TAC THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[ALLPAIRS; ALL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_RULE) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_XOR_BYTES_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_XOR" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_SAFE
    "H_PERMUTE" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(m0:int64) (m1:int64) (m2:int64) (m3:int64) (st:int64) (r:num)
      (mlen:num) (pc:num) (stackpointer:int64) (returnaddress:int64).
      APPEND
       (if mlen MOD r = 0
        then f_ev_t0 m0 m1 m2 m3 st r mlen pc stackpointer returnaddress
        else if mlen MOD r = r - 1
        then f_ev_t1 m0 m1 m2 m3 st r mlen pc stackpointer returnaddress
        else f_ev_t2 m0 m1 m2 m3 st r mlen pc stackpointer returnaddress)
       (if mlen < r
        then f_ev_short m0 m1 m2 m3 st r mlen pc stackpointer returnaddress
        else APPEND
              (f_ev_epil m0 m1 m2 m3 st r mlen pc stackpointer returnaddress)
              (APPEND
                (ENUMERATEL (mlen DIV r)
                  (\i. f_ev_loop m0 m1 m2 m3 st r mlen pc stackpointer
                                 returnaddress i))
                (f_ev_prol m0 m1 m2 m3 st r mlen pc stackpointer
                           returnaddress)))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`st:int64`; `r:num`; `m0:int64`; `m1:int64`; `m2:int64`; `m3:int64`;
    `mlen:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 384 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `800 + mlen <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(m0:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  ENSURES_EVENTS_SEQUENCE_TAC `pc + mlk_keccak_absorb_once_x4_loop1_exit` ABSX4_SAFE_MID THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THENL
     [(*** A message shorter than a block, with no loop ***)

      REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
      X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
       (1--16) THEN
      ARGS_32_TAC [`r:num`] THEN ABSORB_VAL_TAC THEN
      X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
       (17--18) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[DIV_LT; MOD_LT; MULT_CLAUSES; WORD_ADD_0] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;
      ALL_TAC] THEN

    (*** Otherwise the loop over the whole blocks ***)

    ENSURES_EVENTS_WHILE_UP2_TAC `mlen DIV r` `pc + mlk_keccak_absorb_once_x4_loop1` `pc + mlk_keccak_absorb_once_x4_loop1_exit`
      ABSX4_SAFE_INV THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[DIV_EQ_0; ARITH_RULE `0 < r ==> ~(r = 0)`];

      REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
      X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
       (1--16) THEN
      ARGS_32_TAC [`r:num`] THEN ABSORB_VAL_TAC THEN
      X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
       (17--19) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;

      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
      MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_BLOCK_BOUND) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `0 + r <= 200` ASSUME_TAC THENL
       [SIMPLE_ARITH_TAC; ALL_TAC] THEN
      X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
       (1--14) THEN
      ARGS_32_TAC [`r:num`] THEN
      ABSX4_SAFE_XOR_TAC `0` `r:num`
        (ABSX4_SAFE_VARS @ [`i:num`]) 15 THEN
      X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
       (16--17) THEN
      ABSX4_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read RDI s`; `pc:num`; `read RSP s`;
         `read (memory :> bytes64(read RSP s)) s`]
        (ABSX4_SAFE_VARS @ [`i:num`]) 18 THEN
      SUBGOAL_THEN `word_sub (word (mlen - r * i)) (word r):int64 =
                    word(mlen - r * (i + 1))` SUBST_ALL_TAC THENL
       [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
        ANTS_TAC THENL [UNDISCH_TAC `r * i + r <= mlen` THEN ARITH_TAC;
                        DISCH_THEN SUBST1_TAC] THEN
        AP_TERM_TAC THEN ARITH_TAC;
        ALL_TAC] THEN
      X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC
       (19--23) THEN
      SUBGOAL_THEN
       `val(word(mlen - r * (i + 1)):int64) = mlen - r * (i + 1) /\
        val(word r:int64) = r`
       (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [CONJ_TAC THEN MATCH_MP_TAC VAL_WORD_EQ THEN
        REWRITE_TAC[DIMINDEX_64] THEN
        CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
        ALL_TAC] THEN
      X86_STEPS_TAC MLKEM_NATIVE_KECCAK_ABSORB_ONCE_X4_GCC12_O2_EXEC [24] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`mlen:num`; `r:num`; `i:num`] ABSORB_LOOP_TEST) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
      MAP_EVERY (fun _ -> CONJ_TAC THENL
       [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`];
        ALL_TAC]) (1--4) THEN
      DISCHARGE_SAFETY_PROPERTY_TAC;

      REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ABSORB_MOD_EQ] THEN
      DISCHARGE_SAFETY_PROPERTY_TAC];

    (*** The last block ***)

    ASM_CASES_TAC `mlen < r` THEN ASM_REWRITE_TAC[] THEN
    ABSX4_SAFE_TAIL_TAC]);;
