(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_Os/keccak_squeezeblocks_x4_spec.ml";;


let MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_OS_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_OS_IMAGE_SUBROUTINE_FULL
    "H_EXTRACT" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(out0:int64) (out1:int64) (out2:int64) (out3:int64) (nblocks:num)
      (st:int64) (r:num) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      if nblocks = 0
      then f_ev_zero out0 out1 out2 out3 nblocks st r pc stackpointer
                     returnaddress
      else APPEND (f_ev_epil out0 out1 out2 out3 nblocks st r pc stackpointer
                             returnaddress)
            (APPEND
              (ENUMERATEL nblocks
                (\i. f_ev_loop out0 out1 out2 out3 nblocks st r pc
                               stackpointer returnaddress i))
              (f_ev_prol out0 out1 out2 out3 nblocks st r pc stackpointer
                         returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600;
              fst MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  KSQX4_BOUND_TAC THEN KSQX4_PRESERVED_TAC THEN
  ASM_CASES_TAC `nblocks = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_EXEC
     (1--21) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `nblocks:num`
   `pc + 9704` `pc + mlk_keccak_squeezeblocks_x4_loop1_exit`
   `\i s. read X19 s = word(r * i) /\ read X20 s = word(nblocks - i) /\
          read X21 s = st /\ read X22 s = word r /\
          read X23 s = out0 /\ read X24 s = out1 /\
          read X25 s = out2 /\ read X26 s = out3 /\ read X27 s = word r /\
          read SP s = word_add stackpointer (word 240) /\
          read (memory :> bytes64 (word_add stackpointer (word 240))) s =
          x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 248))) s =
          x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 256))) s =
          x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 264))) s =
          x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 272))) s =
          x23_init /\
          read (memory :> bytes64 (word_add stackpointer (word 280))) s =
          x24_init /\
          read (memory :> bytes64 (word_add stackpointer (word 288))) s =
          x25_init /\
          read (memory :> bytes64 (word_add stackpointer (word 296))) s =
          x26_init /\
          read (memory :> bytes64 (word_add stackpointer (word 304))) s =
          x27_init /\
          read (memory :> bytes64 (word_add stackpointer (word 312))) s =
          returnaddress /\
          read (memory :> bytes(out0,r * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * r * j) *
                val(keccak_squeeze (j + 1) S0) MOD 2 EXP (8 * r)) /\
          read (memory :> bytes(out1,r * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * r * j) *
                val(keccak_squeeze (j + 1) S1) MOD 2 EXP (8 * r)) /\
          read (memory :> bytes(out2,r * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * r * j) *
                val(keccak_squeeze (j + 1) S2) MOD 2 EXP (8 * r)) /\
          read (memory :> bytes(out3,r * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * r * j) *
                val(keccak_squeeze (j + 1) S3) MOD 2 EXP (8 * r)) /\
          read (memory :> bytes(st,200)) s =
          val(keccak_squeeze i (S0:1600 word)) /\
          read (memory :> bytes(word_add st (word 200),200)) s =
          val(keccak_squeeze i (S1:1600 word)) /\
          read (memory :> bytes(word_add st (word 400),200)) s =
          val(keccak_squeeze i (S2:1600 word)) /\
          read (memory :> bytes(word_add st (word 600),200)) s =
          val(keccak_squeeze i (S3:1600 word))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_EXEC
     (1--14) THEN
    KSQX4_NONZERO_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_EXEC
     (15--15) THEN
    ARGS_32_TAC [`r:num`] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `r * i + r <= r * nblocks` ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `r * i + r = r * (i + 1)`; LE_MULT_LCANCEL] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `0 + r <= 200` ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_EXEC
     (1--2) THEN
    KSQX4_STATES_TAC THEN
    KSQX4_CS_CALL_TAC "H_PERMUTE"
     [`e:(uarch_event)list`; `read X0 s`; `keccak_squeeze i (S0:1600 word)`;
      `keccak_squeeze i (S1:1600 word)`; `keccak_squeeze i (S2:1600 word)`;
      `keccak_squeeze i (S3:1600 word)`; `pc:num`; `read SP s`;
      `read X30 s`] 3 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_EXEC
     (4--13) THEN
    ARGS_32_TAC [`r:num`] THEN
    KSQX4_STATES_TAC THEN
    KSQX4_CS_CALL_TAC "H_EXTRACT"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
      `read X3 s`; `read X4 s`; `0`; `r:num`;
      `keccak_f1600(keccak_squeeze i (S0:1600 word))`;
      `keccak_f1600(keccak_squeeze i (S1:1600 word))`;
      `keccak_f1600(keccak_squeeze i (S2:1600 word))`;
      `keccak_f1600(keccak_squeeze i (S3:1600 word))`; `pc:num`;
      `read SP s`; `read X30 s`] 14 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_EXEC
     (15--16) THEN
    KSQX4_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [KSQX4_PTR_STEP_TAC; ALL_TAC] THEN
    MAP_EVERY (fun _ -> CONJ_TAC THENL [KSQX4_BYTES_STEP_TAC; ALL_TAC])
     (1--4) THEN
    MAP_EVERY (fun _ -> CONJ_TAC THENL
      [REWRITE_TAC[GSYM ADD1; keccak_squeeze]; ALL_TAC]) (1--4) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_EXEC
     (1--6) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let ENSURES_PREPOST_WEAKEN = MESON[ENSURES_PREPOSTCONDITION_THM]
 `ensures step P Q C
  ==> (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x)
      ==> ensures step P' Q' C`;;

let MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  X_CHOOSE_TAC
   `f:int64->int64->int64->int64->num->int64->num->num->int64->int64->
      (uarch_event)list`
   MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_FULL THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `out0:int64`; `out1:int64`; `out2:int64`;
    `out3:int64`; `nblocks:num`; `st:int64`; `r:num`; `S0:1600 word`;
    `S1:1600 word`; `S2:1600 word`; `S3:1600 word`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  MP_TAC MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_OS_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GHOST_INTRO_TAC `S0:1600 word`
   `read (memory :> wbytes st):armstate->1600 word` THEN
  GHOST_INTRO_TAC `S1:1600 word`
   `read (memory :> wbytes (word_add st (word 200))):armstate->1600 word` THEN
  GHOST_INTRO_TAC `S2:1600 word`
   `read (memory :> wbytes (word_add st (word 400))):armstate->1600 word` THEN
  GHOST_INTRO_TAC `S3:1600 word`
   `read (memory :> wbytes (word_add st (word 600))):armstate->1600 word` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `out0:int64`; `out1:int64`; `out2:int64`;
    `out3:int64`; `nblocks:num`; `st:int64`; `r:num`; `S0:1600 word`;
    `S1:1600 word`; `S2:1600 word`; `S3:1600 word`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_PREPOST_WEAKEN) THEN
  SIMP_TAC[]);;
