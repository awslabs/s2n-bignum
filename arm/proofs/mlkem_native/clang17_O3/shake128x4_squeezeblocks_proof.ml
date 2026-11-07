(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/clang17_O3/shake128x4_squeezeblocks_spec.ml";;


let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`; `nblocks:num`;
    `st:int64`; `S0:1600 word`; `S1:1600 word`; `S2:1600 word`;
    `S3:1600 word`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 288 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** The case nblocks = 0, where nothing is done ***)

  ASM_CASES_TAC `nblocks = 0` THENL
   [ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze];
    ALL_TAC] THEN
  SQX4_BOUND_TAC THEN SQX4_PRESERVED_TAC THEN

  (*** The loop, with i blocks done ***)

  ENSURES_WHILE_UP2_TAC `nblocks:num`
   `pc + mlkem_shake128x4_squeezeblocks_loop1`
   `pc + mlkem_shake128x4_squeezeblocks_loop1_exit`
   `\i s. read X21 s = word_add out3 (word(168 * i)) /\
          read X22 s = word_add out2 (word(168 * i)) /\
          read X23 s = word_add out1 (word(168 * i)) /\
          read X24 s = word_add out0 (word(168 * i)) /\
          read X20 s = word(nblocks - i) /\
          read X19 s = st /\
          read SP s = word_add stackpointer (word 224) /\
          read (memory :> bytes64 (word_add stackpointer (word 224))) s =
          returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 240))) s =
          x24_init /\
          read (memory :> bytes64 (word_add stackpointer (word 248))) s =
          x23_init /\
          read (memory :> bytes64 (word_add stackpointer (word 256))) s =
          x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 264))) s =
          x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 272))) s =
          x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 280))) s =
          x19_init /\
          read (memory :> bytes(out0,168 * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * 168 * j) *
                val(keccak_squeeze (j + 1) S0) MOD 2 EXP (8 * 168)) /\
          read (memory :> bytes(out1,168 * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * 168 * j) *
                val(keccak_squeeze (j + 1) S1) MOD 2 EXP (8 * 168)) /\
          read (memory :> bytes(out2,168 * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * 168 * j) *
                val(keccak_squeeze (j + 1) S2) MOD 2 EXP (8 * 168)) /\
          read (memory :> bytes(out3,168 * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * 168 * j) *
                val(keccak_squeeze (j + 1) S3) MOD 2 EXP (8 * 168)) /\
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

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (1--1) THEN
    SQX4_NONZERO_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (2--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze];

    (*** The loop body: permute, extract a block of each, the loop test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `168 * i + 168 <= 168 * nblocks` ASSUME_TAC THENL
     [UNDISCH_TAC `i < nblocks` THEN ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (1--2) THEN
    SQX4_STATES_TAC THEN
    ARM_SUBROUTINE_SIM_TAC
     (mlkem_native_libmlkem_clang17_O3_mc,
      MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC,
      0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT_F1600)
     [`read X0 s`; `keccak_squeeze i (S0:1600 word)`;
      `keccak_squeeze i (S1:1600 word)`; `keccak_squeeze i (S2:1600 word)`;
      `keccak_squeeze i (S3:1600 word)`; `pc:num`; `read SP s`;
      `read X30 s`] 3 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (4--11) THEN
    SQX4_STATES_TAC THEN
    ARM_SUBROUTINE_SIM_TAC
     (mlkem_native_libmlkem_clang17_O3_mc,
      MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC,
      0x0,mlkem_native_libmlkem_clang17_O3_mc,
    MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_CORRECT)
     [`read X0 s`; `read X1 s`; `read X2 s`; `read X3 s`; `read X4 s`; `0`;
      `168`; `keccak_f1600(keccak_squeeze i (S0:1600 word))`;
      `keccak_f1600(keccak_squeeze i (S1:1600 word))`;
      `keccak_f1600(keccak_squeeze i (S2:1600 word))`;
      `keccak_f1600(keccak_squeeze i (S3:1600 word))`; `pc:num`;
      `read X30 s`] 12 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (13--18) THEN
    SQX4_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        REWRITE_TAC[ARITH_RULE `168 * (i + 1) = 168 * i + 168`] THEN
        NO_TAC) THEN
    TRY(REWRITE_TAC[GSYM ADD1; keccak_squeeze] THEN NO_TAC) THEN
    REWRITE_TAC[ARITH_RULE `168 * (i + 1) = 168 * i + 168`] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
    REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM ADD1; NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
    REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1];

    (*** The return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_IMAGE_SUBROUTINE_SAFE_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_SAFE
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_SAFE
    "H_EXTRACT" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(out0:int64) (out1:int64) (out2:int64) (out3:int64) (nblocks:num)
      (st:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      if nblocks = 0
      then f_ev_zero out0 out1 out2 out3 nblocks st pc stackpointer
                     returnaddress
      else APPEND (f_ev_epil out0 out1 out2 out3 nblocks st pc stackpointer
                             returnaddress)
            (APPEND
              (ENUMERATEL nblocks
                (\i. f_ev_loop out0 out1 out2 out3 nblocks st pc stackpointer
                               returnaddress i))
              (f_ev_prol out0 out1 out2 out3 nblocks st pc stackpointer
                         returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              fst MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SQX4_BOUND_TAC THEN SQX4_PRESERVED_TAC THEN
  ASM_CASES_TAC `nblocks = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `nblocks:num`
   `pc + mlkem_shake128x4_squeezeblocks_loop1`
   `pc + mlkem_shake128x4_squeezeblocks_loop1_exit`
   `\i s. read X21 s = word_add out3 (word(168 * i)) /\
          read X22 s = word_add out2 (word(168 * i)) /\
          read X23 s = word_add out1 (word(168 * i)) /\
          read X24 s = word_add out0 (word(168 * i)) /\
          read X20 s = word(nblocks - i) /\
          read X19 s = st /\
          read SP s = word_add stackpointer (word 224) /\
          read (memory :> bytes64 (word_add stackpointer (word 224))) s =
          returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 240))) s =
          x24_init /\
          read (memory :> bytes64 (word_add stackpointer (word 248))) s =
          x23_init /\
          read (memory :> bytes64 (word_add stackpointer (word 256))) s =
          x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 264))) s =
          x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 272))) s =
          x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 280))) s =
          x19_init` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (1--1) THEN
    SQX4_NONZERO_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (2--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `168 * i + 168 <= 168 * nblocks` ASSUME_TAC THENL
     [UNDISCH_TAC `i < nblocks` THEN ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (1--2) THEN
    SQX4_SAFE_CALL_TAC "H_PERMUTE"
      [`e:(uarch_event)list`; `read X0 s`; `pc:num`; `read SP s`;
       `read X30 s`] 3 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (4--11) THEN
    SQX4_SAFE_CALL_TAC "H_EXTRACT"
      [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
       `read X3 s`; `read X4 s`; `0`; `168`; `pc:num`; `read X30 s`] 12 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (13--18) THEN
    SQX4_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL
     [REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
      REWRITE_TAC[ARITH_RULE `168 * (i + 1) = 168 * i + 168`];
      ALL_TAC]) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_IMAGE_SUBROUTINE_FULL = prove
 (MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_CLANG17_O3_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_CLANG17_O3_IMAGE_SUBROUTINE_FULL
    "H_EXTRACT" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(out0:int64) (out1:int64) (out2:int64) (out3:int64) (nblocks:num)
      (st:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      if nblocks = 0
      then f_ev_zero out0 out1 out2 out3 nblocks st pc stackpointer
                     returnaddress
      else APPEND (f_ev_epil out0 out1 out2 out3 nblocks st pc stackpointer
                             returnaddress)
            (APPEND
              (ENUMERATEL nblocks
                (\i. f_ev_loop out0 out1 out2 out3 nblocks st pc stackpointer
                               returnaddress i))
              (f_ev_prol out0 out1 out2 out3 nblocks st pc stackpointer
                         returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600;
              fst MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `nblocks = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  SQX4_BOUND_TAC THEN SQX4_PRESERVED_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `nblocks:num`
   `pc + mlkem_shake128x4_squeezeblocks_loop1`
   `pc + mlkem_shake128x4_squeezeblocks_loop1_exit`
   `\i s. read X21 s = word_add out3 (word(168 * i)) /\
          read X22 s = word_add out2 (word(168 * i)) /\
          read X23 s = word_add out1 (word(168 * i)) /\
          read X24 s = word_add out0 (word(168 * i)) /\
          read X20 s = word(nblocks - i) /\
          read X19 s = st /\
          read SP s = word_add stackpointer (word 224) /\
          read (memory :> bytes64 (word_add stackpointer (word 224))) s =
          returnaddress /\
          read (memory :> bytes64 (word_add stackpointer (word 240))) s =
          x24_init /\
          read (memory :> bytes64 (word_add stackpointer (word 248))) s =
          x23_init /\
          read (memory :> bytes64 (word_add stackpointer (word 256))) s =
          x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 264))) s =
          x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 272))) s =
          x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 280))) s =
          x19_init /\
          read (memory :> bytes(out0,168 * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * 168 * j) *
                val(keccak_squeeze (j + 1) S0) MOD 2 EXP (8 * 168)) /\
          read (memory :> bytes(out1,168 * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * 168 * j) *
                val(keccak_squeeze (j + 1) S1) MOD 2 EXP (8 * 168)) /\
          read (memory :> bytes(out2,168 * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * 168 * j) *
                val(keccak_squeeze (j + 1) S2) MOD 2 EXP (8 * 168)) /\
          read (memory :> bytes(out3,168 * i)) s =
          nsum {j | j < i}
           (\j. 2 EXP (8 * 168 * j) *
                val(keccak_squeeze (j + 1) S3) MOD 2 EXP (8 * 168)) /\
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
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (1--1) THEN
    SQX4_NONZERO_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (2--11) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `168 * i + 168 <= 168 * nblocks` ASSUME_TAC THENL
     [UNDISCH_TAC `i < nblocks` THEN ARITH_TAC; ALL_TAC] THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (1--2) THEN
    SQX4_STATES_TAC THEN
    SQX4_CS_CALL_TAC "H_PERMUTE"
     [`e:(uarch_event)list`; `read X0 s`; `keccak_squeeze i (S0:1600 word)`;
      `keccak_squeeze i (S1:1600 word)`; `keccak_squeeze i (S2:1600 word)`;
      `keccak_squeeze i (S3:1600 word)`; `pc:num`; `read SP s`;
      `read X30 s`] 3 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (4--11) THEN
    SQX4_STATES_TAC THEN
    SQX4_CS_CALL_TAC "H_EXTRACT"
     [`e:(uarch_event)list`; `read X0 s`; `read X1 s`; `read X2 s`;
      `read X3 s`; `read X4 s`; `0`; `168`;
      `keccak_f1600(keccak_squeeze i (S0:1600 word))`;
      `keccak_f1600(keccak_squeeze i (S1:1600 word))`;
      `keccak_f1600(keccak_squeeze i (S2:1600 word))`;
      `keccak_f1600(keccak_squeeze i (S3:1600 word))`; `pc:num`;
      `read X30 s`] 12 THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (13--18) THEN
    SQX4_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY (fun _ -> CONJ_TAC THENL [SQX4_PTR_STEP_TAC; ALL_TAC])
     (1--4) THEN
    MAP_EVERY (fun _ -> CONJ_TAC THENL [SQX4_BYTES_STEP_TAC; ALL_TAC])
     (1--4) THEN
    MAP_EVERY (fun _ -> CONJ_TAC THENL
      [REWRITE_TAC[GSYM ADD1; keccak_squeeze]; ALL_TAC]) (1--4) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_CLANG17_O3_EXEC
     (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;
