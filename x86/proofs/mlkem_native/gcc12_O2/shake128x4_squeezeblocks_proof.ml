(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/gcc12_O2/shake128x4_squeezeblocks_spec.ml";;


let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL = time prove
 (MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLKEM_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL
    "H_EXTRACT" THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(out0:int64) (out1:int64) (out2:int64) (out3:int64) (nblocks:num)
      (st:int64) (pc:num) (stackpointer:int64) (returnaddress:int64).
      if nblocks = 0
      then f_ev_zero out0 out1 out2 out3 nblocks st pc stackpointer
                     returnaddress
      else APPEND
            (f_ev_epil out0 out1 out2 out3 nblocks st pc stackpointer
                       returnaddress)
            (APPEND
              (ENUMERATEL nblocks
                (\i. f_ev_loop out0 out1 out2 out3 nblocks st pc
                               stackpointer returnaddress i))
              (f_ev_prol out0 out1 out2 out3 nblocks st pc stackpointer
                         returnaddress))
     :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`; `nblocks:num`;
    `st:int64`; `S0:1600 word`; `S1:1600 word`; `S2:1600 word`;
    `S3:1600 word`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 336 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600;
              fst MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `nblocks = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  SQX4_BOUND_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN
  ENSURES_PRESERVED_TAC "rbp_init" `RBP` THEN
  ENSURES_PRESERVED_TAC "r12_init" `R12` THEN
  ENSURES_PRESERVED_TAC "r13_init" `R13` THEN
  ENSURES_PRESERVED_TAC "r14_init" `R14` THEN
  ENSURES_PRESERVED_TAC "r15_init" `R15` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `nblocks:num` `pc + mlkem_shake128x4_squeezeblocks_loop1` `pc + mlkem_shake128x4_squeezeblocks_loop1_exit`
   SQX4_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Initialization, with the pushes ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--1) THEN
    SQX4_NONZERO_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (2--16) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body: permute, extract a block from each state ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `168 * i + 168 <= 168 * nblocks` ASSUME_TAC THENL
     [UNDISCH_TAC `i < nblocks` THEN ARITH_TAC; ALL_TAC] THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--2) THEN
    SQX4_STATES_TAC THEN
    SQX4_STATES_THEN (fun v0 v1 v2 v3 ->
      SQX4_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read RDI s`; v0; v1; v2; v3; `pc:num`;
         `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 3) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (4--16) THEN
    STACK_ARG32_TAC `word_add stackpointer (word 264):int64` THEN
    SQX4_STATES_TAC THEN
    SQX4_STATES_THEN (fun v0 v1 v2 v3 ->
      SQX4_CALL_TAC "H_EXTRACT"
        [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
         `read RCX s`; `read R8 s`; `0`; `168`; v0; v1; v2; v3;
         `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`]
        17) THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (18--21) THEN
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

    (*** The return, with the pops ***)

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  GHOST_INTRO_TAC `e:(uarch_event)list` `read events` THEN
  MP_TAC
   MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL THEN
  DISCH_THEN(CHOOSE_THEN (MP_TAC o SPECL
   [`e:(uarch_event)list`; `out0:int64`; `out1:int64`; `out2:int64`;
    `out3:int64`; `nblocks:num`; `st:int64`; `S0:1600 word`;
    `S1:1600 word`; `S2:1600 word`; `S3:1600 word`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`])) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_RULE) THEN
  SIMP_TAC[]);;

let MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  MP_TAC
   MLKEM_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `out0:int64`; `out1:int64`; `out2:int64`;
    `out3:int64`; `nblocks:num`; `st:int64`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`] THEN
  DISCH_TAC THEN
  MAP_EVERY (fun (a,v) ->
    GHOST_INTRO_TAC v (subst [a,`a:int64`]
     `read (memory :> wbytes a):x86state->1600 word`))
   [`st:int64`,`S0:1600 word`;
    `word_add st (word 200):int64`,`S1:1600 word`;
    `word_add st (word 400):int64`,`S2:1600 word`;
    `word_add st (word 600):int64`,`S3:1600 word`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`e:(uarch_event)list`; `out0:int64`; `out1:int64`; `out2:int64`;
    `out3:int64`; `nblocks:num`; `st:int64`; `S0:1600 word`;
    `S1:1600 word`; `S2:1600 word`; `S3:1600 word`; `pc:num`;
    `stackpointer:int64`; `returnaddress:int64`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP ENSURES_WEAKEN_RULE) THEN
  SIMP_TAC[]);;
