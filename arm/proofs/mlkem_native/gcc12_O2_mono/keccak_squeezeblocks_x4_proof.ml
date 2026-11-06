(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "arm/proofs/mlkem_native/gcc12_O2_mono/keccak_squeezeblocks_x4_spec.ml";;


let SQ_L2 = sq_prove SQ_L2_STMT
  "mlk_keccak_squeezeblocks_x4_loop2" "mlk_keccak_squeezeblocks_x4_loop2_exit"
  (fun i -> "read X0 s = word "^i^" /\\
             (~("^i^" = 0) ==> read X2 s = word ("^i^" - 1)) /\\
             read X19 s = d /\\ read X23 s = a /\\ read X26 s = word len")
  6 true 2;;

let SQ_L3 = sq_prove SQ_L3_STMT
  "mlk_keccak_squeezeblocks_x4_loop3" "mlk_keccak_squeezeblocks_x4_loop3_exit"
  (fun i -> "read X1 s = word "^i^" /\\ read X2 s = word (len - 1) /\\
             read X20 s = d /\\ read X28 s = a")
  5 false 1;;

let SQ_L4 = sq_prove SQ_L4_STMT
  "mlk_keccak_squeezeblocks_x4_loop4" "mlk_keccak_squeezeblocks_x4_loop4_exit"
  (fun i -> "read X1 s = word "^i^" /\\ read X2 s = word (len - 1) /\\
             read X21 s = d /\\ read X25 s = a")
  5 false 1;;

let SQ_L5 = sq_prove SQ_L5_STMT
  "mlk_keccak_squeezeblocks_x4_loop5" "mlk_keccak_squeezeblocks_x4_loop5_exit"
  (fun i -> "read X1 s = word "^i^" /\\ read X2 s = word (len - 1) /\\
             read X22 s = d /\\ read X24 s = a")
  5 false 0;;

let LE_MUL_SELF = prove
 (LE_MUL_SELF_STMT,
  REPEAT STRIP_TAC THEN TRANS_TAC LE_TRANS `1 * n` THEN CONJ_TAC THENL
   [ARITH_TAC; REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC]);;

let MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC
   [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`; `nblocks:num`;
    `st:int64`; `r:num`; `S0:1600 word`; `S1:1600 word`; `S2:1600 word`;
    `S3:1600 word`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 288 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~(r = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN

  (*** The case nblocks = 0, where nothing is done ***)

  ASM_CASES_TAC `nblocks = 0` THENL
   [ASM_REWRITE_TAC[] THEN ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC SQ_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze];
    ALL_TAC] THEN
  SQ_BOUND_TAC THEN SQ_PRESERVED_TAC THEN

  (*** The loop, with i blocks done ***)

  ENSURES_WHILE_UP2_TAC `nblocks:num`
   `pc + mlk_keccak_squeezeblocks_x4_loop1`
   `pc + mlk_keccak_squeezeblocks_x4_loop1_exit`
   `\i s. read X19 s = word_add out0 (word(r * i)) /\
          read X20 s = word_add out1 (word(r * i)) /\
          read X21 s = word_add out2 (word(r * i)) /\
          read X22 s = word_add out3 (word(r * i)) /\
          read X23 s = st /\
          read X24 s = word_add st (word 600) /\
          read X25 s = word_add st (word 400) /\
          read X26 s = word r /\
          read X27 s = word(nblocks - i) /\
          read X28 s = word_add st (word 200) /\
          read SP s = word_add stackpointer (word 192) /\
          read (memory :> bytes64 (word_add stackpointer (word 192))) s =
          x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 200))) s =
          x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 208))) s =
          x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 216))) s =
          x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 224))) s =
          x23_init /\
          read (memory :> bytes64 (word_add stackpointer (word 232))) s =
          x24_init /\
          read (memory :> bytes64 (word_add stackpointer (word 240))) s =
          x25_init /\
          read (memory :> bytes64 (word_add stackpointer (word 248))) s =
          x26_init /\
          read (memory :> bytes64 (word_add stackpointer (word 256))) s =
          x27_init /\
          read (memory :> bytes64 (word_add stackpointer (word 264))) s =
          x28_init /\
          read (memory :> bytes64 (word_add stackpointer (word 272))) s =
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

    (*** Initialization ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC SQ_EXEC (1--1) THEN
    SQ_NONZERO_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (2--18) THEN ARGS_32_TAC [`r:num`] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze];

    (*** The loop body: four permutations, four extractions, the test ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN `r * i + r <= r * nblocks` ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `r * i + r = r * (i + 1)`; LE_MULT_LCANCEL] THEN
      DISJ2_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SQ_STATES_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (1--2) THEN
    KECCAK_STATE_THEN `st:int64` (fun v ->
      SQ_SUB SQ_PERMUTE [`read X0 s`; v; `pc:num`; `read SP s`;
                         `read X30 s`] 3) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN SQ_STATES_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (4--5) THEN
    KECCAK_STATE_THEN `word_add (st:int64) (word 200)` (fun v ->
      SQ_SUB SQ_PERMUTE [`read X0 s`; v; `pc:num`; `read SP s`;
                         `read X30 s`] 6) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN SQ_STATES_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (7--8) THEN
    KECCAK_STATE_THEN `word_add (st:int64) (word 400)` (fun v ->
      SQ_SUB SQ_PERMUTE [`read X0 s`; v; `pc:num`; `read SP s`;
                         `read X30 s`] 9) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN SQ_STATES_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (10--11) THEN
    KECCAK_STATE_THEN `word_add (st:int64) (word 600)` (fun v ->
      SQ_SUB SQ_PERMUTE [`read X0 s`; v; `pc:num`; `read SP s`;
                         `read X30 s`] 12) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC SQ_EXEC (13--14) THEN
    SQ_STATES_TAC THEN
    SQ_SUB SQ_L2 [`read X23 s`; `read X19 s`; `r:num`;
                  `keccak_f1600 (keccak_squeeze i (S0:1600 word))`;
                  `pc:num`] 15 THEN
    SQ_STATES_TAC THEN
    SQ_SUB SQ_L3 [`word_add (st:int64) (word 200)`;
                  `word_add (out1:int64) (word (r * i))`; `r:num`;
                  `keccak_f1600 (keccak_squeeze i (S1:1600 word))`;
                  `pc:num`] 16 THEN
    SQ_STATES_TAC THEN
    SQ_SUB SQ_L4 [`word_add (st:int64) (word 400)`;
                  `word_add (out2:int64) (word (r * i))`; `r:num`;
                  `keccak_f1600 (keccak_squeeze i (S2:1600 word))`;
                  `pc:num`] 17 THEN
    SQ_STATES_TAC THEN
    SQ_SUB SQ_L5 [`word_add (st:int64) (word 600)`;
                  `word_add (out3:int64) (word (r * i))`; `r:num`;
                  `keccak_f1600 (keccak_squeeze i (S3:1600 word))`;
                  `pc:num`] 18 THEN
    ARM_STEPS_TAC SQ_EXEC (19--24) THEN
    SQ_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`] THEN NO_TAC) THEN
    TRY(REWRITE_TAC[GSYM ADD1; keccak_squeeze] THEN NO_TAC) THEN
    TRY(REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`] THEN
        REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
        REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM ADD1; NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
        NO_TAC);

    (*** The return ***)

    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC SQ_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]]);;

let SQ_F2 = sqF_prove SQ_F2_STMT
  "mlk_keccak_squeezeblocks_x4_loop2" "mlk_keccak_squeezeblocks_x4_loop2_exit"
  (fun i -> "read X0 s = word "^i^" /\\
             (~("^i^" = 0) ==> read X2 s = word ("^i^" - 1)) /\\
             read X19 s = d /\\ read X23 s = a /\\ read X26 s = word len")
  6 true 2;;

let SQ_F3 = sqF_prove SQ_F3_STMT
  "mlk_keccak_squeezeblocks_x4_loop3" "mlk_keccak_squeezeblocks_x4_loop3_exit"
  (fun i -> "read X1 s = word "^i^" /\\ read X2 s = word (len - 1) /\\
             read X20 s = d /\\ read X28 s = a")
  5 false 1;;

let SQ_F4 = sqF_prove SQ_F4_STMT
  "mlk_keccak_squeezeblocks_x4_loop4" "mlk_keccak_squeezeblocks_x4_loop4_exit"
  (fun i -> "read X1 s = word "^i^" /\\ read X2 s = word (len - 1) /\\
             read X21 s = d /\\ read X25 s = a")
  5 false 1;;

let SQ_F5 = sqF_prove SQ_F5_STMT
  "mlk_keccak_squeezeblocks_x4_loop5" "mlk_keccak_squeezeblocks_x4_loop5_exit"
  (fun i -> "read X1 s = word "^i^" /\\ read X2 s = word (len - 1) /\\
             read X22 s = d /\\ read X24 s = a")
  5 false 0;;

let MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL = prove
 (MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC SQ_PERMUTE_FULL "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SQ_F2 "H_L2" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SQ_F3 "H_L3" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SQ_F4 "H_L4" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC SQ_F5 "H_L5" THEN
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
              READ_MEMORY_WBYTES_1600; fst SQ_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~(r = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `nblocks = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (1--2) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;
    ALL_TAC] THEN
  SQ_BOUND_TAC THEN SQ_PRESERVED_TAC THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `nblocks:num`
   `pc + mlk_keccak_squeezeblocks_x4_loop1`
   `pc + mlk_keccak_squeezeblocks_x4_loop1_exit`
   `\i s. read X19 s = word_add out0 (word(r * i)) /\
          read X20 s = word_add out1 (word(r * i)) /\
          read X21 s = word_add out2 (word(r * i)) /\
          read X22 s = word_add out3 (word(r * i)) /\
          read X23 s = st /\
          read X24 s = word_add st (word 600) /\
          read X25 s = word_add st (word 400) /\
          read X26 s = word r /\
          read X27 s = word(nblocks - i) /\
          read X28 s = word_add st (word 200) /\
          read SP s = word_add stackpointer (word 192) /\
          read (memory :> bytes64 (word_add stackpointer (word 192))) s =
          x19_init /\
          read (memory :> bytes64 (word_add stackpointer (word 200))) s =
          x20_init /\
          read (memory :> bytes64 (word_add stackpointer (word 208))) s =
          x21_init /\
          read (memory :> bytes64 (word_add stackpointer (word 216))) s =
          x22_init /\
          read (memory :> bytes64 (word_add stackpointer (word 224))) s =
          x23_init /\
          read (memory :> bytes64 (word_add stackpointer (word 232))) s =
          x24_init /\
          read (memory :> bytes64 (word_add stackpointer (word 240))) s =
          x25_init /\
          read (memory :> bytes64 (word_add stackpointer (word 248))) s =
          x26_init /\
          read (memory :> bytes64 (word_add stackpointer (word 256))) s =
          x27_init /\
          read (memory :> bytes64 (word_add stackpointer (word 264))) s =
          x28_init /\
          read (memory :> bytes64 (word_add stackpointer (word 272))) s =
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
    ARM_STEPS_TAC SQ_EXEC (1--1) THEN
    SQ_NONZERO_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (2--18) THEN ARGS_32_TAC [`r:num`] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; SUB_0; WORD_ADD_0; READ_MEMORY_BYTES_TRIVIAL;
                NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    SUBGOAL_THEN `r * i + r <= r * nblocks` ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `r * i + r = r * (i + 1)`; LE_MULT_LCANCEL] THEN
      DISJ2_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SQ_STATES_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (1--2) THEN
    KECCAK_STATE_THEN `st:int64` (fun v ->
      SQ_FULL_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read X0 s`; v; `pc:num`; `read SP s`;
         `read X30 s`] 3) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN SQ_STATES_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (4--5) THEN
    KECCAK_STATE_THEN `word_add (st:int64) (word 200)` (fun v ->
      SQ_FULL_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read X0 s`; v; `pc:num`; `read SP s`;
         `read X30 s`] 6) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN SQ_STATES_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (7--8) THEN
    KECCAK_STATE_THEN `word_add (st:int64) (word 400)` (fun v ->
      SQ_FULL_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read X0 s`; v; `pc:num`; `read SP s`;
         `read X30 s`] 9) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN SQ_STATES_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (10--11) THEN
    KECCAK_STATE_THEN `word_add (st:int64) (word 600)` (fun v ->
      SQ_FULL_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read X0 s`; v; `pc:num`; `read SP s`;
         `read X30 s`] 12) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    ARM_STEPS_TAC SQ_EXEC (13--14) THEN
    SQ_STATES_TAC THEN
    SQ_FULL_CALL_TAC "H_L2"
      [`e:(uarch_event)list`; `read X23 s`; `read X19 s`; `r:num`;
       `keccak_f1600 (keccak_squeeze i (S0:1600 word))`; `pc:num`] 15 THEN
    SQ_STATES_TAC THEN
    SQ_FULL_CALL_TAC "H_L3"
      [`e:(uarch_event)list`; `word_add (st:int64) (word 200)`;
       `word_add (out1:int64) (word (r * i))`; `r:num`;
       `keccak_f1600 (keccak_squeeze i (S1:1600 word))`; `pc:num`] 16 THEN
    SQ_STATES_TAC THEN
    SQ_FULL_CALL_TAC "H_L4"
      [`e:(uarch_event)list`; `word_add (st:int64) (word 400)`;
       `word_add (out2:int64) (word (r * i))`; `r:num`;
       `keccak_f1600 (keccak_squeeze i (S2:1600 word))`; `pc:num`] 17 THEN
    SQ_STATES_TAC THEN
    SQ_FULL_CALL_TAC "H_L5"
      [`e:(uarch_event)list`; `word_add (st:int64) (word 600)`;
       `word_add (out3:int64) (word (r * i))`; `r:num`;
       `keccak_f1600 (keccak_squeeze i (S3:1600 word))`; `pc:num`] 18 THEN
    ARM_STEPS_TAC SQ_EXEC (19--24) THEN
    SQ_COUNTER_TAC THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    FIRST
     [COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC;
      REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
        REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`] THEN NO_TAC;
      REWRITE_TAC[GSYM ADD1; keccak_squeeze] THEN NO_TAC;
      REWRITE_TAC[ARITH_RULE `r * (i + 1) = r * i + r`] THEN
        REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
        REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM ADD1; NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
        NO_TAC;
      DISCHARGE_SAFETY_PROPERTY_TAC];

    REWRITE_TAC[] THEN REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    ARM_STEPS_TAC SQ_EXEC (1--7) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

let MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE = prove
 (MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_SAFE_STMT,
  MP_TAC MLKEM_NATIVE_KECCAK_SQUEEZEBLOCKS_X4_GCC12_O2_MONO_IMAGE_SUBROUTINE_FULL THEN
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
