(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* The proof for mldsa_shake128x4_squeezeblocks (see                         *)
(* shake128x4_squeezeblocks_spec.ml): that of the same code in the x86       *)
(* proofs of mlkem-native                                                    *)
(* (mlkem_native_shake128x4_squeezeblocks_gcc12_O2.ml), with the names       *)
(* changed.                                                                  *)
(* ========================================================================= *)

needs "x86/proofs/mldsa_native/gcc12_O2/shake128x4_squeezeblocks_spec.ml";;
needs "x86/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* Tactics for the four states, the number of blocks and the loop counter.   *)
(* ------------------------------------------------------------------------- *)

let SQX4_STATES_TAC =
  MAP_EVERY KECCAK_STATE_AT_TAC
   [`st:int64`; `word_add (st:int64) (word 200)`;
    `word_add (st:int64) (word 400)`; `word_add (st:int64) (word 600)`];;

let SQX4_STATES_THEN (ttac:term->term->term->term->tactic) =
  KECCAK_STATE_THEN `st:int64` (fun v0 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 200)` (fun v1 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 400)` (fun v2 ->
  KECCAK_STATE_THEN `word_add (st:int64) (word 600)` (fun v3 ->
    ttac v0 v1 v2 v3))));;

let SQX4_BOUND_TAC =
  SUBGOAL_THEN `800 + 168 * nblocks <= 18446744073709551616` ASSUME_TAC THENL
   [MATCH_MP_TAC NONOVERLAPPING_IMP_SMALL_RIGHT_ALT THEN
    MAP_EVERY EXISTS_TAC [`val(st:int64)`; `val(out0:int64)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[NONOVERLAPPING_MODULO_SYM] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word nblocks:int64) = nblocks` ASSUME_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC];;

let SQX4_NONZERO_TAC =
  let t1 = `val(word nblocks:int64) = nblocks` and t2 = `~(nblocks = 0)` in
  RULE_ASSUM_TAC(fun th ->
    if concl th = t1 || concl th = t2 then th
    else REWRITE_RULE[ASSUME t1; ASSUME t2] th);;

let SQX4_COUNTER_TAC =
  SUBGOAL_THEN `word_sub (word (nblocks - i)) (word 1):int64 =
                word(nblocks - (i + 1))` SUBST_ALL_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUB2 o lhand o snd) THEN
    ANTS_TAC THENL [UNDISCH_TAC `i < nblocks` THEN ARITH_TAC;
                    DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `val(word(nblocks - (i + 1)):int64) = nblocks - (i + 1)`
  SUBST_ALL_TAC THENL
   [MATCH_MP_TAC VAL_WORD_EQ THEN REWRITE_TAC[DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMPLE_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(nblocks - (i + 1) = 0) <=> i + 1 < nblocks`
  SUBST_ALL_TAC THENL [ARITH_TAC; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety, using the FULL theorems of  *)
(* mldsa_keccakf1600x4_permute and mldsa_keccakf1600x4_extract_bytes. For    *)
(* each of the four states S, block i of its output, as a number, is the     *)
(* first 168 bytes of keccak_squeeze (i + 1) S, and the state becomes        *)
(* keccak_squeeze nblocks S. The events depend only on the addresses and     *)
(* nblocks. The frame of 336 bytes is at stackpointer, with the registers    *)
(* saved at stackpointer + 288 to 328 and the seventh argument of            *)
(* mldsa_keccakf1600x4_extract_bytes pushed at stackpointer + 264.           *)
(* ------------------------------------------------------------------------- *)

let SQX4_CALL_TAC name ilist n =
  REMOVE_THEN name (fun safety_th ->
    X86_SUBROUTINE_SIM_TAC ~is_safety_thm:true
      (mldsa_native_libmldsa_gcc12_O2_mc,
       MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC,
       0x0,mldsa_native_libmldsa_gcc12_O2_mc,safety_th)
      ilist n THENL
     [EXISTS_E2_TAC (ref
       [`out0:int64`; `out1:int64`; `out2:int64`; `out3:int64`;
        `nblocks:num`; `st:int64`; `pc:num`;
        `stackpointer:int64`; `returnaddress:int64`; `i:num`;
        `f_ev_loop:int64->int64->int64->int64->num->int64->num->int64->
                   int64->num->(uarch_event)list`]);
      LABEL_TAC name safety_th]);;

let SQX4_BYTES_STEP_TAC =
  REWRITE_TAC[ARITH_RULE `168 * (i + 1) = 168 * i + 168`] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[GSYM READ_COMPONENT_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ADD1; NSUM_CLAUSES_NUMSEG_LT; keccak_squeeze] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; DIV_1];;

let SQX4_PTR_STEP_TAC =
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `168 * (i + 1) = 168 * i + 168`];;

let SQX4_INV =
 `\i s. read R14 s = word(nblocks - i) /\
        read R13 s = word_add out0 (word(168 * i)) /\
        read R12 s = word_add out1 (word(168 * i)) /\
        read RBP s = word_add out2 (word(168 * i)) /\
        read RBX s = word_add out3 (word(168 * i)) /\
        read R15 s = st /\
        read RSP s = word_add stackpointer (word 280) /\
        read (memory :> bytes64 (word_add stackpointer (word 288))) s =
        rbx_init /\
        read (memory :> bytes64 (word_add stackpointer (word 296))) s =
        rbp_init /\
        read (memory :> bytes64 (word_add stackpointer (word 304))) s =
        r12_init /\
        read (memory :> bytes64 (word_add stackpointer (word 312))) s =
        r13_init /\
        read (memory :> bytes64 (word_add stackpointer (word 320))) s =
        r14_init /\
        read (memory :> bytes64 (word_add stackpointer (word 328))) s =
        r15_init /\
        read (memory :> bytes64 (word_add stackpointer (word 336))) s =
        returnaddress /\
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
        val(keccak_squeeze i (S3:1600 word))`;;

let MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL_STMT,
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600X4_PERMUTE_GCC12_O2_IMAGE_SUBROUTINE_FULL_F1600
    "H_PERMUTE" THEN
  ASSUME_CALLEE_SAFETY_TAILED_TAC
    MLDSA_NATIVE_KECCAKF1600X4_EXTRACT_BYTES_GCC12_O2_IMAGE_SUBROUTINE_FULL
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
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; ALLPAIRS; PAIRWISE; NONOVERLAPPING_CLAUSES;
              READ_MEMORY_WBYTES_1600;
              fst MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC `nblocks = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
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
  ENSURES_EVENTS_WHILE_UP2_TAC `nblocks:num`
   `pc + mldsa_shake128x4_squeezeblocks_loop1`
   `pc + mldsa_shake128x4_squeezeblocks_loop1_exit`
   SQX4_INV THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];

    (*** Initialization, with the pushes ***)

    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
    X86_STEPS_TAC MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--1) THEN
    SQX4_NONZERO_TAC THEN
    X86_STEPS_TAC MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
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
    X86_STEPS_TAC MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--2) THEN
    SQX4_STATES_TAC THEN
    SQX4_STATES_THEN (fun v0 v1 v2 v3 ->
      SQX4_CALL_TAC "H_PERMUTE"
        [`e:(uarch_event)list`; `read RDI s`; v0; v1; v2; v3; `pc:num`;
         `read RSP s`; `read (memory :> bytes64(read RSP s)) s`] 3) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[READ_MEMORY_WBYTES_1600]) THEN
    X86_STEPS_TAC MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (4--16) THEN
    STACK_ARG32_TAC `word_add stackpointer (word 264):int64` THEN
    SQX4_STATES_TAC THEN
    SQX4_STATES_THEN (fun v0 v1 v2 v3 ->
      SQX4_CALL_TAC "H_EXTRACT"
        [`e:(uarch_event)list`; `read RDI s`; `read RSI s`; `read RDX s`;
         `read RCX s`; `read R8 s`; `0`; `168`; v0; v1; v2; v3;
         `pc:num`; `read RSP s`; `read (memory :> bytes64(read RSP s)) s`]
        17) THEN
    X86_STEPS_TAC MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
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
    X86_STEPS_TAC MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_EXEC
     (1--8) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT =
  prove
 (MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  CORRECT_OF_FULL_TAC
    MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL);;

let MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  SAFE_OF_FULL_TAC
    MLDSA_NATIVE_SHAKE128X4_SQUEEZEBLOCKS_GCC12_O2_IMAGE_SUBROUTINE_FULL);;
