(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "x86/proofs/mlkem_native/gcc12_O2/poly_cbd2_spec.ml";;


let NIBBLE_BIT = prove
 (NIBBLE_BIT_STMT,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN
  SPEC_TAC(`n DIV 2 EXP m`,`x:num`) THEN GEN_TAC THEN
  GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV) [GSYM(SPEC `2` EXP_1)] THEN
  REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; ARITH_RULE `16 = 2 EXP 4`;
              MOD_MOD_EXP_MIN] THEN
  ASM_SIMP_TAC[ARITH_RULE `k < 4 ==> MIN 4 (k + 1) = k + 1`]);;

let CBD2_NIBBLE = prove
 (CBD2_NIBBLE_STMT,
  CONV_TAC EXPAND_CASES_CONV THEN
  CONV_TAC(DEPTH_CONV(NUM_RED_CONV ORELSEC INT_RED_CONV ORELSEC
                      WORD_RED_CONV)));;

let CBD2_LANE = prove
 (CBD2_LANE_STMT,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SUBGOAL_THEN
   `word_subword (word((n DIV 2 EXP (32 * i)) MOD 4294967296):int32)
                 (4 * j,4):4 word =
    word((n DIV 2 EXP (4 * (8 * i + j))) MOD 16)`
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) WORD_SUBWORD_WORD o lhand o snd) THEN
    ANTS_TAC THENL
     [CONV_TAC(DEPTH_CONV DIMINDEX_CONV) THEN ASM_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN REWRITE_TAC[ARITH_RULE `4294967296 = 2 EXP 32`] THEN
    ASM_SIMP_TAC[DIV_MOD_EXP_LOW; ARITH_RULE `j < 8 ==> 4 * j + 4 <= 32`] THEN
    REWRITE_TAC[DIV_DIV; GSYM EXP_ADD; ARITH_RULE `2 EXP 4 = 16`] THEN
    REWRITE_TAC[ARITH_RULE `32 * i + 4 * j = 4 * (8 * i + j)`];
    ALL_TAC] THEN
  SIMP_TAC[CBD2_NIBBLE; MOD_LT_EQ; ARITH_EQ] THEN
  SIMP_TAC[NIBBLE_BIT; ARITH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[GEN_ALL(CONV_RULE NUM_REDUCE_CONV
   (SPECL [`x:num`; `2`; `8`] MOD_MOD))]);;

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT = prove
 (MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_CORRECT_STMT,
  MAP_EVERY X_GEN_TAC [`r:int64`; `a:int64`; `n:num`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 8 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              ALL; NONOVERLAPPING_CLAUSES] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN

  (*** The outer loop, over the 32-bit words of the input ***)

  ENSURES_WHILE_UP_TAC `32` `pc + mlkem_poly_cbd2_loop1` `pc + mlkem_poly_cbd2_loop1_test`
   `\i s. read R8 s = r /\ read R10 s = a /\ read R9 s = word i /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          returnaddress /\
          read (memory :> bytes(a,128)) s = n /\
          !j. j < 8 * i
              ==> read(memory :> bytes16(word_add r (word(2 * j)))) s =
                  iword(&((n DIV 2 EXP (4 * j)) MOD 2 +
                          (n DIV 2 EXP (4 * j + 1)) MOD 2) -
                        &((n DIV 2 EXP (4 * j + 2)) MOD 2 +
                          (n DIV 2 EXP (4 * j + 3)) MOD 2))` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, saving RBX ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (1--5) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT];

    (*** The loop body, for one 32-bit word t and 8 coefficients ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    MP_TAC(SPECL [`a:int64`; `128`; `n:num`; `4 * i`; `s0:x86state`]
                 READ_MEMORY_BYTES32_OF_NUM) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `i < 32` THEN ARITH_TAC; DISCH_TAC] THEN
    VAL_INT64_TAC `i:num` THEN
    ABBREV_TAC `t:int32 = word((n DIV 2 EXP (8 * 4 * i)) MOD 4294967296)` THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (1--9) THEN
    MAP_EVERY (CBD2_INNER_TAC true) (0--7) THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC [138] THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE
     `j < 8 * (i + 1) <=>
      j < 8 * i \/ j = 8 * i \/ j = 8 * i + 1 \/ j = 8 * i + 2 \/
      j = 8 * i + 3 \/ j = 8 * i + 4 \/ j = 8 * i + 5 \/ j = 8 * i + 6 \/
      j = 8 * i + 7`] THEN
    REWRITE_TAC[TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
                FORALL_AND_THM; FORALL_UNWIND_THM2] THEN
    ASM_REWRITE_TAC[];

    (*** The loop-back branch ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (1--2) THEN
    SUBGOAL_THEN `~(val(word_sub (word i) (word 32):int64) = 0)`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [REWRITE_TAC[VAL_WORD_SUB_EQ_0; VAL_WORD; DIMINDEX_64] THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `i < 32 ==> i < 2 EXP 64`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `i < 32` THEN ARITH_TAC;
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];

    (*** The loop exit, restoring RBX, and the return ***)

    ENSURES_INIT_TAC "s0" THEN
    X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o
      CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV) o
      check (fun th -> is_forall(concl th) &&
                       free_in `bytes16` (concl th)))]);;

let MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_SAFE = time prove
 (MLKEM_NATIVE_POLY_CBD2_GCC12_O2_IMAGE_SUBROUTINE_SAFE_STMT,
  CONCRETIZE_F_EVENTS_TAC
    `\(a:int64) (r:int64) (pc:num) (stackpointer:int64)
      (returnaddress:int64).
      APPEND
        (f_ev_epil a r pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 32
            (\i. f_ev_loop a r pc stackpointer returnaddress i))
          (f_ev_prol a r pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`e:(uarch_event)list`; `r:int64`; `a:int64`; `pc:num`] THEN
  WORD_FORALL_OFFSET_TAC 8 THEN
  MAP_EVERY X_GEN_TAC [`stackpointer:int64`; `returnaddress:int64`] THEN
  REWRITE_TAC[C_ARGUMENTS; NONOVERLAPPING_CLAUSES; ALL;
              MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI;
              fst MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_PRESERVED_TAC "rbx_init" `RBX` THEN

  ENSURES_EVENTS_WHILE_UP2_TAC `32` `pc + mlkem_poly_cbd2_loop1` `pc + mlkem_poly_cbd2_loop1_exit`
   `\i s. read R8 s = r /\ read R10 s = a /\ read R9 s = word i /\
          read RSP s = stackpointer /\
          read (memory :> bytes64 stackpointer) s = rbx_init /\
          read (memory :> bytes64 (word_add stackpointer (word 8))) s =
          returnaddress` THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (1--5) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    ALL_TAC;

    REWRITE_TAC[] THEN
    X86_SIM_TAC ~preprocess_tac:(TRY STRIP_EXISTS_ASSUM_TAC)
      ~canonicalize_pc_diff:false
      MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (1--2) THEN
    DISCHARGE_SAFETY_PROPERTY_TAC] THEN

  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_INIT_TAC "s0" THEN TRY STRIP_EXISTS_ASSUM_TAC THEN
  VAL_INT64_TAC `i:num` THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (1--9) THEN
  MAP_EVERY (CBD2_INNER_TAC false) (0--7) THEN
  X86_STEPS_TAC MLKEM_NATIVE_POLY_CBD2_GCC12_O2_EXEC (138--140) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `~(val(word_add (word i) (word 18446744073709551585):int64) = 0) <=>
    i + 1 < 32`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[VAL_WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    UNDISCH_TAC `i < 32` THEN SPEC_TAC(`i:num`,`i:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  CONJ_TAC THENL [COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[WORD_ADD]; ALL_TAC] THEN
  DISCHARGE_SAFETY_PROPERTY_TAC);;
