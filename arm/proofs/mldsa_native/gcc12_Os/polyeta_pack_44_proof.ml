(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 3 bits per coefficient, of 2 - a: the proof. *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/polyeta_pack_44_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/zeroize_1_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The loop handles 8          *)
(* coefficients and 3 bytes in each of its 32 iterations. After the loop the *)
(* code stores the three bytes of the last iteration again, stores the       *)
(* other values of the last iteration to the temporary array on the stack,   *)
(* zeroes it with mld_zeroize_1 and checks the stack guard. As the stores  *)
(* to the output use the registers of the last iteration, the loop of the    *)
(* proof has 31 iterations, ending at its own head, and the last iteration   *)
(* is simulated with the code after the loop. The loop test is the end of    *)
(* the body, as ENSURES_EVENTS_WHILE_UP2_TAC requires, and the events of an  *)
(* iteration depend on its index only.                                       *)
(* ------------------------------------------------------------------------- *)

(*** The end of an iteration, as CHUNK_FULL_FINAL_TAC of                   ***)
(*** utils/mldsa_native_pack.ml, for a loop whose last iteration has index ***)
(*** 30 and goes back to the head: the test of the code compares the       ***)
(*** pointer with the end of the input, which it reaches after iteration   ***)
(*** 31, so the branch is always taken.                                    ***)

let CHUNK_FULL_FINAL_NE_TAC fdef (x:term) =
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  LOOP_TEST_TAC THEN PTR_LOOP_TEST_TAC THEN LOOP_COND_TAC THEN
  REPEAT CONJ_TAC THEN
  TRY(COND_CASES_TAC THEN REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(ASM_REWRITE_TAC[COND_ID] THEN NO_TAC) THEN
  TRY(CONV_TAC WORD_RULE THEN NO_TAC) THEN
  TRY(REWRITE_TAC[CHUNK_OUTPUT_SPLIT; CHUNK_OUTPUT_SPLIT_1] THEN
      ASM_REWRITE_TAC[] THEN
      CONV_TAC EXPAND_CASES_CONV THEN
      REWRITE_TAC[fdef] THEN
      SIMP_TAC[DIVMOD_CHUNK; ARITH] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_CLAUSES; LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
      CONV_TAC(ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[ADD_CLAUSES; WORD_ADD_0] THEN
      CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN APP_BLAST_TAC x THEN
      NO_TAC) THEN
  DISCHARGE_SAFETY_PROPERTY_TAC;;

(*** The output after the last iteration: the first 93 bytes are those of ***)
(*** the first 31 iterations, and the last 3 bytes are written one by one ***)

let PE_LAST3 = prove
 (`!P:num->bool.
     (!j. j < 93 ==> P j) /\ P 93 /\ P 94 /\ P 95 ==> (!j. j < 96 ==> P j)`,
  GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `j < 93` THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `j = 93 \/ j = 94 \/ j = 95` MP_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let PE44_ALLOWED =
  [`pc:num`; `r:int64`; `a:int64`; `guard:int64`; `mf:int64`;
   `stackpointer:int64`; `returnaddress:int64`];;

let PE44_INV =
  `\i s. read X0 s = r /\
         read X1 s = word_add a (word(32 * i)) /\
         read X8 s = word_add r (word(3 * i)) /\
         read X14 s = word_add a (word 1024) /\
         read X6 s = word 2 /\
         read SP s = word_add stackpointer (word 16) /\
         read (memory :> bytes64 (word_add stackpointer (word 16))) s =
         x19_init /\
         read (memory :> bytes64 (word_add stackpointer (word 24))) s =
         returnaddress /\
         read (memory :> bytes64 (word_add stackpointer (word 40))) s =
         canary /\
         read (memory :> bytes64 (word_add (word pc) (word 131064))) s =
         guard /\
         read (memory :> bytes64 guard) s = canary /\
         read (memory :> bytes64 (word_add (word pc) (word 131048))) s = mf /\
         read (memory :> bytes(ea,el)) s = ev /\
         (!j. j < 256
              ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                  x j) /\
         (!j. j < 3 * i
              ==> read(memory :> bytes8(word_add r (word j))) s =
                  mld_polyeta_pack_2 x j)`;;

let MLDSA_NATIVE_POLYETA_PACK_44_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYETA_PACK_44_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLYETA_PACK_44_GCC12_OS_EXEC in
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_ZEROIZE_1_GCC12_OS_IMAGE_SUBROUTINE_FULL th)
     "H_ZERO") THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(r:int64) (a:int64) (guard:int64) (mf:int64) (pc:num)
      (stackpointer:int64) (returnaddress:int64).
      APPEND
        (f_ev_epil r a guard mf pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 31
            (\i. f_ev_loop r a guard mf pc stackpointer returnaddress i))
          (f_ev_prol r a guard mf pc stackpointer returnaddress))
    :(uarch_event)list` THEN
  REPEAT META_EXISTS_TAC THEN
  REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
  REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI; C_ARGUMENTS;
              NONOVERLAPPING_CLAUSES; ALL; ALLPAIRS; PAIRWISE; fst EXEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
              SPECL [`pc:num`; `got_memset:num`] WORD_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [SPECL [`pc:num`; `got_stack_chk_guard:num`] WORD_ADD;
    SPECL [`pc:num`; `got_memset:num`] WORD_ADD]) THEN
  GHOST_INTRO_TAC `canary:int64` `read (memory :> bytes64 guard)` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ENSURES_EXISTING_PRESERVED_TAC `X30` THEN
  ENSURES_PRESERVED_TAC "x19_init" `X19` THEN
  ENSURES_EVENTS_WHILE_UP2_TAC `31` `pc + mldsa44_polyeta_pack_loop1`
   `pc + mldsa44_polyeta_pack_loop1` PE44_INV THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, saving the registers and the stack guard ***)

    FULL_INIT_TAC THEN
    ARM_STEPS_TAC EXEC (1--1) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC EXEC (2--9) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MULT_CLAUSES; CONJUNCT1 LT; ADD_CLAUSES; WORD_ADD_0] THEN
    DISCHARGE_SAFETY_PROPERTY_TAC;

    (*** The loop body ***)

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FULL_INIT_TAC THEN
    CHUNK_INPUT_TAC `x:num->int32` 8 THEN
    ARM_STEPS_TAC EXEC (1--46) THEN
    SUBGOAL_THEN `~(1024 = 32 * i + 32)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    CHUNK_FULL_FINAL_NE_TAC mld_polyeta_pack_2 `x:num->int32`;

    (*** The last iteration, the stores after the loop, the call of ***)
    (*** mld_zeroize_1, the check of the stack guard and the return ***)

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    MAP_EVERY (fun k ->
      let kt = mk_small_numeral k in
      FIRST_ASSUM(fun th ->
        if is_forall(concl th) && free_in `x:num->int32` (concl th) &&
           free_in `a:int64` (concl th)
        then MP_TAC(SPEC kt th) THEN CONV_TAC NUM_REDUCE_CONV THEN
             REWRITE_TAC[] THEN DISCH_TAC
        else failwith "input"))
      (248--255) THEN
    ARM_STEPS_TAC EXEC (1--60) THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc EXEC "H_ZERO"
     [`read X0 s`; `8`; `pc:num`; `read SP s`; `read X30 s`]
     PE44_ALLOWED 61 THEN
    ARM_STEPS_TAC EXEC (62--62) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC EXEC (63--70) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PE_LAST3 THEN CONJ_TAC THENL
       [FIRST_ASSUM(MATCH_ACCEPT_TAC o
          CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV));
        REPEAT CONJ_TAC THEN
        REWRITE_TAC[mld_polyeta_pack_2] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[] THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
        REWRITE_TAC[ADD_CLAUSES] THEN APP_BLAST_TAC `x:num->int32`];
      DISCHARGE_SAFETY_PROPERTY_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYETA_PACK_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYETA_PACK_44_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
       MLDSA_NATIVE_POLYETA_PACK_44_GCC12_OS_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_POLYETA_PACK_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYETA_PACK_44_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
       MLDSA_NATIVE_POLYETA_PACK_44_GCC12_OS_IMAGE_SUBROUTINE_FULL) th)));;
