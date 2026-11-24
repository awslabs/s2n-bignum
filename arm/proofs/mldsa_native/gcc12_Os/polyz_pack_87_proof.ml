(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Packing of a polynomial with 20 bits per coefficient, of 2^19 - a: the    *)
(* proof.                                                                    *)
(* ========================================================================= *)

needs "arm/proofs/mldsa_native/gcc12_Os/polyz_pack_87_spec.ml";;
needs "arm/proofs/mldsa_native/gcc12_Os/zeroize_5_spec.ml";;
needs "arm/proofs/utils/mldsa_native_full.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness, constant time and memory safety. The loop handles 2          *)
(* coefficients and 5 bytes in each of its 128 iterations. After the loop    *)
(* the code stores the values of the last iteration again, zeroes the        *)
(* temporary array on the stack with mld_zeroize_5 and checks the stack      *)
(* guard. As these stores use the registers of the last iteration, the loop  *)
(* of the proof has 127 iterations, ending at its own head, and the last     *)
(* iteration is simulated with the code after the loop. The loop test is the *)
(* end of the body, as ENSURES_EVENTS_WHILE_UP2_TAC requires, and the events *)
(* of an iteration depend on its index only.                                 *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* The end of an iteration, as CHUNK_FULL_FINAL_TAC of                       *)
(* utils/mldsa_native_pack.ml, for a loop whose last iteration has index 126 *)
(* and goes back to the head: the test of the code compares the pointer with *)
(* the end of the output, which it reaches after iteration 127, so the       *)
(* branch is always taken.                                                   *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* The output after the last iteration: the first 635 bytes are those of the *)
(* first 127 iterations, and the last 5 bytes are written one by one.        *)
(* ------------------------------------------------------------------------- *)

let PZ_LAST5 = prove
 (`!P:num->bool.
     (!j. j < 635 ==> P j) /\ P 635 /\ P 636 /\ P 637 /\ P 638 /\ P 639
     ==> (!j. j < 640 ==> P j)`,
  GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `j < 635` THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `j = 635 \/ j = 636 \/ j = 637 \/ j = 638 \/ j = 639`
  MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let PZ87_ALLOWED =
  [`pc:num`; `r:int64`; `a:int64`; `guard:int64`; `mf:int64`;
   `stackpointer:int64`; `returnaddress:int64`];;

let PZ87_INV =
  `\i s. read X0 s = r /\
         read X1 s = word_add a (word(8 * i)) /\
         read X2 s = word_add r (word(5 * i)) /\
         read X8 s = word 524288 /\
         read X9 s = word_add r (word 640) /\
         read SP s = word_add stackpointer (word 16) /\
         read (memory :> bytes64 (word_add stackpointer (word 16))) s =
         returnaddress /\
         read (memory :> bytes64 (word_add stackpointer (word 56))) s =
         canary /\
         read (memory :> bytes64 (word_add (word pc) (word got_stack_chk_guard))) s =
         guard /\
         read (memory :> bytes64 guard) s = canary /\
         read (memory :> bytes64 (word_add (word pc) (word got_memset))) s = mf /\
         read (memory :> bytes(ea,el)) s = ev /\
         (!j. j < 256
              ==> read(memory :> bytes32(word_add a (word(4 * j)))) s =
                  x j) /\
         (!j. j < 5 * i
              ==> read(memory :> bytes8(word_add r (word j))) s =
                  mld_polyz_pack_19 x j)`;;

let MLDSA_NATIVE_POLYZ_PACK_87_GCC12_OS_IMAGE_SUBROUTINE_FULL = prove
 (MLDSA_NATIVE_POLYZ_PACK_87_GCC12_OS_IMAGE_SUBROUTINE_FULL_STMT,
  let EXEC = MLDSA_NATIVE_POLYZ_PACK_87_GCC12_OS_EXEC in
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ASSUME_CALLEE_SAFETY_TAILED_TAC
     (MATCH_MP MLDSA_NATIVE_ZEROIZE_5_GCC12_OS_IMAGE_SUBROUTINE_FULL th)
     "H_ZERO") THEN
  CONCRETIZE_F_EVENTS_TAC
    `\(r:int64) (a:int64) (guard:int64) (mf:int64) (pc:num)
      (stackpointer:int64) (returnaddress:int64).
      APPEND
        (f_ev_epil r a guard mf pc stackpointer returnaddress)
        (APPEND
          (ENUMERATEL 127
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
  ENSURES_EVENTS_WHILE_UP2_TAC `127` `pc + mldsa87_polyz_pack_loop1`
   `pc + mldsa87_polyz_pack_loop1` PZ87_INV THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;

    (*** Initialization, saving the return address and the stack guard ***)

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
    CHUNK_INPUT_TAC `x:num->int32` 2 THEN
    ARM_STEPS_TAC EXEC (1--18) THEN
    SUBGOAL_THEN `~(640 = 5 * i + 5)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    CHUNK_FULL_FINAL_NE_TAC mld_polyz_pack_19 `x:num->int32`;

    (*** The last iteration, the stores after the loop, the call of ***)
    (*** mld_zeroize_5, the check of the stack guard and the return ***)

    REWRITE_TAC[] THEN FULL_INIT_TAC THEN
    MAP_EVERY (fun k ->
      let kt = mk_small_numeral k in
      FIRST_ASSUM(fun th ->
        if is_forall(concl th) && free_in `x:num->int32` (concl th) &&
           free_in `a:int64` (concl th)
        then MP_TAC(SPEC kt th) THEN CONV_TAC NUM_REDUCE_CONV THEN
             REWRITE_TAC[] THEN DISCH_TAC
        else failwith "input"))
      [254; 255] THEN
    ARM_STEPS_TAC EXEC (1--27) THEN
    FIRST_X_ASSUM(fun th ->
      if can (term_match [] `read (memory :> bytes16 a) s = v`) (concl th)
      then STRIP_ASSUME_TAC
            (CONV_RULE(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
              (CONV_RULE(READ_MEMORY_SPLIT_CONV 1) th))
      else failwith "bytes16") THEN
    FULL_CALL_TAC mldsa_native_libmldsa_gcc12_Os_mc EXEC "H_ZERO"
     [`read X0 s`; `16`; `pc:num`; `read SP s`; `read X30 s`]
     PZ87_ALLOWED 28 THEN
    ARM_STEPS_TAC EXEC (29--29) THEN
    MLKEM_NATIVE_ADRP_TAC THEN
    ARM_STEPS_TAC EXEC (30--37) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PZ_LAST5 THEN CONJ_TAC THENL
       [FIRST_ASSUM(MATCH_ACCEPT_TAC o
          CONV_RULE(ONCE_DEPTH_CONV NUM_MULT_CONV));
        REPEAT CONJ_TAC THEN
        REWRITE_TAC[mld_polyz_pack_19] THEN
        CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
        CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN REWRITE_TAC[] THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NUM_RED_CONV) THEN
        REWRITE_TAC[ADD_CLAUSES] THEN APP_BLAST_TAC `x:num->int32`];
      DISCHARGE_SAFETY_PROPERTY_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Correctness, and constant time and memory safety alone.                   *)
(* ------------------------------------------------------------------------- *)

let MLDSA_NATIVE_POLYZ_PACK_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT = prove
 (MLDSA_NATIVE_POLYZ_PACK_87_GCC12_OS_IMAGE_SUBROUTINE_CORRECT_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> CORRECT_OF_FULL_TAC
    (MP (SPEC_ALL
       MLDSA_NATIVE_POLYZ_PACK_87_GCC12_OS_IMAGE_SUBROUTINE_FULL) th)));;

let MLDSA_NATIVE_POLYZ_PACK_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE = prove
 (MLDSA_NATIVE_POLYZ_PACK_87_GCC12_OS_IMAGE_SUBROUTINE_SAFE_STMT,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> SAFE_OF_FULL_TAC
    (MP (SPEC_ALL
       MLDSA_NATIVE_POLYZ_PACK_87_GCC12_OS_IMAGE_SUBROUTINE_FULL) th)));;
